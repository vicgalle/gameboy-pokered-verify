# pokered-verify

A Lean 4 formalization of the Game Boy's Sharp SM83 CPU, validated through machine-checked proofs of known bugs in [Pokemon Red](https://github.com/pret/pokered).

## What This Is

The main contribution is a **formal model of the SM83 instruction set** in Lean 4 — covering registers, flags, memory, and ~40 opcodes with semantics faithful to the hardware specification. The model is designed to be reusable for any Game Boy program analysis.

As an application, we use this model to **formally verify known bugs in Pokemon Red**: translating buggy assembly routines into Lean, proving the bugs exist, characterizing exactly when they trigger, and verifying that proposed fixes are correct. Lean's type checker is the trusted oracle — if it compiles, the proofs are valid.

## SM83 CPU Model

The core of this project is a Lean 4 formalization of the Sharp SM83, the CPU powering the original Game Boy.

### Architecture

The CPU state is modeled as a structure with all eight 8-bit registers (A, F, B, C, D, E, H, L), 16-bit SP and PC, a total memory function `BitVec 16 -> BitVec 8`, and a halt flag. Register pair accessors (BC, DE, HL, AF) and little-endian memory read/write are derived from this.

The flag register F follows the SM83 spec: bit 7 = Zero, bit 6 = Subtract, bit 5 = Half-carry, bit 4 = Carry, bits 3-0 always zero. Every arithmetic and logic opcode sets flags according to the hardware reference.

### Instruction Coverage

| Category | Opcodes | File |
|---|---|---|
| Arithmetic | ADD, ADC, SUB, SBC, CP, INC, DEC (8-bit), INC/DEC (16-bit), ADD HL | `Arithmetic.lean` |
| Logic | AND, OR, XOR, CPL, SCF, CCF | `Logic.lean` |
| Shifts & Rotates | SRL, SLA, SRA, SWAP, RLCA, RRCA, RLA, RRA | `Logic.lean` |
| Bit Operations | BIT, SET, RES | `Logic.lean` |
| Loads | LD r,r / LD r,n / LD r,[HL] / LD [HL],r / LD A,[nn] / LD [nn],A / LDI / LDD | `Load.lean` |
| Stack | PUSH, POP (BC, DE, HL, AF) | `Load.lean` |
| Control Flow | JP, JR (unconditional + NZ/Z/NC/C), CALL, RET (unconditional + conditional), JP [HL] | `Control.lean` |
| Misc | HALT, NOP, DI, EI | `Control.lean` |

### Validation

Each opcode includes `#eval` tests that run at build time, cross-referenced against the SM83 hardware specification:

```
-- ADD A, 0xFF when A = 0x01 → A = 0x00, Z=1, H=1, C=1
#eval
  let s := defaultState.setA 0x01
  let s' := execAddA s 0xFF
  (s'.a == 0x00, s'.zFlag == true, s'.hFlag == true, s'.cFlag == true)
  -- output: (true, true, true, true)
```

16 validation tests cover arithmetic (ADD, SUB, CP, INC, DEC with edge cases like overflow and zero) and logic (SRL, SLA, AND, XOR, SWAP, BIT) including flag behavior.

## Application: Pokemon Red Bug Verification

As a demonstration of the CPU model, we formally verify known bugs from the [pret/pokered](https://github.com/pret/pokered) disassembly.

### Focus Energy Critical Hit Bug

Focus Energy is supposed to **quadruple** the critical hit rate. Instead, it **halves** it — the assembly uses `srl b` (shift right = divide by 2) instead of two `sla b` (shift left = multiply by 4).

**Proved theorems:**

| Theorem | Statement |
|---|---|
| `focus_energy_bug` | The bug exists (witness: rate=4 gives 2 instead of 16) |
| `focus_energy_exact_characterization` | Bug affects all nonzero rates **except** 73 |
| `focus_energy_73_coincidence` | r=73 is the unique overflow coincidence (73>>>1 = 73<<<2 = 36) |
| `focus_energy_wrong_practical` | Bug always manifests for practical game rates (1..64) |
| `focus_energy_makes_crits_worse` | Actual result < intended result for rates 1..63 |
| `focus_energy_fix_correct` | Replacing `srl` with two `sla` matches the spec for all inputs |
| `focus_energy_cpu_bug` | Bug reproduces at the full SM83 CPU model level |

**Discovery via formal verification:** The original analysis claimed the bug affects *all* nonzero crit rates. Lean's type checker rejected this — `native_decide` found that rate=73 is a unique overflow coincidence where `73 >>> 1 = 36 = (73 <<< 2) mod 256`. This is exactly the kind of subtle insight that formal verification catches and informal reasoning misses.

### BugClaim Harness

The `Harness.BugClaim` structure defines a reusable contract for verified bugs:

- `impl`: the buggy code, translated from assembly
- `spec`: the intended behavior
- `BugWitness`: a concrete input where impl diverges from spec (L1)
- `BugFix`: a replacement that matches spec for all inputs (L3)

Difficulty levels range from L1 (concrete witness) through L4 (relational/desync proofs).

### Target Bugs

| # | Bug | Category | Status |
|---|---|---|---|
| 1 | Focus Energy wrong shift | Wrong bitwise op | Verified |
| 2 | 1/256 accuracy miss | Off-by-one | Planned |
| 3 | 1/256 crit miss | Off-by-one | Planned |
| 4 | Substitute 0 HP | Arithmetic underflow | Planned |
| 5 | Heal overflow at 255/511 | Integer truncation | Planned |
| 6 | CooltrainerF AI always switches | Dead code | Planned |
| 7 | Blaine AI Super Potion | Missing precondition | Planned |
| 8 | Psywave link desync | Symmetry violation | Planned |
| 9 | Counter damage persists | Stale state | Planned |
| 10 | Reflect/Light Screen overflow | Arithmetic overflow | Planned |

## Project Structure

```
pokered-verify/
├── SM83/                          # SM83 CPU formalization (main contribution)
│   ├── Basic.lean                 # BitVec helpers, bit/nibble ops
│   ├── State.lean                 # CPUState: registers, memory, flags
│   ├── Flags.lean                 # Z/N/H/C flag semantics
│   ├── Memory.lean                # Memory read/write, stack ops
│   ├── Arithmetic.lean            # ADD, SUB, INC, DEC, CP (+16-bit)
│   ├── Logic.lean                 # AND, OR, XOR, shifts, BIT/SET/RES
│   ├── Load.lean                  # LD variants, PUSH/POP
│   └── Control.lean               # JP, JR, CALL, RET, conditions
├── PokeredBugs/                   # Application: verified pokered bugs
│   └── Proofs/
│       └── FocusEnergy.lean
├── Harness/
│   └── BugClaim.lean              # Structured type for bug claims
├── lakefile.toml
└── lean-toolchain                 # Lean 4.28.0
```

## Building

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).

```sh
lake build SM83 PokeredBugs Harness
```

All 33 build jobs should complete with no errors. Validation tests run automatically during the build.

## License

This project references the [pret/pokered](https://github.com/pret/pokered) disassembly for bug analysis. The Lean formalization and proofs are original work.
