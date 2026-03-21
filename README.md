# gameboy-pokered-verify

[![Lean Action CI](https://github.com/vicgalle/gameboy-pokered-verify/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vicgalle/gameboy-pokered-verify/actions/workflows/lean_action_ci.yml)

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

**The bug:** In `CriticalHitTest`, the crit rate `b` starts as `base_speed >>> 1` (always ≤ 127). The Focus Energy branch should do `sla b` (double it back), but instead does `srl b` (halves it again) — quartering the rate instead of restoring it.

```
                        With Focus Energy (bug)     Without Focus Energy
b = base_speed / 2      73 → srl → 36              73 → srl → 36
Focus Energy branch      36 → srl → 18 (BUG)        36 → sla → 72
```

**Proved theorems:**

| Theorem | Statement |
|---|---|
| `focus_energy_bug` | The bug exists (witness: base_speed=4) |
| `focus_energy_always_wrong` | Bug is unconditionally wrong for all base speeds ≥ 2 |
| `focus_energy_reduces_rate` | Buggy result ≤ correct result for all inputs |
| `focus_energy_strictly_worse` | Buggy result < correct result for base speeds ≥ 4 |
| `focus_energy_quarter_rate` | Correct result is at least 4x the buggy result (for base speeds ≥ 4) |
| `focus_energy_fix_correct` | Replacing `srl` with `sla` matches the no-Focus-Energy path |
| `crit_input_bounded` | After initial `srl`, input is always ≤ 127 (no overflow possible) |
| `focus_energy_cpu_bug` | Bug reproduces at the full SM83 opcode level |

**Modeling lesson:** An early naive model (treating the bug as `x >>> 1` vs `x <<< 2` on raw 8-bit values) produced a false "discovery" that rate=73 was an overflow coincidence. The real assembly bounds the input to ≤ 127 via an initial `srl`, making overflow impossible. Lean caught the error in the naive model — but the fix was to model the assembly more faithfully, not to weaken the theorem. This highlights that **formal verification is only as good as the model**: Lean guarantees your proofs are correct, but cannot guarantee your model matches the real code.

### Blaine AI Super Potion Bug

**The bug:** Blaine's AI calls `AIUseSuperPotion` without first checking if his Pokemon's HP is low enough to need healing. Every other healing trainer (Erika, Lorelei, Agatha, Sabrina, Rival) calls `AICheckIfHPBelowFraction` first.

```asm
BlaineAI:                          ErikaAI:
  cp 25 percent + 1                  cp 50 percent + 1
  ret nc                             ret nc
  jp AIUseSuperPotion  ; BUG!        ld a, 10
                                     call AICheckIfHPBelowFraction  ; ← HP check
                                     ret nc
                                     jp AIUseSuperPotion
```

**Proved theorems:**

| Theorem | Statement |
|---|---|
| `blaine_heals_at_full_hp` | Blaine uses Super Potion even at full HP |
| `blaine_always_heals` | Blaine's AI unconditionally heals (always returns `some`) |
| `blaine_wastes_when_healthy` | For any HP above the threshold, Blaine wastes the item |
| `full_hp_zero_gain` | At full HP, 0 HP is gained — complete waste |
| `partial_waste` | When HP is within 50 of max, less than 50 HP is gained |
| `blaine_fix_heals_when_needed` / `_skips_when_healthy` | Fixed AI heals iff HP is low |
| `blaine_unique_unconditional` | Blaine is the only trainer who heals unconditionally |

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
| 7 | Blaine AI Super Potion | Missing precondition | Verified |
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
│       ├── FocusEnergy.lean
│       └── BlaineAI.lean
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
