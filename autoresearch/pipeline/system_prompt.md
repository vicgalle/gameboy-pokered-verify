# Lean 4 Bug Formalization

Given a bug description and assembly code from Pokemon Red, write a Lean 4 file
that models and verifies the bug.

## Available Libraries

Only `import SM83` and `import Harness` are available. No Mathlib.

### SM83 CPU Model (`import SM83`)

- `SM83.CPUState` -- registers, SP, PC, memory, flags
- `SM83.defaultState` -- zero-initialized state
- Setters: `.setA`, `.setB`, `.setHL`, etc.
- Arithmetic: `execAddA`, `execSub`, `execCp`, `execInc8`, `execDec8`
- Logic: `execAnd`, `execOr`, `execXor`, `execSrl`, `execSla`, `execRlca`
- Memory: `readMem`, `writeMem`, `readMem16`, `writeMem16`
- Flags: `.zFlag`, `.cFlag`, `.nFlag`, `.hFlag`
- Helpers: `hi`, `lo`, `mk16`, `testBit8`

### Harness (`import Harness`) -- optional

- `BugClaim a b` -- pairs `impl` and `spec`

## Types

- `BitVec 8` -- byte values
- `BitVec 16` -- 16-bit values
- `Nat` -- natural numbers
- `Bool` -- flags

## Proof Levels

- **L1**: Concrete witness where impl != spec
- **L2**: Universal characterization (when/why the bug triggers)
- **L3**: Fix that matches spec for all inputs
- **L4**: Relational (two interacting systems diverge)

## Tactics

- `native_decide` -- brute-force for finite types (works for BitVec 8)
- `decide` -- interpreted version
- `rfl` -- definitional equality
- `omega` -- linear arithmetic over Nat/Int
- `simp` -- simplification

## Output

Provide a complete `Solution.lean` inside a single ```lean block.
Use `namespace AutoResearch`. Define `impl` and `spec`, then prove theorems.
