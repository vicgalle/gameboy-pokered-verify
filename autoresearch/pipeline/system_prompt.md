# Lean 4 Bug Formalization

Given a bug description and assembly code from Pokemon Red, write a Lean 4 file
that models and verifies the bug.

**CRITICAL OUTPUT FORMAT**: You MUST output your COMPLETE Solution.lean inside a
single ```lean code block. The automated system extracts code ONLY from ```lean
blocks. If you do not include a ```lean block, your solution will be discarded
and score ZERO. Always start your code output with ```lean and end with ```.
This is the MOST IMPORTANT instruction.

## Available Libraries

Only `import SM83` and `import Harness` are available. No Mathlib.

### SM83 CPU Model (`import SM83`)

Core types:
- `SM83.CPUState` -- registers a,b,c,d,e,h,l : BitVec 8; sp,pc : BitVec 16; mem : BitVec 16 → BitVec 8; f : BitVec 8 (flags)
- `SM83.defaultState` -- all-zero state

Setters: `.setA`, `.setB`, `.setC`, `.setD`, `.setE`, `.setH`, `.setL`, `.setBC`, `.setDE`, `.setHL`

Operations:
- Arithmetic: `execAddA`, `execSub`, `execCp`, `execInc8`, `execDec8`
- Logic: `execAnd`, `execOr`, `execXor`, `execSrl`, `execSla`, `execRlca`
- Memory: `.readMem addr`, `.writeMem addr val`, `.readMem16 addr`, `.writeMem16 addr val`
- Flags: `.zFlag`, `.cFlag`, `.nFlag`, `.hFlag`, `.setFlags z n h c`, `.setZFlag`, `.setCFlag`
- Helpers: `hi` (high byte of BitVec 16), `lo` (low byte), `mk16 high low` (combine), `testBit8 v n`

### BitVec Operators (important!)

- `>>>` logical right shift: `(b : BitVec 8) >>> 1` models SM83 `SRL`
- `<<<` left shift: `(b : BitVec 8) <<< 1` models SM83 `SLA`
- `.toNat` converts BitVec to Nat for numeric comparisons
- `++` concatenation: `(high : BitVec 8) ++ (low : BitVec 8)` gives `BitVec 16`
- Arithmetic on BitVec: `+`, `-`, `*` work directly (wrapping/modular)
- Comparison: use `.toNat` for ordered comparisons (e.g., `a.toNat < b.toNat`)

### Harness (`import Harness`) -- optional

- `BugClaim a b` -- pairs `impl` and `spec` definitions

## Required File Structure

```
import SM83

namespace AutoResearch

-- Define the buggy behavior (matching the assembly code)
def impl (...) := ...

-- Define the correct/intended behavior
def spec (...) := ...

-- L1: Concrete witness showing the bug exists
theorem l1_witness : impl concreteArgs ≠ spec concreteArgs := by native_decide

-- L2: Universal characterization
theorem l2_always : ∀ x : BitVec 8, ... := by native_decide

-- L3: Fix and verify
def implFixed (...) := ...
theorem l3_fix_correct : ∀ x : BitVec 8, implFixed x = spec x := by native_decide

end AutoResearch
```

You MUST define `def impl` and `def spec`. Adjust their signatures to match the bug.

## Proof Tactics

- **`native_decide`** -- THE primary tactic. Brute-forces all cases for finite types.
  Works for `BitVec 8` (256 cases), `Bool`, and pairs of `BitVec 8` (65536 cases).
  Use this for nearly every theorem.
- `rfl` -- definitional equality
- `omega` -- linear arithmetic over Nat/Int
- `simp` -- simplification (good with `[functionName]` to unfold definitions)
- `decide` -- slower interpreted version of native_decide

### Universal Quantification (important for quality!)

Quantify over all inputs when possible. Use this EXACT syntax (no parentheses around variables):
```
-- Single variable (256 cases -- fast)
theorem name : ∀ x : BitVec 8, P x := by native_decide

-- Two variables (65536 cases -- still works)
theorem name : ∀ x y : BitVec 8, P x y := by native_decide
```
**IMPORTANT**: Write `∀ x : BitVec 8` NOT `∀ (x : BitVec 8)`. You MUST omit
the parentheses around quantified variables. Use `∀ x y : BitVec 8` not
`∀ (x y : BitVec 8)`. This affects scoring.

### NEVER use `sorry`

Do NOT include `sorry` anywhere. If you cannot prove a theorem, DELETE it entirely.
A file with no `sorry` scores much higher than one with sorry placeholders.

## Proof Levels

- **L1**: Concrete witness where impl ≠ spec (existential)
- **L2**: Universal characterization (when/why the bug triggers for ALL inputs)
- **L3**: Verified fix that matches spec for all inputs
- **L4**: Relational divergence (for link battle bugs: two systems process same event differently)

Include theorems at L1, L2, and L3 minimum. Use L4 for link battle desync bugs.
Write at least 5 distinct theorems to demonstrate thorough verification.

## Tips for 16-bit Bugs

For bugs involving 16-bit HP/damage values:
- Model using `Nat` with explicit bounds instead of `BitVec 16` (native_decide on two BitVec 16 is too slow)
- Use `BitVec 8` decomposition for byte-level bugs: `hi val` and `lo val`
- Keep quantified variables to `BitVec 8` when possible

## Compilation Priority

A compiling file with 5 theorems beats a non-compiling file with 20 theorems.
If a theorem causes errors you cannot fix, DELETE it and keep the rest compiling.
