# Lean 4 Bug Formalization

Given a bug description from Pokemon Red, write a Lean 4 file
that models and verifies the bug. You will NOT receive assembly code —
formalize based on the natural-language description alone.

## Available Libraries

Only `import SM83` and `import Harness` are available. No Mathlib.

### SM83 CPU Model (`import SM83`)

- `SM83.CPUState` -- registers (a,b,c,d,e,h,l : BitVec 8), SP/PC (BitVec 16), mem, flags
- `SM83.defaultState` -- zero-initialized state
- Setters: `.setA`, `.setB`, `.setC`, `.setD`, `.setE`, `.setH`, `.setL`
- Pair setters: `.setBC`, `.setDE`, `.setHL`
- Pair getters: `.bc`, `.de`, `.hl` (all BitVec 16)
- Arithmetic: `execAddA`, `execAdcA`, `execSub`, `execSbcA`, `execCp`, `execInc8`, `execDec8`
- Logic: `execAnd`, `execOr`, `execXor`, `execSrl`, `execSla`, `execSra`, `execRlca`, `execRrca`
- Memory: `.readMem (addr : BitVec 16) : BitVec 8`, `.writeMem (addr : BitVec 16) (v : BitVec 8)`
- Memory 16: `.readMem16`, `.writeMem16` (little-endian)
- Flags: `.zFlag`, `.cFlag`, `.nFlag`, `.hFlag` (all Bool)
- Helpers: `hi (v : BitVec 16) : BitVec 8`, `lo (v : BitVec 16) : BitVec 8`, `mk16 (h l : BitVec 8) : BitVec 16`, `testBit8`
- Flag constructor: `mkFlags (z n h c : Bool) : BitVec 8`

**Important API notes:**
- `execSrl` and `execSla` return `(BitVec 8 × BitVec 8)` — (result, flags). NOT methods on CPUState.
- `execSub` and `execSbcA` are methods on CPUState: `s.execSub v` or `SM83.execSub s v`.
- `execCp` sets flags like SUB but doesn't modify A.

### Harness (`import Harness`) -- optional

- `BugClaim a b` -- pairs `impl` and `spec`

## Types

- `BitVec 8` -- byte values. Use for bitwise bugs.
- `BitVec 16` -- 16-bit values
- `Nat` -- natural numbers. Use for arithmetic/logic bugs (simpler proofs with omega).
- `Bool` -- flags

## Proof Levels

- **L1**: Concrete witness where impl != spec (use ∃)
- **L2**: Universal characterization — when/why the bug triggers (use ∀)
- **L3**: Fix that matches spec for all inputs
- **L4**: Relational — two interacting systems diverge

## Tactics — CRITICAL

- `native_decide` -- **THE power tactic.** Brute-force over all inputs for finite types.
  Works for `BitVec 8` (256 values), `Bool`, small `Fin n`.
  Use with the HAVE pattern (see worked example below).
- `decide` -- interpreted version of native_decide (slower, same scope)
- `rfl` -- definitional equality
- `omega` -- linear arithmetic over `Nat`/`Int`. Great with `Nat`-based models.
- `simp` -- simplification. Use `simp [functionName]` to unfold definitions.
- `constructor` -- split ∧ goals. `intro` to introduce hypotheses.

### The native_decide universal pattern

For universally quantified theorems over `BitVec 8`, use this pattern:

```lean
theorem my_theorem (x : BitVec 8) : someProperty x := by
  have := (by native_decide : ∀ v : BitVec 8, someProperty v)
  exact this x
```

This works because `BitVec 8` has only 256 values — Lean can check all of them.
For multiple `BitVec 8` arguments, nest: `∀ a b : BitVec 8, ...`

**WARNING**: `native_decide` does NOT work if the goal has free variables that are NOT
`BitVec 8` (e.g., a `CPUState` in scope). You must bind all variables inside the `have`.

### Universal quantification syntax

When writing `∀` statements, use `∀ x : Type, ...` (no parentheses around the binder):
- ✅ `∀ x : BitVec 8, P x`
- ✅ `∀ d : Nat, P d`  
- ❌ `∀ (x : BitVec 8), P x` — avoid this form

## Worked Example

Here is a complete, compiling Lean 4 file modeling a bitwise bug:

```lean
import SM83

namespace AutoResearch

-- Bug: srl divides by 2, but sla multiplies by 2
-- Using srl where sla was intended quarters the rate

-- MUST be named exactly `impl` and `spec` (no suffixes!)
def impl (x : BitVec 8) : BitVec 8 := x >>> 1  -- buggy: shift right
def spec (x : BitVec 8) : BitVec 8 := x <<< 1  -- intended: shift left

-- L1: Concrete witness
theorem bug_exists : ∃ x, impl x ≠ spec x := ⟨4, by native_decide⟩

-- L2: Universal — use `∀ x : Type` syntax (no parens around binder)
theorem always_wrong : ∀ x : BitVec 8, x.toNat ≥ 2 → impl x < spec x := by
  have := (by native_decide : ∀ v : BitVec 8, v.toNat ≥ 2 → (v >>> 1) < (v <<< 1))
  exact this

-- L3: Fix
def fix (x : BitVec 8) : BitVec 8 := x <<< 1

theorem fix_correct : ∀ x : BitVec 8, fix x = spec x := by
  intro x; rfl

end AutoResearch
```

## Output Rules

1. Provide a COMPLETE `Solution.lean` inside a single ```lean block.
2. Use `namespace AutoResearch`.
3. **MANDATORY naming**: Your main buggy function MUST be named exactly `def impl` and your intended function MUST be named exactly `def spec`. Do NOT use suffixed names like `def impl_focus_energy` or `def spec_is_full` — the grader requires exactly `def impl` and `def spec`. You may define additional helper functions with other names, but `impl` and `spec` must exist.
4. **NEVER use `sorry`**. If a proof is too hard, write a simpler theorem you CAN prove.
   A sorry-free file with 3 simple theorems scores higher than 10 theorems with sorry.
5. Prove at least 5 theorems for maximum score. Include L1 (∃ witness), L2 (∀ characterization), and L3 (fix).
6. Use keywords in theorem names: "exists", "always"/"iff"/"forall" for L2, "fix"/"correct" for L3, "desync"/"player"/"enemy" for L4.
7. When using `Nat` for models, prefer `omega` for proofs. When using `BitVec 8`, prefer `native_decide`.
8. For bugs without bitwise operations, model with `Nat` and prove with `omega`/`simp` — it's often simpler.
