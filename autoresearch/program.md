# Bug Formalization Research Program

You are an autonomous research agent. Your task: given an informal description of
a known bug in the Game Boy game Pokemon Red, **formally verify** it by writing a
Lean 4 proof file that compiles and proves properties about the bug.

## Overview

Pokemon Red was written in Z80/SM83 assembly for the Game Boy. The complete
disassembly is available at `/Users/victorgallego/pokered` (the pret/pokered project).
Your job is to:

1. Read the informal bug description in `bug_description.md`
2. Find the relevant assembly code in the pokered disassembly
3. Model the buggy and correct behaviors as Lean 4 functions
4. Prove properties at increasing difficulty levels
5. Iterate until your file compiles cleanly

## Setup Checklist

Before starting, verify:
- [ ] Read `bug_description.md` to understand the bug
- [ ] Read the SM83 infrastructure (`SM83.lean`, `SM83/`) to know what's available
- [ ] Optionally read `Harness/BugClaim.lean` for the structured claim type
- [ ] Confirm `lake build` works on the empty project (compiles SM83/Harness)

**IMPORTANT**: Do NOT read any files outside this workspace except for the pokered
disassembly at `/Users/victorgallego/pokered`. Do NOT look for existing proof files
or solutions anywhere.

## Available Infrastructure

### SM83 CPU Model (`import SM83`)
A Lean 4 formalization of the Game Boy's Sharp SM83 CPU:
- `SM83.CPUState` — registers (A, B, C, D, E, F, H, L), SP, PC, memory, flags
- `SM83.defaultState` — zero-initialized CPU state
- Setters: `.setA`, `.setB`, `.setHL`, etc.
- Arithmetic: `execAdd`, `execSub`, `execInc`, `execDec`, `execCp`
- Logic: `execAnd`, `execOr`, `execXor`, `execSrl`, `execSla`, `execRlc`
- Memory: `execLd`, `execPush`, `execPop`, `readMem16`, `writeMem16`
- Control: `execJp`, `execJr`, `execCall`, `execRet`
- Flags: `.zFlag`, `.cFlag`, `.nFlag`, `.hFlag`

You can model bugs at any abstraction level:
- **High-level**: Model the arithmetic/logic directly using `BitVec`, `Nat`, `UInt16`, etc.
- **CPU-level**: Model individual SM83 instructions using `CPUState`

High-level is usually simpler and sufficient. Use CPU-level only if it adds insight.

### Bug Claim Harness (`import Harness`)
Optional structured type for bug claims:
- `BugClaim α β` — pairs an `impl` and `spec` function
- `BugWitness` — a concrete input where `impl ≠ spec`
- `BugFix` — a replacement that matches `spec` everywhere

Using the harness is optional. You can also just write standalone definitions and theorems.

### Pokered Disassembly (`/Users/victorgallego/pokered`)
The complete game source in RGBDS assembly. Key directories:
- `engine/battle/` — Battle system (damage, AI, moves, effects)
- `engine/battle/core.asm` — Core battle routines (hit test, crit, damage calc)
- `engine/battle/trainer_ai.asm` — Trainer AI logic
- `engine/battle/effects.asm` — Move effect handlers
- `data/moves/` — Move data tables
- `data/pokemon/` — Pokemon base stats
- `constants/` — Game constants and definitions
- `macros/` — Assembly macros (useful for understanding magic numbers)
- `home/` — Core engine (RNG, math, text, etc.)

Tips for searching assembly:
- Labels end with `:` (e.g., `CriticalHitTest:`)
- Comments start with `;`
- `call` invokes a subroutine, `jp`/`jr` are jumps
- `cp` sets flags for comparison (carry if a < operand)
- `ld` loads values between registers/memory

## Methodology

### Step 1: Understand the Bug
Read `bug_description.md`. Identify:
- What game mechanic is affected?
- What is the incorrect behavior?
- What should the correct behavior be?
- What kind of error is it (wrong opcode, missing check, off-by-one, etc.)?

### Step 2: Find the Assembly
Search the pokered codebase. Use `grep` to find relevant routines:
```bash
grep -rn "LabelName" /Users/victorgallego/pokered/engine/
```
Read the surrounding assembly to understand the full context. Pay attention to:
- What registers are used and how
- What branches/jumps exist
- What other routines are called
- What constants are referenced

### Step 3: Model in Lean
Write `Solution.lean` with:

```lean
import SM83  -- and/or import Harness

namespace AutoResearch

-- Model the buggy behavior (matching the assembly)
def impl (input : ...) : ... := ...

-- Model the intended/correct behavior
def spec (input : ...) : ... := ...

-- Proofs go here...

end AutoResearch
```

Choose types carefully:
- `BitVec 8` for byte values (registers, small game values)
- `BitVec 16` for 16-bit values (addresses, HP)
- `UInt16` for game-level 16-bit quantities
- `Nat` for abstract numeric reasoning
- `Bool` for flags and conditions
- Custom structures for complex state

### Step 4: Prove Properties

Attempt proofs at increasing difficulty:

**L1 — Bug Exists** (easiest): Find a concrete witness.
```lean
theorem bug_exists : ∃ x, impl x ≠ spec x := ⟨witness, by native_decide⟩
```

**L2 — Characterization** (medium): Universal properties about when/why the bug triggers.
```lean
-- "The bug triggers iff <condition>"
theorem bug_iff (x : InputType) : impl x ≠ spec x ↔ <condition> := by ...

-- or: "The bug ALWAYS triggers for nonzero inputs"
theorem bug_always (x : InputType) (h : x ≠ 0) : impl x ≠ spec x := by ...
```

**L3 — Fix Correctness** (medium): Show a fix matches the spec.
```lean
def fix (x : InputType) : OutputType := ...
theorem fix_correct (x : InputType) : fix x = spec x := by ...
```

**L4 — Relational** (hard): For bugs involving two interacting systems (e.g., link battles).
Model both systems and prove they diverge under certain conditions.

### Step 5: Compile and Iterate

```bash
lake build
```

If there are errors:
1. Read the error message carefully — Lean's errors are precise
2. Common fixes:
   - Type mismatch: check your function signatures
   - Tactic failed: try a different proof strategy
   - Unknown identifier: check imports and namespaces
   - `native_decide` timeout: your type might be too large (use manual tactics)
3. Fix the error and re-compile
4. Repeat until clean compilation

## Proof Tactics Reference

**Automated** (Lean's kernel decides — preferred when possible):
- `native_decide` — Compiled decision procedure. Works for decidable propositions
  over small finite types. For `BitVec 8` (256 values), this brute-forces all cases.
  **This is your most powerful tool for byte-level proofs.**
- `decide` — Interpreted version of native_decide (slower but sometimes works where native_decide doesn't)
- `rfl` — Proves definitional equality (a = a, or things that reduce to the same term)

**Semi-automated**:
- `omega` — Linear arithmetic over `Nat` and `Int`. Great for inequalities.
- `simp` / `simp_all` — Simplification with lemma database
- `norm_num` — Numeric computation

**Manual** (when automation fails):
- `constructor` — Split a goal like `A ∧ B` into two subgoals
- `intro` — Introduce a hypothesis for `∀` or `→`
- `exact ⟨witness, proof⟩` — Provide exact proof term
- `have h := ...` — Introduce intermediate fact
- `cases` / `match` — Case split on a value
- `induction` — Structural induction (for recursive functions)
- `unfold` — Unfold a definition

**Pattern for universal BitVec 8 proofs**:
```lean
theorem my_theorem (x : BitVec 8) : P x := by
  have := (by native_decide : ∀ x : BitVec 8, P x)
  exact this x
```
This works because BitVec 8 is finite (256 values) and Lean can check all of them.

**Warning**: `native_decide` does NOT work for `UInt16` or larger types (65536+ values).
For those, use `omega`, `simp`, or manual reasoning.

## Experiment Loop

Follow this loop until your file compiles with maximum proof coverage:

```
REPEAT (max 20 iterations):
  1. Write or modify Solution.lean
  2. Run: lake build 2>&1
  3. If COMPILES:
     - Check which levels you've achieved (L1, L2, L3, L4)
     - If you can add more theorems at higher levels, go to step 1
     - If satisfied or stuck on higher levels, STOP — record results
  4. If ERRORS:
     - Read error messages
     - Fix the specific issues
     - Go to step 2
  5. If STUCK (same error 3+ times):
     - Try a fundamentally different modeling approach
     - Simplify: drop to a lower abstraction level
     - If still stuck after 5 attempts at alternatives, STOP with what compiles
```

## Output

When done, your `Solution.lean` should:
- Be in the `AutoResearch` namespace
- Import `SM83` (and optionally `Harness`)
- Include a module docstring explaining your approach and what you found
- Compile without errors (`lake build` succeeds)
- Prove as many levels as possible (L1 minimum, L2-L4 stretch goals)
- Include `#eval` demonstrations showing concrete bug behavior

After finishing, create a file `results.md` summarizing:
- What you found in the assembly
- How you modeled it
- What you proved (list theorems)
- What levels you achieved
- Any difficulties or interesting observations
- Number of compile iterations needed

## Important Rules

1. **No peeking**: Do NOT look for existing proofs or solutions anywhere in the filesystem
   outside this workspace and the pokered disassembly.
2. **Model fidelity**: Your `impl` function must faithfully represent what the assembly
   actually does. Don't just make something that "looks buggy" — match the real code.
3. **Start simple**: Get L1 (witness) first. Then try L2. Then L3. Don't attempt L4
   unless the bug involves two interacting systems.
4. **Commit progress**: After each successful compilation, `git add` and `git commit`
   your work so you don't lose progress.
5. **Time awareness**: If you've spent 15+ iterations without compilation, simplify
   your model drastically and prove what you can.
