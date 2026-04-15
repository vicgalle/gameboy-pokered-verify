# Three-Way Analysis: Sonnet Full vs Sonnet Minimal vs Opus Minimal

**Date**: 2026-04-13
**Conditions**:
- **Sonnet full** (`batch_01`): Sonnet, full bug description (gameplay + root cause + file pointers)
- **Sonnet min** (`batch_minimal`): Sonnet, gameplay description only
- **Opus min** (`batch_minimal_opus`): Opus, gameplay description only

All runs use the same SM83 infrastructure, same pokered codebase, same 5 bugs.

## Summary Table

| # | Bug | | Sonnet full | Sonnet min | Opus min | Ground Truth |
|---|---|---|---|---|---|---|
| 1 | Focus Energy | compiles | yes | yes | yes | yes |
| | | theorems | 8 | 18 | 8 | 10 |
| | | levels | L1,L2,L3 | L1,L2,L3 | L1,L2,L3 | L1,L2,L3 |
| | | LOC | 187 | 222 | 158 | 195 |
| | | time | ~9m | ~8m | ~10m | -- |
| | | iters | 2 | 2 | 3 | -- |
| 2 | 1/256 Accuracy | compiles | yes | yes | yes | yes |
| | | theorems | 13 | 4 | **17** | 12 |
| | | levels | L1,L2,L3 | L1,L2,L3 | L1,L2,L3 | L1,L2,L3 |
| | | LOC | 195 | 133 | 298 | 182 |
| | | time | ~9m | ~13m | ~11m | -- |
| | | iters | 2 | 2 | 3 | -- |
| 3 | Blaine AI | compiles | yes | yes | yes | yes |
| | | theorems | 8 | 7 | **13** | 12 |
| | | levels | L1,L2,L3 | L1,L2,L3 | L1,L2,L3 | L1,L2,L3 |
| | | LOC | 182 | 182 | 227 | 205 |
| | | time | ~12m | ~5m | ~6m | -- |
| | | iters | 3 | 2 | 3 | -- |
| 4 | Heal Overflow | compiles | yes | yes | yes | yes |
| | | theorems | 17 | 11 | 13 | 11 |
| | | levels | L1,L2,L3 | L1,L2,L3 | L1,L2,L3 | L1,L2,L3 |
| | | LOC | 328 | 174 | 202 | 143 |
| | | time | ~15m | ~12m | ~16m | -- |
| | | iters | 2 | 2 | 3 | -- |
| 5 | Psywave Desync | compiles | yes | yes | yes | yes |
| | | theorems | 14 | 12 | 15 | 10 |
| | | levels | L1,L2,L3,L4 | L1,L2,L3,L4 | L1,L2,L3,L4 | L1,L2,L3,L4 |
| | | LOC | 312 | 260 | 245 | 227 |
| | | time | ~8m | ~21m | ~10m | -- |
| | | iters | 2 | 3 | 3 | -- |

## Aggregate Totals

| Metric | Sonnet full | Sonnet min | Opus min | Ground Truth |
|---|---|---|---|---|
| Compilation rate | 5/5 (100%) | 5/5 (100%) | 5/5 (100%) | -- |
| Level coverage | 100% | 100% | 100% | -- |
| Total theorems | 60 | 52 | **66** | 55 |
| Total LOC | 1204 | 971 | 1130 | 952 |
| Total time | ~53m | ~59m | ~53m | -- |
| Mean iters | 2.2 | 2.2 | 3.0 | -- |

## Key Finding: Opus Minimal Outperforms All Others on Theorem Count

Opus in minimal mode produced **66 theorems** — more than Sonnet full (60), Sonnet
minimal (52), and even the human ground truth (55). It achieved this while having
the same information as Sonnet minimal (gameplay description only, no root cause
or file pointers). All three conditions maintain 100% compilation and 100% level
coverage.

## Per-Bug Analysis

### Bug 1 — Focus Energy

| | Sonnet full | Sonnet min | Opus min |
|---|---|---|---|
| Theorems | 8 | 18 | 8 |
| LOC | 187 | 222 | 158 |
| Time | ~9m | ~8m | ~10m |

All three independently found the `srl`/`sla` mismatch in `CriticalHitTest`. Opus
produced a notably different model: it includes `sla_cap` (modeling the overflow
cap at 0xFF after sla) and models the `focusEnergy` parameter as a `Bool` toggle
rather than separate functions. This is arguably the most faithful model of the
assembly's actual branching structure. Opus also proved `fix_fe_beneficial` — that
the fix makes Focus Energy actually helpful (inverse ordering) — a result neither
Sonnet run included.

However, Opus produced fewer theorems (8) because it didn't generate private helper
lemmas. Sonnet minimal's 18 theorems include 8 private helpers.

### Bug 2 — 1/256 Accuracy

| | Sonnet full | Sonnet min | Opus min |
|---|---|---|---|
| Theorems | 13 | 4 | **17** |
| LOC | 195 | 133 | 298 |
| Time | ~9m | ~13m | ~11m |

**Opus dominates here.** It produced the richest formalization across all three
conditions with 17 theorems. Notably, Opus:

- Modeled both MoveHitTest and CriticalHitTest separately (like Sonnet full)
- Built `rlc3` with a correct implementation and proved `rlc3_injective`
- Proved `rlc_period_8` — that 8 rotations are the identity (a result no other
  run discovered)
- Added **CPU-level verification**: `cpuAccuracyCheck` using `SM83.execCp` and
  `cpuCritCheck` using `SM83.execRlca`, with theorems proving they match the
  high-level model (`cpu_accuracy_eq_impl`, `cpu_crit_eq_impl`)
- Proposed a concrete assembly-level fix (`cp b; jr c, .hit; jr z, .hit`) and
  verified it CPU-level (`cpuAccuracyFix` uses `cFlag || zFlag`)

The CPU-level proofs are unique to Opus — neither Sonnet run attempted them.
This is the closest any agent came to our ground truth's `sm83_accuracy_matches_model`.

Sonnet minimal produced only 4 theorems for this bug — the biggest performance
gap in the dataset. The root-cause hint clearly helps Sonnet but Opus doesn't
need it.

### Bug 3 — Blaine AI

| | Sonnet full | Sonnet min | Opus min |
|---|---|---|---|
| Theorems | 8 | 7 | **13** |
| LOC | 182 | 182 | 227 |
| Time | ~12m | ~5m | ~6m |

Opus produced the most comprehensive Blaine formalization: 13 theorems matching
our ground truth (12). It combined both approaches seen in the Sonnet runs:

- Abstract Boolean model (`impl`, `spec`, `fix`) with full characterization
- Concrete numeric model (`blaineAI_numeric`, `correctAI_numeric`) with specific
  HP/RNG witnesses
- BugClaim harness with witness and fix

The dual-model approach (abstract + concrete) is unique to Opus and provides
both clean reasoning and concrete grounding. Opus also computed the actual
threshold value (`rng_threshold_calc: 25 * 255 / 100 + 1 = 64`).

### Bug 4 — Heal Overflow

| | Sonnet full | Sonnet min | Opus min |
|---|---|---|---|
| Theorems | 17 | 11 | 13 |
| LOC | 328 | 174 | 202 |
| Time | ~15m | ~12m | ~16m |

All three achieved L1-L3 with strong characterizations. Opus's unique contribution:

- Used `bv_decide` tactic (from `Std.Tactic.BVDecide`) for the main
  `false_positive_iff` theorem — a more elegant approach than Sonnet full's
  manual case-splitting with 7 helper lemmas
- Added 16-bit wrappers (`buggyFullCheck16`, `correctFullCheck16`) using `SM83.hi`
  and `SM83.lo` for integration with the CPU model
- Proved gap values explicitly: `bug_gap_255`, `bug_gap_511`, `bug_gap_767`
  compute the numeric gap and confirm the bug triggers
- Proposed a concrete assembly-level fix using `sub`/`sub`/`or` (different from
  the simple equality check other runs used) and verified it

The `bv_decide` usage is notable — it's a more modern Lean 4 approach than the
exhaustive `native_decide` pattern used everywhere else.

### Bug 5 — Psywave Desync

| | Sonnet full | Sonnet min | Opus min |
|---|---|---|---|
| Theorems | 14 | 12 | **15** |
| LOC | 312 | 260 | 245 |
| Time | ~8m | ~21m | ~10m |

All three achieved L4 (relational). Opus's formalization:

- Uses `BitVec 8` for random values (vs `Nat`/`List Nat` in Sonnet runs) — more
  faithful to the assembly
- Proved `bug_characterization` as a universal biconditional over all `BitVec 8`
  values via `native_decide` — cleaner than Sonnet minimal's structural induction
- Added `consumeUntil_disagree_on_zero`: a **generic** theorem about any two
  acceptance predicates that disagree on zero — an abstraction neither Sonnet run
  attempted
- Proved `maxDamage_ge_three` for game-valid levels and `level_one_degenerate`
  (at level 1, the player loop would hang)

Opus also recovered from the minimal description much faster than Sonnet minimal
(~10m vs ~21m).

## Model and Proof Strategy Comparison

### Modeling Philosophy

| Bug | Sonnet full | Sonnet min | Opus min |
|---|---|---|---|
| 1 | BitVec 8, separate fns | BitVec 8 + 8 private helpers | BitVec 8, Bool toggle, `sla_cap` |
| 2 | BitVec 8, rlc3 | BitVec 8, manual trichotomy | BitVec 8, rlc3 + **CPU-level** |
| 3 | Nat (rand, HP) | Abstract Bool struct | **Both**: Bool abstract + Nat concrete |
| 4 | BitVec 8 x4, 7 helpers | BitVec 8 x4, 1 key lemma | BitVec 8 x4, **bv_decide** + 16-bit |
| 5 | List Nat, predicates | Nat->List Nat->Option Nat | **BitVec 8** lists, `consumeUntil` |

Opus consistently builds the most faithful-to-assembly models while maintaining
clean proof structure. The dual-level approach (high-level + CPU-level for Bug 2,
abstract + concrete for Bug 3) is a distinctive Opus pattern.

### Tactic Usage

| Tactic | Sonnet full | Sonnet min | Opus min |
|---|---|---|---|
| `native_decide` | dominant | moderate | dominant |
| `bv_decide` | not used | not used | **Bug 4** |
| `decide` | rare | moderate | moderate |
| `induction` | Bug 5 | Bug 5 (deep) | not used |
| CPU-level SM83 | not used | not used | **Bug 2** |
| manual case split | rare | Bug 2, 5 | rare |

Opus's use of `bv_decide` and CPU-level SM83 instructions are unique capabilities
not seen in either Sonnet run.

### Unique Results by Condition

**Only Sonnet full produced**:
- Heal Overflow: 7 private BitVec ordering lemmas (most verbose characterization)

**Only Sonnet minimal produced**:
- 1/256: Manual `Nat.lt_trichotomy` proof of `bug_iff` (most insightful proof)
- Psywave: Structural induction proof of `desync_implies_enemy_zero` (deepest proof)

**Only Opus minimal produced**:
- 1/256: CPU-level verification (`cpuAccuracyCheck`, `cpuCritCheck`, `cpuAccuracyFix`)
- 1/256: `rlc_period_8` — rotation has period 8
- Blaine: Dual abstract + concrete model with `rng_threshold_calc`
- Heal Overflow: `bv_decide` usage; 16-bit wrappers; assembly-level `sub/sub/or` fix
- Psywave: `consumeUntil_disagree_on_zero` — generic desync theorem
- Psywave: `level_one_degenerate` — level 1 edge case analysis

## Time and Iteration Comparison

| Bug | Sonnet full | Sonnet min | Opus min |
|---|---|---|---|
| 1 Focus Energy | ~9m / 2 iter | ~8m / 2 iter | ~10m / 3 iter |
| 2 1/256 | ~9m / 2 iter | ~13m / 2 iter | ~11m / 3 iter |
| 3 Blaine AI | ~12m / 3 iter | ~5m / 2 iter | ~6m / 3 iter |
| 4 Heal Overflow | ~15m / 2 iter | ~12m / 2 iter | ~16m / 3 iter |
| 5 Psywave | ~8m / 2 iter | ~21m / 3 iter | ~10m / 3 iter |
| **Total** | **~53m / 2.2** | **~59m / 2.2** | **~53m / 3.0** |

Opus consistently takes 3 iterations (vs Sonnet's 2-2.2), suggesting it attempts
more ambitious proofs that require refinement. Despite this, total wall-clock time
matches Sonnet full (~53m each), indicating Opus converges faster per iteration.

The Psywave result is striking: Opus takes ~10m in minimal mode where Sonnet
minimal took ~21m — Opus recovers from minimal descriptions much more efficiently
on the hardest (L4 relational) bug.

## Lean Checker Iterations (lake build cycles)

Self-reported by the agent in results.md. Each iteration = one `lake build` attempt.

| Bug | Sonnet full | Sonnet min | Opus min |
|---|---|---|---|
| 1 Focus Energy | 2 | 3 | **1** |
| 2 1/256 Accuracy | 2 | 3 | **1** |
| 3 Blaine AI | 2 | **1** | **1** |
| 4 Heal Overflow | 3 | 3 | 3 |
| 5 Psywave Desync | **1** | 5 | 2 |
| **Total** | **10** | **15** | **8** |
| **Mean** | **2.0** | **3.0** | **1.6** |

### Error patterns by condition

**Sonnet full** (10 iterations, mean 2.0):
- Bug 1: `native_decide` with free variables (3 errors). Fixed with `have h : forall x, ... := by native_decide; exact h b` pattern.
- Bug 2: Tried `Finset.univ.filter` (not available without Mathlib, 9 errors). Restructured away from set-based counting.
- Bug 3: Unused variable warnings + `omega` failure on `BLAINE_THRESHOLD` constant.
- Bug 4: Unknown identifiers, type mismatches, substitution issues (6 errors, then 3).
- Bug 5: **Compiled on first attempt** — the easiest for Sonnet full.

**Sonnet minimal** (15 iterations, mean 3.0):
- Bug 1: `native_decide` free variables, then a false theorem (`bug_iff_speed_ge4` should be `ge2`).
- Bug 2: Broken proof structure, `BitVec.toNat_inj` unavailable, needed custom `bv_toNat_eq` helper.
- Bug 3: **Compiled on first attempt** — the abstract Bool model is trivially decidable.
- Bug 4: Wrong witness value, `omega` failing on BitVec, `beq`/`Prop` conversion issues.
- Bug 5: **5 iterations** — doc comment backticks, `lemma` keyword, `split_ifs` unknown tactic, spurious `rfl`. The most iterations in any run.

**Opus minimal** (8 iterations, mean 1.6):
- Bug 1: **First attempt** — all 8 theorems compiled.
- Bug 2: **First attempt** — 17 theorems including CPU-level proofs compiled.
- Bug 3: **First attempt** — dual-model (abstract + concrete) compiled.
- Bug 4: 3 iterations — needed `import Std.Tactic.BVDecide`, missing `Decidable` instances, wrong lemma names.
- Bug 5: 2 iterations — import placement error + false overflow theorem.

### Analysis

**Opus has the best first-attempt success rate: 3/5 bugs compiled on the first try** (Bugs 1, 2, 3). Sonnet full had 1/5 (Bug 5), Sonnet minimal had 1/5 (Bug 3).

The error types differ qualitatively:
- **Sonnet** struggles with tactic availability (`Finset`, `split_ifs`, `BitVec.toNat_inj`) and Lean 4 idioms (`native_decide` free variables, `lemma` vs `theorem`).
- **Opus** mostly gets syntax and imports right on the first try, but when it fails (Bug 4), it's on discovering non-obvious imports (`Std.Tactic.BVDecide`).

The total compile iteration count creates a clear ranking: **Opus (8) < Sonnet full (10) < Sonnet min (15)**. Removing information hurts Sonnet's compile success (+50% more iterations) but barely affects Opus.

## Conclusions

1. **Opus minimal is the strongest condition overall.** 66 theorems vs 60 (Sonnet
   full), 52 (Sonnet min), and 55 (ground truth). It achieves this with only
   gameplay-level descriptions — no root cause hints, no file pointers.

2. **Opus produces qualitatively different proofs.** CPU-level verification,
   `bv_decide` usage, dual-model approach, and generic theorems are unique to Opus.
   These represent deeper engagement with the formalization infrastructure.

3. **The model hierarchy is**: Opus min > Sonnet full > Ground Truth > Sonnet min
   on theorem count. All four achieve identical level coverage (100%).

4. **Information hints help Sonnet more than Opus.** Sonnet drops from 60 to 52
   theorems (-13%) when hints are removed; Opus produces 66 theorems without hints.
   The biggest gap is Bug 2 (1/256): Sonnet min gets 4 theorems while Opus min
   gets 17 — Opus independently discovers `rlc3`, CPU-level proofs, and rotation
   properties.

5. **Opus recovers from minimal descriptions faster on hard bugs.** Psywave
   (the L4 relational bug) takes Opus ~10m vs Sonnet ~21m in minimal mode.

6. **For the paper, the three-condition design tells a rich story**:
   - Sonnet full: baseline for what's achievable with moderate guidance
   - Sonnet min: ablation showing the cost of removing hints
   - Opus min: demonstrates that a stronger model compensates for less information
