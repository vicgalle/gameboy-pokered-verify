# Full vs Minimal Condition: Comparative Analysis

**Date**: 2026-04-13
**Model**: Claude Sonnet (both batches)
**Full condition** (`batch_01`): Title + Gameplay + Root Cause + Where to Look + Severity
**Minimal condition** (`batch_minimal`): Title + Gameplay Description only

## Side-by-Side Results

| # | Bug | Cond | Comp | Thm | Def | LOC | Levels | Time | Iters |
|---|---|---|---|---|---|---|---|---|---|
| 1 | Focus Energy | full | yes | 8 | 9 | 187 | L1,L2,L3 | ~9m | 2 |
| 1 | Focus Energy | **min** | yes | **18** | 7 | 222 | L1,L2,L3 | ~8m | 2 |
| 2 | 1/256 Accuracy | full | yes | **13** | 7 | 195 | L1,L2,L3 | ~9m | 2 |
| 2 | 1/256 Accuracy | **min** | yes | 4 | 3 | 133 | L1,L2,L3 | ~13m | 2 |
| 3 | Blaine AI | full | yes | 8 | 5 | 182 | L1,L2,L3 | ~12m | 3 |
| 3 | Blaine AI | **min** | yes | 7 | 6 | 182 | L1,L2,L3 | ~5m | 2 |
| 4 | Heal Overflow | full | yes | **17** | 3 | 328 | L1,L2,L3 | ~15m | 2 |
| 4 | Heal Overflow | **min** | yes | 11 | 3 | 174 | L1,L2,L3 | ~12m | 2 |
| 5 | Psywave Desync | full | yes | 14 | 15 | 312 | L1,L2,L3,L4 | ~8m | 2 |
| 5 | Psywave Desync | **min** | yes | 12 | 10 | 260 | L1,L2,L3,L4 | ~21m | 3 |

## Aggregate Comparison

| Metric | Full | Minimal | Ground Truth |
|---|---|---|---|
| Compilation rate | 5/5 (100%) | 5/5 (100%) | -- |
| Level coverage | 100% | 100% | -- |
| Total theorems | 60 | 52 | 55 |
| Total LOC | 1204 | 971 | 952 |
| Total time | ~53m | ~59m | -- |
| Mean iterations | 2.2 | 2.2 | -- |

## Key Finding: Minimal Matches Full on Level Coverage

**Both conditions achieve 100% compilation and 100% level coverage.** The minimal
condition — with only a gameplay-level description and no hints about root cause,
assembly location, or error type — still produced correct formalizations at all
target levels for all 5 bugs. This is the headline result.

## Per-Bug Analysis

### Bug 1 — Focus Energy

The minimal agent found the bug independently and produced **more** theorems (18 vs 8),
including 8 private helper lemmas proved by `native_decide` that establish universal
properties cleanly. It correctly identified `srl` vs `sla` in `CriticalHitTest`,
modeled the full pipeline, and proved the quarter-rate relationship — all without
being told the root cause is a wrong shift direction.

**Minimal wins**: more theorems, more systematic helper infrastructure.

### Bug 2 — 1/256 Accuracy

The full agent significantly outperformed (13 vs 4 theorems). The full description's
mention of "strict inequality" and the `cp`/`jr nc` comparison pattern appears to
have guided the agent toward a richer formalization with `rlc3` modeling and
uniqueness proofs. The minimal agent found the bug and proved the key characterization
(`bug_iff`: disagree iff `r = a`) but with a manual proof rather than `native_decide`,
and did not model the critical hit check separately.

**Full wins**: richer formalization, separate crit modeling, uniqueness proofs.

Notably, the minimal agent's `bug_iff` proof uses an explicit `Nat.lt_trichotomy`
case split with a custom `bv_toNat_eq` helper — a more manual but arguably more
insightful proof strategy than the full agent's `native_decide` brute-force.

### Bug 3 — Blaine AI

Both conditions produced similar results (8 vs 7 theorems). The minimal agent
chose a more abstract model — `AIInput` with `(randPasses : Bool, hpLow : Bool)` —
which is elegant and makes the bug characterization (`bug_iff`) trivially decidable.
The full agent used `Nat` values for rand/HP, which is more concrete but requires
`omega` reasoning.

**Tie**: different modeling philosophies, both valid. Minimal was actually faster (~5m vs ~12m).

### Bug 4 — Heal Overflow

The full agent produced more theorems (17 vs 11) and a longer, more verbose file
(328 vs 174 LOC). However, the minimal agent achieved a cleaner characterization:
`bug_false_positive_iff` is a tight biconditional (`cL = mL + 1` when `cH < mH`)
proved via a dedicated `sbc_zero_bool_iff` lemma. The full agent built 7 private
helper lemmas covering both the primary and exotic false-positive cases.

**Full wins on quantity; minimal wins on conciseness.** Both capture the essential
characterization.

### Bug 5 — Psywave Desync

Both achieved L4 (relational). The minimal agent took notably longer (~21m vs ~8m)
and needed 3 iterations — this is the bug where lack of direction hurts most, since
the agent must independently discover that there are *two separate implementations*.

However, the minimal agent produced a **stronger L2 characterization**: the theorem
`bug_iff_enemy_zero` is a true biconditional (`desync ↔ enemy returned some 0`)
proved by induction, compared to the full agent's more example-driven approach.
The minimal agent also proved `desync_implies_enemy_zero` by structural induction
on the stream — a non-trivial proof that required understanding the recursive
function structure.

**Full wins on speed; minimal wins on proof depth.**

## Modeling Choice Differences

| Bug | Full model | Minimal model |
|---|---|---|
| 1 Focus Energy | `BitVec 8`, pipeline functions | `BitVec 8`, pipeline + 8 private helpers |
| 2 1/256 | `BitVec 8` + `rlc3` rotation model | `BitVec 8`, manual trichotomy proof |
| 3 Blaine AI | `Nat` (rand, curHP, maxHP) | Abstract `AIInput` struct (Bool, Bool) |
| 4 Heal Overflow | `BitVec 8` x4, 7 private lemmas | `BitVec 8` x4, 1 key algebraic lemma |
| 5 Psywave | `List Nat`, acceptance predicates | `Nat -> List Nat -> Option Nat`, recursive |

An interesting pattern: the minimal agent tends toward more abstract models
(Bool-level for Blaine, direct recursion for Psywave) while the full agent,
primed with concrete assembly details, builds closer-to-hardware models.

## Proof Strategy Differences

The minimal agent used more manual proof tactics overall:

| Tactic | Full (batch_01) | Minimal (batch_minimal) |
|---|---|---|
| `native_decide` | dominant | still used, but less |
| `induction` | Bug 5 only | Bug 5 (deeper use) |
| `simp` | moderate | heavy |
| `omega` | Bug 3 | not used |
| manual case splits | rare | Bug 2 (trichotomy), Bug 5 (by_cases) |

The minimal agent, working without root-cause hints, appears to reason more
structurally rather than brute-forcing with `native_decide`.

## Time Analysis

| Bug | Full time | Minimal time | Delta |
|---|---|---|---|
| 1 Focus Energy | ~9m | ~8m | -1m (minimal faster) |
| 2 1/256 Accuracy | ~9m | ~13m | +4m |
| 3 Blaine AI | ~12m | ~5m | -7m (minimal faster) |
| 4 Heal Overflow | ~15m | ~12m | -3m (minimal faster) |
| 5 Psywave Desync | ~8m | ~21m | +13m |
| **Total** | **~53m** | **~59m** | **+6m (+11%)** |

The minimal condition was only 11% slower overall. Bugs 1, 3, and 4 were actually
*faster* in minimal mode — the agent spent less time parsing detailed descriptions
and went straight to codebase exploration. Bug 5 (Psywave) accounted for most of
the slowdown, as discovering the two-implementation asymmetry from scratch took
significantly longer.

## Conclusions

1. **Level coverage is robust to information reduction.** Both conditions achieve
   L1-L3 on all single-system bugs and L4 on the relational bug. The agent can
   independently locate assembly code, identify root causes, and build formal
   models from gameplay-only descriptions.

2. **Theorem count drops modestly.** 52 vs 60 theorems (-13%). The main loss is in
   Bug 2 (1/256), where the root-cause hint ("strict inequality") guided the full
   agent toward a richer treatment with `rlc3` and uniqueness.

3. **Time cost is small.** +11% overall. The hardest bug (Psywave) takes 2.5x longer
   in minimal mode, but simpler bugs are sometimes faster (less prompt to parse).

4. **Modeling philosophy shifts.** Without implementation hints, the agent gravitates
   toward more abstract models. This can produce cleaner formalizations (Blaine AI)
   or miss domain-specific structure (1/256 without `rlc3`).

5. **For a paper, both conditions are interesting.** The full condition shows what's
   achievable with modest guidance; the minimal condition shows the agent's raw
   capability for independent formal verification from gameplay descriptions alone.
   The comparison quantifies exactly what "telling the agent where to look" is worth.
