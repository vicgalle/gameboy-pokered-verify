# Autoresearch Results: Scoring v2 + Sparse Pipeline

**Date:** 2026-04-15
**Branch:** `ar/apr15-gemini-flash`
**Researcher model:** Claude Opus (via Claude Code CLI)
**Formalizer model:** `gemini-3-flash-preview` (via Google GenAI SDK)
**Inner loop iterations:** K=3
**Bugs:** 10
**Scoring:** v2 (6-component, harder ceiling)
**Pipeline start:** Sparse (42-line system prompt, minimal feedback template)

## Scoring v2 Components

| Component | Weight | What it measures |
|-----------|--------|-----------------|
| Compiles | +0.10 | Basic compilation |
| Theorems | +0.05/thm (max +0.25) | Needs 5 theorems (was 3 in v1) |
| Sorry-free | +0.20 | No `sorry` anywhere |
| Theme coverage | +0.25 | Proportional L1-L4 match vs ground truth |
| Structural fidelity | +0.10 | Has both `def impl` and `def spec` |
| Proof depth | +0.10 | Has universal quantification (`∀`/`forall`) |

## Optimization Trajectory

| Exp | Score | Delta | Time | Bugs=1.0 | Status | What the researcher changed |
|-----|-------|-------|------|----------|--------|-----------------------------|
| 0 | **8.300** | — | 1316s | 2/10 | keep | Baseline (sparse prompt) |
| 1 | **9.800** | +1.500 | 1035s | 8/10 | keep | Naming rules, API fixes, sorry ban, keyword guidance |
| 2 | **9.950** | +0.150 | 1012s | 9/10 | keep | `∀ x : Type,` syntax (no parens) for regex match |
| 3 | 9.817 | -0.133 | 1074s | 9/10 | **discard** | Attempted further change, regressed |

**Final score: 9.95/10** with bug 6 (substitute) at 0.95 as the sole holdout.

## Per-Bug Trajectory

| Bug | Baseline | Exp 1 | Exp 2 | Failure modes |
|-----|----------|-------|-------|---------------|
| 1 focus_energy | 0.75 | 0.90 | **1.00** | Missing universal quant → fixed |
| 2 one_in_256 | 0.90 | **1.00** | **1.00** | — |
| 3 blaine_ai | **0.30** | 0.90 | **1.00** | 0 theorems → naming rules fixed it |
| 4 heal_overflow | 0.75 | **1.00** | **1.00** | sorry → sorry ban |
| 5 psywave_desync | 0.85 | **1.00** | **1.00** | Missing L4 keywords → keyword guidance |
| 6 substitute | 0.95 | **1.00** | **0.95** | Regressed! Only 4 theorems (needs 5) |
| 7 bide_desync | 0.90 | **1.00** | **1.00** | — |
| 8 reflect_overflow | **1.00** | **1.00** | **1.00** | Perfect throughout |
| 9 acc_eva_cancel | **1.00** | **1.00** | **1.00** | Perfect throughout |
| 10 badge_reflect | 0.90 | **1.00** | **1.00** | Needed 5 theorems → prompt got it |

## What the Researcher Discovered (in order)

### Exp 1 (+1.500) — Five simultaneous improvements

1. `"Output CODE, not documentation"` — prevents prose-heavy responses
2. Added `execAdcA`, `execSbcA`, `mkFlags` to the SM83 API docs — the formalizer was
   missing operations it needed for carry-based arithmetic
3. **Required structure** section — mandated exact names `def impl`, `def spec`,
   `theorem bug_exists`
4. **Sorry ban** — "Never use sorry. Simplify the theorem or use native_decide."
5. **Keyword guidance** — told the formalizer to include `∃`, `∀`, `fix`, `correct`,
   `desync` etc. in theorem names to trigger scoring components

### Exp 2 (+0.150) — Surgical regex fix

Changed `"∀ (x : Type)"` guidance to `"∀ x : Type,"` (no parens) — the scoring
regex `(∀|forall)\s+\w+` requires the variable immediately after `∀`, not inside
parentheses. The researcher figured out the scoring function's implementation detail
and instructed the formalizer to match it.

### Exp 3 (-0.133) — Discarded

Attempted further change but regressed to 9.817 (bug 3 dropped to 0.817). Correctly
reverted via `git checkout -- pipeline/`.

## Key Observations

### The scoring v2 created a 3-step optimization

Under v1, the same starting point would have been ~9.0/10 and been fixed in 1 step.
Under v2, the baseline dropped to 8.3/10 and the researcher needed 2 kept experiments
plus 1 discard — a meaningfully longer trajectory.

### The researcher reverse-engineered the scoring function

Exp 2's change is the most interesting finding: the researcher noticed that
`∀ (x : BitVec 8)` wasn't triggering the "universal quantification" bonus, and
specifically instructed the formalizer to write `∀ x : BitVec 8,` instead. This is
the researcher agent *modeling the evaluation metric*, not just improving the formalizer.

### The whack-a-mole effect

Bug 6 (substitute) regressed from 1.0 to 0.95 in exp 2. The `∀` syntax change may
have caused the formalizer to restructure its output, dropping from 5 to 4 theorems.
Fixing one bug's score can regress another — exactly the kind of trade-off that makes
the outer loop interesting.

### The discard mechanism works

Exp 3 scored 9.817 (below exp 2's 9.95) and was correctly reverted. The researcher
is doing proper hill-climbing.

## Comparison: Scoring v1 vs v2

| Metric | v1 (old) | v2 (new) |
|--------|----------|----------|
| Baseline score | 9.07/10 (90.7%) | 8.30/10 (83.0%) |
| Bugs at 1.0 at baseline | 8/10 | 2/10 |
| Steps to near-perfect | 1 | 2 (+ 1 discard) |
| Final score | 10.0/10 | 9.95/10 |
| Remaining gap | 0 | 0.05 (bug 6) |
| Most interesting finding | Code-first prompt | Regex reverse-engineering |

## Raw Data

### Baseline (exp 0) — run 20260415_170245

All 10 bugs compile, sorry-free except bug 4 (heal_overflow).
- 2 bugs at 1.0: reflect_overflow, acc_eva_cancel
- 4 bugs below 0.9: focus_energy (0.75), blaine_ai (0.30), heal_overflow (0.75),
  psywave_desync (0.85)
- Main failures: missing theorems, sorry, missing level keywords, no universal quant

### Exp 1 — run 20260415_172644

8 bugs at 1.0. Remaining: focus_energy (0.90), blaine_ai (0.90).

### Exp 2 — run 20260415_174543

9 bugs at 1.0. Remaining: substitute (0.95, 4 theorems instead of 5).

### Discarded run — 20260415_180916

Score 9.817. Bug 3 (blaine_ai) dropped to 0.817. Reverted.
