# Autoresearch Results: Claude Sonnet 4.6 as Formalizer

**Date:** 2026-04-16
**Branch:** `ar/apr15-sonnet`
**Researcher model:** Claude Opus (via Claude Code CLI)
**Formalizer model:** `claude-sonnet-4-6`
**Inner loop iterations:** K=2
**Bugs:** 10
**Scoring:** v2 (6-component, harder ceiling)
**Pipeline start:** Sparse (42-line system prompt, minimal feedback template)

## 3-Run Trajectory

The Sonnet run produced **3 complete runs** (not 2 as results.tsv shows). The
initial run was excluded from results.tsv because the laptop was suspended
mid-run, inflating its wall time. However, the actual scores are valid.

| Run | Timestamp | Score | Bugs@1.0 | Wall Time | Status |
|-----|-----------|-------|----------|-----------|--------|
| **Initial** (missing from TSV) | 20260415_204930 | **7.025** | 4/10 | 7471s (~2h) | Pre-suspension |
| **Baseline** (exp 0 in TSV) | 20260416_024349 | **7.900** | 7/10 | 31635s (inflated by suspension) | Recorded baseline |
| **Exp 1** | 20260416_113222 | **10.000** | 10/10 | 5069s (~84min) | After researcher optimized prompt |

## Per-Bug Breakdown (all 3 runs)

| Bug | Initial (7.025) | Baseline (7.9) | Exp 1 (10.0) | Notes |
|-----|-----------------|----------------|--------------|-------|
| 1 focus_energy | **1.0** (21 thms) | 0.0 (no file!) | **1.0** (12 thms) | Flipped between runs |
| 2 one_in_256 | 0.0 (no file!) | **1.0** (8 thms) | **1.0** (7 thms) | Flipped between runs |
| 3 blaine_ai | 0.8 (3 thms) | **1.0** (11 thms) | **1.0** (10 thms) | Partial → perfect |
| 4 heal_overflow | 0.0 (no file!) | **1.0** (8 thms) | **1.0** (11 thms) | Flipped between runs |
| 5 psywave_desync | 0.425 (0 thms!) | **1.0** (7 thms) | **1.0** (10 thms) | Compiled but no theorems |
| 6 substitute | **1.0** (11 thms) | **1.0** (13 thms) | **1.0** (16 thms) | Stable throughout |
| 7 bide_desync | **1.0** (8 thms) | 0.0 (no file!) | **1.0** (10 thms) | Flipped between runs |
| 8 reflect_overflow | **1.0** (9 thms) | **1.0** (11 thms) | **1.0** (10 thms) | Stable |
| 9 acc_eva_cancel | 0.9 (19 thms) | **1.0** (6 thms) | **1.0** (8 thms) | Fixed |
| 10 badge_reflect | 0.9 (15 thms) | 0.9 (14 thms) | **1.0** (14 thms) | Persistent holdout until exp 1 |

## What the Researcher Changed (Exp 1, +2.1)

Two changes to `system_prompt.md`, growing it from 42 to ~120 lines:

### 1. Critical output format instruction

Added a prominent block:
> **CRITICAL OUTPUT FORMAT**: You MUST output your COMPLETE Solution.lean inside a
> single ```lean code block. The automated system extracts code ONLY from ```lean
> blocks. If you do not include a ```lean block, your solution will be discarded
> and score ZERO.

This directly targeted Sonnet's dominant failure mode: bugs scoring 0.0 had **no
Solution.lean file at all** — the formalizer wasn't wrapping code in the expected
` ```lean ` blocks, so code extraction failed silently.

### 2. Reinforced non-parenthesized ∀ syntax

Added:
> **IMPORTANT**: Write `∀ x : BitVec 8` NOT `∀ (x : BitVec 8)`. You MUST omit
> the parentheses around quantified variables. This affects scoring.

Same fix the researcher discovered for Gemini Flash — the scoring regex
`(∀|forall)\s+\w+` requires the variable immediately after `∀`.

### 3. Additional improvements (bundled)

- Expanded SM83 API documentation (full register list, BitVec operators, flag setters)
- Required file structure template with `def impl`, `def spec`, and proof levels
- Sorry ban: "Do NOT include `sorry` anywhere"
- "Write at least 5 distinct theorems" guidance
- Tips for 16-bit bugs (use Nat, BitVec 8 decomposition)
- Compilation priority: "A compiling file with 5 theorems beats a non-compiling file with 20"

## Key Observations

### 1. Code extraction was Sonnet's dominant failure mode

Bugs scoring 0.0 have **no Solution.lean file** in their workspace — the formalizer
didn't produce output in the expected ` ```lean ` block format. This is fundamentally
different from Gemini Flash, which always produced extractable code but sometimes had
partial scores from missing keywords or `sorry`.

### 2. High baseline variance (stochastic)

Bugs 1, 2, 4, 7 flip between 0.0 and 1.0 across the initial and baseline runs **with
the same prompt**. The extraction failure is non-deterministic — Sonnet sometimes wraps
code in ` ```lean ` and sometimes doesn't. This bimodal behavior (0.0 or ~1.0) contrasts
with Flash's smoother partial-score distribution.

### 3. Single step to perfection

The researcher jumped from 7.9 → 10.0 in a single experiment (+2.1), compared to
Gemini Flash's 2 steps + 1 discard (8.3 → 9.8 → 9.95). Once the extraction format was
fixed, Sonnet's underlying Lean 4 capability was already sufficient for all 10 bugs.

### 4. The researcher discovered DIFFERENT strategies per model

| Strategy | Gemini Flash | Sonnet |
|----------|-------------|--------|
| Code extraction format | Not needed | **Critical** (fixes 0.0 bugs) |
| Sorry ban | **Critical** | Not needed (Sonnet avoids sorry naturally) |
| Naming rules (impl/spec) | **Critical** | Not needed |
| API documentation expansion | Moderate | Moderate |
| ∀ syntax (no parens) | **Critical** | **Critical** |
| Keyword guidance | **Critical** | Not needed |

This confirms the workshop assessment's prediction: *the outer loop adapts to the
inner model's failure modes.*

### 5. Sonnet solved Flash's holdout bug

Bug 6 (substitute), the persistent 0.95 holdout for Gemini Flash (only 4 theorems
instead of the required 5), was trivially solved by Sonnet in all 3 runs
(11→13→16 theorems). The 5-theorem ceiling was a Flash-specific failure.

## Comparison: Sonnet vs Gemini Flash

| Metric | Gemini Flash (v2 scoring) | Sonnet |
|--------|--------------------------|--------|
| True baseline | 8.30/10 | 7.025/10 (initial) or 7.9/10 (stable) |
| Final score | 9.95/10 | **10.0/10** |
| Steps to final | 2 kept + 1 discard | **1 kept** |
| Remaining gap | 0.05 (bug 6 substitute) | **0** (perfect) |
| Per-run wall time | ~1000s (~17min) | ~5000s (~84min) |
| Dominant failure mode | Partial scores (missing keywords, sorry) | Binary (code extraction or perfect) |
| Prompt growth | 42 → ~80 lines | 42 → ~120 lines |
| Baseline bugs@1.0 | 2/10 | 4-7/10 (varies) |

## Implications for the Paper

### Different failure profiles per model

Sonnet is **bimodal** (0.0 or ~1.0) while Flash is **smoother** (partial scores of
0.3, 0.425, 0.75, 0.8, 0.85, 0.9). This means scoring v2 reveals genuinely different
optimization landscapes per model — a strong contribution for the multi-model comparison.

### The initial run (7.025) adds value

It shows baseline variance and gives a 3-point trajectory (7.025 → 7.9 → 10.0) even
though only one was an actual researcher experiment. The variance between runs 1 and 2
(same prompt, different bugs fail) is itself a finding worth discussing.

### Cost/speed trade-off

Sonnet is ~5x slower per run but needs fewer optimization steps. Total wall time to
perfection: Sonnet ~3.5h (2h initial + 1.4h exp1) vs Flash ~1.5h (17min × 4 runs).

## Raw Data

### Initial run — 20260415_204930

Score 7.025. Solutions dir missing bug2 (one_in_256) and bug4 (heal_overflow) — no
Solution.lean extracted. Bug5 (psywave_desync) compiled but had 0 theorems (score
0.425). Bug3 (blaine_ai) compiled with only 3 theorems (score 0.8).

### Baseline (exp 0) — 20260416_024349

Score 7.9. Solutions dir missing bug1 (focus_energy) and bug7 (bide_desync) — same
extraction failure, different bugs. 7 bugs at 1.0, bug10 at 0.9 (persistent partial).

### Exp 1 — 20260416_113222

Score 10.0. All 10 bugs at 1.0. All compile, all sorry-free. Theorem counts range
7-16 per bug (total 108 theorems across 10 bugs).

## Updated Data Collection Summary

| Run | Model | K | Scoring | Baseline | Final | Steps | Notes |
|-----|-------|---|---------|----------|-------|-------|-------|
| 5-bug K=5 | Gemini Flash | 5 | v1 | 4.27/5 | 5.0/5 | 1 | |
| 10-bug K=2 | Gemini Flash | 2 | v1 | 9.07/10 | 10.0/10 | 2 | |
| 10-bug K=3 | Gemini Flash | 3 | v2 | 8.30/10 | 9.95/10 | 2 (+1 discard) | |
| 10-bug K=2 | **Sonnet 4.6** | 2 | v2 | 7.9/10 | **10.0/10** | **1** | Initial run at 7.025 shows variance |
