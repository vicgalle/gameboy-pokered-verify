# Autoresearch Results: 10 bugs, K=2, `gemini-3-flash-preview`

**Date:** 2026-04-15
**Branch:** `ar/apr15-flash`
**Researcher model:** Claude Opus (via Claude Code CLI)
**Formalizer model:** `gemini-3-flash-preview` (via Google GenAI SDK)
**Inner loop iterations:** K=2
**Bugs:** 10 (5 original + 5 new, including 2 novel discoveries)

## Score Progression

| Exp | Score | Delta | Time | Status | Key change |
|-----|-------|-------|------|--------|------------|
| 0 (baseline) | **9.067**/10 | +0.000 | 939s | keep | Default pipeline |
| 1 | **9.700**/10 | +0.633 | 483s | keep | Code-first emphasis + minimal working example |
| 2 | **10.000**/10 | +0.933 | 588s | keep | Sorry-delete guidance + 16-bit decomposition pattern |

**Perfect 10/10 in two researcher iterations**, even with K=2.

## Per-Bug Scores Across Experiments

| Bug | Name | Category | Exp 0 | Exp 1 | Exp 2 |
|-----|------|----------|-------|-------|-------|
| 1 | focus_energy | Wrong bitwise op | 1.0 | 1.0 | 1.0 |
| 2 | one_in_256 | Off-by-one | 1.0 | 1.0 | 1.0 |
| 3 | blaine_ai | Missing precondition | **0.5** | 1.0 | 1.0 |
| 4 | heal_overflow | Broken 16-bit comparison | **0.567** | **0.7** | 1.0 |
| 5 | psywave_desync | Symmetry violation (L4) | 1.0 | 1.0 | 1.0 |
| 6 | substitute | Arithmetic underflow | 1.0 | 1.0 | 1.0 |
| 7 | bide_desync | Asymmetric memory zeroing (L4) | 1.0 | 1.0 | 1.0 |
| 8 | reflect_overflow | Arithmetic overflow | 1.0 | 1.0 | 1.0 |
| 9 | acc_eva_cancel | Truncated fractions (novel) | 1.0 | 1.0 | 1.0 |
| 10 | badge_reflect | Emergent interaction (novel) | 1.0 | 1.0 | 1.0 |

## Baseline Failure Analysis

Two bugs struggled at baseline, both familiar culprits from the earlier 5-bug run:

- **Bug 3 (Blaine AI)**: Score 0.5 -- compiled, sorry-free, but **0 theorems**. The formalizer wrote definitions without any `theorem` declarations.
- **Bug 4 (Heal Overflow)**: Score 0.567 -- compiled, sorry-free, but **0 theorems**. Same pattern: definitions only.

All 5 **new bugs** (6-10) scored 1.0 on the baseline, including the two novel discoveries (acc_eva_cancel, badge_reflect).

## What the Researcher Discovered

### Exp 1: Code-first emphasis (+0.633)

Two changes to `pipeline/system_prompt.md`:

1. **"CODE FIRST, COMMENTS LATER" rule** -- forces the formalizer to produce at least `impl`, `spec`, and 3+ theorem declarations. Prevents the failure mode of writing long commentary without actual proofs.
2. **Minimal working example** appended to the prompt -- a complete compiling template showing the `impl`/`spec`/`bug_exists`/`fix_correct` structure.

**Impact:** Fixed Bug 3 (0.5 -> 1.0) and partially fixed Bug 4 (0.567 -> 0.7). Bug 4 still had `sorry` in some proofs.

### Exp 2: Sorry-delete + 16-bit decomposition (+0.300)

Two surgical changes to `pipeline/system_prompt.md`:

1. **"Delete rather than sorry" guidance** -- changed from "sorry is acceptable as a placeholder" to "DELETE the theorem entirely rather than leaving sorry; 3 sorry-free theorems score higher than 5 theorems with sorry." This aligns the formalizer's incentives with the scoring function.
2. **16-bit decomposition pattern** -- showed how to model 16-bit HP values as pairs of `BitVec 8` (hi byte, lo byte) so `native_decide` works on the per-byte comparison logic:
   ```lean
   def healCheck (curr_hi curr_lo max_hi max_lo : BitVec 8) : Bool :=
     let carry := curr_hi < max_hi
     let result := curr_lo - max_lo - (if carry then 1 else 0)
     result == 0
   ```

**Impact:** Fixed Bug 4 (0.7 -> 1.0). The 16-bit decomposition was specifically targeted at the heal overflow bug's byte-by-byte `cp`/`sbc` comparison.

## Key Observations

### The new bugs were easier than expected

All 5 new bugs (substitute, bide_desync, reflect_overflow, acc_eva_cancel, badge_reflect) hit 1.0 from the very first run. This includes our two novel discoveries, which undermines the contamination-testing hypothesis somewhat -- the model generalizes from its general Lean 4 and game mechanics knowledge rather than from memorized solutions for specific bugs.

### The hard bugs are consistently hard

Blaine AI and Heal Overflow were the two weak points in the original 5-bug run with K=5, and they remain the weak points at K=2 with 10 bugs. Bug 4 in particular is the "last to fall" across both experiments -- its 16-bit byte-by-byte comparison requires a modeling trick (hi/lo decomposition) that the formalizer doesn't discover without explicit guidance in the system prompt.

### The researcher's discoveries are transferable

Both key insights (code-first structure, sorry-delete strategy) were the same ones found in the earlier 5-bug run. The 16-bit decomposition pattern was new and specifically targeted -- this is the kind of domain-specific prompt engineering that a human researcher would also perform.

### Runtime scales linearly

| Configuration | Bugs | K | Total time | Per-bug-per-iter |
|--------------|------|---|-----------|-----------------|
| 5-bug baseline | 5 | 5 | 1131s | ~45s |
| 10-bug baseline | 10 | 2 | 939s | ~47s |
| 10-bug exp 2 | 10 | 2 | 588s | ~29s |

Runtime per bug per iteration is consistent (~45s at baseline). The optimized prompt produces shorter, more focused output, cutting per-iteration time to ~29s.

## Comparison with 5-Bug Run (K=5)

| Metric | 5-bug K=5 | 10-bug K=2 |
|--------|-----------|------------|
| Baseline score | 4.266/5 (85.3%) | 9.067/10 (90.7%) |
| Final score | 5.0/5 (100%) | 10.0/10 (100%) |
| Iterations to perfect | 1 | 2 |
| Baseline failures | Bug 3, Bug 4 | Bug 3, Bug 4 |
| Key fix | Concise code-first prompt | Same + 16-bit decomposition |
| Baseline time | 1131s | 939s |
| Final time | 603s | 588s |

The 10-bug benchmark at K=2 is harder (more bugs, fewer iterations) but the researcher still reaches perfect score quickly. The same two bugs (Blaine AI, Heal Overflow) are consistently the bottleneck.

## Scoring Function

Per-bug score on [0.0, 1.0]:
- **+0.2** if the Lean file compiles
- **+0.1** per theorem (up to +0.3 for 3+ theorems)
- **+0.3** if completely sorry-free
- **+0.2** scaled by ground truth theme coverage (matching proof levels L1-L4)

Aggregate: Phi(c) = sum of 10 bug scores. Range [0.0, 10.0].

## Bug Taxonomy

| # | Bug | Category | Novel? | Difficulty |
|---|-----|----------|--------|------------|
| 1 | Focus Energy | Wrong bitwise op | No | Easy |
| 2 | 1/256 Miss | Off-by-one | No | Easy |
| 3 | Blaine AI | Missing precondition | No | Medium |
| 4 | Heal Overflow | Broken 16-bit comparison | No | Hard |
| 5 | Psywave Desync | Symmetry violation (L4) | No | Easy |
| 6 | Substitute | Arithmetic underflow | No | Easy |
| 7 | Bide Desync | Asymmetric memory zeroing (L4) | No | Easy |
| 8 | Reflect Overflow | Arithmetic overflow | No | Easy |
| 9 | Acc/Eva Cancel | Truncated fractions | **Yes (latent)** | Easy |
| 10 | Badge + Reflect | Emergent interaction | **Yes (discovery)** | Easy |

"Difficulty" reflects the formalizer's empirical performance, not the inherent complexity of the bug. Bug 4 (Heal Overflow) is the only bug that requires domain-specific prompt guidance (16-bit decomposition) to solve at K=2.
