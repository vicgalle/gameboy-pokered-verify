# Autoresearch Results: No-Assembly Ablation (Gemini 3 Flash)

**Date:** 2026-04-16
**Branch:** `ar/apr16-noasm`
**Researcher model:** Claude Opus (via Claude Code CLI)
**Formalizer model:** `gemini-3-flash-preview`
**Inner loop iterations:** K=2
**Bugs:** 10
**Scoring:** v2 (6-component, harder ceiling)
**Pipeline start:** Sparse (42-line system prompt, minimal feedback template)
**Ablation:** `--no-asm` — assembly context disabled, formalizer sees only natural-language bug descriptions

## Purpose

This run isolates the contribution of assembly context to formalizer performance.
In the standard pipeline, each bug prompt includes extracted SM83 assembly snippets
(routines, grep context) from the pokered disassembly. With `--no-asm`, the formalizer
receives only the markdown bug description — no assembly code, no opcodes, no labels.

The question: how much does raw assembly context matter, and can the researcher's
outer loop compensate for its absence?

## Optimization Trajectory

| Exp | Score | Delta | Time | Bugs@1.0 | Status | What the researcher changed |
|-----|-------|-------|------|----------|--------|-----------------------------|
| 0 | **8.050** | — | 1452s | 3/10 | keep | Baseline (sparse prompt, no assembly) |
| 1 | **9.400** | +1.350 | 912s | 5/10 | keep | Worked example, native_decide pattern, sorry ban, API details |
| 2 | **10.000** | +0.600 | 1028s | 10/10 | keep | Strict `def impl`/`def spec` naming, `∀` syntax (no parens) |

**Final score: 10.0/10** — perfect, with 0 discards.

## Per-Bug Trajectory

| Bug | Baseline (8.05) | Exp 1 (9.40) | Exp 2 (10.0) | Failure modes |
|-----|-----------------|--------------|--------------|---------------|
| 1 focus_energy | **1.0** (5 thms) | 0.8 (5 thms) | **1.0** (6 thms) | Regressed in exp 1, recovered |
| 2 one_in_256 | 0.3 (0 thms!) | **1.0** (6 thms) | **1.0** (6 thms) | Compiled but 0 theorems at baseline |
| 3 blaine_ai | 0.7 (5 thms, sorry) | **1.0** (6 thms) | **1.0** (6 thms) | sorry → sorry ban fixed |
| 4 heal_overflow | 0.55 (4 thms, sorry) | 0.9 (6 thms) | **1.0** (7 thms) | sorry + few theorems → gradual fix |
| 5 psywave_desync | 0.75 (4 thms) | 0.9 (6 thms) | **1.0** (7 thms) | Missing keywords → gradual fix |
| 6 substitute | 0.9 (6 thms) | **1.0** (7 thms) | **1.0** (7 thms) | — |
| 7 bide_desync | 0.95 (4 thms) | **1.0** (7 thms) | **1.0** (5 thms) | — |
| 8 reflect_overflow | **1.0** (5 thms) | 0.9 (7 thms) | **1.0** (6 thms) | Regressed in exp 1, recovered |
| 9 acc_eva_cancel | **1.0** (5 thms) | **1.0** (8 thms) | **1.0** (7 thms) | Perfect throughout |
| 10 badge_reflect | 0.9 (7 thms) | 0.9 (6 thms) | **1.0** (7 thms) | Persistent partial until exp 2 |

## What the Researcher Discovered

### Exp 1 (+1.350) — Compensating for missing assembly

The researcher adapted its strategy to the no-assembly setting with several changes:

1. **Explicitly acknowledged the ablation** in the system prompt: "You will NOT receive
   assembly code — formalize based on the natural-language description alone."

2. **Added a complete worked example** — a full compiling Lean 4 file modeling a
   bitwise bug with `impl`, `spec`, `∃` witness, `∀` characterization, and a fix.
   This gives the formalizer a concrete template to imitate, compensating for the
   lack of assembly code as a structural anchor.

3. **Introduced the `native_decide` universal pattern**:
   ```lean
   theorem my_theorem (x : BitVec 8) : someProperty x := by
     have := (by native_decide : ∀ v : BitVec 8, someProperty v)
     exact this x
   ```
   This tactic recipe was not discovered in any of the with-ASM runs. It's a
   no-assembly-specific adaptation: without assembly to guide the model's code
   structure, it needs more explicit tactic guidance.

4. **Expanded API documentation** with type signatures and return types (e.g.,
   "`execSrl` returns `(BitVec 8 x BitVec 8)` — (result, flags)").

5. **Sorry ban** and guidance to model with `Nat` + `omega` for non-bitwise bugs.

### Exp 2 (+0.600) — Convergent discoveries

Two changes that have appeared in every run regardless of model or assembly context:

1. **Strict `def impl`/`def spec` naming** — "Your main buggy function MUST be named
   exactly `def impl`... Do NOT use suffixed names like `def impl_focus_energy`."
   This fixes the structural fidelity scoring component.

2. **`∀` syntax without parentheses** — "Use `∀ x : Type, ...` not `∀ (x : Type), ...`."
   This fixes the proof depth scoring regex.

## Key Findings

### 1. Assembly context contributes ~0.25 points to the baseline

| Condition | Baseline | Model |
|-----------|----------|-------|
| With ASM | 8.30/10 | Gemini Flash (v2 scoring) |
| **No ASM** | **8.05/10** | Gemini 3 Flash (v2 scoring) |

The drop is modest: 0.25 points. All 10 bugs still compile at baseline without
assembly. The main effect is on partial scores (more sorry, fewer theorems, missing
keywords) rather than compilation failures.

### 2. The researcher fully compensates — and exceeds the with-ASM result

| Metric | With ASM | No ASM |
|--------|----------|--------|
| Baseline | 8.30 | 8.05 |
| Final | 9.95 | **10.00** |
| Steps | 2 kept + 1 discard | **2 kept, 0 discards** |
| Remaining gap | 0.05 (bug 6) | **0** |

The no-ASM run actually reaches a *higher* final score (10.0 vs 9.95). The with-ASM
run's persistent bug 6 holdout (4 theorems instead of 5) doesn't occur here. The
researcher's worked example may help the formalizer produce more consistent output
structure than the assembly context does.

### 3. The researcher discovers different strategies without assembly

| Strategy | With ASM | No ASM |
|----------|----------|--------|
| Worked example (full Lean file) | Not used | **Key innovation** |
| `native_decide` universal pattern | Not used | **Key innovation** |
| "No assembly" acknowledgement | N/A | Yes |
| API documentation expansion | Yes | Yes |
| Sorry ban | Yes | Yes |
| `def impl`/`def spec` naming | Yes | Yes |
| `∀` syntax (no parens) | Yes | Yes |

The top two strategies are unique to the no-ASM setting. The bottom four are
convergent — discovered in every run.

### 4. Convergent vs divergent researcher discoveries

Across all runs (Gemini Flash with ASM, Sonnet, Gemini Flash no-ASM), certain
discoveries recur:

**Always discovered (convergent):**
- `def impl`/`def spec` strict naming → structural fidelity score
- `∀ x : Type,` without parens → proof depth score
- Sorry ban → sorry-free score

**Model/setting-specific (divergent):**
- Worked example + tactic recipe (no-ASM only)
- Code extraction format instruction (Sonnet only)
- Keyword guidance for L1-L4 (with-ASM Gemini Flash only)

The convergent discoveries reflect the scoring function's structure. The divergent
ones reflect adaptation to the specific formalizer model and available context.

### 5. The whack-a-mole effect persists

Bug 1 (focus_energy) and bug 8 (reflect_overflow) both regressed from 1.0 to
0.8/0.9 in exp 1, then recovered in exp 2. This bidirectional regression matches
the pattern from other runs (bug 6 in with-ASM Flash, bugs 1/7 flipping in Sonnet).

## Comparison: All Runs (Scoring v2)

| Run | Formalizer | ASM | K | Baseline | Final | Steps | Discards |
|-----|------------|-----|---|----------|-------|-------|----------|
| apr15-flash | Gemini Flash | Yes | 3 | 8.30 | 9.95 | 2 | 1 |
| apr15-sonnet | Sonnet 4.6 | Yes | 2 | 7.9 | 10.0 | 1 | 0 |
| **apr16-noasm** | **Gemini 3 Flash** | **No** | **2** | **8.05** | **10.0** | **2** | **0** |

## Implications for the Paper

### The ablation tells a clear story

Assembly context provides a **modest baseline boost** (+0.25) but is **not necessary
for perfect scores**. The researcher agent compensates by shifting strategy: instead
of helping the formalizer map assembly to Lean, it provides a complete worked example
the formalizer can structurally imitate.

This supports the framing that **the outer loop adapts to the information available**,
not just to the inner model's failure modes. When assembly is removed, the researcher
doesn't just try harder with the same approach — it invents a qualitatively different
strategy (worked examples + tactic recipes).

### What assembly context actually provides

The natural-language bug descriptions already contain the bug's *logic* (what goes
wrong, why, what the correct behavior should be). Assembly adds *implementation detail*
(specific opcodes, register usage, code structure). For the scoring function — which
measures formal proof structure, not assembly faithfulness — the logic is sufficient.

A harder scoring function that evaluated whether the Lean model faithfully reproduced
the assembly-level computation (not just the bug's logical structure) would likely
show a larger gap. This is a limitation worth noting.

### Convergent discoveries strengthen the paper

The fact that 3/6 researcher strategies are independently discovered across all runs
(different models, different contexts) is strong evidence that these are fundamental
to the scoring function, not artifacts of a single run. The divergent strategies show
genuine adaptation. Together, they make the multi-run comparison more compelling than
any single trajectory.

## Raw Data

### Baseline (exp 0) — run 20260416_160926

Score 8.05. All 10 bugs compile. Two bugs have sorry (blaine_ai, heal_overflow).
Bug 2 (one_in_256) compiled with 0 theorems (score 0.3). Three bugs at 1.0
(focus_energy, reflect_overflow, acc_eva_cancel).

### Exp 1 — run 20260416_163611

Score 9.40. All 10 sorry-free. Five bugs at 1.0. Bug 1 regressed (1.0 → 0.8),
bug 8 regressed (1.0 → 0.9). Bugs 4, 5, 10 improved but not yet perfect.

### Exp 2 — run 20260416_165535

Score 10.0. All 10 bugs at 1.0. All compile, all sorry-free. Theorem counts
5-7 per bug (total 64 theorems across 10 bugs).
