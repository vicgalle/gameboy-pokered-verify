# Workshop Paper Assessment: AI4Math @ ICML 2026

**Workshop:** 3rd AI for Math Workshop — Toward Self-Evolving Scientific Agents
**Venue:** ICML 2026, Seoul, South Korea
**Deadline:** May 25, 2026 (AOE)
**Format:** 2-8 pages, ICML format, double-blind, non-archival
**URL:** https://ai4math2026.github.io/

## Fit Assessment: Strong

The workshop theme is literally "Toward Self-Evolving Scientific Agents" — our
two-level autoresearch loop (researcher agent that self-improves a formalizer pipeline)
is exactly that. Three topic tracks align simultaneously:

- **Formal theorem proving** — LLM generating Lean 4 proofs against a real CPU model
- **Autoformalization** — informal bug descriptions + assembly → formal Lean
- **Scientific agents** — the self-evolving researcher loop

The novel angle no one else has: **autoresearch applied to formal verification**.
Everyone else is doing autoresearch for training neural nets or solving competition
math. Applying it to Lean 4 proofs of real software bugs is a fresh application that
fits the "transcend Olympiad questions to support real-world mathematics" framing in
the CFP.

## What We Have

A clean 3-step optimization curve (8.3 → 9.8 → 9.95) with a discard, on a 10-bug
benchmark with a 6-component scoring function. The researcher agent discovers 5+
independent improvements, reverse-engineers the scoring regex, and hits the
whack-a-mole trade-off (bug 6 regresses when bug 1 gets fixed). That's enough
dynamics for 1.5 pages of experiments.

### Data collected

| Run | Model | K | Scoring | Baseline | Final | Steps |
|-----|-------|---|---------|----------|-------|-------|
| 5-bug K=5 | Gemini Flash | 5 | v1 | 4.27/5 | 5.0/5 | 1 |
| 10-bug K=2 | Gemini Flash | 2 | v1 | 9.07/10 | 10.0/10 | 2 |
| 10-bug K=3 | Gemini Flash | 3 | v2 | 8.30/10 | 9.95/10 | 2 (+1 discard) |

## What to Add Before May 25

### Must-have: Second inner model

Run **Claude Sonnet as formalizer** with the same sparse starting pipeline and scoring
v2. If the researcher discovers *different* strategies for Sonnet vs Gemini Flash
(plausible — they have different failure modes), that's a strong contribution: the
outer loop adapts to the inner model. If it discovers the *same* strategies, that's
also interesting — it suggests the improvements are about the task structure, not the
model.

### Nice-to-have: Ablations

- **K=1 ablation** (single shot, no feedback) — isolates how much comes from the
  model's priors vs the compile-feedback loop vs the pipeline optimization
- **No assembly context** — run without assembly extraction to quantify its contribution
- **Weaker model** (Gemini Flash 8B or Haiku) where the outer loop might need more
  iterations

## Suggested Paper Structure (6 pages)

1. **Introduction** (1p): LLMs can generate Lean 4 proofs, but how do you
   systematically optimize the pipeline? We adapt the autoresearch framework (Karpathy
   2025) to formal verification.

2. **Framework** (1.5p):
   - Two-level architecture diagram
   - Inner loop: formalizer via Claude Agent SDK / Gemini API, K iterations, lake
     build feedback
   - Outer loop: researcher agent modifies pipeline/ (system prompt, feedback
     template, helpers, iteration logic)
   - Scoring function Phi(c) v2 with 6 components
   - Information barrier
   - The structural analogy table (Karpathy's train.py ↔ our pipeline/)

3. **Benchmark** (1p): 10 Pokemon Red bugs as a formal verification benchmark.
   Diverse categories (bitwise, overflow, link desync, emergent interaction),
   including 2 novel discoveries. Why this is interesting: real assembly, real bugs,
   real Lean 4 compilation. The scoring v2 design and why it matters.

4. **Experiments** (1.5p):
   - Gemini Flash trajectory (8.3 → 9.8 → 9.95)
   - Claude Sonnet trajectory (TBD)
   - Comparison: what the researcher discovers for each model
   - The git diff of each kept pipeline change as a figure/table
   - Scoring v1 vs v2 comparison showing deeper optimization

5. **Analysis & Discussion** (1p):
   - What the researcher discovers and in what order
   - The regex reverse-engineering observation
   - The whack-a-mole effect (trade-offs between bugs)
   - Training contamination: novel bugs (9, 10) scored 1.0 immediately
   - Limitations: benchmark saturates, prompt engineering dominates reasoning

## Key Selling Points for Reviewers

1. **Fresh application domain.** Autoresearch for formal verification is new. Everyone
   else does competition math or neural net training.

2. **Real artifacts, not toy problems.** The bugs come from a real Game Boy game
   codebase. The proofs compile in Lean 4 against a real CPU model. The assembly is
   from the actual pokered disassembly.

3. **The researcher agent exhibits interesting behaviors.** Reverse-engineering the
   scoring regex. Discovering 5 improvements simultaneously. Trading off between
   bugs. These are emergent behaviors, not designed.

4. **Reproducible and open.** The entire framework, benchmark, and pipeline
   configurations can be released. Non-archival workshop means no conflict with a
   future full paper.

5. **Multi-model.** Claude Agent SDK + Gemini API dispatch shows the framework is
   model-agnostic (and the inner/outer model separation is principled).

## Risks

- **"Too easy" critique**: Even with scoring v2, the baseline is 83% and saturates
  in 2-3 steps. Mitigate by showing the scoring v1 → v2 progression and arguing
  for harder future benchmarks.

- **"Just prompt engineering" critique**: The researcher's improvements are all
  system prompt edits. Mitigate by framing this as the finding: "for current LLMs,
  formal verification quality is dominated by prompt structure, not model capability
  or iteration depth."

- **Small benchmark**: 10 bugs. Mitigate by noting diversity (7 categories,
  2 novel discoveries, L1-L4 coverage) and that scaling to more bugs is
  straightforward.

## Verdict

**Submit it.** The results with scoring v2 and the sparse pipeline give enough
dynamics for a compelling workshop paper. The deadline is May 25 — 5.5 weeks is
plenty for one more model run and the writeup.
