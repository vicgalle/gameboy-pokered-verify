# Workshop Paper Assessment: AI4Math @ ICML 2026

**Workshop:** 3rd AI for Math Workshop — Toward Self-Evolving Scientific Agents
**Venue:** ICML 2026, Seoul, South Korea (Coex Convention & Exhibition Center)
**Date:** July 10 or 11, 2026
**Deadline:** May 25, 2026 (AOE)
**Decision:** June 15, 2026
**Camera-ready:** June 25, 2026
**Format:** 2-8 pages, ICML 2026 format, double-blind, non-archival
**Review:** OpenReview, double-blind
**URL:** https://ai4math2026.github.io/

## Fit Assessment: Very Strong

The workshop theme is literally "Toward Self-Evolving Scientific Agents" — our
two-level autoresearch loop (researcher agent that self-improves a formalizer pipeline)
is exactly that. Four of the eight topic tracks align simultaneously:

- **Formal theorem proving** — LLM generating Lean 4 proofs against a real CPU model
- **Autoformalization** — informal bug descriptions + assembly → formal Lean
- **Verification & evaluation** — 6-component scoring function, multi-model comparison
- **Scientific agents** — the self-evolving researcher loop

The novel angle no one else has: **autoresearch applied to formal verification of
real software**. Everyone else is doing autoresearch for training neural nets or solving
competition math. Applying it to Lean 4 proofs of real assembly bugs is a fresh
application that fits the "transcend Olympiad questions to support real-world
mathematics" framing in the CFP.

### Speaker alignment

The invited speaker list strengthens our fit considerably:

- **Leonardo de Moura** (Lean creator, AWS/Lean FRO) — our work is built entirely on
  Lean 4. The SM83 formalization and LLM-generated proofs showcase Lean 4 as a
  verification target for AI agents.
- **Emily First** (Rutgers) — works on AI for theorem proving in Lean/Rocq/Isabelle.
  Our inner-loop compile-feedback mechanism is directly related.
- **Joseph Tooby-Smith** (Bath, PhysLean) — formalizes physics in Lean 4. Our SM83
  CPU formalization is a parallel effort formalizing hardware semantics. Both expand
  Lean 4 beyond pure mathematics.
- **Jia Li** (Project Numina, Kimina-Prover) — LLMs for formal reasoning. Our
  multi-model comparison (Gemini Flash vs Sonnet) evaluates different LLMs as formal
  reasoning backends.

## What We Have (as of April 16)

### Three artifacts

**1. Autoresearch framework for formal verification**

The two-level optimization loop adapted from Karpathy (2025): an outer researcher
agent (Claude Opus) that modifies a pipeline (system prompt, feedback template, helpers)
to improve an inner formalizer LLM's Lean 4 output, scored by a 6-component function.

**2. Multi-model experimental results**

Complete optimization trajectories for two formalizer models on a 10-bug benchmark:

| Run | Formalizer | K | Scoring | Baseline | Final | Steps | Notes |
|-----|------------|---|---------|----------|-------|-------|-------|
| 5-bug K=5 | Gemini Flash | 5 | v1 | 4.27/5 | 5.0/5 | 1 | Early pilot |
| 10-bug K=2 | Gemini Flash | 2 | v1 | 9.07/10 | 10.0/10 | 2 | |
| 10-bug K=3 | Gemini Flash | 3 | v2 | 8.30/10 | 9.95/10 | 2 (+1 discard) | |
| 10-bug K=2 | **Sonnet 4.6** | 2 | v2 | 7.9/10 | **10.0/10** | **1** | Initial run at 7.025 shows variance |

The multi-model comparison reveals that the researcher discovers **different strategies
per model** (code extraction format for Sonnet vs sorry ban + keyword guidance for
Flash), which is itself a key finding.

**3. SM83 CPU formalization in Lean 4**

A standalone artifact: a complete formal model of the Sharp SM83 (Game Boy CPU) in
Lean 4, consisting of **1,104 lines of code** across **9 modules**:

| Module | LOC | Contents |
|--------|-----|----------|
| Properties.lean | 280 | 32 algebraic theorems (involutions, rotation periods, cancellation) |
| Arithmetic.lean | 228 | ADD, ADC, SUB, SBC, CP, INC, DEC (8-bit and 16-bit) |
| Logic.lean | 157 | AND, OR, XOR, shifts (SRL/SLA/SRA), rotates (RLCA/RRCA/RLA/RRA), bit ops |
| Load.lean | 114 | LD variants, LDI/LDD, PUSH/POP stack ops |
| State.lean | 101 | CPUState structure (8 registers, SP, PC, memory, flags) |
| Control.lean | 83 | JP, JR, CALL, RET (conditional/unconditional), HALT, NOP |
| Flags.lean | 57 | Z/N/H/C flag semantics, hardware invariants |
| Memory.lean | 39 | Pure functional memory model, named Game Boy regions, little-endian access |
| Basic.lean | 36 | BitVec utilities (hi, lo, mk16, sign extension) |

Key properties:
- **~40 SM83 opcodes** formalized with full flag semantics
- **32 machine-checked theorems** on instruction properties (e.g., RLCA has period 8,
  CPL is an involution, XOR self-annihilation, memory frame rules)
- **Pure functional memory model** — `BitVec 16 → BitVec 8`, enabling equational
  reasoning and `native_decide`
- **18 compile-time validation tests** cross-referenced against SM83 hardware docs
- To our knowledge, the **first SM83 formalization in Lean 4** (or any modern ITP)

This artifact has value independent of the autoresearch framework: it's a reusable
CPU model for Game Boy program verification, and it demonstrates formalizing a real
(non-toy) ISA in Lean 4 outside the usual competition math context.

## What to Add Before May 25

### Must-have: Paper writeup (~5.5 weeks)

All experimental data is collected. The remaining work is writing.

### Nice-to-have: Ablations

- **K=1 ablation** (single shot, no feedback) — isolates how much comes from the
  model's priors vs the compile-feedback loop vs the pipeline optimization
- **No assembly context** — run without assembly extraction to quantify its contribution
- **Weaker model** (Haiku or smaller Flash) where the outer loop might need more
  iterations and reveal more optimization dynamics

### Nice-to-have: Deeper SM83 analysis

- Count proof-relevant vs boilerplate LOC in generated solutions
- Compare generated solutions against hand-written ground truth structurally
- Measure how many generated theorems are genuinely about the bug vs padding

## Suggested Paper Structure (6 pages)

1. **Introduction** (1p): LLMs can generate Lean 4 proofs, but how do you
   systematically optimize the pipeline? We adapt the autoresearch framework (Karpathy
   2025) to formal verification, and contribute a Lean 4 formalization of the SM83 CPU
   as a verification target.

2. **Framework** (1.5p):
   - Two-level architecture diagram
   - Inner loop: formalizer via Claude Agent SDK / Gemini API, K iterations, lake
     build feedback
   - Outer loop: researcher agent modifies pipeline/ (system prompt, feedback
     template, helpers, iteration logic)
   - Scoring function Phi(c) v2 with 6 components
   - Information barrier
   - The structural analogy table (Karpathy's train.py <-> our pipeline/)

3. **SM83 CPU Model & Benchmark** (1p):
   - The SM83 formalization: architecture, design choices (pure functional memory,
     BitVec 8 as the decidable core), 1.1K LOC, 40 opcodes, 32 properties
   - Why formalize a real CPU: the gap between Lean's usual Mathlib domain and
     systems-level verification
   - 10 Pokemon Red bugs as a formal verification benchmark: diverse categories
     (bitwise, overflow, link desync, emergent interaction), including 2 novel
     discoveries
   - Scoring v2 design and why it matters

4. **Experiments** (1.5p):
   - Gemini Flash trajectory (8.3 -> 9.8 -> 9.95)
   - Sonnet trajectory (7.025 -> 7.9 -> 10.0)
   - **Key finding: different strategies per model** — the researcher adapts to each
     formalizer's failure modes
   - The git diff of each kept pipeline change as a figure/table
   - Scoring v1 vs v2 comparison showing deeper optimization
   - Baseline variance analysis (Sonnet's bimodal 0/1 vs Flash's smooth partials)

5. **Analysis & Discussion** (1p):
   - What the researcher discovers and in what order
   - The regex reverse-engineering observation (Gemini Flash)
   - The code extraction failure mode (Sonnet)
   - The whack-a-mole effect (trade-offs between bugs)
   - Training contamination: novel bugs (9, 10) scored 1.0 immediately
   - The SM83 model as a reusable artifact for Game Boy verification
   - Limitations: benchmark saturates, prompt engineering dominates reasoning

## Key Selling Points for Reviewers

1. **Fresh application domain.** Autoresearch for formal verification is new. Everyone
   else does competition math or neural net training.

2. **Real artifacts, not toy problems.** The bugs come from a real Game Boy game
   codebase. The proofs compile in Lean 4 against a real CPU model. The assembly is
   from the actual pokered disassembly.

3. **A new Lean 4 formalization.** The SM83 CPU model is (to our knowledge) the first
   formal model of the Game Boy processor in a modern ITP. It includes 32 machine-checked
   algebraic properties and is immediately reusable. This extends Lean 4's reach beyond
   pure math into hardware/systems verification — directly relevant given Leo de Moura
   is an invited speaker.

4. **Multi-model comparison with emergent adaptation.** The researcher agent discovers
   *different* strategies for Gemini Flash vs Claude Sonnet. This is not designed — it
   emerges from the optimization loop adapting to each model's failure modes. Confirmed
   by the workshop assessment's prediction before running the experiment.

5. **The researcher agent exhibits interesting behaviors.** Reverse-engineering the
   scoring regex. Discovering 5 improvements simultaneously. Trading off between bugs.
   Adapting to model-specific failure modes. These are emergent behaviors, not designed.

6. **Reproducible and open.** The entire framework, SM83 model, benchmark, and pipeline
   configurations can be released. Non-archival workshop means no conflict with a
   future full paper.

7. **Multi-model.** Claude Agent SDK + Gemini API dispatch shows the framework is
   model-agnostic (and the inner/outer model separation is principled).

## Risks and Mitigations

- **"Too easy" critique**: Even with scoring v2, the benchmark saturates in 1-3 steps.
  Mitigate by: (a) showing the scoring v1 -> v2 progression and arguing for harder
  future benchmarks, (b) emphasizing the *qualitative* findings (different strategies
  per model, emergent behaviors) over the raw scores, (c) framing saturation as a
  feature of the benchmark's tractability for a workshop paper.

- **"Just prompt engineering" critique**: The researcher's improvements are all system
  prompt edits. Mitigate by framing this as *the* finding: "for current LLMs, formal
  verification quality is dominated by prompt structure, not model capability or
  iteration depth." This is a useful negative result.

- **Small benchmark**: 10 bugs. Mitigate by noting diversity (7 categories, 2 novel
  discoveries, L1-L4 coverage) and that scaling to more bugs is straightforward. The
  SM83 model supports any Game Boy program, not just Pokemon Red.

- **"CPU model is too simple" critique**: The SM83 is an 8-bit CPU with ~40 opcodes —
  far simpler than ARM or RISC-V. Mitigate by arguing this is a *feature*: the
  decidability of `BitVec 8` via `native_decide` enables fully automated proofs, making
  it an ideal testbed for LLM-guided verification. Scaling to more complex ISAs is
  future work.

## Verdict

**Submit it.** We now have all the experimental data needed:

- Two complete multi-model trajectories (Gemini Flash and Sonnet) with different
  optimization dynamics
- A standalone Lean 4 artifact (SM83 CPU, 1.1K LOC, 32 theorems) that has independent
  value
- A clear story: autoresearch for formal verification, with a real CPU model, real bugs,
  and emergent researcher behaviors that differ across models

The deadline is May 25 — 5.5 weeks is comfortable for writing a 6-page paper. The
only remaining experimental work (ablations) is nice-to-have, not blocking.
