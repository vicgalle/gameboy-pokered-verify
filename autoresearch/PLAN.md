# PLAN: True Autoresearch — Outer Optimization Loop

## Problem

What we currently have is **sequential independent formalization**: the agent
receives each bug separately and formalizes it from scratch. There is no outer
loop that iteratively improves a shared pipeline. This is a benchmark, not
autoresearch.

True autoresearch requires: **modify pipeline → run all bugs → measure aggregate
score → keep/discard → repeat**. The optimizable artifact is the formalization
pipeline itself (prompts, tactics, examples, scaffolding), and the metric is
aggregate formalization quality across all 5 bugs.

## Current Architecture (what exists)

```
run.sh / run_all.sh
  └─ For each bug:
       Claude Code agent receives (program.md + bug description)
       → searches pokered → writes Solution.lean → compiles → done

evaluate.py
  └─ Post-hoc analysis: counts theorems, detects levels, compares with GT
```

**Missing**: No outer loop. No pipeline modification. No keep/discard.

## Target Architecture (what we need)

Two-level system following the paper's c = (p, t, φ, H, ι, v) framework:

```
OUTER LOOP (Researcher R = Claude Code + researcher_program.md):
  ├─ Reads results from previous experiment
  ├─ Modifies pipeline/ (the optimizable artifact)
  ├─ git commit
  ├─ Runs: python3 run_inner.py > run.log 2>&1
  ├─ Reads: grep "^SCORE:" run.log
  ├─ If score improved → keep (advance branch)
  ├─ If score worse → discard (git reset --hard HEAD~1)
  └─ LOOP FOREVER

INNER LOOP (Formalizer M = Claude API via anthropic SDK):
  ├─ For each of 5 bugs:
  │    ├─ Constructs prompt from pipeline/ config + bug description
  │    ├─ K iterations: send prompt → get Lean code → lake build → feedback
  │    └─ Saves best attempt
  └─ Returns aggregate score Φ(c)
```

## Implementation Plan

### Phase 1: Create the pipeline/ directory (the modifiable artifact)

These are the files the Researcher agent will iteratively modify:

```
autoresearch/pipeline/
├── config.yaml               # K iterations, temperature, model
├── system_prompt.md           # What the formalizer knows about Lean/SM83
├── feedback_template.md       # How compilation errors are presented
├── helpers.py                 # Assembly extraction, Lean scaffolding, error parsing
└── iteration_logic.py         # Multi-turn strategy (restart vs continue)
```

**Initial content**: Extract the current program.md into these components.
- `system_prompt.md`: The Lean tactics reference, SM83 API docs, methodology
  sections from the current program.md
- `feedback_template.md`: Template for formatting `lake build` errors back to
  the formalizer. Placeholders: `{errors}`, `{parsed_issues}`
- `helpers.py`: Functions for extracting assembly context from pokered,
  generating Lean scaffolding, parsing Lean error messages
- `iteration_logic.py`: Controls whether to restart the conversation or
  continue iterating after a failed compilation
- `config.yaml`: Model (claude-sonnet-4-6-20250514), temperature (0.3),
  max_tokens (8192), iterations_per_bug (5)

### Phase 2: Write run_inner.py (the inner loop orchestrator)

Fixed file — NOT modified by the Researcher. Analogous to Karpathy's `uv run train.py`.

**Responsibilities**:
1. Load pipeline config from `pipeline/`
2. For each of 5 bugs:
   a. Load bug description from `bugs/`
   b. Extract assembly context using `helpers.extract_relevant_asm()`
   c. Construct prompt = `system_prompt.md` + bug description + assembly
   d. Run K iterations via Claude API (`anthropic.Anthropic().messages.create`)
   e. Each iteration: send prompt → get Lean code → write to temp workspace →
      `lake build` → format errors via `feedback_template.md` → send feedback
   f. Save best (compiling, most theorems) attempt
3. Evaluate all 5 results using scoring function
4. Print grep-able output:
   ```
   SCORE:            3.450
   focus_energy:     0.850  (compiles=True, theorems=6, sorry=0)
   one_in_256:       0.700  (compiles=True, theorems=4, sorry=1)
   ...
   ```

**Key design**: The formalizer is invoked via the **Claude API** (anthropic SDK),
NOT as a nested Claude Code session. This gives precise control over what the
formalizer sees (information barrier) and avoids recursive agent issues.

**Information barrier enforcement**: `run_inner.py` constructs API messages from
ONLY: `pipeline/system_prompt.md`, `bugs/<name>.md`, extracted assembly, and
previous formalizer output + build errors. A `FORBIDDEN_PATHS` check ensures no
content from `ground_truth.json`, existing proofs, or the project README leaks
into any API message.

**Dependencies**: `anthropic`, `pyyaml` (add to a `pyproject.toml`)

### Phase 3: Write scoring function (in run_inner.py or separate evaluate_inner.py)

Per-bug score on [0, 1]:
- **+0.2** if the Lean file compiles
- **+0.1** per theorem (up to +0.3 for 3+ theorems)
- **+0.3** if completely sorry-free
- **+0.2** scaled by ground truth theme coverage (matching theorem categories)

Aggregate: **Φ(c) = sum of 5 bug scores. Range [0.0, 5.0].**

Theme coverage uses keyword matching against ground truth categories:
- `bug_exists` / `witness` → L1
- `always` / `iff` / `characteriz` → L2
- `fix` / `correct` → L3
- `desync` / `player` / `enemy` / `diverge` → L4

This scoring function must be **deterministic** and **fast** (no LLM calls).

### Phase 4: Write researcher_program.md (outer loop instructions)

Adapted from Karpathy's program.md. The Researcher agent:

```markdown
## What you CAN modify
Everything under pipeline/ — this is the only directory you edit:
- config.yaml (K, temperature, model)
- system_prompt.md (what the formalizer knows)
- feedback_template.md (how errors are presented)
- helpers.py (assembly extraction, scaffolding, error parsing)
- iteration_logic.py (multi-turn strategy)

## What you CANNOT modify
- run_inner.py (fixed orchestrator)
- bugs/*.md (fixed bug descriptions)
- ground_truth.json (fixed evaluation reference)
- evaluate.py (post-hoc analysis, separate from scoring)

## The experiment loop
LOOP FOREVER:
1. Read results.tsv + diff history
2. Hypothesize what pipeline change will improve Φ(c)
3. Modify something in pipeline/
4. git commit
5. Run: python3 run_inner.py > run.log 2>&1
6. Read: grep "^SCORE:" run.log
7. Log to results.tsv
8. If SCORE improved → keep. If worse → git reset --hard HEAD~1
9. Go to 1.

## NEVER STOP
Run autonomously until manually interrupted.
```

**Critical constraint**: The Researcher CAN read `ground_truth.json` (to
understand what good proofs look like) but must NOT copy content from it into
`pipeline/` files (information barrier).

### Phase 5: Adapt existing scripts

- **run.sh** → Keep for single-bug manual testing
- **run_all.sh** → Keep for batch runs without outer loop
- **evaluate.py** → Keep for post-hoc analysis, add `--score` mode that
  outputs the Φ(c) score compatible with `run_inner.py`
- **Add `pyproject.toml`** with `anthropic` and `pyyaml` dependencies

### Phase 6: Lean workspace management in run_inner.py

For each bug's K iterations, `run_inner.py` needs a temporary Lean project:

```python
def create_eval_project(run_id: str) -> Path:
    """Create a temp Lean project with SM83 dependency for compilation testing."""
    eval_dir = Path(tempfile.mkdtemp(prefix=f"pokered-eval-{run_id}-"))
    # lakefile.toml with path dependency on SM83 from parent project
    # lean-toolchain matching parent (leanprover/lean4:v4.28.0)
    # Generated/ directory for formalizer output
    return eval_dir
```

The lakefile.toml uses a `[[require]]` path dependency on the parent project
for SM83, avoiding copying ~9 files per run.

### Phase 7: Validation and first experiment

1. Run `python3 run_inner.py` once manually → verify scoring works
2. Launch Researcher: `claude -p "Read researcher_program.md and start"`
3. Observe 2-3 iterations to verify keep/discard logic works
4. Let it run overnight for ~12 experiments

## File Structure After Implementation

```
autoresearch/
├── researcher_program.md       # NEW: Outer loop instructions (Karpathy-style)
├── program.md                  # Existing: inner loop agent instructions (for run.sh)
├── run_inner.py                # NEW: Inner loop orchestrator (Claude API)
├── run.sh                      # Existing: single-bug manual runs
├── run_all.sh                  # Existing: batch runs
├── evaluate.py                 # Existing: post-hoc analysis
├── ground_truth.json           # Existing: GT for comparison
├── pyproject.toml              # NEW: Python dependencies
├── results.tsv                 # NEW: Outer loop experiment log (untracked)
├── pipeline/                   # NEW: *** THE MODIFIABLE ARTIFACT ***
│   ├── config.yaml
│   ├── system_prompt.md
│   ├── feedback_template.md
│   ├── helpers.py
│   └── iteration_logic.py
├── bugs/                       # Existing: informal descriptions (minimal)
├── bugs_full/                  # Existing: full descriptions
├── template/                   # Existing: Lean workspace template (for run.sh)
├── results/                    # Existing: batch experiment outputs
├── .results_1/                 # Existing: Sonnet full results
└── .results_minimal/           # Existing: Sonnet minimal results
```

## What the Researcher Will Optimize

The configuration space c = (p, t, φ, H, ι, v):

| Component | File | Examples of changes |
|---|---|---|
| **p** (system prompt) | `system_prompt.md` | Add tactic examples, SM83 API details, worked examples |
| **t** (feedback template) | `feedback_template.md` | Better error parsing, strategic hints for common failures |
| **φ** (feedback function) | `helpers.py:parse_lean_errors()` | Classify errors, suggest specific fixes |
| **H** (helper library) | `helpers.py:generate_lean_scaffold()` | Better starting templates, assembly extraction |
| **ι** (iteration logic) | `iteration_logic.py` | Restart vs continue, decompose into sub-goals |
| **v** (validation) | `config.yaml` | K iterations, temperature, model selection |

## Expected Experimental Results

The Researcher should discover improvements like:
- "Adding the `have h : ∀ x, ... := by native_decide; exact h b` pattern to the
  system prompt eliminates the #1 compile error across all bugs" (we know this
  from batch_01's error patterns)
- "Providing the BugClaim harness structure in the system prompt improves theorem
  organization"
- "Temperature 0.5 produces more diverse modeling approaches for Bug 5"
- "Restarting the conversation after 2 failed compiles helps more than continuing"

## Estimated Cost and Time

- Each inner loop: ~25 Claude API calls (5 bugs × 5 iterations) ≈ $1-2 (Sonnet)
- Outer loop: ~5-10 minutes per experiment (dominated by Lean build times)
- Overnight run: ~72 experiments in 12 hours
- Total: ~$72-144 for a full overnight Sonnet run

## Risks and Mitigations

1. **Inner loop is slow** (5 bugs × 5 iterations × Lean build): Each experiment
   takes ~10-20 min. Mitigation: reduce K to 3 initially; parallelize bug
   formalizations if possible.

2. **Score is noisy** (LLM output varies): Same pipeline config can give different
   scores. Mitigation: run each config 2x and average; or use temperature=0 for
   determinism.

3. **Researcher might overfit to specific bugs**: A change that helps Bug 1 might
   hurt Bug 5. Mitigation: the aggregate Φ(c) captures this; also log per-bug
   scores so the Researcher can reason about tradeoffs.

4. **Information leakage**: Researcher reads ground_truth.json and might be tempted
   to encode specific theorems in the system prompt. Mitigation: run_inner.py has
   a FORBIDDEN_PATHS check; also, the Researcher prompt explicitly forbids this.
