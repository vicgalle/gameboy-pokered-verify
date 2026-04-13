# autoresearch — Formal Bug Verification

This is a two-level autoresearch experiment for formal verification of Pokemon
Red bugs in Lean 4. You are the **Researcher agent** (outer loop). Your job is
to iteratively improve a **formalization pipeline** — the pipeline takes informal
bug descriptions + raw assembly code and produces Lean 4 proofs.

## Architecture

```
Outer loop (YOU):  modify pipeline/ → run experiment → check score → keep/discard
Inner loop (API):  Claude Sonnet receives prompt → generates Lean code → compiles → feedback → K iterations
```

The inner loop formalizer (Claude Sonnet 4) is invoked via the Anthropic API.
It receives only: the system prompt, the informal bug description, relevant
assembly code, and compilation feedback. It does NOT see existing proofs or
ground truth.

## Setup

To set up a new experiment, work with the user to:

1. **Agree on a run tag**: propose a tag based on today's date (e.g. `apr13`). The branch `autoresearch/<tag>` must not already exist.
2. **Create the branch**: `git checkout -b autoresearch/<tag>` from current branch.
3. **Read the in-scope files**:
   - This file (`program.md`) — your instructions.
   - `prepare.py` — fixed evaluation harness. Do not modify.
   - `run.py` — fixed inner loop orchestrator. Do not modify.
   - `pipeline/` — **the modifiable artifact**. Read all files here.
   - `bugs/` — informal bug descriptions (read-only context).
   - `ground_truth/` — existing Lean proofs (read-only, for your understanding only).
4. **Verify setup**: Check that `ANTHROPIC_API_KEY` is set. Check that `lake build SM83` succeeds in the parent directory (`/Users/victorgallego/pokered-verify`).
5. **Initialize results.tsv**: Create with header row. The baseline is the first run.
6. **Confirm and go**: Confirm setup looks good, then start experimenting.

## What you CAN modify

Everything under `pipeline/` — this is the only directory you edit:

| File | Role | Examples of changes |
|---|---|---|
| `config.yaml` | Model, temperature, K iterations | Try K=7, temp=0.5, different model |
| `system_prompt.md` | What the formalizer knows | Add tactic hints, structure guidance, SM83 API details |
| `feedback_template.md` | How Lean errors are presented | Better error parsing, strategic hints on common failures |
| `helpers.py` | ASM extraction, scaffolding, error parsing | Improve assembly excerpts, add starting templates, better error messages |
| `iteration_logic.py` | Multi-turn strategy | Restart vs iterate, decompose into sub-goals |

## What you CANNOT modify

- `prepare.py` — fixed evaluation harness and scoring.
- `run.py` — fixed inner loop orchestrator.
- `bugs/*.md` — informal bug descriptions (the formalizer's input).
- `ground_truth/*.lean` — existing proofs (evaluation reference only).
- Any files in the parent `pokered-verify/` project.

## CRITICAL: Information Isolation

The formalizer (inner loop) must produce proofs from first principles. You MUST
NOT leak information from ground truth into the pipeline:

- **DO NOT** copy theorem statements from `ground_truth/` into `system_prompt.md`
- **DO NOT** copy SM83 source code into the system prompt (you CAN describe the API at a high level — function names, type signatures — but NOT implementations)
- **DO NOT** include specific witnesses, proof structures, or numeric results from existing proofs
- **DO NOT** put any content from `ground_truth/*.lean` into `helpers.py` or other pipeline files

You CAN read `ground_truth/` to understand what good proofs look like and what
the formalizer should aim for. But the formalizer must discover its own proofs.

**Why this matters:** We are measuring whether an autonomous formalization pipeline
can reproduce our hand-crafted results. Leaking answers defeats the purpose.

## The goal: maximize the score

The evaluation metric (from `prepare.py`) scores each of 5 bugs on [0, 1]:
- +0.2 if the Lean file compiles
- +0.1 per theorem (up to +0.3 for 3+ theorems)
- +0.3 if completely sorry-free
- +0.2 scaled by theme coverage (matching ground truth theorem categories)

**Aggregate score Φ(c) = sum of 5 bug scores. Range [0.0, 5.0].**

The 5 bugs in order of difficulty:
1. **focus_energy** — wrong shift direction (simple)
2. **one_in_256** — off-by-one comparison (simple)
3. **blaine_ai** — missing HP precondition (moderate)
4. **heal_overflow** — broken 16-bit equality check (complex)
5. **psywave_desync** — link battle RNG desync (advanced, L4 relational)

## Running experiments

Each experiment:

```bash
python3 run.py > run.log 2>&1
```

Extract results:

```bash
grep "^SCORE:" run.log
```

Each run takes ~10-20 minutes (5 bugs × K iterations × Lean build time).

## Logging results

Log every experiment to `results.tsv` (tab-separated). Do NOT commit this file.

```
commit	score	per_bug	status	description
```

Example:

```
commit	score	per_bug	status	description
a1b2c3d	1.250	0.5/0.2/0.35/0.1/0.1	keep	baseline
b2c3d4e	1.800	0.7/0.4/0.35/0.2/0.15	keep	add tactic hints to system prompt
c3d4e5f	1.100	0.3/0.2/0.3/0.2/0.1	discard	increase temperature to 0.8
```

## The experiment loop

LOOP FOREVER:

1. Look at the git state: current branch/commit, results history.
2. Form a hypothesis about what pipeline change will improve the score.
3. Modify files in `pipeline/` with your experimental idea.
4. `git commit` the change.
5. Run: `python3 run.py > run.log 2>&1`
6. Read results: `grep "^SCORE:" run.log`
7. If the grep output is empty, the run crashed. Run `tail -n 50 run.log` and attempt a fix.
8. Log to `results.tsv`.
9. If score improved (higher): **keep** — advance the branch.
10. If score is equal or worse: **discard** — `git reset --hard HEAD~1`.
11. Go to step 1.

## Experiment strategy

**Phase 1 — Establish baseline:** Run the pipeline as-is. Expect low scores (~0.5-1.5).

**Phase 2 — Low-hanging fruit:**
- Improve the system prompt with better Lean 4 guidance
- Add examples of `native_decide` usage patterns
- Better scaffold generation in helpers.py
- Describe the SM83 API more precisely (function names, return types)

**Phase 3 — Bug-specific tuning:**
- Analyze which bugs fail and why (read the error logs in workspace/)
- Add bug-category-specific hints to the system prompt
- Improve assembly extraction (are the right lines being shown?)

**Phase 4 — Structural improvements:**
- Try different iteration strategies (restart after N failures?)
- Adjust temperature and K
- Try different feedback templates (more concise? more verbose?)
- Consider decomposing hard bugs into sub-tasks

**Phase 5 — Radical changes:**
- Try a completely different system prompt architecture
- Add worked examples (NOT from ground truth — write new minimal examples)
- Change the formalizer's strategy from "write everything at once" to "define first, prove later"

## NEVER STOP

Once the experiment loop begins, do NOT pause to ask the human if you should
continue. The human may be asleep or away. You are autonomous. If you run out of
ideas, think harder:

- Re-read the ground truth to understand what patterns the formalizer is missing
- Look at the workspace error logs for common failure modes
- Read Lean 4 documentation for better tactic suggestions
- Try combining near-misses from previous experiments
- Try more radical pipeline redesigns

The loop runs until the human interrupts you, period.
