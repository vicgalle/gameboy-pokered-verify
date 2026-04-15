# Autoresearch: Lean 4 Bug Formalization Pipeline Optimization

You are an autonomous researcher agent. Your goal is to **maximize the aggregate
formalization score Phi(c)** by iteratively modifying the **pipeline configuration**
-- the prompts, feedback templates, helper functions, and iteration logic that govern
how a formalizer LLM produces Lean 4 proofs for Pokemon Red bugs.

You work in a two-level loop: modify the pipeline -> run the inner formalization
loop -> observe the score -> keep or discard -> repeat. You never stop.

## Context

This project formally verifies known bugs in Pokemon Red using Lean 4 and a
formalization of the Game Boy's SM83 CPU. Ten bugs are tested:

1. **Focus Energy** -- wrong bitwise shift (srl vs sla) quarters crit rate
2. **1/256 Miss** -- off-by-one in accuracy/crit check (cp + jr nc)
3. **Blaine AI** -- missing HP precondition for healing item use
4. **Heal Overflow** -- 16-bit HP comparison done byte-by-byte overflows
5. **Psywave Desync** -- two different random loops desynchronize link battle
6. **Substitute** -- integer division gives 0 HP shield; user survives at 0 HP
7. **Bide Desync** -- asymmetric memory zeroing desyncs link battle (L4)
8. **Reflect Overflow** -- uncapped doubling wraps at 1024, reduces defense
9. **Acc/Eva Cancel** -- truncated fractions + floor division prevent cancellation (novel, latent)
10. **Badge + Reflect** -- badge stacking enables catastrophic Reflect overflow (novel discovery)

### The two levels

**Inner loop** (FROZEN -- you do NOT modify this):
A formalizer LLM receives a bug description + assembly context + system prompt, and
iterates K times: generate Lean code -> compile via `lake build` -> receive feedback
-> improve. The orchestrator (`run_inner.py`) handles workspace creation, compilation,
and scoring.

**Outer loop** (YOUR JOB):
You modify the pipeline configuration -- the files in `autoresearch/pipeline/` -- that
control what information and guidance the formalizer receives. You then run the inner
loop via `measure.sh` and observe the resulting score.

### Scoring function Phi(c)

Per-bug score on [0.0, 1.0]:
- **+0.2** if the Lean file compiles
- **+0.1** per theorem (up to +0.3 for 3+ theorems)
- **+0.3** if completely sorry-free
- **+0.2** scaled by ground truth theme coverage (matching proof levels L1-L4)

Aggregate: **Phi(c) = sum of 10 bug scores. Range [0.0, 10.0].**

## What you CAN modify

All files in `autoresearch/pipeline/`:

| File | Component | Examples of changes |
|------|-----------|-------------------|
| `pipeline/config.yaml` | Iteration params | K iterations, model, build timeout |
| `pipeline/system_prompt.md` | System prompt | Tactic examples, SM83 API details, worked examples, proof patterns |
| `pipeline/feedback_template.md` | Error feedback | Better error formatting, strategic hints for common failures |
| `pipeline/helpers.py` | Helper functions | Assembly extraction targets, error parsing, Lean scaffolding |
| `pipeline/iteration_logic.py` | Iteration strategy | Restart vs continue logic, failure thresholds |

## What you CANNOT modify

- `run_inner.py` -- the inner loop orchestrator (frozen)
- `bugs/*.md` -- the bug descriptions (frozen)
- `ground_truth.json` -- the evaluation reference (frozen)
- `evaluate.py` -- post-hoc analysis (frozen)
- `measure.sh` -- the measurement script (frozen)

You CAN (and should) read these files plus the pokered disassembly at
`/Users/victorgallego/pokered` and existing experiment results to understand the
problem deeply.

## Constraints

1. **The inner loop must complete successfully.** `run_inner.py` must finish without
   crashing. A crash = experiment failure.
2. **Information barrier.** You CAN read `ground_truth.json` to understand what good
   proofs look like, but you MUST NOT copy specific theorem statements, proof code,
   or key_insights from it into `pipeline/` files.
3. **No trivial leakage.** Do not embed complete solutions in the system prompt.
4. **Prompt accuracy.** The system prompt must accurately describe the SM83 API and
   tactics available to the formalizer.

## The experiment loop

LOOP FOREVER:

1. **Ideate**: Think about what pipeline modification to try next. Review your
   results.tsv, the current pipeline code, and the codebase.
2. **Implement**: Edit files in `autoresearch/pipeline/`. You may change one file or
   multiple.
3. **Run**: Execute `./autoresearch/measure.sh dense` (add `--model MODEL` to override).
4. **Evaluate**: Did the inner loop succeed? Did the score increase?
5. **Decision**:
   - If score **increased** and run succeeded: **KEEP**. Commit the pipeline changes
     with a descriptive message.
   - If score **same/decreased** or run **failed**: **DISCARD**. Revert with
     `git checkout -- autoresearch/pipeline/`.
6. **Log**: Record the result in `autoresearch/results.tsv`.
7. **Go to 1**.

**NEVER STOP.** Run experiments continuously until I interrupt you.

## Logging

Maintain `autoresearch/results.tsv` (tab-separated):

```
experiment	commit	score	bug1	bug2	bug3	bug4	bug5	delta	run_time_s	status	description
```

- **experiment**: Sequential number (0 = baseline)
- **commit**: Short git hash, or `-` for discarded
- **score**: Aggregate Phi(c) [0.0, 5.0]
- **bug1-bug5**: Per-bug scores [0.0, 1.0]
- **delta**: Change in score from baseline
- **run_time_s**: Wall-clock time
- **status**: `keep`, `discard`, or `crash`
- **description**: What pipeline modification was tried

## Strategy space

### Prompt engineering (system_prompt.md)
- Add worked examples of specific proof patterns (e.g., the BitVec 8 universal pattern)
- Add more SM83 API details (which operations set which flags, gotchas)
- Add tactic selection guidance per proof type
- Add assembly reading tips for common patterns
- Restructure for clarity and prioritization

### Feedback engineering (feedback_template.md)
- Better error categorization (type errors vs tactic failures vs unknown identifiers)
- Strategic suggestions based on error patterns ("if native_decide fails, try simp")
- Graduated hints (vague early, specific later)
- Progress encouragement when score improves

### Helper improvements (helpers.py)
- Better assembly extraction (add more labels/patterns per bug)
- Better error parsing (structured categories, severity ranking)
- Custom Lean scaffolding per bug type (bitwise, overflow, AI logic, link battle)

### Iteration logic (iteration_logic.py)
- Tune restart threshold (when to give up and start fresh)
- Progressive simplification (reduce theorem ambition after repeated failures)
- Different strategies for "compiles but low score" vs "doesn't compile"

## Tips

- **Read the assembly first.** Search `/Users/victorgallego/pokered` to understand each
  bug deeply. The better you understand the bugs, the better assembly you can extract.
- **Read existing results.** Check `autoresearch/results/` for what previous batch runs
  produced. Analyze common failure modes.
- **Compilation first.** A compiling file with fewer theorems scores higher than a
  non-compiling file with many.
- **The formalizer has no file access.** Everything it knows comes from the system prompt
  and the context provided by helpers.py. If it needs assembly, you must add it to the
  extraction targets.
- **native_decide is the power tool.** Most proofs over BitVec 8 can be solved with it.
  Make sure the system prompt emphasizes this.
- **One change at a time.** Isolate your modifications to understand what helps and what
  doesn't.
