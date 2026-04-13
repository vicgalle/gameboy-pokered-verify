# Autoresearch Batch Results: Sonnet `batch_01`

**Date**: 2026-04-13
**Model**: Claude Sonnet
**Bugs**: 5 (Focus Energy, 1/256 Accuracy, Blaine AI, Heal Overflow, Psywave Desync)
**Total wall-clock time**: ~53 minutes
**Information given to agent**: Informal bug description + pokered codebase path only

## Headline Numbers

| # | Bug | Compiles | Agent Thm | GT Thm | Agent LOC | GT LOC | Levels | Time | Iters |
|---|---|---|---|---|---|---|---|---|---|
| 1 | Focus Energy | **yes** | 8 | 10 | 187 | 195 | L1,L2,L3 | ~9m | 2 |
| 2 | 1/256 Accuracy | **yes** | 13 | 12 | 195 | 182 | L1,L2,L3 | ~9m | 2 |
| 3 | Blaine AI | **yes** | 8 | 12 | 182 | 205 | L1,L2,L3 | ~12m | 3 |
| 4 | Heal Overflow | **yes** | 17 | 11 | 328 | 143 | L1,L2,L3 | ~15m | 2 |
| 5 | Psywave Desync | **yes** | 14 | 10 | 312 | 227 | L1,L2,L3,L4 | ~8m | 2 |
| | **Totals** | **5/5** | **60** | **55** | **1204** | **952** | **100% coverage** | **~53m** | |

- **Compilation rate**: 5/5 (100%)
- **Level coverage**: 100% (agent matched all target levels on every bug)
- **Agent total theorems**: 60 vs 55 manual (agent proved more overall)

## Qualitative Analysis Per Bug

### Bug 1 — Focus Energy (wrong bitwise op)

The agent correctly identified `srl` vs `sla` in `CriticalHitTest`
(`engine/battle/core.asm`), modeled the full 3-shift pipeline, and proved the
"quarters the crit rate" relationship (`critRateBuggy = critRateNoFocus >>> 2`).
It also used the `BugClaim` harness with a structured witness and fix.

Slightly fewer theorems than our manual version (8 vs 10) — missing
`focus_energy_speed1_degenerate` and `crit_input_bounded` — but captures all
essential properties. The agent independently noted that fixed Focus Energy gives
the same rate as no-Focus-Energy for normal moves.

**Modeling choice**: `BitVec 8`, same as ours. Faithful to the assembly.

### Bug 2 — 1/256 Accuracy (off-by-one)

The agent **outperformed** our manual version (13 vs 12 theorems). It independently
modeled `rlc3` (the three-rotation bijection in `CriticalHitTest`), proved
`rlc3_injective`, and proved both existence and uniqueness of the crit bug trigger
per threshold — a result we did not explicitly state.

It also found the `percent` macro (`macros/data.asm`) and its implications. The
`bug_iff` characterization (`impl != spec <-> r = t`) exactly matches our
`bug_iff_equal`.

**Modeling choice**: `BitVec 8`, same as ours. Separate accuracy and crit sections.

### Bug 3 — Blaine AI (missing precondition)

Modeled with `Nat` instead of `UInt16` (reasonable for this bug — avoids wrapping
issues and makes `omega` easier). The bug characterization (`bug_characterization`)
is a clean biconditional. The `hpFraction_full_health_false` lemma — proving that
`hp < hp / 4` is impossible for any `hp` — is a nice touch.

Fewer theorems than our version (8 vs 12). The agent did not:
- Model other trainers (Erika, Lorelei, Agatha) for comparison
- Quantify waste (`full_hp_zero_gain`, `partial_waste`)

However, the core properties (existence, characterization, fix) are all present.

**Modeling choice**: `Nat` (we used `UInt16`). Both valid, different trade-offs.

### Bug 4 — Heal Overflow (broken 16-bit comparison)

The agent produced the **strongest characterization** of the batch:
`false_positive_char` is a complete biconditional over all 4 input bytes,
identifying both the primary case (`h1 < h2 /\ l1 = l2 + 1`) and the exotic
case (`h2 < h1 /\ l1 = l2`).

At 17 theorems and 328 LOC it is the most verbose. The 7 helper lemmas about
`BitVec 8` ordering (`bv8_sub1_eq_zero_iff`, `bv8_lt_asymm`, etc.) are
infrastructure our manual version avoided by using `native_decide` more
aggressively on the final theorems. But the characterization theorem is arguably
more explicit and self-contained than ours.

**Modeling choice**: `BitVec 8` for the four bytes, same as ours. Faithful to
the assembly's byte-by-byte processing.

### Bug 5 — Psywave Desync (symmetry violation, L4 relational)

The most impressive result. The agent achieved **L4** (relational), modeling
`LinkBattleState` and `simulateLinkBattle` to prove cross-system divergence.

Key results:
- `desync_on_zero_prefix`: universal theorem (not just concrete examples)
- `accepts_agree_on_nonzero`: zero is the sole divergence source
- `link_battle_desync_general`: for any `level >= 1` with a leading zero in the
  RNG stream, the two Game Boys permanently diverge
- `fix_correct`: proved via function-equality rewriting

Used `List Nat` rather than our `LinkRNG` structure — functionally equivalent
but more transparent. Compiled on the **first attempt** (1 iteration).

**Modeling choice**: `List Nat + Nat` (we used a `LinkRNG` structure with index).
Agent's version is more explicit; ours is more encapsulated.

## Structural Observations

### Modeling choices diverge in interesting ways

| Bug | Agent model | Manual model | Notes |
|---|---|---|---|
| 1 (Focus Energy) | `BitVec 8` | `BitVec 8` | Same approach |
| 2 (1/256) | `BitVec 8` | `BitVec 8` | Agent added `rlc3` modeling |
| 3 (Blaine AI) | `Nat` | `UInt16` | Agent avoids wrapping, enables `omega` |
| 4 (Heal Overflow) | `BitVec 8` x4 | `BitVec 8` x4 | Same approach |
| 5 (Psywave) | `List Nat` | `LinkRNG` struct | Functionally equivalent |

### The agent is more verbose

1204 vs 952 total lines. The agent writes more helper lemmas, longer docstrings,
and more `#eval` demonstrations. For Bug 4, it built 7 `BitVec 8` ordering lemmas
that we handled implicitly. This is a different proof style (explicit helper
infrastructure vs more aggressive `native_decide`), not necessarily a flaw.

### Assembly analysis is excellent

Every `results.md` contains accurate line numbers, faithful assembly transcriptions,
and correct identification of the root cause. The agent correctly found and quoted
self-documenting comments:
- Bug 2: "note that this means that even the highest accuracy is still just a
  255/256 chance, not 100%"
- Bug 5: "it's possible for the enemy to do 0 damage with Psywave, but the player
  always does at least 1 damage"

### Compile iteration count is low

| Bug | Iterations | Notes |
|---|---|---|
| 1 | 2 | Fixed `native_decide` free-variable pattern |
| 2 | 2 | Removed `Finset`-based approach (no Mathlib) |
| 3 | 3 | Fixed `omega`/`simp` interaction with constants |
| 4 | 2 | Worked around `omega` not supporting BitVec ordering |
| 5 | 2 | Compiled on first real attempt |

The agent consistently diagnosed `native_decide` free-variable issues and
`omega`/`BitVec` limitations correctly, converging quickly.

## What the Agent Missed

Compared to our manual formalizations:

1. **No CPU-level proofs** for bugs 3-5. Our versions include
   `sm83_accuracy_matches_model` and `critCalcBuggySM83` that validate the
   high-level model against the SM83 CPU state. The agent stayed high-level.

2. **No cross-trainer comparison** for Bug 3. We modeled Erika, Lorelei, and
   Agatha to show Blaine is the *only* trainer who heals unconditionally.

3. **No waste quantification** for Bug 3. We proved `full_hp_zero_gain` (zero
   effective healing at full HP) and `partial_waste` (< 50 HP gained near max).

4. **No gameplay reachability analysis** for Bug 4. We named specific Pokemon
   (Snorlax at 524 HP, Chansey at 703 HP) with exact HP values demonstrating
   the bug in real gameplay.

5. Some proofs used `decide` instead of `native_decide` — both valid but
   `native_decide` is faster for large finite types.

## What the Agent Did Better

1. **Bug 2**: Proved `rlc3_injective` (bijectivity of the rotation) and used it
   to establish uniqueness of the crit bug trigger — a result we did not state.

2. **Bug 4**: Complete biconditional characterization covering both the primary
   and exotic false-positive cases in a single theorem.

3. **Bug 5**: Universal desync theorem (`link_battle_desync_general`) proved by
   lemma composition rather than concrete-example enumeration.

4. **BugClaim harness usage**: Bugs 1 and 5 used the structured `Harness.BugClaim`
   type with witnesses and fixes — a feature we built but the agent adopted
   independently.

## Verdict

The autonomous Sonnet agent, given only informal bug descriptions and a codebase
pointer, produced formalizations that **match or exceed** our manually crafted
proofs on all 5 bugs in terms of level coverage. The total wall-clock time was
~53 minutes for all 5 bugs combined.

The results are strong enough that they could be merged into the project with
minor polish (namespace renaming, removing redundant helpers). The main gap is
in "bonus" content — cross-trainer comparisons, gameplay reachability, CPU-level
validation — rather than in core formalization quality.

### Summary Scores

| Metric | Score |
|---|---|
| Compilation rate | 5/5 (100%) |
| Level coverage | 5/5 bugs at full target levels (100%) |
| Theorem count vs GT | 60 vs 55 (agent +9%) |
| LOC vs GT | 1204 vs 952 (agent +26%, more verbose) |
| Mean iterations | 2.2 (low — fast convergence) |
| Mean time per bug | ~10.6 minutes |
