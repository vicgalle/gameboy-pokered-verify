# gameboy-pokered-verify

[![Lean Action CI](https://github.com/vicgalle/gameboy-pokered-verify/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vicgalle/gameboy-pokered-verify/actions/workflows/lean_action_ci.yml)

A Lean 4 formalization of the Game Boy's Sharp SM83 CPU, validated through machine-checked proofs of known bugs in [Pokemon Red](https://github.com/pret/pokered).

## What This Is

The main contribution is a **formal model of the SM83 instruction set** in Lean 4 — covering registers, flags, memory, and ~40 opcodes with semantics faithful to the hardware specification. The model is designed to be reusable for any Game Boy program analysis.

As an application, we use this model to **formally verify known bugs in Pokemon Red**: translating buggy assembly routines into Lean, proving the bugs exist, characterizing exactly when they trigger, and verifying that proposed fixes are correct. Lean's type checker is the trusted oracle — if it compiles, the proofs are valid.

## SM83 CPU Model

The core of this project is a Lean 4 formalization of the Sharp SM83, the CPU powering the original Game Boy.

### Architecture

The CPU state is modeled as a structure with all eight 8-bit registers (A, F, B, C, D, E, H, L), 16-bit SP and PC, a total memory function `BitVec 16 -> BitVec 8`, and a halt flag. Register pair accessors (BC, DE, HL, AF) and little-endian memory read/write are derived from this.

The flag register F follows the SM83 spec: bit 7 = Zero, bit 6 = Subtract, bit 5 = Half-carry, bit 4 = Carry, bits 3-0 always zero. Every arithmetic and logic opcode sets flags according to the hardware reference.

### Instruction Coverage

| Category | Opcodes | File |
|---|---|---|
| Arithmetic | ADD, ADC, SUB, SBC, CP, INC, DEC (8-bit), INC/DEC (16-bit), ADD HL | `Arithmetic.lean` |
| Logic | AND, OR, XOR, CPL, SCF, CCF | `Logic.lean` |
| Shifts & Rotates | SRL, SLA, SRA, SWAP, RLCA, RRCA, RLA, RRA | `Logic.lean` |
| Bit Operations | BIT, SET, RES | `Logic.lean` |
| Loads | LD r,r / LD r,n / LD r,[HL] / LD [HL],r / LD A,[nn] / LD [nn],A / LDI / LDD | `Load.lean` |
| Stack | PUSH, POP (BC, DE, HL, AF) | `Load.lean` |
| Control Flow | JP, JR (unconditional + NZ/Z/NC/C), CALL, RET (unconditional + conditional), JP [HL] | `Control.lean` |
| Misc | HALT, NOP, DI, EI | `Control.lean` |

### Validation

Each opcode includes `#eval` tests that run at build time, cross-referenced against the SM83 hardware specification:

```
-- ADD A, 0xFF when A = 0x01 → A = 0x00, Z=1, H=1, C=1
#eval
  let s := defaultState.setA 0x01
  let s' := execAddA s 0xFF
  (s'.a == 0x00, s'.zFlag == true, s'.hFlag == true, s'.cFlag == true)
  -- output: (true, true, true, true)
```

16 validation tests cover arithmetic (ADD, SUB, CP, INC, DEC with edge cases like overflow and zero) and logic (SRL, SLA, AND, XOR, SWAP, BIT) including flag behavior.

## Application: Pokemon Red Bug Verification

As a demonstration of the CPU model, we formally verify known bugs from the [pret/pokered](https://github.com/pret/pokered) disassembly.

### Focus Energy Critical Hit Bug

**The bug:** In `CriticalHitTest`, the crit rate `b` starts as `base_speed >>> 1` (always ≤ 127). The Focus Energy branch should do `sla b` (double it back), but instead does `srl b` (halves it again) — quartering the rate instead of restoring it.

```
                        With Focus Energy (bug)     Without Focus Energy
b = base_speed / 2      73 → srl → 36              73 → srl → 36
Focus Energy branch      36 → srl → 18 (BUG)        36 → sla → 72
```

**Proved theorems:**

| Theorem | Statement |
|---|---|
| `focus_energy_bug` | The bug exists (witness: base_speed=4) |
| `focus_energy_always_wrong` | Bug is unconditionally wrong for all base speeds ≥ 2 |
| `focus_energy_reduces_rate` | Buggy result ≤ correct result for all inputs |
| `focus_energy_strictly_worse` | Buggy result < correct result for base speeds ≥ 4 |
| `focus_energy_quarter_rate` | Correct result is at least 4x the buggy result (for base speeds ≥ 4) |
| `focus_energy_fix_correct` | Replacing `srl` with `sla` matches the no-Focus-Energy path |
| `crit_input_bounded` | After initial `srl`, input is always ≤ 127 (no overflow possible) |
| `focus_energy_cpu_bug` | Bug reproduces at the full SM83 opcode level |

**Modeling lesson:** An early naive model (treating the bug as `x >>> 1` vs `x <<< 2` on raw 8-bit values) produced a false "discovery" that rate=73 was an overflow coincidence. The real assembly bounds the input to ≤ 127 via an initial `srl`, making overflow impossible. Lean caught the error in the naive model — but the fix was to model the assembly more faithfully, not to weaken the theorem. This highlights that **formal verification is only as good as the model**: Lean guarantees your proofs are correct, but cannot guarantee your model matches the real code.

### Blaine AI Super Potion Bug

**The bug:** Blaine's AI calls `AIUseSuperPotion` without first checking if his Pokemon's HP is low enough to need healing. Every other healing trainer (Erika, Lorelei, Agatha, Sabrina, Rival) calls `AICheckIfHPBelowFraction` first.

```asm
BlaineAI:                          ErikaAI:
  cp 25 percent + 1                  cp 50 percent + 1
  ret nc                             ret nc
  jp AIUseSuperPotion  ; BUG!        ld a, 10
                                     call AICheckIfHPBelowFraction  ; ← HP check
                                     ret nc
                                     jp AIUseSuperPotion
```

**Proved theorems:**

| Theorem | Statement |
|---|---|
| `blaine_heals_at_full_hp` | Blaine uses Super Potion even at full HP |
| `blaine_always_heals` | Blaine's AI unconditionally heals (always returns `some`) |
| `blaine_wastes_when_healthy` | For any HP above the threshold, Blaine wastes the item |
| `full_hp_zero_gain` | At full HP, 0 HP is gained — complete waste |
| `partial_waste` | When HP is within 50 of max, less than 50 HP is gained |
| `blaine_fix_heals_when_needed` / `_skips_when_healthy` | Fixed AI heals iff HP is low |
| `blaine_unique_unconditional` | Blaine is the only trainer who heals unconditionally |

### 1/256 Accuracy Miss & Critical Hit Miss

**The bugs:** Two routines use `cp b; jr/ret nc` to compare a random byte against a threshold. The SM83 `cp` sets carry when `a < b`, so `jr nc` jumps when `a >= b`. This gives `>=` where `>` (strictly greater) is needed — the boundary value `random == threshold` is a "fail" instead of a "pass".

```asm
; MoveHitTest (accuracy)          ; CriticalHitTest (crits)
call BattleRandom                 call BattleRandom
cp b                              cp b
jr nc, .moveMissed  ; BUG         ret nc              ; BUG
; miss when random >= accuracy    ; no crit when random >= critRate
; should be: random > accuracy    ; should be: random > critRate
```

Both share the same arithmetic structure (`<` vs `≤`), so we prove the properties generically and instantiate for both.

**Proved theorems:**

| Theorem | Statement |
|---|---|
| `accuracy_bug_exists` / `crit_bug_exists` | The bugs exist (witness: random=255, threshold=255) |
| `bug_iff_equal` | Bug triggers **iff** random == threshold (exact characterization) |
| `bug_at_every_threshold` | The bug affects every threshold value, not just 255 |
| `no_bug_when_unequal` | When random ≠ threshold, actual and spec agree |
| `exactly_one_extra_hit` | The spec accepts exactly one more value per threshold |
| `fix_correct` | The fix (`≤` instead of `<`) matches spec for all inputs |
| `max_threshold_always_passes` | With the fix, threshold=255 gives 100% pass rate |
| `sm83_accuracy_matches_model` | CPU-level `cp b; jr nc` matches the abstract model |

**Insight from formalization:** The community describes these as "100% accuracy moves can miss 1/256 of the time." The formal characterization is stronger: the bug affects **every** accuracy/crit-rate value, not just 255. A move with accuracy 200 has a 200/256 hit chance instead of 201/256. The 1/256 penalty applies universally — it's just most noticeable at 255 where it's the difference between "always" and "almost always."

**Evidence of developer intent:** The `percent` macro (`DEF percent EQUS "* $ff / 100"`) uses 255 as the denominator — `100 percent = 255`. The developers' mental model was "255 = 100%", which only works with `≤`. The strict `<` comparison breaks this model for every threshold value. For crits, the evidence is weaker (thresholds come from base speed, not the macro), but the arithmetic bug is identical.

### Psywave Link Battle Desync (L4 — Relational)

**The bug:** In link battles, both Game Boys share a synchronized random number list. Psywave has two *different* implementations — one for when the player attacks (rejects 0, range `[1, b)`) and one for the enemy (accepts 0, range `[0, b)`). When a 0 appears in the shared list, the player's loop consumes an extra random number, desynchronizing the shared RNG index. All subsequent battle randomness diverges permanently.

```asm
; Player (core.asm 4664-4670)     ; Enemy (core.asm 4785-4789)
.loop                              .loop
  call BattleRandom                  call BattleRandom
  and a          ; test if 0         cp b
  jr z, .loop    ; REJECT 0 ←BUG    jr nc, .loop   ; reject >= b only
  cp b                               ld b, a        ; accept [0, b)
  jr nc, .loop   ; reject >= b
  ld b, a        ; accept [1, b)
```

**Proved theorems:**

| Theorem | Statement |
|---|---|
| `player_never_zero` | Player Psywave always deals ≥ 1 damage (universal, by induction) |
| `enemy_can_deal_zero` | Enemy Psywave can deal 0 damage |
| `desync_level50` / `desync_level100` | Concrete desyncs: player idx=2, enemy idx=1 after seeing 0 |
| `desync_multiple_zeros` | Multiple leading zeros widen the desync (idx=3 vs idx=1) |
| `no_desync_when_nonzero` | No desync when first value is nonzero (both agree) |
| `desync_propagates` | After desync, all subsequent random draws diverge |
| `fix_preserves_sync` | Making both loops identical preserves link sync |
| `player_psywave_strictly_better` | Even outside link battles, player's Psywave has higher expected damage |

**Insight:** This is our only **L4 relational** bug — the property isn't about a single computation being wrong, but about two *copies* of the game diverging. The formalization models the shared `LinkRNG` state and proves that the asymmetric zero-rejection is the root cause, and that the desync is permanent (all subsequent draws diverge). As a corollary, the same asymmetry means the player's Psywave can never deal 0 damage while the enemy's can — a known but often overlooked consequence (E[damage] differs by 0.5 HP at level 50).

### Stat Scaling: Defense-Zero Freeze & Wrapping Analysis

**The routine:** When either attack or defense exceeds 255, both stats are divided by 4 to fit in a byte (`ld b, l` takes only the low byte). Values > 1023 wrap around: `scaled = (stat/4) mod 256`. The offensive stat is bumped to 1 if zero, but **the defensive stat is not** — causing a division-by-zero freeze.

**Proved theorems:**

| Theorem | Statement |
|---|---|
| `defense_zero_freeze` | Defense 1-3 becomes 0 after /4 scaling → division by zero freeze |
| `defense_4_survives` | Defense 4 is the minimum that survives scaling |
| `damage_cliff_1024` | At the 1023→1024 boundary: damage ratio drops from 10 to 0 |
| `attack_not_monotone` | Increasing attack does NOT always increase damage (for uncapped values) |
| `periodic_collapse` | Wrapping recurs at every multiple of 1024 |
| `scaling_is_mod256` | Exact characterization: `(stat/4) mod 256` |

**Reachability — independent analysis correction:** The 999 stat cap (`MAX_STAT_VALUE`) in `effects.asm` prevents the *offensive* stat from exceeding 1023 through normal stat stages (Swords Dance). With the cap, the actual SD progression is 1, 3, 4, **4** — not 1, 3, 4, 1. The sawtooth wrapping theorems (`swords_dance_regression`, `three_sds_equals_zero_sds`) are mathematically correct for uncapped values but **do not occur in normal gameplay for the offensive stat**.

However, **Reflect/Light Screen bypass the 999 cap** entirely — see the next section.

The **defense-zero freeze** is confirmed reachable in normal gameplay: a Level 100 physical attacker (attack > 255) vs a low-level Pokémon whose defense has been reduced to 1-3 via Leer/Screech triggers the freeze.

### Reflect/Light Screen Overflow (Verified — Reachable)

**The bug:** Reflect doubles defense via `sla c; rl b` with **no cap**. When defense ≥ 512 (achievable via Barrier/Harden on high-defense Pokémon), the doubled value exceeds 1023 and wraps in `.scaleStats`. Reflect then **reduces** effective defense — the opposite of its purpose. At exactly 512, it causes a **game freeze**.

```
Defense with attack=300 (triggers scaling):
  def=400: no_reflect=100, reflect=200  ← Reflect helps ✓
  def=511: no_reflect=127, reflect=255  ← Reflect peaks
  def=512: no_reflect=128, reflect=0    ← GAME FREEZE!
  def=520: no_reflect=130, reflect=4    ← Reflect gives 4 instead of 130!
  def=696: no_reflect=174, reflect=92   ← Reflect nearly halves defense
  def=999: no_reflect=249, reflect=243  ← Reflect costs 6 points
```

**Proved theorems:**

| Theorem | Statement |
|---|---|
| `reflect_512_freezes` | Defense 512 + Reflect → effective defense 0 (freeze) |
| `no_reflect_512_ok` | Without Reflect, defense 512 scales to 128 (fine) |
| `reflect_hurts_cloyster` | Cloyster with Barrier + Reflect: defense drops from 174 to 92 |
| `modest_defense_catastrophe` | Defense 520 + Reflect: drops from 130 to 4 |
| `reflect_helps_below_512` / `reflect_hurts_above_512` | 512 is the exact threshold |
| `reflect_sawtooth` | Full sawtooth pattern: peaks at 511 (255), crashes at 512 (0) |

**Reachability (independently verified):** Cloyster (base defense 180) at level 100 has defense 458. A single **Withdraw** (+1 stage = 1.5x) gives 687 — already above 512. With Reflect: effective defense drops from 171 to 87. **One Withdraw + Reflect makes Cloyster take roughly twice the physical damage.** This is a natural competitive line that completely backfires due to the overflow.

Independent analysis confirmed that the specific practical consequence — **Reflect reducing defense after stat boosts** — is **not documented** on Bulbapedia, Smogon, or the pret wiki. The disassembly comments warn of "weird things" but no community resource explicitly states that Reflect can make a Pokémon take more damage. Light Screen has the identical bug with the Special stat.

### Badge Boost Stacking + Reflect (New Discovery — Emergent Interaction)

**The discovery:** Three separate mechanisms combine catastrophically: (1) badge boost stacking reapplies 9/8 to ALL stats on every stat change, (2) Reflect doubles defense without cap, (3) `.scaleStats` wraps at 1024. The result: **the opponent using Growl enables the Reflect overflow without any action from the player.**

```
Cloyster (defense=458), Thunder Badge, attack=300:
  Growls  Defense  No Reflect  With Reflect
  0       458      114         229  ← Reflect helps
  1       515      128         1    ← Reflect gives DEFENSE=1!!!
  2       579      144         33   ← still catastrophic
  3       651      162         69
  7       999      249         243
```

**Proved theorems:**

| Theorem | Statement |
|---|---|
| `one_growl_exceeds_512` | One badge boost pushes Cloyster's defense from 458 to 515 (> 512) |
| `one_growl_reflect_catastrophe` | One Growl + Reflect: effective defense = 1 (was 128) |
| `reflect_128x_worse` | Reflect divides effective defense by 128 instead of doubling it |
| `no_player_action_needed` | The overflow requires zero defensive moves from the player |
| `badge_reflect_near_freeze` | At defense 456, one badge boost + Reflect causes a game FREEZE |
| `badge_stacking_progression` | Complete stacking progression: 458→515→579→...→999 |

**Why this is novel (independently verified):** The Reflect overflow was known to the disassembly annotators, but the badge-boost-stacking enabler is undocumented. The disassembly warning at line 4084 assumes the Pokemon "already has 512+ defense" — it doesn't account for badge stacking dynamically crossing the threshold during battle. The scenario — *opponent uses Growl, player uses Reflect, Cloyster's effective defense drops to 1* — requires no setup from the player. Independent analysis confirmed that **Cloyster is the only Gen 1 Pokemon** where a single Growl triggers this (base defense 180 is the only value ≥ 179 among Reflect learners). At base defense 456 (DV=14), the interaction causes a **game freeze** (defense wraps to exactly 0).

### Accuracy/Evasion Stage Non-Cancellation (New Discovery — Latent Bug)

**The bug:** The `CalcHitChance` routine computes effective accuracy in two passes using the `StatModifierRatios` table. Two factors cause **equal accuracy and evasion boosts to not cancel**:

1. **Truncated fractions:** The table stores approximations (stage -1 = `66/100` instead of exact `2/3`). Product: `15/10 × 66/100 = 0.99 ≠ 1.0`.
2. **Intermediate truncation:** Even when the fraction product IS exact (stage ±3: `25/10 × 40/100 = 1.0`), floor division between the two passes loses precision. `255 × 25 / 10 = 637` (truncated from 637.5), then `637 × 40 / 100 = 254` (truncated from 254.8).

```
Equal ±stages on 255-accuracy move:  ±0→255  ±1→252  ±2→255  ±3→254  ±4→252  ±5→249  ±6→255
                                     loss:    0       3       0       1       3       6       0
```

**Proved theorems:**

| Theorem | Statement |
|---|---|
| `plus1_reduces_accuracy` | Equal ±1 boosts reduce effective accuracy (252 < 255) |
| `plus5_worst_noncancellation` | Equal ±5 boosts lose 6 accuracy points (249 vs 255) |
| `noncancellation_table` | Complete table: only ±0, ±2, ±6 perfectly cancel |
| `ratio_product_not_one` | Root cause 1: `15/10 × 66/100 = 990/1000 ≠ 1` |
| `plus3_almost` | Root cause 2: ±3 fractions are exact but intermediate truncation still loses 1 |
| `order_matters` | Reversing pass order gives different results (non-commutative) |
| `order_difference` | ±5 reversed: 248 vs 249 (both wrong, but differently!) |

**Practical impact — latent in Gen 1:** Independent analysis revealed that **no Gen 1 move raises accuracy stages** and **no Gen 1 move lowers evasion stages**. Accuracy can only go down (Flash, Sand-Attack), evasion can only go up (Double Team). The equal-boost cancellation scenario is impossible in normal Gen 1 gameplay. The bug is a genuine arithmetic artifact of the engine that becomes exploitable only in later generations where accuracy-raising moves (Hone Claws, Coil) exist. Stage ±3 is particularly notable: it proves that even with exact fraction products, the two-pass integer truncation alone is sufficient to break cancellation — a purely emergent property of the calculation order.

### BugClaim Harness

The `Harness.BugClaim` structure defines a reusable contract for verified bugs:

- `impl`: the buggy code, translated from assembly
- `spec`: the intended behavior
- `BugWitness`: a concrete input where impl diverges from spec (L1)
- `BugFix`: a replacement that matches spec for all inputs (L3)

Difficulty levels range from L1 (concrete witness) through L4 (relational/desync proofs).

### Target Bugs

| # | Bug | Category | Status |
|---|---|---|---|
| 1 | Focus Energy wrong shift | Wrong bitwise op | Verified |
| 2 | 1/256 accuracy miss | Off-by-one | Verified |
| 3 | 1/256 crit miss | Off-by-one | Verified |
| 4 | Substitute 0 HP | Arithmetic underflow | Planned |
| 5 | Heal overflow at 255/511 | Integer truncation | Planned |
| 6 | CooltrainerF AI always switches | Dead code | Planned |
| 7 | Blaine AI Super Potion | Missing precondition | Verified |
| 8 | Psywave link desync | Symmetry violation | Verified |
| 9 | Counter damage persists | Stale state | Planned |
| 10 | Reflect/Light Screen overflow | Arithmetic overflow | **Verified (reachable)** |
| 11 | Stat scaling defense-zero freeze | Division by zero / 8-bit wrapping | Verified |
| 12 | **Acc/Eva stage non-cancellation** | **Truncated fractions + intermediate truncation** | **Verified (new, latent in Gen 1)** |
| 13 | **Badge stacking + Reflect** | **Emergent interaction (3 systems)** | **Verified (new discovery)** |

## Project Structure

```
pokered-verify/
├── SM83/                          # SM83 CPU formalization (main contribution)
│   ├── Basic.lean                 # BitVec helpers, bit/nibble ops
│   ├── State.lean                 # CPUState: registers, memory, flags
│   ├── Flags.lean                 # Z/N/H/C flag semantics
│   ├── Memory.lean                # Memory read/write, stack ops
│   ├── Arithmetic.lean            # ADD, SUB, INC, DEC, CP (+16-bit)
│   ├── Logic.lean                 # AND, OR, XOR, shifts, BIT/SET/RES
│   ├── Load.lean                  # LD variants, PUSH/POP
│   └── Control.lean               # JP, JR, CALL, RET, conditions
├── PokeredBugs/                   # Application: verified pokered bugs
│   └── Proofs/
│       ├── FocusEnergy.lean
│       ├── BlaineAI.lean
│       ├── OneIn256.lean
│       ├── PsywaveDesync.lean
│       ├── StatScaling.lean
│       ├── AccEvaCancel.lean
│       ├── ReflectOverflow.lean
│       └── BadgeReflect.lean
├── Harness/
│   └── BugClaim.lean              # Structured type for bug claims
├── lakefile.toml
└── lean-toolchain                 # Lean 4.28.0
```

## Building

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).

```sh
lake build SM83 PokeredBugs Harness
```

All 33 build jobs should complete with no errors. Validation tests run automatically during the build.

## Proof Metrics

A standalone script computes quantitative metrics across all proof files: line breakdowns, theorem counts, tactic frequency, and automation rate.

```sh
uv run scripts/metrics.py
```

No extra setup needed — `uv` handles the Python dependency automatically via the inline metadata in the script.

## License

This project references the [pret/pokered](https://github.com/pret/pokered) disassembly for bug analysis. The Lean formalization and proofs are original work.
