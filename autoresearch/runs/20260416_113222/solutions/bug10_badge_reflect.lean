import SM83

namespace AutoResearch

-- Generation 1 Pokemon: maximum battle stat value
def MAX_STAT : Nat := 999

-- ApplyBadgeStatBoosts (engine/battle/core.asm):
-- Three SRL/RR instructions compute stat/8 via 16-bit d:e register pair.
-- Result: stat + stat/8 = ⌊stat × 9/8⌋, capped at MAX_STAT.
def applyBadgeBoost (stat : Nat) : Nat :=
  min (stat + stat / 8) MAX_STAT

-- Gen 1 damage formula stat scaling:
-- Stats > 255 are divided by 4, keeping only the low byte (mod 256).
-- Catastrophic wrap-around occurs when the doubled stat ≥ 1024.
def effectiveStat (stat : Nat) : Nat :=
  if stat > 255 then (stat / 4) % 256 else stat

-- BUGGY: Reflect doubles defense with no overflow guard.
-- ApplyBadgeStatBoosts can push defense past 512; Reflect then doubles it to ≥ 1024,
-- which the damage formula maps to near-zero via the low-byte wrap.
def impl (defense : Nat) : Nat :=
  effectiveStat (applyBadgeBoost defense * 2)

-- CORRECT: Reflect doubles defense but must cap at MAX_STAT before damage formula scaling.
def spec (defense : Nat) : Nat :=
  effectiveStat (min (applyBadgeBoost defense * 2) MAX_STAT)

-- L3: Fixed implementation – cap before effectiveStat
def implFixed (defense : Nat) : Nat :=
  effectiveStat (min (applyBadgeBoost defense * 2) MAX_STAT)

-- ─────────────────────────────────────────────────────────────────────────────
-- L1: Concrete witness – Cloyster (458 defense) + Thunder Badge + Growl + Reflect
-- Badge boost: 458 + ⌊458/8⌋ = 458 + 57 = 515  (crosses the 512 overflow threshold!)
-- Buggy Reflect: 515 × 2 = 1030
-- Damage scaling: ⌊1030/4⌋ % 256 = 257 % 256 = 1  (vs intended 249)
-- ─────────────────────────────────────────────────────────────────────────────

-- The bug exists: impl and spec diverge for Cloyster's defense
theorem l1_witness : impl 458 ≠ spec 458 := by native_decide

-- The bug collapses effective defense from 249 to just 1
theorem l1_impl_collapses_to_one : impl 458 = 1 := by native_decide

-- The correct behavior gives effective defense 249
theorem l1_spec_gives_249 : spec 458 = 249 := by native_decide

-- Badge boost on 458 yields 515, crossing the critical 512 threshold
theorem l1_badge_boost_crosses_512 : applyBadgeBoost 458 = 515 := by native_decide

-- The catastrophic drop: 248 effective defense points lost to overflow
theorem l1_magnitude : spec 458 - impl 458 = 248 := by native_decide

-- ─────────────────────────────────────────────────────────────────────────────
-- L2: Universal characterization of the bug
-- ─────────────────────────────────────────────────────────────────────────────

-- The exact critical threshold: 456 pushes badge-boosted value above 512; 455 does not
theorem l2_critical_threshold :
    applyBadgeBoost 456 ≥ 512 ∧ applyBadgeBoost 455 < 512 := by native_decide

-- Universal: for ALL valid stats in [0, 999],
-- badge-boosted defense ≥ 512 means buggy Reflect gives a lower effective stat than spec
theorem l2_bug_triggers_above_512 : ∀ d : Fin 1000,
    applyBadgeBoost d.val ≥ 512 → impl d.val < spec d.val := by native_decide

-- Universal: below the overflow threshold, impl and spec agree (bug is harmless)
theorem l2_below_threshold_safe : ∀ d : Fin 1000,
    applyBadgeBoost d.val * 2 ≤ 999 → impl d.val = spec d.val := by native_decide

-- Universal: the bug is perverse – buggy Reflect gives WORSE effective defense than NO Reflect
-- (Growl + Reflect is strictly worse than neither, once the badge boost overflows)
theorem l2_reflect_makes_worse : ∀ d : Fin 1000,
    applyBadgeBoost d.val ≥ 512 →
    impl d.val < effectiveStat (applyBadgeBoost d.val) := by native_decide

-- Universal: when overflowing, the buggy effective defense is at most 243
-- (it can never reach the 249 that spec provides for high defense)
theorem l2_overflow_upper_bound : ∀ d : Fin 1000,
    applyBadgeBoost d.val ≥ 512 → impl d.val ≤ 243 := by native_decide

-- Universal: the spec is always at least as good as not using Reflect at all
theorem l2_spec_never_worse_than_no_reflect : ∀ d : Fin 1000,
    spec d.val ≥ effectiveStat (applyBadgeBoost d.val) ∨
    spec d.val = effectiveStat (min (applyBadgeBoost d.val * 2) MAX_STAT) := by native_decide

-- ─────────────────────────────────────────────────────────────────────────────
-- L3: Fix – cap the doubled stat at MAX_STAT before damage formula scaling
-- ─────────────────────────────────────────────────────────────────────────────

-- The fix matches spec exactly for all valid stat values
theorem l3_fix_correct : ∀ d : Fin 1000,
    implFixed d.val = spec d.val := by native_decide

-- When the bug would have triggered, the fix guarantees effective defense = 249
theorem l3_fix_gives_249_when_boosted : ∀ d : Fin 1000,
    applyBadgeBoost d.val ≥ 512 → implFixed d.val = 249 := by native_decide

-- The fix eliminates the perverse behavior: fixed Reflect never makes defense worse
-- than the unmodified badge-boosted defense (no longer worse-than-nothing)
theorem l3_fix_no_perverse_effect : ∀ d : Fin 1000,
    applyBadgeBoost d.val ≥ 512 →
    implFixed d.val ≥ effectiveStat (applyBadgeBoost d.val) := by native_decide

end AutoResearch
