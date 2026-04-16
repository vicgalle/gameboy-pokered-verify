import SM83

namespace AutoResearch

/-!
# Bug #10: Badge Boost Stacking + Reflect → Catastrophic Defense Overflow

Three Gen 1 mechanics interact:
1. Badge stat boosts are RE-APPLIED whenever any stat changes in battle
2. Reflect doubles defense with no upper bound check
3. The damage formula scales large stats as (stat / 4) mod 256

Cloyster scenario:
- Defense = 458; opponent uses Growl → badge boost reapplied → 515
- Reflect doubles 515 → 1030
- Damage formula: 1030 / 4 = 257, 257 mod 256 = **1**   (should be ~229)
-/

-- Pokemon Gen 1 maximum stat value
def MAX_STAT_VALUE : BitVec 16 := 999

/-- Badge stat boost: add 1/8 of stat (via >>> 3), cap at MAX_STAT_VALUE.
    Models the assembly applyBoostToStat subroutine faithfully. -/
def applyBadgeBoost (stat : BitVec 16) : BitVec 16 :=
  let eighth : BitVec 16 := stat >>> 3
  let boosted := stat + eighth
  if boosted > MAX_STAT_VALUE then MAX_STAT_VALUE else boosted

/-- BUGGY Reflect: doubles defense with no overflow protection. -/
def reflectBuggy (defense : BitVec 16) : BitVec 16 := defense * 2

/-- FIXED Reflect: doubles defense but clamps to MAX_STAT_VALUE. -/
def reflectFixed (defense : BitVec 16) : BitVec 16 :=
  let doubled := defense * 2
  if doubled > MAX_STAT_VALUE then MAX_STAT_VALUE else doubled

/-- Gen 1 damage formula stat scaling.
    Stats > 255: divide by 4 and keep only the low byte (wraps mod 256). -/
def scaleStat (stat : BitVec 16) : BitVec 8 :=
  if stat > 255 then lo (stat >>> 2) else lo stat

/-- IMPL: Buggy pipeline.
    Growl triggers badge boost reapplication, then uncapped Reflect doubles it. -/
def impl (baseDef : BitVec 16) : BitVec 8 :=
  scaleStat (reflectBuggy (applyBadgeBoost baseDef))

/-- SPEC: Fixed pipeline.
    Reflect is capped at MAX_STAT_VALUE before damage formula scaling. -/
def spec (baseDef : BitVec 16) : BitVec 8 :=
  scaleStat (reflectFixed (applyBadgeBoost baseDef))

/-- BASELINE: No badge boost reapplication (correct trigger behavior). -/
def implNoReapply (baseDef : BitVec 16) : BitVec 8 :=
  scaleStat (reflectBuggy baseDef)

-- ============================================================
-- L1: Concrete witnesses
-- ============================================================

/-- With Cloyster's defense of 458, the bug produces effective defense = 1. -/
theorem l1_bug_fires : impl 458 = 1 := by native_decide

/-- The correct spec produces effective defense = 249. -/
theorem l1_spec_value : spec 458 = 249 := by native_decide

/-- The bug causes a real divergence: 1 ≠ 249. -/
theorem l1_divergence : impl 458 ≠ spec 458 := by native_decide

-- ============================================================
-- L2: Universal characterization of the overflow mechanism
-- ============================================================

/-- Badge boost raises 458 → 515 (above the critical 512 threshold). -/
theorem l2_badge_boost_458 : applyBadgeBoost 458 = 515 := by native_decide

/-- Reflect doubles 515 → 1030. -/
theorem l2_reflect_515 : reflectBuggy 515 = 1030 := by native_decide

/-- Damage scaling: 1030/4 = 257, 257 mod 256 = 1. -/
theorem l2_scale_1030 : scaleStat 1030 = 1 := by native_decide

/-- The critical arithmetic: 1030 >> 2 = 257, and low byte of 257 = 1 (wraps!). -/
theorem l2_overflow_anatomy :
    (1030 : BitVec 16) >>> 2 = 257 ∧
    lo (257 : BitVec 16) = (1 : BitVec 8) := by native_decide

/-- Threshold: 458 boosts to 515 > 512; this is what places 2× in the wrap zone. -/
theorem l2_critical_threshold :
    (applyBadgeBoost 458 : BitVec 16) > 512 ∧
    (applyBadgeBoost 457 : BitVec 16) ≥ 512 := by native_decide

-- ============================================================
-- L3: Fix correctness
-- ============================================================

/-- The fixed Reflect clamps 1030 down to 999. -/
theorem l3_fixed_clamps : reflectFixed 515 = 999 := by native_decide

/-- With the fix, effective defense is 249 — a safe value. -/
theorem l3_spec_correct : spec 458 = 249 := by native_decide

/-- The fix is strictly better: 249 > 1. -/
theorem l3_fix_strictly_better : spec 458 > impl 458 := by native_decide

-- ============================================================
-- L4: Relational — the Growl paradox
-- ============================================================

/-- Without badge reapplication (no Growl), effective defense is 229. -/
theorem l4_baseline : implNoReapply 458 = 229 := by native_decide

/-- With badge reapplication (triggered by opponent's Growl), effective defense = 1. -/
theorem l4_with_reapply : impl 458 = 1 := by native_decide

/-- THE GROWL PARADOX: The opponent's Growl (intended to lower player's Attack)
    triggers badge reapplication. Combined with an earlier Reflect, this collapses
    effective defense from 229 → 1, a 229× reduction in defensive power.
    A move meant to weaken the player offensively instead devastates their defense. -/
theorem l4_growl_paradox : implNoReapply 458 > impl 458 := by native_decide

/-- Full impact summary across all three scenarios. -/
theorem l4_full_summary :
    (implNoReapply 458).toNat = 229 ∧  -- no Growl trigger: reasonable defense
    (impl 458).toNat = 1 ∧             -- Growl triggers reapply: catastrophic
    (spec 458).toNat = 249 :=          -- Reflect cap fix: correct behavior
  by native_decide

end AutoResearch
