import SM83

namespace AutoResearch

def MAX_STAT_VALUE : Nat := 999

-- Apply badge boost: multiply stat by 9/8, cap at MAX_STAT_VALUE
-- Models .applyBoostToStat: shifts right 3x to get stat/8, adds to stat, caps
def applyBadgeBoost (stat : Nat) : Nat :=
  let boosted := stat + stat / 8
  min boosted MAX_STAT_VALUE

-- Reflect doubles the defense stat (no upper bound check in the buggy game)
def applyReflect (stat : Nat) : Nat :=
  stat * 2

-- Damage scaling: if stat > 255, divide by 4 and keep low byte only
-- Models the damage formula overflow: result stored in 8-bit register
def damageScaleDefense (stat : Nat) : Nat :=
  if stat > 255 then (stat / 4) % 256
  else stat

-- Buggy impl: badge boost can push stat above 512, then reflect causes overflow
def impl (baseDef : Nat) : Nat :=
  damageScaleDefense (applyReflect (applyBadgeBoost baseDef))

-- Spec: cap after reflect to prevent damage formula overflow
def spec (baseDef : Nat) : Nat :=
  damageScaleDefense (min (applyReflect (applyBadgeBoost baseDef)) MAX_STAT_VALUE)

-- Fixed implementation: cap the doubled stat before damage scaling
def implFixed (baseDef : Nat) : Nat :=
  damageScaleDefense (min (applyBadgeBoost baseDef * 2) MAX_STAT_VALUE)

-- L1: Concrete witness - Cloyster's 458 defense

-- Badge boost: 458 + 458/8 = 458 + 57 = 515
theorem l1_badge_boost : applyBadgeBoost 458 = 515 := by native_decide

-- Reflect: 515 * 2 = 1030 (exceeds 1023, causes catastrophic low-byte wrap)
theorem l1_reflect : applyReflect 515 = 1030 := by native_decide

-- Damage scaling: 1030/4 = 257, 257 % 256 = 1 (catastrophic!)
theorem l1_damage_scale : damageScaleDefense 1030 = 1 := by native_decide

-- Full chain: 458 → 515 → 1030 → effective defense of 1
theorem l1_impl_is_one : impl 458 = 1 := by native_decide

-- Bug exists: impl ≠ spec for Cloyster's defense
theorem l1_witness : impl 458 ≠ spec 458 := by native_decide

-- L2: Characterize the bug

-- Badge boost pushes stat above 512 (reflect of >512 exceeds 1024, overflows calc)
theorem l2_above_512_threshold : applyBadgeBoost 458 > 512 := by native_decide

-- Reflected value exceeds 1023, causing low-byte wrap in damage formula
theorem l2_reflected_exceeds_1023 : applyReflect (applyBadgeBoost 458) > 1023 := by native_decide

-- Severity: effective defense drops from 249 to 1 (factor of 249x reduction)
theorem l2_severity : impl 458 = 1 ∧ spec 458 = 249 := by native_decide

-- Even worse case: 456 defense → badge boost → 513 → reflect → 1026
-- 1026/4 = 256, 256 % 256 = 0: complete nullification of defense!
theorem l2_zero_defense_case : impl 456 = 0 ∧ spec 456 = 249 := by native_decide

-- Growl + Reflect interaction: opponent's Growl triggers badge reapplication
-- so defense goes 458 → 515 before reflect. The reflect then causes overflow.
theorem l2_growl_triggers_reapply : applyBadgeBoost 458 = 515 ∧ 515 > 511 := by native_decide

-- L3: Fix - cap after reflect prevents damage formula overflow

theorem l3_fix_matches_spec : implFixed 458 = spec 458 := by native_decide

theorem l3_fix_gives_249 : implFixed 458 = 249 := by native_decide

-- Fixed version is dramatically better than buggy (249 vs 1)
theorem l3_fix_much_better : implFixed 458 > impl 458 * 100 := by native_decide

-- Fix also handles the 456 case correctly (was 0, now 249)
theorem l3_fix_456 : implFixed 456 = spec 456 := by native_decide

end AutoResearch
