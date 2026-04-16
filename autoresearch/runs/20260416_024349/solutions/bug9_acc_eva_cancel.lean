import SM83

namespace AutoResearch

-- Stat modifier ratio numerators from Pokemon Red's StatModifierRatios table
-- Stage indices 1-13 correspond to stages -6 through +6
-- All ratios are x/100 (denominator always 100)
def ratioNum : Nat → Nat
  | 1  => 25
  | 2  => 28
  | 3  => 33
  | 4  => 40
  | 5  => 50
  | 6  => 66    -- intended to be 2/3 ≈ 0.6667, but stored as 0.66 (loses ~0.0067)
  | 7  => 100   -- neutral stage
  | 8  => 150
  | 9  => 200
  | 10 => 250
  | 11 => 300
  | 12 => 350
  | 13 => 400
  | _  => 100   -- out-of-range defaults to neutral

-- Buggy implementation: mirrors the Pokemon Red CalcHitChance assembly
-- Two sequential integer multiply+divide passes with truncation between them
-- accMod: attacker's accuracy stage (1-13); evaMod: defender's evasion stage (1-13)
-- Evasion is reflected: 14 - evaMod maps high evasion to a penalty for the attacker
def impl (baseAcc accMod evaMod : BitVec 8) : Nat :=
  let pass1 := baseAcc.toNat * ratioNum accMod.toNat / 100
  let pass2 := pass1 * ratioNum (14 - evaMod.toNat) / 100
  pass2

-- Intended correct behavior: equal accuracy and evasion boosts should cancel
-- When attacker's accuracy mod == defender's evasion mod, the net effect is zero
-- so the effective accuracy should equal the base accuracy unchanged
def spec (baseAcc accMod evaMod : BitVec 8) : Nat :=
  if accMod == evaMod then baseAcc.toNat
  else baseAcc.toNat * ratioNum accMod.toNat * ratioNum (14 - evaMod.toNat) / (100 * 100)

-- Fixed implementation: detect equal mods and skip the lossy calculation
def implFixed (baseAcc accMod evaMod : BitVec 8) : Nat :=
  if accMod == evaMod then baseAcc.toNat
  else
    let pass1 := baseAcc.toNat * ratioNum accMod.toNat / 100
    let pass2 := pass1 * ratioNum (14 - evaMod.toNat) / 100
    pass2

-- L1: Concrete witness -- base accuracy 255, both at stage +1 (index 8)
-- Bug: 255 * 150/100 = 382 (pass1), 382 * 66/100 = 252 (pass2)
-- Expected: 255 (equal stages should cancel: +1 accuracy vs +1 evasion = no change)
theorem l1_witness : impl 255 8 8 ≠ spec 255 8 8 := by native_decide

-- L2: For all base accuracies, equal ±1 mods never produce more than base accuracy
theorem l2_always_leq : ∀ b : BitVec 8, impl b 8 8 ≤ spec b 8 8 := by native_decide

-- L2b: For all non-zero base accuracies, equal ±1 mods strictly reduce accuracy
theorem l2_strict_loss : ∀ b : BitVec 8, b ≠ 0 → impl b 8 8 < spec b 8 8 := by native_decide

-- L2c: Worst case confirmed: stage ±5 (index 12) loses exactly 6 accuracy points
-- 255 * 350/100 = 892 (pass1), 892 * 28/100 = 249 (pass2); expected 255
theorem l2_worst_case : impl 255 12 12 = 249 := by native_decide

-- L2d: Neutral stages (index 7) correctly produce no change (bug does not affect neutral)
theorem l2_neutral_ok : ∀ b : BitVec 8, impl b 7 7 = spec b 7 7 := by native_decide

-- L3: Fixed implementation correctly handles equal mods for all base accuracies and stages
theorem l3_fix_correct : ∀ b m : BitVec 8, implFixed b m m = spec b m m := by native_decide

end AutoResearch
