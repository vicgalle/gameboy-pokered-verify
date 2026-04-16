import SM83

namespace AutoResearch

-- Buggy HP-full check from HealEffect_ in engine/battle/move_effects/heal.asm
-- The assembly uses `cp` on high bytes to get a carry flag, then `sbc` on
-- low bytes, checking if the result is zero. The bug: it never verifies that
-- the high bytes themselves are equal — only that their difference propagates
-- the right carry into the low-byte subtraction.
-- Effect: healing is blocked when max HP is exactly 255, 511, ... (256k-1)
-- points higher than current HP.
def impl (cH cL mH mL : BitVec 8) : Bool :=
  -- cp on high bytes: C=1 if currentHigh < maxHigh (carry propagates to sbc)
  let carry : BitVec 8 := if cH.toNat < mH.toNat then 1 else 0
  -- sbc: currentLow - maxLow - carry; jp z .failed (incorrectly skips heal)
  (cL - mL - carry) == 0

-- Correct "is HP at max?" check: true only when all 16-bit bytes match
def spec (cH cL mH mL : BitVec 8) : Bool :=
  cH == mH && cL == mL

-- L1: Bug witness #1 — 255 HP gap causes false "full HP" report
-- current HP = 0x0001 (1 HP), max HP = 0x0100 (256 HP), gap = 255
-- Heal is incorrectly blocked even though the Pokemon needs 255 HP restored
theorem l1_witness : impl 0x00 0x01 0x01 0x00 = true ∧
                     spec 0x00 0x01 0x01 0x00 = false := by native_decide

-- L1: Bug witness #2 — 511 HP gap also triggers the bug
-- current HP = 0x0001 (1 HP), max HP = 0x0200 (512 HP), gap = 511
theorem l1_witness2 : impl 0x00 0x01 0x02 0x00 = true ∧
                      spec 0x00 0x01 0x02 0x00 = false := by native_decide

-- L2: For ALL low-byte values, the 255-point HP gap triggers the bug
-- When maxHigh = currentHigh + 1 and currentLow = maxLow + 1,
-- impl always returns true (false positive) while spec always returns false
theorem l2_255_gap_universal : ∀ lo : BitVec 8,
    impl 0x00 (lo + 1) 0x01 lo = true ∧
    spec 0x00 (lo + 1) 0x01 lo = false := by native_decide

-- L2: Same universal false positive for the 511-point HP gap
theorem l2_511_gap_universal : ∀ lo : BitVec 8,
    impl 0x00 (lo + 1) 0x02 lo = true ∧
    spec 0x00 (lo + 1) 0x02 lo = false := by native_decide

-- L2: No false negatives — when HP is truly at max, impl always agrees
-- (The bug only produces false positives, never false negatives)
theorem l2_no_false_negatives : ∀ h l : BitVec 8,
    impl h l h l = true := by native_decide

-- L2: spec correctly identifies equal HP for all byte combinations
theorem l2_spec_identifies_full : ∀ h l : BitVec 8,
    spec h l h l = true := by native_decide

-- L2: impl is strictly more permissive than spec (superset of "true" cases)
-- On equal inputs both agree; on the buggy gap inputs impl fires but spec doesn't
theorem l2_false_positive_exists : ∃ cH cL mH mL : BitVec 8,
    impl cH cL mH mL = true ∧ spec cH cL mH mL = false :=
  ⟨0x00, 0x01, 0x01, 0x00, by native_decide, by native_decide⟩

-- L3: Fixed implementation — check true 16-bit equality of all bytes
def implFixed (cH cL mH mL : BitVec 8) : Bool :=
  cH == mH && cL == mL

-- The fix is definitionally identical to spec (same boolean formula)
theorem l3_fix_equals_spec : ∀ cH cL mH mL : BitVec 8,
    implFixed cH cL mH mL = spec cH cL mH mL := by
  intro cH cL mH mL; rfl

-- The fix correctly rejects the previously-buggy 255-gap case
theorem l3_fix_rejects_255_gap : ∀ lo : BitVec 8,
    implFixed 0x00 (lo + 1) 0x01 lo = false := by native_decide

-- The fix correctly rejects the previously-buggy 511-gap case
theorem l3_fix_rejects_511_gap : ∀ lo : BitVec 8,
    implFixed 0x00 (lo + 1) 0x02 lo = false := by native_decide

-- L3: Fixed version agrees with buggy version when HP is truly full
-- (Ensures the fix doesn't introduce false negatives)
theorem l3_fix_preserves_true_full : ∀ h l : BitVec 8,
    implFixed h l h l = true := by native_decide

end AutoResearch
