import SM83

namespace AutoResearch

-- Model of the 1/256 miss bug in Pokemon Red/Blue.
-- The move hit/crit check uses strict < comparison (from the SM83 cp + ret nc pattern).
-- When accuracy = 0xFF (255, representing 100%), a random value of 0xFF
-- still causes a miss because 255 < 255 is false, giving a 1/256 miss chance
-- on moves intended to always hit.

-- Buggy implementation: a move hits if randomVal < accuracy
-- When accuracy = 0xFF (the max, representing 100%), randomVal = 0xFF still misses
def impl (randomVal : BitVec 8) (accuracy : BitVec 8) : Bool :=
  randomVal.toNat < accuracy.toNat

-- Correct specification: accuracy = 0xFF should guarantee a hit (100% means 100%)
def spec (randomVal : BitVec 8) (accuracy : BitVec 8) : Bool :=
  accuracy == 0xFF || randomVal.toNat < accuracy.toNat

-- L1: Concrete witness showing the bug exists
-- With max accuracy (0xFF) and random value 0xFF, impl misses but spec hits
theorem l1_witness : impl 0xFF 0xFF ≠ spec 0xFF 0xFF := by native_decide

-- L2a: Universal characterization - the bug triggers exactly when both args are 0xFF
theorem l2_characterization : ∀ r acc : BitVec 8,
    (impl r acc = false ∧ spec r acc = true) ↔ (r = 0xFF ∧ acc = 0xFF) := by
  native_decide

-- L2b: With max accuracy, impl misses exactly when randomVal = 0xFF (1 in 256 cases)
theorem l2_miss_only_at_boundary : ∀ r : BitVec 8,
    impl r 0xFF = false ↔ r = 0xFF := by native_decide

-- L2c: spec with max accuracy always returns true (no 1/256 miss)
theorem l2_spec_max_always_hits : ∀ r : BitVec 8, spec r 0xFF = true := by native_decide

-- L2d: For any accuracy below max, impl and spec agree (bug only affects 0xFF)
theorem l2_agree_below_max : ∀ r acc : BitVec 8,
    acc ≠ 0xFF → impl r acc = spec r acc := by native_decide

-- L3: Fixed implementation - explicitly handle the max-accuracy boundary case
def implFixed (randomVal : BitVec 8) (accuracy : BitVec 8) : Bool :=
  accuracy == 0xFF || randomVal.toNat < accuracy.toNat

-- L3a: The fix matches spec for all inputs
theorem l3_fix_correct : ∀ r acc : BitVec 8, implFixed r acc = spec r acc := by
  native_decide

-- L3b: The fix only differs from impl at the single boundary point r=0xFF, acc=0xFF
theorem l3_fix_differs_only_at_max : ∀ r acc : BitVec 8,
    implFixed r acc ≠ impl r acc ↔ r = 0xFF ∧ acc = 0xFF := by native_decide

-- L3c: The fix is backward compatible: for all non-max accuracy, behavior is unchanged
theorem l3_fix_backward_compatible : ∀ r acc : BitVec 8,
    acc ≠ 0xFF → implFixed r acc = impl r acc := by native_decide

end AutoResearch
