import SM83

namespace AutoResearch

/-- Buggy hit accuracy check from Pokemon Red's MoveHitTest.

    Models the SM83 sequence: `call BattleRandom; cp [accuracy]; ret nc`
    Returns true (hit) when rand < accuracy, false (miss) otherwise.

    Bug: at accuracy = 255 (representing 100% hit chance), rolling rand = 255
    evaluates 255 < 255 = false, causing a spurious miss 1/256 of the time. -/
def impl (rand : BitVec 8) (accuracy : BitVec 8) : Bool :=
  decide (rand.toNat < accuracy.toNat)

/-- Correct intended behavior: accuracy = 255 (100%) should always hit.
    For accuracy < 255, the strict < comparison gives the correct probability.
    The fix is to special-case 255 so it truly means "never miss." -/
def spec (rand : BitVec 8) (accuracy : BitVec 8) : Bool :=
  accuracy == 255 || decide (rand.toNat < accuracy.toNat)

-- L1: Concrete witness showing the 1/256 miss bug
-- Rolling rand=255 against max accuracy=255 yields a miss when it should hit
theorem l1_witness : impl 255 255 ≠ spec 255 255 := by native_decide

-- L2a: The bug triggers if and only if both rand=255 and accuracy=255
-- (the only case where the strict-less-than gives a different answer than
--  the intended "always hit at max accuracy" behavior)
theorem l2_disagree_iff : ∀ rand acc : BitVec 8,
    impl rand acc ≠ spec rand acc ↔ rand = 255 ∧ acc = 255 := by native_decide

-- L2b: Spec guarantees a hit at max accuracy for all random values
theorem l2_spec_full_accuracy : ∀ rand : BitVec 8, spec rand 255 = true := by native_decide

-- L2c: For any accuracy strictly below 255, the buggy impl and correct spec agree
-- (the 1/256 bug is only observable at the maximum accuracy value)
theorem l2_lower_acc_agree : ∀ rand acc : BitVec 8,
    acc.toNat < 255 → impl rand acc = spec rand acc := by native_decide

-- L2d: At max accuracy, the buggy impl misses exactly when rand = 255
theorem l2_impl_max_miss_iff : ∀ rand : BitVec 8,
    impl rand 255 = false ↔ rand = 255 := by native_decide

-- L2e: The bug only introduces extra misses -- if impl says "hit", spec also says "hit"
-- (the buggy code never produces a phantom hit that the spec would miss)
theorem l2_impl_hit_implies_spec_hit : ∀ rand acc : BitVec 8,
    impl rand acc = true → spec rand acc = true := by native_decide

-- L3: Fix -- explicitly handle the 100% accuracy case to eliminate the 1/256 miss
def implFixed (rand : BitVec 8) (accuracy : BitVec 8) : Bool :=
  if accuracy == 255 then true
  else decide (rand.toNat < accuracy.toNat)

theorem l3_fix_correct : ∀ rand acc : BitVec 8, implFixed rand acc = spec rand acc := by
  native_decide

end AutoResearch
