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

-- ============================================================
-- Accuracy Bug Theorems
-- ============================================================

-- L1: Concrete witness showing the 1/256 miss bug
-- Rolling rand=255 against max accuracy=255 yields a miss when it should hit
theorem l1_witness : impl 255 255 ≠ spec 255 255 := by native_decide

-- L2a: The bug triggers if and only if both rand=255 and accuracy=255
theorem l2_disagree_iff : ∀ rand acc : BitVec 8,
    impl rand acc ≠ spec rand acc ↔ rand = 255 ∧ acc = 255 := by native_decide

-- L2b: Spec guarantees a hit at max accuracy for all random values
theorem l2_spec_full_accuracy : ∀ rand : BitVec 8, spec rand 255 = true := by native_decide

-- L2c: For any accuracy strictly below 255, the buggy impl and correct spec agree
theorem l2_lower_acc_agree : ∀ rand acc : BitVec 8,
    acc.toNat < 255 → impl rand acc = spec rand acc := by native_decide

-- L2d: At max accuracy, the buggy impl misses exactly when rand = 255
theorem l2_impl_max_miss_iff : ∀ rand : BitVec 8,
    impl rand 255 = false ↔ rand = 255 := by native_decide

-- L2e: The bug only introduces extra misses -- impl hit implies spec hit
theorem l2_impl_hit_implies_spec_hit : ∀ rand acc : BitVec 8,
    impl rand acc = true → spec rand acc = true := by native_decide

-- L2f: Conversely, spec miss implies impl miss (spec is strictly more permissive)
theorem l2_spec_miss_implies_impl_miss : ∀ rand acc : BitVec 8,
    spec rand acc = false → impl rand acc = false := by native_decide

-- L2g: At accuracy 0, both impl and spec always miss (0% accuracy = never hit)
theorem l2_zero_acc_always_miss : ∀ rand : BitVec 8,
    impl rand 0 = false ∧ spec rand 0 = false := by native_decide

-- L2h: Unique bug input -- only (255, 255) causes disagreement
theorem l2_unique_bug_input : ∀ rand acc : BitVec 8,
    impl rand acc ≠ spec rand acc → rand = 255 ∧ acc = 255 := by native_decide

-- L2i: impl is monotone in accuracy: higher accuracy cannot decrease the hit chance
theorem l2_impl_monotone_acc : ∀ rand acc1 acc2 : BitVec 8,
    acc1.toNat ≤ acc2.toNat → impl rand acc1 = true → impl rand acc2 = true := by native_decide

-- L2j: impl is antitone in rand: lower rand values are strictly more likely to hit
theorem l2_impl_antitone_rand : ∀ rand1 rand2 acc : BitVec 8,
    rand1.toNat ≤ rand2.toNat → impl rand2 acc = true → impl rand1 acc = true := by native_decide

-- L3: Fix -- explicitly handle the 100% accuracy case to eliminate the 1/256 miss
def implFixed (rand : BitVec 8) (accuracy : BitVec 8) : Bool :=
  if accuracy == 255 then true
  else decide (rand.toNat < accuracy.toNat)

theorem l3_fix_correct : ∀ rand acc : BitVec 8, implFixed rand acc = spec rand acc := by
  native_decide

-- L3b: The fix only changes behavior at the single bug point (255, 255)
theorem l3_fix_minimal : ∀ rand acc : BitVec 8,
    ¬(rand = 255 ∧ acc = 255) → implFixed rand acc = impl rand acc := by native_decide

-- ============================================================
-- Critical Hit Bug Model
-- ============================================================
-- CriticalHitTest uses: `rlc a` × 3, then `cp b; ret nc`
-- Three consecutive `rlc a` = left rotation by 3 positions
-- `ret nc` returns (no crit) if carry not set, i.e., rotated_rand >= critRate
-- At critRate = 255: only rotated_rand = 255 triggers no-crit, i.e., rand = 255

/-- Left rotation by 3 positions (models three consecutive `rlc a` instructions) -/
def rlc3 (b : BitVec 8) : BitVec 8 := (b <<< 3) ||| (b >>> 5)

/-- Buggy critical hit check: crit if rotated_rand < critRate.
    At critRate = 255 (max), misses exactly when rotated_rand = 255, i.e., rand = 255. -/
def critImpl (rand : BitVec 8) (critRate : BitVec 8) : Bool :=
  decide ((rlc3 rand).toNat < critRate.toNat)

/-- Correct critical hit behavior: at critRate = 255, always crit. -/
def critSpec (rand : BitVec 8) (critRate : BitVec 8) : Bool :=
  critRate == 255 || decide ((rlc3 rand).toNat < critRate.toNat)

-- L1 for crits: concrete witness of 1/256 false no-crit at max crit rate
theorem l1_crit_witness : critImpl 255 255 ≠ critSpec 255 255 := by native_decide

-- L2 for crits: rotation of 255 is always 255 (255 is a fixed point of any rotation)
theorem l2_crit_rotation_fixed : ∀ rand : BitVec 8,
    rlc3 rand = 255 ↔ rand = 255 := by native_decide

-- L2 for crits: crit bug triggers iff rand = 255 and critRate = 255
theorem l2_crit_disagree_iff : ∀ rand rate : BitVec 8,
    critImpl rand rate ≠ critSpec rand rate ↔ rand = 255 ∧ rate = 255 := by native_decide

-- L2 for crits: spec guarantees a crit at max crit rate for all rand values
theorem l2_crit_spec_full : ∀ rand : BitVec 8, critSpec rand 255 = true := by native_decide

-- L3 for crits: the analogous fix eliminates the 1/256 no-crit at max rate
def critImplFixed (rand : BitVec 8) (critRate : BitVec 8) : Bool :=
  if critRate == 255 then true
  else decide ((rlc3 rand).toNat < critRate.toNat)

theorem l3_crit_fix_correct : ∀ rand rate : BitVec 8,
    critImplFixed rand rate = critSpec rand rate := by native_decide

-- ============================================================
-- Cross-Bug Comparison
-- ============================================================

-- L4-style: accuracy bug and crit bug have identical triggering conditions
-- Both disagree iff rand = 255 and the threshold = 255
theorem l4_bugs_identical_condition : ∀ rand thresh : BitVec 8,
    (impl rand thresh ≠ spec rand thresh) ↔ (critImpl rand thresh ≠ critSpec rand thresh) := by
  native_decide

-- Both bugs are triggered by the same single input pair (255, 255)
theorem l4_bugs_single_failure_point :
    impl 255 255 = false ∧ critImpl 255 255 = false := by native_decide

end AutoResearch
