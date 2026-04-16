import SM83

namespace AutoResearch

/-- Buggy HP-full check from Pokemon Red's HealEffect_.
    The assembly does:
      cp  [hl]    ; compare highCur vs highMax, sets carry if highCur < highMax
      inc de      ; advance to lowCur
      inc hl      ; advance to lowMax
      ld  a, [de] ; a = lowCur
      sbc [hl]    ; a = lowCur - lowMax - carry
      jp  z, .failed  ; block heal if a == 0
    Bug: when highCur < highMax (carry=1), the check fires if lowCur = lowMax + 1,
    blocking healing when currentHP is 255 or 511 HP below maxHP. -/
def impl (highCur lowCur highMax lowMax : BitVec 8) : Bool :=
  let carry : Nat := if highCur.toNat < highMax.toNat then 1 else 0
  (lowCur.toNat + 256 - lowMax.toNat - carry) % 256 == 0

/-- Correct: HP is full iff both bytes of current HP equal both bytes of max HP -/
def spec (highCur lowCur highMax lowMax : BitVec 8) : Bool :=
  highCur == highMax && lowCur == lowMax

/-- Fixed implementation: check both bytes independently -/
def implFixed (highCur lowCur highMax lowMax : BitVec 8) : Bool :=
  highCur == highMax && lowCur == lowMax

/-- Core check parameterized by carry for tractable 2-variable theorems -/
def implCore (carry : Bool) (lowCur lowMax : BitVec 8) : Bool :=
  let c : Nat := if carry then 1 else 0
  (lowCur.toNat + 256 - lowMax.toNat - c) % 256 == 0

-- L1: Bug witness, 255-HP gap: currentHP = 0x0164 = 356, maxHP = 0x0263 = 611
-- Game blocks healing despite 255 HP missing
theorem l1_bug_gap255 : impl 1 100 2 99 = true ∧ spec 1 100 2 99 = false := by
  native_decide

-- L1b: Bug witness, 511-HP gap: currentHP = 0x0064 = 100, maxHP = 0x0263 = 611
theorem l1_bug_gap511 : impl 0 100 2 99 = true ∧ spec 0 100 2 99 = false := by
  native_decide

-- L2a: Without carry (high bytes equal or cur ≥ max), low-byte comparison is exact
theorem l2_no_carry_exact : ∀ lo hi : BitVec 8,
    implCore false lo hi = (lo == hi) := by native_decide

-- L2b: With carry=1 (highCur < highMax), check fires on off-by-one — the false positive
theorem l2_carry_off_by_one : ∀ lo hi : BitVec 8,
    implCore true lo hi = (lo == hi + 1) := by native_decide

-- L2c: True full HP is always detected in the no-carry path (no false negatives)
theorem l2_full_hp_detected : ∀ lo : BitVec 8,
    implCore false lo lo = true := by native_decide

-- L2d: When high bytes are equal (carry = 0), impl matches spec exactly
theorem l2_equal_high_correct : ∀ lo lm : BitVec 8,
    impl 0x80 lo 0x80 lm = spec 0x80 lo 0x80 lm := by native_decide

-- L3: Fix is definitionally identical to spec
theorem l3_fix_eq_spec : ∀ hc lc hm lm : BitVec 8,
    implFixed hc lc hm lm = spec hc lc hm lm := by intros; rfl

-- L3b: Fix correctly rejects the exact bug scenario (highCur < highMax, any low bytes)
theorem l3_fix_rejects_bug_scenario : ∀ lo hi : BitVec 8,
    implFixed 1 lo 2 hi = false := by native_decide

end AutoResearch
