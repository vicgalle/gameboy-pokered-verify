import SM83

namespace AutoResearch

-- The bug occurs because an 8-bit MSB comparison sets a carry flag
-- which is incorrectly factored into the 8-bit LSB subtraction (sbc).
def impl (curr max : BitVec 16) : Bool :=
  let carry := curr.hi < max.hi  -- cp [hl] (MSB comparison sets carry if curr < max)
  let res := curr.lo - max.lo - (if carry then 1 else 0) -- sbc [hl] (LSB subtraction)
  res == 0 -- jp z, .failed

-- Intended behavior: Healing only fails if current HP is exactly equal to max HP.
def spec (curr max : BitVec 16) : Bool := curr == max

-- L1: Bug Exists - Healing fails when current HP is 1 and max HP is 256 (Gap of 255).
theorem bug_exists : ∃ c m, impl c m ∧ c ≠ m :=
  ⟨(1 : BitVec 16), (256 : BitVec 16), by native_decide⟩

-- L2: Characterization - Universal trigger condition for the faulty check.
theorem bug_trigger (c m : BitVec 16) :
  impl c m ↔ (if c.hi < m.hi then c.lo = m.lo + 1 else c.lo = m.lo) := by
  have h := (by native_decide : ∀ (cl ml : BitVec 8) (cry : Bool),
    (cl - ml - (if cry then 1 else 0) == 0) ↔ (if cry then cl = ml + 1 else cl = ml))
  exact h c.lo m.lo (c.hi < m.hi)

-- L3: Fix Correctness - A standard 16-bit equality check.
def fix (c m : BitVec 16) : Bool := c == m
theorem fix_correct (c m : BitVec 16) : fix c m = spec c m := rfl

-- L4: Safety property - The bug never causes the move to heal a full-HP Pokemon.
theorem bug_no_false_negatives (c m : BitVec 16) : spec c m → impl c m := by
  intro h; rw [h, bug_trigger]; simp [BitVec.lt_irrefl]

-- L4: Documented gaps - Verify the bug triggers on the "magic gaps" of 255 and 511.
theorem bug_documented_gaps :
  impl 1 256 ∧   -- Gap 255 (MSB: 0 < 1, LSB: 1 - 0 - 1 = 0)
  impl 1 512 ∧   -- Gap 511 (MSB: 0 < 2, LSB: 1 - 0 - 1 = 0)
  impl 257 512   -- Gap 255 (MSB: 1 < 2, LSB: 1 - 0 - 1 = 0)
  := by native_decide

-- L4: Analytical proof for general gaps of (256*k - 1) when curr.lo > 0.
theorem bug_gap_property (c : BitVec 16) (h_lo : c.lo ≠ 0) (k : Nat)
  (h_k : k = 1 ∨ k = 2) (h_bound : c.toNat + 256 * k - 1 < 65536) :
  let m := BitVec.ofNat 16 (c.toNat + 256 * k - 1)
  impl c m ∧ c ≠ m := by
  let n := 256 * k - 1
  let m := BitVec.ofNat 16 (c.toNat + n)
  have h_m_lo : m.lo = c.lo - 1 := by
    apply BitVec.eq_of_toNat_eq
    have : m.toNat % 256 = (c.toNat + n) % 256 := by simp [m, h_bound]
    simp [this, BitVec.toNat_lo, Nat.add_mod]
    have : n % 256 = 255 := by cases h_k <;> subst k <;> decide
    rw [this]; have := c.lo.toNat_prop; omega
  have h_m_hi : c.hi < m.hi := by
    apply BitVec.lt_def.mpr
    simp [m, BitVec.toNat_hi, BitVec.toNat_ofNat, h_bound]
    rw [BitVec.toNat_hi_lo, Nat.add_assoc, Nat.add_div_left _ (by decide)]
    have : (c.lo.toNat + n) / 256 = k := by
      have h_clo := c.lo.toNat_prop; cases h_k <;> subst k <;> (simp [n]; omega)
    rw [this]; omega
  constructor
  · rw [bug_trigger]; simp [h_m_hi, h_m_lo]
  · intro h_eq; injection h_eq with h_val; omega

end AutoResearch
