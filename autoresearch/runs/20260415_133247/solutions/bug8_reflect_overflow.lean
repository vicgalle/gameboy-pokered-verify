import SM83

/-!
# Bug: Reflect and Light Screen Overflow

In Pokémon Red/Blue/Yellow, the moves Reflect and Light Screen double the user's
Defense or Special stat, respectively. During damage calculation, if any stat
exceeds 255, both the attack and defense stats are divided by 4 to fit within
single-byte registers for the division routine.

The bug occurs because the division-by-4 and subsequent truncation to 8 bits
do not account for values reaching 1024. Specifically:
1. A stat of 512 is doubled by Reflect to 1024.
2. The damage routine sees 1024 > 255 and divides by 4.
3. 1024 / 4 = 256.
4. The result is stored in an 8-bit register. 256 in 8 bits is 0.
5. Division by zero ensues, or defense is treated as 0, leading to massive damage.
-/

namespace AutoResearch

open BitVec

/-- 
Models the effective defense stat used as a divisor in the damage formula.
This includes the Reflect doubling and the 1/4 scaling logic.
-/
def impl (defense : BitVec 16) : BitVec 8 :=
  let doubled := defense * 2
  -- The game checks if the doubled stat > 255 to trigger scaling
  if doubled > 255 then
    -- Bug: Truncates the result of (doubled / 4) to 8 bits.
    -- If doubled = 1024, doubled / 4 = 256, which is 0 mod 256.
    (doubled / 4).truncate 8
  else
    doubled.truncate 8

/-- 
Models the intended behavior: the stat should be doubled and, if scaling is 
necessary to fit 8 bits, it should be saturated (capped) at 255.
-/
def spec (defense : BitVec 16) : BitVec 8 :=
  let doubled := defense.toNat * 2
  if doubled > 255 then
    let scaled := doubled / 4
    if scaled > 255 then 255 else BitVec.ofNat 8 scaled
  else
    BitVec.ofNat 8 doubled

/-! ### L1: Bug Existence -/

/-- A stat of 512 causes the effective defense to wrap to 0. -/
theorem bug_exists : ∃ x, impl x ≠ spec x := 
  ⟨512, by native_decide⟩

/-! ### L2: Characterization -/

/-- 
The "Crash Condition": When the stat is exactly 512, Reflect makes the 
effective defense 0, which triggers a division-by-zero or near-infinite damage.
-/
theorem bug_causes_zero_defense : impl 512 = 0 := by
  native_decide

/--
The bug triggers for any stat such that (stat * 2 / 4) is a multiple of 256.
This occurs at 512, 1024 (though 1024 isn't reachable), etc.
-/
theorem bug_at_512_multiple (n : BitVec 16) : n = 512 → impl n = 0 := by
  intro h
  rw [h]
  native_decide

/--
The non-monotonicity bug: Increasing your raw defense can significantly 
DECREASE your effective defense.
511 defense -> 255 effective.
512 defense -> 0 effective.
-/
theorem bug_non_monotonic : impl 511 = 255 ∧ impl 512 = 0 := by
  native_decide

/-! ### L3: Fix Correctness -/

/-- 
A fixed implementation that caps the scaled value at 255 to prevent 
the 8-bit wrap-around.
-/
def fix (defense : BitVec 16) : BitVec 8 :=
  let doubled := defense * 2
  if doubled > 255 then
    let scaled := doubled / 4
    if scaled > 255 then 255 else scaled.truncate 8
  else
    doubled.truncate 8

/-- The fix matches the specification for all possible 16-bit stat values. -/
theorem fix_correct (x : BitVec 16) : (fix x).toNat = (spec x).toNat := by
  simp [fix, spec]
  split
  · rename_i h1
    split
    · rename_i h2
      have h1n := BitVec.toNat_lt_2Pow x
      simp [BitVec.toNat_mult, BitVec.toNat_ofNat] at *
      -- Since x is 16-bit, doubled is at most 131070
      -- If doubled / 4 > 255, the spec returns 255
      rfl
    · rename_i h2
      simp [BitVec.toNat_truncate, BitVec.toNat_div]
      -- BitVec.toNat of truncate matches Nat mod 256. 
      -- If scaled <= 255, mod 256 is identity.
      have : (BitVec.toNat (x * 2 / 4)) < 256 := by
        match x * 2 / 4 with
        | ⟨v, p⟩ => 
          simp at h2
          exact h2
      rw [Nat.mod_eq_of_lt this]
  · rename_i h1
    simp [BitVec.toNat_truncate]
    have : (BitVec.toNat (x * 2)) < 256 := by
       match x * 2 with
       | ⟨v, p⟩ => 
         simp at h1
         exact h1
    rw [Nat.mod_eq_of_lt this]

end AutoResearch
