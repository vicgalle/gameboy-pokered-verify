import SM83

namespace AutoResearch

-- Model the buggy healing check in Pokémon Red (engine/battle/move_effects/heal.asm).
-- The code compares the MSB but only uses the resulting carry flag.
-- It then performs an 'sbc' on the LSB and fails if that result is zero.
def impl (curr max : BitVec 16) : Bool :=
  let carry := curr.hi < max.hi
  let res := curr.lo - max.lo - (if carry then 1 else 0)
  res == 0

-- Correct/intended behavior: healing should only fail if current HP is already maximum.
def spec (curr max : BitVec 16) : Bool := curr == max

-- L1: Bug exists - Healing fails when MaxHP=256 and CurrentHP=1 (difference of 255).
-- In this case, 0 < 1 sets carry=1, then 1 - 0 - 1 = 0 triggers the failure check.
theorem bug_exists : ∃ c m : BitVec 16, impl c m ∧ c ≠ m :=
  ⟨1, 256, by native_decide⟩

-- L2: Characterization - The bug triggers if current LSB matches max LSB (when MSB >= max MSB)
-- or if current LSB is max LSB + 1 (when MSB < max MSB).
theorem bug_always (c m : BitVec 16) :
  impl c m ↔ (if c.hi < m.hi then c.lo = m.lo + 1 else c.lo = m.lo) := by
  have h : ∀ (cl ml : BitVec 8) (carry : Bool),
    (cl - ml - (if carry then 1 else 0) == 0) ↔ (if carry then cl = ml + 1 else cl = ml) := by native_decide
  exact h c.lo m.lo (c.hi < m.hi)

-- L3: Fix correctness
-- Replacing the buggy logic with a full 16-bit equality check fixes the move.
def fix (curr max : BitVec 16) : Bool := curr == max

theorem fix_correct (c m : BitVec 16) : fix c m = spec c m := rfl

-- L4: Relational - Specific failure cases (difference is multiple of 256 minus 1)
theorem bug_triggers_on_255_gap : impl 1 256 = true := by rfl
theorem bug_triggers_on_511_gap : impl 1 512 = true := by rfl

end AutoResearch

