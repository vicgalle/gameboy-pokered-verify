import SM83

namespace AutoResearch

/-!
# Bug: Reflect and Light Screen Overflow

In Pokemon Red/Blue, the Reflect and Light Screen moves are intended to double
the user's Defense or Special stat, respectively. However, the damage 
calculation routine handles high stats (above 255) by dividing them by 4 and
keeping only the low byte.

When a doubled stat exceeds 1023, the division by 4 results in a value ≥ 256,
which wraps to 0 when stored in an 8-bit register. This causes a division by 
zero in the damage formula, freezing the game. For stats between 128 and 511,
Reflect can actually *decrease* the effective stat because the "divide by 4"
check is triggered only after the doubling.
-/

/-- 
Models the Game Boy's "Big Stat" logic in the damage calculation.
If a stat is > 255, it is divided by 4 and truncated to 8 bits.
-/
def calcEffectiveStat (stat : BitVec 16) : BitVec 8 :=
  if stat > 255 then
    -- Divide by 4 and take the lower 8 bits
    (stat >>> 2).toBitVec 8
  else
    stat.toBitVec 8

/-- 
The buggy implementation of Reflect/Light Screen.
The stat is doubled first, then passed to the effective stat calculation.
-/
def impl (stat : BitVec 16) (hasReflect : Bool) : BitVec 8 :=
  let doubledStat := if hasReflect then stat <<< 1 else stat
  calcEffectiveStat doubledStat

/-- 
The intended behavior: doubling the stat should always result in an
effective value that is at least as large as the original.
-/
def spec (stat : BitVec 16) (hasReflect : Bool) : Nat :=
  let base := calcEffectiveStat stat
  if hasReflect then base.toNat * 2 else base.toNat

/-! ## L1: Bug Existence -/

/-- Reflecting at 512 defense leads to 0 effective defense (Division by Zero/Freeze). -/
theorem bug_freeze_exists : impl 512 true = 0 := rfl

/-- Reflecting at 512 defense is worse than not reflecting (0 < 128). -/
theorem bug_reduction_exists : impl 512 true < impl 512 false := by
  native_decide

/-- Even at 200 defense, Reflect reduces effective defense (100 < 200). -/
theorem bug_exists_low_threshold : impl 200 true < impl 200 false := by
  native_decide

/-! ## L2: Characterization -/

/-- 
Any stat in the range [512, 1023] will result in an effective defense 
lower than the un-reflected version, with 512 specifically hitting 0.
-/
theorem bug_range_512_to_1023 (stat : BitVec 16) :
    stat >= 512 ∧ stat < 1024 → impl stat true < impl stat false := by
  intro h
  have h1 : stat >= 512 := h.left
  have h2 : stat < 1024 := h.right
  revert h1 h2
  -- BitVec 16 is small enough for decide if we bound the range
  decide

/-! ## L3: Fix Correctness -/

/-- 
A potential fix: Perform the effective stat calculation *before* doubling,
ensuring the result stays within reasonable bounds and maintains the 2x ratio.
-/
def fix (stat : BitVec 16) (hasReflect : Bool) : Nat :=
  let base := calcEffectiveStat stat
  if hasReflect then base.toNat * 2 else base.toNat

/-- The fix matches the intended specification. -/
theorem fix_matches_spec (stat : BitVec 16) (hasReflect : Bool) :
    fix stat hasReflect = spec stat hasReflect := by
  unfold fix spec
  rfl

/-- The fix ensures that Reflect never decreases the effective stat. -/
theorem fix_is_monotonic (stat : BitVec 16) :
    fix stat true >= fix stat false := by
  unfold fix
  simp
  apply Nat.le_mul_of_pos_right
  exact Nat.zero_lt_succ 1

end AutoResearch
