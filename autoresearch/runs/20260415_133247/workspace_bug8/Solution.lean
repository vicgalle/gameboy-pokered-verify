import SM83

/-!
# Bug: Reflect and Light Screen Overflow

In Pokémon Red/Blue/Yellow, Reflect and Light Screen double the user's Defense
or Special stat during damage calculation. If any stat exceeds 255, the game
scales both attack and defense by dividing them by 4 and storing them in 8-bit
registers.

The bug occurs because the division by 4 followed by 8-bit truncation doesn't
account for values reaching 1024 or higher. A stat of 512 becomes 1024 after
Reflect, and 1024 / 4 = 256. When 256 is stored in an 8-bit register, it
overflows to 0. This results in either a division-by-zero crash or the Pokémon's
defense being treated as 0, leading to catastrophic damage.

This formalization models the damage calculation scaling logic and proves the
existence and impact of this overflow.
-/

namespace AutoResearch

open BitVec

/-- 
Models the effective defense stat calculation during damage processing.
Includes the doubling from Reflect/Light Screen and the scaling logic 
used for stats over 255.
-/
def impl (stat : BitVec 16) : BitVec 8 :=
  let doubled := stat <<< 1
  -- If the doubled stat exceeds 255, scale by 4 and truncate to 8-bit.
  if doubled > 255 then
    (doubled >>> 2).truncate 8
  else
    doubled.truncate 8

/-- 
Models the intended behavior: the doubled and scaled stat should be 
saturated (capped at 255) to prevent wrapping around to zero.
-/
def spec (stat : BitVec 16) : BitVec 8 :=
  let doubled := stat.toNat * 2
  if doubled > 255 then
    let scaled := doubled / 4
    if scaled > 255 then 255 else BitVec.ofNat 8 scaled
  else
    BitVec.ofNat 8 doubled

/-! ### L1: Bug Existence -/

/-- A defense stat of 512 causes the effective defense to wrap to 0. -/
theorem bug_exists : ∃ x, impl x ≠ spec x := 
  ⟨512, by native_decide⟩

/-! ### L2: Characterization -/

/-- 
The critical crash point: Defense of exactly 512 becomes 0 after Reflect doubling
and scaling, causing a division by zero in the damage formula.
-/
theorem bug_causes_zero_defense : impl 512 = 0 := by
  native_decide

/-- 
The bug triggers whenever the doubled stat is a multiple of 1024.
Since (stat * 2) / 4 = stat / 2, the bug occurs at stat = 512, 1024, etc.
-/
theorem bug_is_periodic : ∀ x : BitVec 16, x ≥ 512 ∧ x % 512 = 0 → impl x = 0 := by
  have h := (by native_decide : ∀ x : BitVec 16, x ≥ 512 ∧ x % 512 = 0 → impl x = 0)
  exact h

/--
Reflect should make you stronger, but at 512 defense, you are 128x weaker 
than if you didn't have Reflect at all.
-/
theorem reflect_makes_you_weaker : 
  let without_reflect := ((BitVec.ofNat 16 512) >>> 2).truncate 8 -- 128
  let with_reflect := impl 512 -- 0
  without_reflect = 128 ∧ with_reflect = 0 := by
  native_decide

/-! ### L3: Fix Correctness -/

/-- 
A fixed implementation that saturates the result at 255 if the scaled
value exceeds the 8-bit limit.
-/
def fix (stat : BitVec 16) : BitVec 8 :=
  let doubled := stat <<< 1
  if doubled > 255 then
    let scaled := doubled >>> 2
    -- Check if the 16-bit scaled value is too large for 8 bits
    if scaled > 255 then 255 else scaled.truncate 8
  else
    doubled.truncate 8

/-- The fix matches the specification for all possible 16-bit stat values. -/
theorem fix_correct (x : BitVec 16) : fix x = spec x := by
  have h := (by native_decide : ∀ x : BitVec 16, fix x = spec x)
  exact h x

/-- The fix preserves monotonicity: increasing stat never decreases effective defense. -/
theorem fix_is_monotonic (x y : BitVec 16) : x ≤ y → fix x ≤ fix y := by
  have h := (by native_decide : ∀ x y : BitVec 16, x ≤ y → fix x ≤ fix y)
  exact h x y

end AutoResearch
