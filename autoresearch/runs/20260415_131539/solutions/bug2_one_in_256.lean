import SM83

namespace AutoResearch

/-!
# Bug: 1/256 Miss Chance on "100% Accuracy" Moves

In Pokémon Red and Blue, moves with "100% accuracy" (where the threshold is 255) 
and "maximum critical hit rates" (where the threshold is capped at 255) still 
fail to hit or crit if the random number generator produces the value 255.

This occurs because the SM83 assembly uses the `cp` (compare) instruction, 
which sets the carry flag only if `A < B`. The code then checks the carry flag 
to determine success. Since the random value `A` can be 255 and the maximum 
threshold `B` is also 255, the condition `255 < 255` is false, leading to 
a failure (a miss or a non-crit).
-/

/--
The buggy implementation of generic accuracy and critical hit checks.
It generates a random byte and compares it to a threshold using strictly-less-than logic.
-/
def impl (threshold : BitVec 8) (rand : BitVec 8) : Bool :=
  rand < threshold

/--
The intended behavior for a generic hit test.
A threshold of 255 is intended to represent a 100% success rate (256/256).
-/
def spec (threshold : BitVec 8) (rand : BitVec 8) : Bool :=
  if threshold == 255 then true else rand < threshold

/-! ### L1: Bug Exists -/

/--
A move with maximum accuracy (threshold = 255) will miss if the RNG produces 255.
-/
theorem bug_exists : ∃ (t r : BitVec 8), impl t r = false ∧ spec t r = true := by
  -- Witness: threshold 255, random roll 255
  use 255, 255
  native_decide

/-! ### L2: Characterization -/

/--
The bug triggers if and only if the move is intended to be 100% accurate 
(threshold 255) but the random number generated is 255.
-/
theorem bug_iff_100_percent_fail (t r : BitVec 8) :
    (impl t r = false ∧ spec t r = true) ↔ (t = 255 ∧ r = 255) := by
  have h := (by native_decide : ∀ (t r : BitVec 8), 
    (impl t r = false ∧ spec t r = true) ↔ (t = 255 ∧ r = 255))
  exact h t r

/--
For a "guaranteed" move (threshold 255), there is exactly one value out 
of the 256 possible random outcomes that causes a miss.
-/
theorem one_in_256_miss_chance :
    ∃! (r : BitVec 8), impl 255 r ≠ spec 255 r := by
  use 255
  constructor
  · -- Prove it is a witness
    native_decide
  · -- Prove it is the only witness
    intro r hr
    simp [impl, spec] at hr
    -- rand < 255 is false AND true is true
    -- implies rand >= 255. Since it's 8-bit, rand must be 255.
    have : ¬(r < 255) := hr
    have : r ≥ 255 := BitVec.not_lt.mp this
    exact BitVec.le_antisymm (by native_decide) this

/-! ### L3: Fix Correctness -/

/--
A simple fix: if the threshold is 255, bypass the random check and return success.
Alternatively, the comparison could be changed to inclusive (rand <= threshold) 
if the probability scale is intended to be out of 256.
-/
def fix (threshold : BitVec 8) (rand : BitVec 8) : Bool :=
  if threshold == 255 then true else rand < threshold

theorem fix_is_correct (t r : BitVec 8) : fix t r = spec t r := by
  rfl

/--
An alternative assembly-level fix: using an inclusive comparison (rand <= threshold).
In SM83 assembly, this would be `cp b` followed by `jr c, .hit` OR `jr z, .hit`.
-/
def inclusive_fix (threshold : BitVec 8) (rand : BitVec 8) : Bool :=
  rand <= threshold

/-- 
This fix ensures that for threshold 255, all 256 random values result in a hit.
-/
theorem inclusive_fix_100_percent (r : BitVec 8) : inclusive_fix 255 r = true := by
  have h := (by native_decide : ∀ (r : BitVec 8), inclusive_fix 255 r = true)
  exact h r

end AutoResearch
