import SM83

namespace AutoResearch

/-!
# Bug: 1/256 Miss Chance on "100% Accuracy" Moves

In Pokemon Red/Blue, accuracy and critical hit checks are performed by comparing 
a random byte (0-255) against a threshold value derived from move stats and modifiers.

The bug is that the game uses a "strictly less than" comparison (`roll < threshold`)
instead of a "less than or equal to" comparison (`roll <= threshold`). 
Because the RNG produces values up to 255, and the maximum threshold is also 255, 
a roll of 255 will result in a miss even if the move's threshold is at its maximum 
possible value (255/255).
-/

/--
The buggy implementation used in Pokemon Red/Blue.
A hit or critical is determined by `roll < threshold`.
-/
def impl (threshold : BitVec 8) (roll : BitVec 8) : Bool :=
  roll < threshold

/--
The intended specification. 
A hit should occur if the roll is within the inclusive range [0, threshold].
For a 100% move (255/255), any roll from 0 to 255 should hit.
-/
def spec (threshold : BitVec 8) (roll : BitVec 8) : Bool :=
  roll <= threshold

/-! ### L1: Concrete Witness -/

/--
L1: Concrete witness of the 1/256 miss bug.
For a move with "100%" accuracy (threshold 255), the RNG value 255 
causes a miss in the implementation but a hit in the specification.
-/
theorem exists_1in256_miss : ∃ (roll : BitVec 8), impl 255 roll = false ∧ spec 255 roll = true := by
  exists 255
  simp [impl, spec]
  native_decide

/-! ### L2: Universal Characterization -/

/--
L2: Universal characterization of the bug.
The implementation and specification differ if and only if the random roll 
is exactly equal to the threshold value.
-/
theorem bug_iff_roll_matches_threshold (t r : BitVec 8) : 
    (impl t r ≠ spec t r) ↔ (r = t) := by
  have h := (by native_decide : ∀ (t' r' : BitVec 8), (r' < t' ≠ r' <= t') ↔ (r' = t'))
  exact h t r

/--
L2: The "1 in 256" property.
For any given threshold, there is exactly one RNG roll (the one equal to the threshold)
that causes the implementation to diverge from the specification.
-/
theorem unique_roll_causes_discrepancy (t : BitVec 8) : 
    ∃! r : BitVec 8, impl t r ≠ spec t r := by
  have h := (by native_decide : ∀ (t' : BitVec 8), ∃! r' : BitVec 8, (r' < t' ≠ r' <= t'))
  exact h t

/-! ### L3: The Fix -/

/--
L3: A fix for the bug. 
By replacing the strictly-less-than check with a less-than-or-equal check, 
the behavior matches the intended specification.
-/
def fix (t r : BitVec 8) : Bool := r <= t

theorem fix_is_correct : ∀ t r, fix t r = spec t r := by
  intro t r; rfl

/-! ### L4: Relational Divergence & Consistency -/

/-- 
L4: The specification correctly handles "guaranteed" moves.
In the specification, a move with accuracy threshold 255 will never miss.
-/
theorem spec_100_percent_accuracy_always_hits : ∀ (roll : BitVec 8), spec 255 roll = true := by
  have h := (by native_decide : ∀ (r : BitVec 8), r <= 255 = true)
  exact h

/-- 
L4: The implementation fails to guarantee "guaranteed" moves.
In the buggy implementation, for a 100% accuracy move, there exists a roll (255) 
that causes the move to miss.
-/
theorem impl_100_percent_accuracy_can_miss : ∃ (roll : BitVec 8), impl 255 roll = false := by
  exists 255
  native_decide

/--
L4: Directional Bias (Pessimism).
The buggy implementation is strictly worse for the player/actor than the specification.
It never incorrectly "hits" when it should miss; it only incorrectly misses.
-/
theorem impl_is_always_pessimistic : ∀ (t r : BitVec 8), impl t r = true → spec t r = true := by
  have h := (by native_decide : ∀ (t' r' : BitVec 8), (r' < t' = true) → (r' <= t' = true))
  exact h t

/--
L4: Monotonicity preservation.
Even with the bug, increasing the threshold never decreases the chance of hitting.
This shows the bug is a consistent offset rather than a chaotic failure.
-/
theorem impl_remains_monotonic : ∀ (r t1 t2 : BitVec 8), t1 <= t2 → impl t1 r = true → impl t2 r = true := by
  have h := (by native_decide : ∀ (r' t1' t2' : BitVec 8), t1' <= t2' → (r' < t1' = true) → (r' < t2' = true))
  exact h

end AutoResearch

