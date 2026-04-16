import SM83

namespace AutoResearch

/-
  # Bug: 1/256 Miss Chance on "100% Accuracy" Moves

  In Pokemon Red/Blue, move accuracy checks use an 8-bit comparison:
  `random_value < accuracy_threshold`

  Both the random value and the accuracy threshold are 8-bit integers (0-255).
  For moves intended to have 100% accuracy, the threshold is set to 255.
  However, since the random generator can produce the value 255, the condition
  `255 < 255` evaluates to false, causing a miss.

  The same logic applies to critical hits: even when the critical hit threshold 
  is capped at its maximum value (255), a random roll of 255 results in no critical hit.
-/

/--
  The buggy implementation of the hit check.
  `acc`: move accuracy or critical hit threshold (0-255).
  `rand`: random number generated (0-255).
  Returns true if the check succeeds (hits/crits), false if it fails.
-/
def impl (acc rand : BitVec 8) : Bool :=
  rand.toNat < acc.toNat

/--
  The intended specification for the hit check.
  A move with maxed accuracy (255) should be guaranteed to hit.
-/
def spec (acc rand : BitVec 8) : Bool :=
  if acc == 255 then true else rand.toNat < acc.toNat

-- L1: Concrete witness showing the bug
-- When accuracy is 255 and the random roll is 255, the implementation misses.
theorem bug_exists : ∃ acc rand : BitVec 8, impl acc rand ≠ spec acc rand := by
  exists 255, 255
  native_decide

-- L2: Universal characterization
-- The implementation and specification diverge if and only if accuracy and roll are both 255.
theorem bug_iff_maxed_values : ∀ acc rand : BitVec 8, 
  (impl acc rand ≠ spec acc rand) ↔ (acc = 255 ∧ rand = 255) := by
  intro acc rand
  have := (by native_decide : ∀ a r : BitVec 8, 
    ((r.toNat < a.toNat) ≠ (if a == 255 then true else r.toNat < a.toNat)) ↔ (a = 255 ∧ r = 255))
  exact this acc rand

-- L2: Universal property: In Gen 1, a roll of 255 ALWAYS causes a miss/non-crit,
-- regardless of the accuracy or critical hit threshold.
theorem roll_255_always_misses : ∀ acc : BitVec 8, impl acc 255 = false := by
  intro acc
  have := (by native_decide : ∀ a : BitVec 8, (255 : BitVec 8).toNat < a.toNat = false)
  exact this acc

-- L3: Proposed fix
-- We can fix the bug by allowing the 255 threshold to represent a guaranteed success.
def fix (acc rand : BitVec 8) : Bool :=
  acc == 255 || rand.toNat < acc.toNat

theorem fix_correct : ∀ acc rand : BitVec 8, fix acc rand = spec acc rand := by
  intro acc rand
  simp [fix, spec]

-- L4: Relational Property
-- The implementation is strictly "weaker" than the specification; 
-- if the implementation hits, the specification would also have hit.
theorem impl_implies_spec : ∀ acc rand : BitVec 8, impl acc rand = true → spec acc rand = true := by
  intro acc rand
  have := (by native_decide : ∀ a r : BitVec 8, (r.toNat < a.toNat = true) → (if a == 255 then true else r.toNat < a.toNat) = true)
  exact this acc rand

-- L4: Relational Property - 100% Accuracy
-- In the specification, it is possible to guarantee a hit.
theorem spec_can_be_guaranteed : ∃ acc : BitVec 8, ∀ rand : BitVec 8, spec acc rand = true := by
  exists 255
  intro rand
  simp [spec]

-- L4: Relational Property - The "One-in-256" Curse
-- In the buggy implementation, NO move/threshold can ever be 100% guaranteed.
-- For any possible accuracy value, there is always at least one roll (255) that results in failure.
theorem impl_never_guaranteed : ∀ acc : BitVec 8, ∃ rand : BitVec 8, impl acc rand = false := by
  intro acc
  exists 255
  apply roll_255_always_misses

-- L4: Relational Property
-- The divergence occurs only at the 100% (255) accuracy mark. 
-- For any other accuracy value, the implementation matches the specification.
theorem impl_matches_spec_below_max : ∀ acc : BitVec 8, acc ≠ 255 → (∀ rand, impl acc rand = spec acc rand) := by
  intro acc h rand
  simp [impl, spec, h]

end AutoResearch
