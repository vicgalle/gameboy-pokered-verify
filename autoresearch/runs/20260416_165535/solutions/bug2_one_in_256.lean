import SM83

namespace AutoResearch

/-
  Bug: The "one_in_256" Miss Chance
  In Pokemon Red/Blue, the hit check for moves is:
  `random_value < accuracy_threshold`
  
  Since both `random_value` and `accuracy_threshold` are 8-bit (0-255),
  even for a move with "100% accuracy" (threshold = 255), if the random 
  generator rolls 255, the check `255 < 255` evaluates to false, 
  causing an unintended miss.
-/

/--
  The buggy implementation of accuracy check used in Gen 1.
  `acc`: move accuracy (0-255).
  `rand`: random number generated (0-255).
  Returns true if the move hits, false if it misses.
-/
def impl (acc rand : BitVec 8) : Bool :=
  rand.toNat < acc.toNat

/--
  The intended accuracy check.
  A move with 255/255 accuracy should be guaranteed to hit.
-/
def spec (acc rand : BitVec 8) : Bool :=
  if acc == 255 then true else rand.toNat < acc.toNat

-- L1: Prove that a bug exists (Concrete witness)
-- When accuracy is 255 and the random roll is 255, the move misses (impl = false),
-- but it should have hit (spec = true).
theorem bug_exists : ∃ acc rand, impl acc rand ≠ spec acc rand := by
  -- Witness: Max accuracy (255) and Max random roll (255)
  exists 255, 255
  native_decide

-- L2: Universal characterization of the bug
-- The bug occurs if and only if the accuracy is 255 and the random roll is 255.
theorem bug_iff_max_values : ∀ acc rand : BitVec 8, 
  (impl acc rand ≠ spec acc rand) ↔ (acc = 255 ∧ rand = 255) := by
  intro acc rand
  have := (by native_decide : ∀ a r : BitVec 8, 
    ((r.toNat < a.toNat) ≠ (if a == 255 then true else r.toNat < a.toNat)) ↔ (a = 255 ∧ r = 255))
  exact this acc rand

-- L2: Specifically for 100% accuracy moves (threshold 255), 
-- the move misses if and only if the roll is exactly 255.
theorem max_accuracy_miss_condition : ∀ rand : BitVec 8, 
  impl 255 rand = false ↔ rand = 255 := by
  intro rand
  have := (by native_decide : ∀ r : BitVec 8, (r.toNat < 255) = false ↔ r = 255)
  exact this rand

-- L3: A fixed version of the accuracy check.
-- We can fix it by either using a special case for 255 or changing the comparison.
def fix (acc rand : BitVec 8) : Bool :=
  acc == 255 || rand.toNat < acc.toNat

-- L3: Verification that the fix matches the specification.
theorem fix_correct : ∀ acc rand : BitVec 8, fix acc rand = spec acc rand := by
  intro acc rand
  simp [fix, spec]

-- L4: Relational/Universal Property
-- In the buggy implementation, no move can ever be 100% guaranteed.
-- For any accuracy value provided, there is at least one random roll (255) that causes a miss.
theorem impl_never_guaranteed : ∀ acc : BitVec 8, ∃ rand : BitVec 8, impl acc rand = false := by
  intro acc
  -- The roll 255 always fails the "rand < acc" check because acc <= 255
  exists 255
  have := (by native_decide : ∀ a : BitVec 8, ((255 : BitVec 8).toNat < a.toNat) = false)
  exact this acc

-- L4: Relational Property
-- In the intended specification, there is at least one accuracy value that guarantees a hit.
theorem spec_can_be_guaranteed : ∃ acc : BitVec 8, ∀ rand : BitVec 8, spec acc rand = true := by
  exists 255
  intro rand
  simp [spec]

end AutoResearch
