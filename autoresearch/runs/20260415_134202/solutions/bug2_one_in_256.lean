import SM83

namespace AutoResearch

/--
Models the comparison logic used in MoveHitTest and CriticalHitTest.
In the SM83 CPU:
`cp b` computes `A - B`.
The Carry flag (C) is set if `A < B` (unsigned).
The code typically follows this with `ret nc` (Return No Carry), meaning
it exits the hit/crit logic early if `A >= B`.
Success (hitting/critting) only continues if `A < B`.
-/
def check_success (threshold rand : BitVec 8) : Bool :=
  -- Carry is set if rand < threshold
  rand.toNat < threshold.toNat

/--
The buggy implementation found in Pokémon Red/Blue.
Even when the intended probability is "100%", the engine caps the threshold at 255 ($FF).
Since the random roll `rand` is also an 8-bit value (0-255), the condition
`rand < 255` will fail when `rand` is 255, leading to a 1/256 failure rate.
-/
def impl (threshold rand : BitVec 8) : Bool :=
  check_success threshold rand

/--
The intended behavior: a move or effect with a "100% rate" (represented by 
the maximum threshold 255) should always succeed regardless of the random roll.
-/
def spec (threshold rand : BitVec 8) : Bool :=
  if threshold == 255 then true else check_success threshold rand

/-- 
L1: Bug Existence. 
We demonstrate that for a maximum accuracy/crit threshold of 255, 
a random roll of 255 causes a failure (miss) where the spec expects success.
-/
theorem bug_exists : ∃ t r, t = 255 ∧ r = 255 ∧ impl t r = false ∧ spec t r = true := by
  exists 255, 255
  simp [impl, spec, check_success]
  native_decide

/-- 
L2: Characterization.
The bug triggers (impl differs from spec) if and only if the threshold
is set to the maximum (255) and the random roll hits exactly 255.
-/
theorem bug_iff (t r : BitVec 8) :
  impl t r ≠ spec t r ↔ (t = 255 ∧ r = 255) := by
  revert t r
  native_decide

/--
L2: Probability Ceiling.
No matter how high the threshold is (up to 255), there is always at least 
one random value that results in failure in the buggy implementation.
-/
theorem always_possible_to_miss (t : BitVec 8) : ∃ r, impl t r = false := by
  -- For any t, if we roll 255, the condition `255 < t` is always false
  -- because 255 is the maximum BitVec 8 value.
  exists 255
  simp [impl, check_success]
  have h := t.toNat_lt_256
  omega

/--
L3: Fix Correctness.
A common fix is to handle the 255 threshold case specifically to ensure 
it always returns true, or to use a 16-bit comparison.
-/
def fix (t r : BitVec 8) : Bool :=
  if t == 255 then true else r.toNat < t.toNat

theorem fix_is_correct (t r : BitVec 8) : fix t r = spec t r := by
  -- The fix is definitionally equal to the spec
  rfl

/--
Alternative L3 Fix: Using the SM83 `adc` or a comparison that considers the 
overflow, or conceptually checking if `rand <= threshold` if threshold was 
allowed to be 0-254 for 1-255 and some other flag for 256. 
In reality, the simplest fix is just checking for 255.
-/
theorem fix_matches_spec_universal (t r : BitVec 8) : fix t r = spec t r := by
  revert t r
  native_decide

end AutoResearch
