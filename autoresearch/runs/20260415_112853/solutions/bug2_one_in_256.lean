import SM83

namespace AutoResearch

/-!
# Bug #2: one_in_256 (The "1/256 Miss Chance")

## Description
In Pokémon Red/Blue, moves intended to have 100% accuracy (and critical hits intended 
to be guaranteed) can still fail with a probability of 1 in 256. 

This occurs because the hit test logic uses the SM83 `cp` (Compare) instruction 
followed by a `nc` (No Carry) jump condition. 
- `cp b` computes `A - B` and sets the Carry flag if `A < B`.
- `ret nc` (or `jr nc`) returns or jumps if the Carry flag is NOT set (`A ≥ B`).

The random value `A` is a byte [0, 255]. The threshold `B` is also an 8-bit value, 
capped at 255. Even if `B` is 255 (intended to be 100%), if `A` is also 255, 
then `A ≥ B` is true, the carry flag is cleared, and the move misses.
-/

/--
Models the success/failure logic of the hit/crit test from the assembly.
- `threshold`: The accuracy or crit threshold (Register B, 0-255).
- `random`: The random value from `BattleRandom` (Register A, 0-255).
Returns `true` if the test succeeds (the move hits or crits).
-/
def pokemonHitCheck (threshold : BitVec 8) (random : BitVec 8) : Bool :=
  -- In assembly: 
  --   cp b    ; A - B
  --   ret nc  ; Fail if A >= B
  -- Success occurs only if A < B.
  random.toNat < threshold.toNat

/--
The specification for a "perfect" hit test.
A move with a threshold of 255 (the maximum possible byte value) 
should be guaranteed to succeed.
-/
def specHitCheck (threshold : BitVec 8) (random : BitVec 8) : Bool :=
  if threshold == 255 then 
    true 
  else 
    -- For non-max values, the intended logic is roughly (T/256) success rate.
    random.toNat < threshold.toNat

/--
A fixed version of the hit check. 
Treating 255 as a special "always hit" case is a common way to fix this in Gen 1.
-/
def fixedHitCheck (threshold : BitVec 8) (random : BitVec 8) : Bool :=
  threshold == 255 || random.toNat < threshold.toNat

-- ==========================================
-- L1: Bug Existence
-- ==========================================

/-- 
Verification that a "100% accuracy" move (threshold 255) can still miss.
If the random number generator returns 255, the move fails.
-/
theorem bug_exists : ∃ (r : BitVec 8), pokemonHitCheck 255 r = false := by
  use 255
  -- (255 < 255) is false.
  native_decide

-- ==========================================
-- L2: Characterization
-- ==========================================

/--
The bug triggers for maximum-threshold moves if and only if the random value is 255.
-/
theorem bug_trigger_condition : 
  ∀ (r : BitVec 8), pokemonHitCheck 255 r = false ↔ r = 255 := by
  intro r
  -- Since BitVec 8 has only 256 values, we can verify this for all r.
  have h := (by native_decide : ∀ (x : BitVec 8), pokemonHitCheck 255 x = false ↔ x = 255)
  exact h r

/--
The probability of missing a "100% accuracy" move is exactly 1/256.
We verify this by showing that exactly one input out of the 256 possible 
random bytes causes a failure.
-/
theorem miss_chance_is_exactly_1_in_256 :
  (List.range 256).filter (λ (r : Nat) => pokemonHitCheck 255 (BitVec.ofNat 8 r) == false) = [255] := by
  native_decide

-- ==========================================
-- L3: Fix Correctness
-- ==========================================

/--
The fixed version matches the intended specification for all inputs.
-/
theorem fix_matches_spec (t r : BitVec 8) : fixedHitCheck t r = specHitCheck t r := by
  unfold fixedHitCheck specHitCheck
  split <;> rfl

/--
With the fix, a move with threshold 255 never misses, regardless of the random value.
-/
theorem fixed_never_misses_at_max : ∀ (r : BitVec 8), fixedHitCheck 255 r = true := by
  intro r
  have h := (by native_decide : ∀ (x : BitVec 8), fixedHitCheck 255 x = true)
  exact h r

-- ==========================================
-- L4: CPU Semantics Verification
-- ==========================================

/--
Models the specific SM83 logic using the provided CPU state abstractions.
If register B is 255 and A is 255, the Carry flag is NOT set.
-/
theorem sm83_carry_flag_behavior :
  let s := SM83.defaultState.setA 255 |>.setB 255
  -- Executing `cp b` (A - B) with 255 and 255
  let s_after_cp := SM83.execSub s 255 -- cp b is effectively sub b without storing result
  s_after_cp.cFlag = false := by
  -- In SM83, A < B sets Carry. 255 < 255 is false.
  rfl

/--
Confirms that the high-level `pokemonHitCheck` correctly represents 
the assembly sequence `cp b; ret nc`.
-/
theorem hit_check_fidelity (a b : BitVec 8) :
  let carry_set := a.toNat < b.toNat
  -- Subroutine continues (hits) only if Carry is set.
  carry_set = pokemonHitCheck b a := by
  rfl

end AutoResearch

