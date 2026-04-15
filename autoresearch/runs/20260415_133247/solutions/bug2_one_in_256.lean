import SM83

/-!
# Bug: 1/256 Miss Chance (the "one_in_256" bug)

In Pokémon Red/Blue, the accuracy and critical hit checks use a comparison 
where a random roll `r` (0-255) is compared against a threshold `t` (0-255).
The check is implemented as `r < t`. Even when the threshold is the maximum 
value (255), a roll of 255 results in a failure (255 < 255 is false), 
creating a 1/256 chance of failure for "guaranteed" events.
-/

namespace AutoResearch

/-- 
Models the buggy hit/crit check in the SM83 assembly.
The assembly uses `cp b` followed by `jr nc, .missed` (or `ret nc` for crits).
`cp` sets the carry flag if `A < b`. `nc` (no carry) occurs if `A >= b`.
Therefore, the move hits (or crits) ONLY if `random_roll < threshold`.
-/
def impl (threshold : BitVec 8) (random_roll : BitVec 8) : Bool :=
  random_roll < threshold

/-- 
The intended behavior: a threshold of 255 should represent a 100% 
success rate, meaning the move should hit for any random roll 0-255.
-/
def spec (threshold : BitVec 8) (random_roll : BitVec 8) : Bool :=
  if threshold == 255 then true else random_roll < threshold

/-! ### L1: Bug Existence -/

/-- There exists a case (max threshold and max roll) where the move misses. -/
theorem bug_exists : ∃ t r, impl t r ≠ spec t r :=
  ⟨255, 255, by native_decide⟩

/-! ### L2: Characterization -/

/-- 
The bug triggers if and only if the threshold is 255 and the roll is 255.
For any other roll or threshold, the buggy code matches the intended 
behavior for sub-100% accuracy.
-/
theorem bug_iff (t r : BitVec 8) : 
    impl t r ≠ spec t r ↔ (t = 255 ∧ r = 255) := by
  native_decide

/-- 
For a move with "100% accuracy" (threshold 255), the probability of 
failure is exactly 1/256. 
-/
theorem miss_count_at_max_accuracy : 
    (List.range 256).filter (λ r => !impl 255 (BitVec.ofNat 8 r)) |>.length = 1 := by
  native_decide

/-! ### L3: Fix Correctness -/

/-- 
A potential fix: change the comparison to 'less than or equal' (using `cp` 
and checking if the result is carry OR zero, or simply adjusting the logic).
Alternatively, handle the $ff case explicitly.
-/
def fix (t r : BitVec 8) : Bool :=
  r < t || (t == 255)

/-- The fix matches the specification for all possible inputs. -/
theorem fix_correct (t r : BitVec 8) : fix t r = spec t r := by
  have h := (by native_decide : ∀ t r : BitVec 8, fix t r = spec t r)
  exact h t r

/-! ### CPU-Level Verification -/

/-- 
Verifies that the SM83 `cp` instruction logic indeed results in 'no carry' 
when the random roll in A is equal to the threshold in B.
-/
theorem sm83_logic_failure : 
    let s := SM83.defaultState.setA 255 |>.setB 255
    let s' := SM83.execCp (BitVec.ofNat 8 255) s -- cp b
    s'.cFlag = false := by
  -- In SM83, cp A, B is A - B. 
  -- If A >= B, Carry flag is 0.
  -- 255 - 255 = 0, no borrow needed, so Carry = 0.
  simp [SM83.execCp, SM83.CPUState.setA, SM83.CPUState.setB]
  native_decide

end AutoResearch
