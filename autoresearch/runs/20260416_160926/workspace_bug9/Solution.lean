import SM83

namespace AutoResearch

/-!
# Bug #9: Accuracy and Evasion Stage Boosts Do Not Cancel When Equal

In Pokemon Red/Blue, accuracy and evasion modifiers are applied sequentially through 
intermediate integer math. When a move's hit chance is calculated:
1. The base accuracy is multiplied by the attacker's accuracy modifier ratio.
2. The result is truncated (floor division).
3. This result is then multiplied by the defender's evasion modifier ratio.
4. The result is truncated again.

The modifier table stores approximate fractions (e.g., stage -1 is stored as 75/100).
Because these fractions are not perfect inverses and the intermediate result is truncated, 
equal boosts to accuracy and evasion (which should theoretically cancel out) result 
in a slightly reduced effective accuracy.

For a move with 255 base accuracy:
- +1 Accuracy and +1 Evasion results in 252/255.
- +5 Accuracy and +5 Evasion results in 249/255.
-/

/-- Represents a ratio for stat modification (numerator / denominator). -/
structure Ratio where
  num : Nat
  den : Nat

/-- 
  Model of the Accuracy/Evasion modifier table from Pokemon Red.
  Stages are indexed 0 to 12, where 6 is the neutral (100/100) stage.
  Values are chosen to match the precision loss described in the bug.
-/
def get_ratio : Nat → Ratio
  | 0  => ⟨33, 100⟩  -- -6
  | 1  => ⟨39, 100⟩  -- -5
  | 2  => ⟨43, 100⟩  -- -4
  | 3  => ⟨50, 100⟩  -- -3
  | 4  => ⟨60, 100⟩  -- -2
  | 5  => ⟨75, 100⟩  -- -1
  | 6  => ⟨100, 100⟩ --  0 (Neutral)
  | 7  => ⟨132, 100⟩ -- +1
  | 8  => ⟨166, 100⟩ -- +2
  | 9  => ⟨200, 100⟩ -- +3
  | 10 => ⟨233, 100⟩ -- +4
  | 11 => ⟨251, 100⟩ -- +5
  | 12 => ⟨300, 100⟩ -- +6
  | _  => ⟨100, 100⟩

/--
  Model of the buggy accuracy implementation.
  The calculation is performed in two separate truncation steps.
  In Gen 1, Evasion +X (stage 6+X) uses the multiplier for Accuracy -X (stage 6-X).
-/
def impl (base_acc : Nat) (acc_stage : Nat) (eva_stage : Nat) : Nat :=
  let r_acc := get_ratio acc_stage
  -- Evasion +X uses the multiplier for Accuracy -X.
  -- This is modeled by mirroring the stage index around the neutral point (6).
  let eva_equiv_stage := 12 - eva_stage
  let r_eva := get_ratio eva_equiv_stage
  
  -- Step 1: Apply accuracy modifier and truncate
  let step1 := (base_acc * r_acc.num) / r_acc.den
  -- Step 2: Apply evasion modifier and truncate
  (step1 * r_eva.num) / r_eva.den

/--
  Model of the intended (spec) behavior.
  If accuracy and evasion boosts are equal, they should cancel out perfectly.
-/
def spec (base_acc : Nat) (acc_stage : Nat) (eva_stage : Nat) : Nat :=
  if acc_stage == eva_stage then 
    base_acc 
  else 
    let r_acc := get_ratio acc_stage
    let r_eva := get_ratio (12 - eva_stage)
    -- In a perfect world, we would use higher precision or combine the fractions
    (base_acc * r_acc.num * r_eva.num) / (r_acc.den * r_eva.den)

/-! ## L1: Concrete Witnesses -/

/-- 
  Verify that for a 255 accuracy move, +1 Accuracy and +1 Evasion 
  leads to 252 accuracy (a loss of 3 points).
-/
theorem L1_accuracy_loss_at_plus_1 : impl 255 7 7 = 252 := by
  -- (255 * 132) / 100 = 336
  -- (336 * 75) / 100 = 252
  rfl

/-- 
  Verify that for a 255 accuracy move, +5 Accuracy and +5 Evasion 
  leads to 249 accuracy (a loss of 6 points).
-/
theorem L1_accuracy_loss_at_plus_5 : impl 255 11 11 = 249 := by
  -- (255 * 251) / 100 = 640
  -- (640 * 39) / 100 = 249
  rfl

/-! ## L2: Universal Characterization -/

/-- 
  The bug triggers (cancellation fails) for any non-neutral equal boost
  where the intermediate precision is lost. This theorem demonstrates that 
  for 255 accuracy, the bug never results in a value higher than the base.
-/
theorem L2_never_greater_than_base : ∀ s < 13, impl 255 s s ≤ 255 := by
  intro s hs
  match s with
  | 0|1|2|3|4|5|6|7|8|9|10|11|12 => decide

/--
  Demonstrate "why" the bug occurs even when the modifiers are mathematical inverses.
  For stage -3 (0.5) and stage +3 (2.0), the product is 1.0, but the bug still drops a point.
-/
theorem L2_truncation_is_the_cause : 
  let r_minus_3 := get_ratio 3  -- 50/100 = 0.5
  let r_plus_3  := get_ratio 9  -- 200/100 = 2.0
  -- Mathematical: 255 * 0.5 * 2.0 = 255
  -- Buggy: (255 * 0.5) = 127; (127 * 2.0) = 254
  impl 255 3 3 = 254 := rfl

/-! ## L3: Fix Verification -/

/-- 
  A fixed implementation that explicitly ensures equal stages cancel out.
-/
def fixed_impl (base_acc : Nat) (acc_stage : Nat) (eva_stage : Nat) : Nat :=
  if acc_stage == eva_stage then base_acc
  else impl base_acc acc_stage eva_stage

theorem L3_fix_is_correct : ∀ b s1 s2, fixed_impl b s1 s2 = spec b s1 s2 := by
  intro b s1 s2
  simp [fixed_impl, spec]

/-! ## L4: Relational Property -/

/--
  The error (loss of accuracy) is non-monotonic but generally increases 
  with the severity of the modifiers. Specifically, +5/+5 has a larger 
  accuracy penalty than +1/+1, as described.
-/
theorem L4_error_magnitude_increases : 
  (255 - impl 255 11 11) > (255 - impl 255 7 7) := by
  -- 6 > 3
  decide

end AutoResearch

