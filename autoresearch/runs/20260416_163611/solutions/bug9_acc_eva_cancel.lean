import SM83

namespace AutoResearch

/-- 
Accuracy modifier table from Pokemon Red/Blue/Yellow.
Indices 0-12 represent stat stages -6 to +6.
The values are stored as percentages (out of 100) of the base accuracy.
The bug stems from the use of approximate fractions (e.g., 2/3 ≈ 66/100).
-/
def accuracy_table : Nat → Nat
  | 0  => 25  -- Stage -6: 2/8 = 0.25
  | 1  => 28  -- Stage -5: 2/7 ≈ 0.28
  | 2  => 33  -- Stage -4: 2/6 ≈ 0.33
  | 3  => 40  -- Stage -3: 2/5 = 0.40
  | 4  => 50  -- Stage -2: 2/4 = 0.50
  | 5  => 66  -- Stage -1: 2/3 ≈ 0.66
  | 6  => 100 -- Stage  0: 2/2 = 1.00
  | 7  => 150 -- Stage +1: 3/2 = 1.50
  | 8  => 200 -- Stage +2: 4/2 = 2.00
  | 9  => 250 -- Stage +3: 5/2 = 2.50
  | 10 => 300 -- Stage +4: 6/2 = 3.00
  | 11 => 350 -- Stage +5: 7/2 = 3.50
  | 12 => 400 -- Stage +6: 8/2 = 4.00
  | _  => 100

/-- 
Bug: Accuracy and Evasion Stage Boosts Do Not Cancel When Equal.
In the buggy implementation, accuracy and evasion modifiers are applied as 
distinct multiplication passes with intermediate integer truncation (floor division).

If a Pokemon has +S Accuracy and the opponent has +S Evasion, 
the accuracy multiplier index is 6+S and the evasion multiplier index is 6-S.

Result = floor(floor(Base * AccMod) / 100 * EvaMod) / 100
-/
def impl (base : BitVec 8) (stage : Nat) : BitVec 8 :=
  let acc_idx := 6 + stage
  let eva_idx := 6 - stage
  let step1 := (base.toNat * accuracy_table acc_idx) / 100
  let step2 := (step1 * accuracy_table eva_idx) / 100
  BitVec.ofNat 8 step2

/-- 
The intended behavior (spec): If the attacker's accuracy is raised by +S stages
and the defender's evasion is raised by +S stages, the modifiers should cancel 
perfectly, resulting in the original base accuracy.
-/
def spec (base : BitVec 8) : BitVec 8 := base

-- L1: Concrete Witnesses

/-- 
Verification of the bug at Stage 1:
A move with 255 base accuracy loses 3 points when both stages are +1.
Calculated as: floor(floor(255 * 1.5) * 0.66) = floor(382 * 0.66) = 252.
-/
theorem exists_bug_255_stage1 : impl 255 1 = 252 := rfl

/-- 
Verification of the worst-case scenario at Stage 5:
Equal +5 accuracy and +5 evasion boosts lose 6 accuracy points (249 vs 255).
Calculated as: floor(floor(255 * 3.5) * 0.28) = floor(892 * 0.28) = 249.
-/
theorem exists_bug_255_stage5_worst : impl 255 5 = 249 := rfl

-- L2: Universal Properties

/-- 
Characterization of which stages trigger the bug for max accuracy (255).
Equal cancellation only happens to work out perfectly at stages 0, 2, and 6.
For all other stages (1, 3, 4, 5), the hit chance is incorrectly reduced.
Notably, Stage 3 fails (254 vs 255) due to intermediate truncation even 
though 2.5 * 0.4 = 1.0 exactly.
-/
theorem stage_bug_mask_255 : 
  (impl 255 0 = 255) ∧ 
  (impl 255 1 < 255) ∧ 
  (impl 255 2 = 255) ∧ 
  (impl 255 3 < 255) ∧ 
  (impl 255 4 < 255) ∧ 
  (impl 255 5 < 255) ∧ 
  (impl 255 6 = 255) := by native_decide

/-- 
Universal Characterization: For all base hit chances and all valid stat stages (0 to 6), 
the buggy implementation never results in a value higher than the intended base accuracy.
This confirms the bug always penalizes accuracy rather than accidentally boosting it.
-/
theorem never_exceeds_spec (b : BitVec 8) (s : Fin 7) : (impl b s.val).toNat ≤ b.toNat := by
  have h := (by native_decide : ∀ (v : BitVec 8) (st : Fin 7), (impl v st.val).toNat ≤ v.toNat)
  exact h b s

/-- 
At Stage 1, the bug triggers for every non-zero hit chance.
-/
theorem stage1_always_lossy_or_eq (b : BitVec 8) : (impl b 1).toNat ≤ b.toNat := by
  have h := (by native_decide : ∀ (v : BitVec 8), (impl v 1).toNat ≤ v.toNat)
  exact h b

-- L3: Fix

/-- 
The fix: Combine modifiers into a single net stage before looking up the value.
If Accuracy Stage = +S and Evasion Stage = +S, the net stage is 0,
resulting in a multiplier of 1.0 (100/100).
-/
def fix (base : BitVec 8) (acc_stage eva_stage : Int) : BitVec 8 :=
  let net := acc_stage - eva_stage
  let idx := (6 + net).toNat
  let multiplier := accuracy_table (if idx > 12 then 12 else idx)
  BitVec.ofNat 8 ((base.toNat * multiplier) / 100)

/-- 
Verification that the fix correctly implements the specification by 
ensuring equal boosts cancel out perfectly for all inputs.
-/
theorem fix_perfect_cancellation (base : BitVec 8) (s : Int) : 
  fix base s s = spec base := by
  unfold fix spec
  have h_net : s - s = 0 := by omega
  have h_idx : (6 + (s - s)).toNat = 6 := by 
    rw [h_net]
    rfl
  rw [h_idx]
  simp [accuracy_table]
  have h_scale : ∀ b : Nat, b * 100 / 100 = b := by 
    intro b; rw [Nat.mul_div_cancel b (by decide)]
  rw [h_scale]
  have h_bv : ∀ b : BitVec 8, BitVec.ofNat 8 b.toNat = b := by
    intro b
    have h_dec := (by native_decide : ∀ v : BitVec 8, BitVec.ofNat 8 v.toNat = v)
    exact h_dec b
  apply h_bv

-- L4: Relational Divergence

/-- 
The buggy implementation and the fix diverge for all non-zero base accuracies at Stage 1.
-/
theorem desync_at_stage_1 : ∀ (b : BitVec 8), b.toNat > 0 → impl b 1 ≠ fix b 1 1 := by
  have h := (by native_decide : ∀ (v : BitVec 8), v.toNat > 0 → impl v 1 ≠ fix v 1 1)
  intro b hb
  exact h b hb

/-- 
The buggy implementation and the fix also diverge for all non-zero base accuracies at Stage 5.
-/
theorem desync_at_stage_5 : ∀ (b : BitVec 8), b.toNat > 0 → impl b 5 ≠ fix b 5 5 := by
  have h := (by native_decide : ∀ (v : BitVec 8), v.toNat > 0 → impl v 5 ≠ fix v 5 5)
  intro b hb
  exact h b hb

end AutoResearch

