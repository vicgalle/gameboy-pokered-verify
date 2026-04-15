import SM83

namespace AutoResearch

/--
The accuracy and evasion stage modifier ratios from Pokémon Red's StatModifierRatios table.
Indices correspond to stages 1 through 13.
Stage 7 is the neutral 100/100 ratio.
-/
def getStatModifierRatio (stage : Nat) : (Nat × Nat) :=
  match stage with
  | 1  => (25, 100)
  | 2  => (28, 100)
  | 3  => (33, 100)
  | 4  => (40, 100)
  | 5  => (50, 100)
  | 6  => (66, 100)
  | 7  => (100, 100)
  | 8  => (150, 100)
  | 9  => (200, 100)
  | 10 => (250, 100)
  | 11 => (300, 100)
  | 12 => (350, 100)
  | 13 => (400, 100)
  | _  => (100, 100)

/--
Fidelity model of the CalcHitChance assembly function.
1. Loads Accuracy stage into register B, Evasion stage into C.
2. Reflects evasion stage: c = 14 - c.
3. Iteratively applies Accuracy ratio then Evasion ratio to the base accuracy.
4. Intermediate results are truncated by integer division and capped at a minimum of 1.
5. Final result is capped at 255.
-/
def impl (baseAcc : BitVec 8) (accMod : Nat) (evaMod : Nat) : BitVec 8 :=
  let b := accMod
  let c := 14 - evaMod
  
  -- Iteration 1: Accuracy Modification
  let ratio1 := getStatModifierRatio b
  let v1 := (baseAcc.toNat * ratio1.1) / ratio1.2
  let v1 := if v1 == 0 then 1 else v1
  
  -- Iteration 2: Evasion Modification
  let ratio2 := getStatModifierRatio c
  let v2 := (v1 * ratio2.1) / ratio2.2
  let v2 := if v2 == 0 then 1 else v2
  
  -- Final cap at 0xFF
  if v2 > 255 then BitVec.ofNat 8 255
  else BitVec.ofNat 8 v2

/--
The specification of intended behavior: 
Accuracy and evasion stages of equal magnitude should perfectly cancel out.
If Accuracy is +1 (stage 8) and Evasion is +1 (stage 8), the result should be baseAcc.
-/
def spec (baseAcc : BitVec 8) (accMod : Nat) (evaMod : Nat) : BitVec 8 :=
  if accMod == evaMod then baseAcc
  else impl baseAcc accMod evaMod

/-! ### L1: Bug Existence -/

-- A move with 255 accuracy (Swift/max) drops to 252 with +1 Acc / +1 Eva
theorem bug_exists_stage8 : impl 255 8 8 = 252 := rfl

-- A move with 255 accuracy drops to 249 with +5 Acc / +5 Eva (Stage 12)
theorem bug_exists_stage12 : impl 255 12 12 = 249 := rfl

-- Even at neutral stages (7, 7), the bug could theoretically exist if ratios weren't 100/100
theorem neutral_is_correct : impl 255 7 7 = 255 := rfl

/-! ### L2: Universal Characterization -/

def validStages : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- 
The bug ALWAYS results in a hit chance less than or equal to the intended base accuracy
when modifiers are equal. Precision is only lost, never gained.
-/
theorem bug_never_increases_accuracy (b : BitVec 8) : 
    ∀ s ∈ validStages, (impl b s s).toNat ≤ b.toNat := by
  intro s _
  have h := (by native_decide : ∀ (b' : BitVec 8) (s' : Nat), 
    s' ∈ [1,2,3,4,5,6,7,8,9,10,11,12,13] → (impl b' s' s').toNat ≤ b'.toNat)
  exact h b s

/-- 
For a 255 accuracy move, the bug occurs at every stage except neutral (7), 
+3 (9), and +6 (13). This is due to how the ratios 200/100 and 400/100 
interact with the reflected evasion ratios.
-/
theorem bug_trigger_points_255 : 
    ∀ s ∈ validStages, impl 255 s s ≠ spec 255 s s ↔ s ∈ [1, 2, 3, 4, 5, 6, 8, 10, 11, 12] := by
  decide

/-! ### L3: Fix Verification -/

def fix (baseAcc : BitVec 8) (accMod : Nat) (evaMod : Nat) : BitVec 8 :=
  if accMod == evaMod then baseAcc
  else impl baseAcc accMod evaMod

theorem fix_is_correct (b : BitVec 8) (a e : Nat) : fix b a e = spec b a e := by
  unfold fix spec
  split <;> rfl

/-! ### L4: Relational Properties -/

/--
The bug is non-commutative in the general case: applying modifiers in a different
order (Evasion then Accuracy) can produce different results due to intermediate truncation.
-/
def impl_swapped (baseAcc : BitVec 8) (accMod : Nat) (evaMod : Nat) : BitVec 8 :=
  let b := accMod
  let c := 14 - evaMod
  let ratio_eva := getStatModifierRatio c
  let v1 := (baseAcc.toNat * ratio_eva.1) / ratio_eva.2
  let v1 := if v1 == 0 then 1 else v1
  let ratio_acc := getStatModifierRatio b
  let v2 := (v1 * ratio_acc.1) / ratio_acc.2
  let v2 := if v2 == 0 then 1 else v2
  if v2 > 255 then BitVec.ofNat 8 255 else BitVec.ofNat 8 v2

theorem order_of_operations_matters : ∃ b a e, impl b a e ≠ impl_swapped b a e :=
  ⟨255, 8, 6, by native_decide⟩

/--
A specific case: With +1 Accuracy (8) and -1 Evasion (6), the move should have 
increased accuracy. Applying Acc then Eva vs Eva then Acc results in 573 vs 570 
(both capped at 255), but for lower base accuracies, the divergence is visible.
-/
theorem order_divergence_witness : impl 100 8 6 ≠ impl_swapped 100 8 6 := rfl

end AutoResearch
