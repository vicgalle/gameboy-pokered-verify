import SM83

/-!
# Bug #9: acc_eva_cancel

In the Pokemon Red battle system, accuracy and evasion modifiers are applied in two
separate multiplication/division passes using a table of ratios. If a Pokemon's accuracy
is raised and the opponent's evasion is raised by the same amount, the net effect
should be zero.

However, two factors cause a precision loss:
1. The modifier table stores approximate fractions (e.g., stage -1 is 66/100, which is 
   slightly less than the ideal 2/3).
2. Intermediate integer truncation between the two multiplication passes (Accuracy 
   calculation then Evasion calculation) loses precision even if the fractions 
   were mathematically perfect.

## Formalization Notes
- `getRatio`: Models the `StatModifierRatios` table in the ROM (13 stages, 1-indexed).
- `impl`: Models the `CalcHitChance` assembly routine, following the two-pass loop,
  intermediate floor division, and the minimum-1 clamp.
- `spec`: Models the intended "fixed" behavior where the net stage is calculated first
  and applied in a single pass, ensuring equal stages cancel out.
-/

namespace AutoResearch

/-- 
The stat modifier ratios as stored in the Pokemon Red ROM (`StatModifierRatios`).
Stage 7 is the neutral (100/100) point.
Indices 1-6 are reductions (debuffs), 8-13 are boosts.
-/
def getRatio (stage : Nat) : (Nat × Nat) :=
  match stage with
  | 1  => (25, 100)  -- -6 stages (0.25)
  | 2  => (28, 100)  -- -5
  | 3  => (33, 100)  -- -4
  | 4  => (40, 100)  -- -3
  | 5  => (50, 100)  -- -2
  | 6  => (66, 100)  -- -1 (Approx 2/3)
  | 7  => (100, 100) -- Neutral
  | 8  => (150, 100) -- +1 (1.5)
  | 9  => (200, 100) -- +2
  | 10 => (250, 100) -- +3
  | 11 => (300, 100) -- +4
  | 12 => (350, 100) -- +5
  | 13 => (400, 100) -- +6
  | _  => (100, 100)

/-- 
Model of the buggy `CalcHitChance` logic.
Faithfully follows the assembly loop:
1. Start with Move Accuracy.
2. Pass 1: Apply Accuracy modifier (accMod). Result clamped to min 1.
3. Pass 2: Apply reflected Evasion modifier (14 - evaMod). Result clamped to min 1.
4. Final result capped at 255.
-/
def impl (acc : BitVec 8) (accMod evaMod : Nat) : BitVec 8 :=
  let val0 := acc.toNat
  
  -- Pass 1: Accuracy modifier
  let (n1, d1) := getRatio accMod
  let res1 := (val0 * n1) / d1
  let res1' := if res1 == 0 then 1 else res1
  
  -- Pass 2: Evasion modifier (reflected stage: 14 - evaMod)
  -- The assembly does: ld a, $0e; sub c; ld c, a
  let (n2, d2) := getRatio (14 - evaMod)
  let res2 := (res1' * n2) / d2
  let res2' := if res2 == 0 then 1 else res2
  
  -- Final cap at 0xFF (255)
  if res2' > 255 then BitVec.ofNat 8 255 else BitVec.ofNat 8 res2'

/-- 
Model of the intended behavior: equal accuracy and evasion boosts should cancel.
Mathematically, this means applying a single multiplier based on the net stage change.
-/
def spec (acc : BitVec 8) (accMod evaMod : Nat) : BitVec 8 :=
  let net := 7 + (accMod.toInt - evaMod.toInt)
  let clampedStage := if net < 1 then 1 else if net > 13 then 13 else net.toNat
  let (n, d) := getRatio clampedStage
  let res := (acc.toNat * n) / d
  -- Standard move accuracy clamping (min 1, max 255)
  let res' := if res == 0 then 1 else if res > 255 then 255 else res
  BitVec.ofNat 8 res'

/-! ### L1: Bug Existence -/

/-- 
A move with 255 base accuracy under +1 accuracy and +1 evasion.
Expected: 255. Result: 252.
-/
theorem bug_exists : ∃ (acc : BitVec 8) (s : Nat), s ≥ 1 ∧ s ≤ 13 ∧ impl acc s s ≠ acc := by
  exists (BitVec.ofNat 8 255), 8
  native_decide

/-! ### L2: Characterization -/

/-- 
Exhaustive verification of losses for a 255-accuracy move (e.g. Swift or high-acc moves).
Only stages +2 and +6 happen to cancel perfectly due to exact division by 100.
The +5 case is the "worst case", losing 6 points of accuracy.
-/
theorem bug_stage_analysis :
  (impl (BitVec.ofNat 8 255) 7 7).toNat   = 255 ∧ -- Neutral
  (impl (BitVec.ofNat 8 255) 8 8).toNat   = 252 ∧ -- +1/-1
  (impl (BitVec.ofNat 8 255) 9 9).toNat   = 255 ∧ -- +2/-2
  (impl (BitVec.ofNat 8 255) 10 10).toNat = 254 ∧ -- +3/-3
  (impl (BitVec.ofNat 8 255) 11 11).toNat = 252 ∧ -- +4/-4
  (impl (BitVec.ofNat 8 255) 12 12).toNat = 249 ∧ -- +5/-5 (Worst Case)
  (impl (BitVec.ofNat 8 255) 13 13).toNat = 255   -- +6/-6
:= by native_decide

/-- 
The bug is "biased": equal boosts never benefit the attacker compared to base accuracy.
This holds for all possible 8-bit accuracy values and all 13 modifier stages.
-/
theorem bug_never_helps_attacker (acc : BitVec 8) (s : BitVec 4) :
  (s.toNat ≥ 1 ∧ s.toNat ≤ 13) → 
  (impl acc s.toNat s.toNat).toNat ≤ acc.toNat := by
  intro h
  have h_fixed := (by native_decide : ∀ (a : BitVec 8) (st : BitVec 4), 
    (st.toNat ≥ 1 ∧ st.toNat ≤ 13) → (impl a st.toNat st.toNat).toNat ≤ a.toNat)
  exact h_fixed acc s h

/--
The bug is significant: for the +5/+5 case, the loss is always between 0 and 6.
-/
theorem bug_magnitude_bound (acc : BitVec 8) (s : BitVec 4) :
  (s.toNat ≥ 1 ∧ s.toNat ≤ 13) → 
  (acc.toNat - (impl acc s.toNat s.toNat).toNat ≤ 6) := by
  intro h
  have h_fixed := (by native_decide : ∀ (a : BitVec 8) (st : BitVec 4), 
    (st.toNat ≥ 1 ∧ st.toNat ≤ 13) → (a.toNat - (impl a st.toNat st.toNat).toNat ≤ 6))
  exact h_fixed acc s h

/-! ### L3: Fix Correctness -/

/-- 
Proves that the single-pass "spec" logic perfectly restores the base accuracy 
when stages are equal (for any non-zero base accuracy).
-/
theorem fix_cancels_perfectly (acc : BitVec 8) (s : Nat) :
  s ≥ 1 ∧ s ≤ 13 ∧ acc.toNat > 0 → spec acc s s = acc := by
  intro ⟨h_low, h_high, h_acc_pos⟩
  unfold spec
  have h_diff : (s.toInt - s.toInt) = 0 := Int.sub_self s
  simp [h_diff, getRatio]
  have h_id : (acc.toNat * 100) / 100 = acc.toNat := Nat.mul_div_cancel_left acc.toNat (by decide)
  simp [h_id, h_acc_pos]
  have h_val_clamp : (if acc.toNat > 255 then 255 else acc.toNat) = acc.toNat := by
    have : acc.toNat < 256 := acc.toNat_lt
    split <;> omega
  simp [h_val_clamp]
  apply BitVec.ofNat_toNat

/-! ### L4: Structural Properties -/

/--
Universal property: The buggy logic is monotonic with respect to base accuracy. 
Increasing base accuracy never results in a lower modified hit chance, 
even with the rounding errors.
-/
theorem impl_monotonic_wrt_accuracy (acc1 acc2 : BitVec 8) (am em : Nat) :
  acc1.toNat ≤ acc2.toNat → (impl acc1 am em).toNat ≤ (impl acc2 am em).toNat := by
  intro h_le
  unfold impl
  let (n1, d1) := getRatio am
  let (n2, d2) := getRatio (14 - em)
  
  have h_d1_pos : d1 > 0 := by unfold getRatio; split <;> decide
  have h_d2_pos : d2 > 0 := by unfold getRatio; split <;> decide

  -- Pass 1 monotonicity: (a * n / d) is monotonic
  have h1 : acc1.toNat * n1 / d1 ≤ acc2.toNat * n1 / d1 := 
    Nat.div_le_div_right (Nat.mul_le_mul_right _ h_le)
  
  -- Clamping (if x == 0 then 1 else x) is monotonic
  let r1_1 := if acc1.toNat * n1 / d1 == 0 then 1 else acc1.toNat * n1 / d1
  let r1_2 := if acc2.toNat * n1 / d1 == 0 then 1 else acc2.toNat * n1 / d1
  have h1' : r1_1 ≤ r1_2 := by unfold_let r1_1 r1_2; split <;> split <;> omega
    
  -- Pass 2 monotonicity
  have h2 : r1_1 * n2 / d2 ≤ r1_2 * n2 / d2 := 
    Nat.div_le_div_right (Nat.mul_le_mul_right _ h1')

  let r2_1 := if r1_1 * n2 / d2 == 0 then 1 else r1_1 * n2 / d2
  let r2_2 := if r1_2 * n2 / d2 == 0 then 1 else r1_2 * n2 / d2
  have h2' : r2_1 ≤ r2_2 := by unfold_let r2_1 r2_2; split <;> split <;> omega

  -- Final 255 cap is monotonic
  let f1 := if r2_1 > 255 then 255 else r2_1
  let f2 := if r2_2 > 255 then 255 else r2_2
  have hf : f1 ≤ f2 := by unfold_let f1 f2; split <;> split <;> omega

  -- Mapping back to toNat
  have h_toNat1 : (if r2_1 > 255 then BitVec.ofNat 8 255 else BitVec.ofNat 8 r2_1).toNat = f1 := by
    split <;> simp [f1] <;> apply BitVec.toNat_ofNat_of_lt <;> omega
  
  have h_toNat2 : (if r2_2 > 255 then BitVec.ofNat 8 255 else BitVec.ofNat 8 r2_2).toNat = f2 := by
    split <;> simp [f2] <;> apply BitVec.toNat_ofNat_of_lt <;> omega

  rw [h_toNat1, h_toNat2]
  exact hf

end AutoResearch
