import SM83

/-!
# Bug #9: acc_eva_cancel

In the Pokemon Red battle system, accuracy and evasion modifiers are applied in two 
separate multiplication/division passes. Because the stat modifier ratios are 
stored as approximate integers (e.g., 2/3 is stored as 66/100) and intermediate 
integer truncation occurs between passes, equal accuracy and evasion boosts do 
not perfectly cancel out.

For example, if a move has 255 base accuracy and both the attacker's accuracy 
and the defender's evasion are raised by 1 stage, the result is 252 rather than 255.
-/

namespace AutoResearch

/-- 
The stat modifier ratios as stored in the Pokemon Red ROM (`StatModifierRatios`).
Each stage from 1 to 13 corresponds to a (numerator, denominator) pair.
Stage 7 is the neutral (100/100) point.
-/
def getRatio (stage : Nat) : (Nat × Nat) :=
  match stage with
  | 1  => (25, 100)  -- -6 stages
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
Model of the buggy `CalcHitChance` assembly logic.
The logic applies the accuracy modifier first, clamps to a minimum of 1, 
then applies the reflected evasion modifier, clamps again, and finally caps at 255.
-/
def impl (acc : BitVec 8) (accMod evaMod : Nat) : BitVec 8 :=
  let val0 := acc.toNat
  
  -- Iteration 1: Accuracy modifier
  let (n1, d1) := getRatio accMod
  let val1 := (val0 * n1) / d1
  let val1' := if val1 == 0 then 1 else val1
  
  -- Iteration 2: Evasion modifier (reflected stage: 14 - evaMod)
  let (n2, d2) := getRatio (14 - evaMod)
  let val2 := (val1' * n2) / d2
  let val2' := if val2 == 0 then 1 else val2
  
  -- Final cap at 0xFF
  if val2' > 255 then BitVec.ofNat 8 255 else BitVec.ofNat 8 val2'

/-- 
Model of the intended behavior: equal accuracy and evasion boosts should cancel.
A standard fix is to compute a single net stage before applying the multiplier.
-/
def spec (acc : BitVec 8) (accMod evaMod : Nat) : BitVec 8 :=
  let net := 7 + (accMod.toInt - evaMod.toInt)
  let clampedStage := if net < 1 then 1 else if net > 13 then 13 else net.toNat
  let (n, d) := getRatio clampedStage
  let val := (acc.toNat * n) / d
  let val' := if val == 0 then 1 else val
  if val' > 255 then BitVec.ofNat 8 255 else BitVec.ofNat 8 val'

/-- L1: Bug Existence - Equal boosts do not cancel. -/
theorem bug_exists : ∃ (acc : BitVec 8) (stage : Nat),
  stage >= 1 ∧ stage <= 13 ∧ stage ≠ 7 ∧
  impl acc stage stage ≠ spec acc stage stage := by
  -- Witness: Max accuracy (255) with +1/+1 modifiers
  use BitVec.ofNat 8 255, 8
  native_decide

/-- L2: Characterization - Confirming specific accuracy losses mentioned in reports. -/

-- A +1 boost for accuracy and evasion results in 252/255 hit chance.
theorem bug_plus_one_loss : impl (BitVec.ofNat 8 255) 8 8 = BitVec.ofNat 8 252 := by
  native_decide

-- A +5 boost for accuracy and evasion results in 249/255 hit chance (the worst case).
theorem bug_plus_five_loss : impl (BitVec.ofNat 8 255) 12 12 = BitVec.ofNat 8 249 := by
  native_decide

/-- L3: Fix Correctness - The single-pass approach correctly cancels equal modifiers. -/
def fix := spec

theorem fix_cancels_equal_mods (acc : BitVec 8) (stage : Nat) :
  stage >= 1 ∧ stage <= 13 ∧ acc.toNat > 0 → fix acc stage stage = acc := by
  intro h
  have ⟨h_low, h_high, h_acc_pos⟩ := h
  unfold fix spec
  -- net = 7 + (stage - stage) = 7
  have h_net : (stage.toInt - stage.toInt) = 0 := by omega
  simp [h_net, getRatio]
  -- result = (acc * 100) / 100 = acc
  have h_id : (acc.toNat * 100) / 100 = acc.toNat := by
    apply Nat.mul_div_cancel_left
    decide
  simp [h_id, h_acc_pos]
  -- 8-bit cap logic
  have h_bound : acc.toNat < 256 := acc.toNat_lt
  if h_cap : acc.toNat > 255 then
    omega
  else
    simp [h_cap]
    exact BitVec.ofNat_toNat acc

end AutoResearch
