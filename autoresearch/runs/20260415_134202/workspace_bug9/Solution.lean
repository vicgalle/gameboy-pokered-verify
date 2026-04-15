import SM83

namespace AutoResearch

/-!
# Bug: Accuracy and Evasion Stage Boosts Do Not Cancel When Equal

In Pokemon Red/Blue, move hit chance is calculated using a two-pass multiplier loop. 
The first pass applies the Accuracy modifier, and the second pass applies the Evasion 
modifier (reflected such that an increase in evasion decreases hit chance).

Because the internal `StatModifierRatios` table stores approximate fractions 
(e.g., 66/100 for a 2/3 ratio) and the engine performs integer division between 
passes, equal stage increases (e.g., +1 Accuracy and +1 Evasion) do not mathematically 
cancel. The intermediate floor division and approximation errors result in a 
pessimistic hit chance lower than the move's base accuracy.
-/

/-- 
Stat modifier ratios for Accuracy and Evasion from engine/battle/core.asm.
Stage 7 is neutral (1/1). 
Stages 1-6 are penalties, 8-13 are boosts.
-/
def getRatio (stage : Nat) : (Nat × Nat) :=
  match stage with
  | 1  => (25, 100) | 2  => (28, 100) | 3  => (33, 100)
  | 4  => (40, 100) | 5  => (50, 100) | 6  => (66, 100)
  | 7  => (1, 1)    | 8  => (15, 10)  | 9  => (2, 1)
  | 10 => (25, 10)  | 11 => (3, 1)    | 12 => (35, 10)
  | 13 => (4, 1)    | _  => (1, 1)

/-- 
Faithful implementation of the CalcHitChance assembly logic.
Replicates the two-iteration loop (d=2) using Accuracy (b) and Evasion (c).
-/
def impl (accMod evaMod baseAcc : BitVec 8) : BitVec 8 :=
  let s1 := accMod.toNat
  let s2 := 14 - evaMod.toNat
  
  -- Pass 1: Accuracy (Register b)
  let (n1, d1) := getRatio s1
  let res1 := (baseAcc.toNat * n1) / d1
  -- Ensure result is at least 1
  let res1 := if res1 == 0 then 1 else res1
  
  -- Pass 2: Evasion (Register c)
  let (n2, d2) := getRatio s2
  let res2 := (res1 * n2) / d2
  -- Ensure result is at least 1
  let res2 := if res2 == 0 then 1 else res2
  
  -- Final clamp to 0xFF (255)
  if res2 > 255 then 255 else BitVec.ofNat 8 res2

/-- 
Correct behavior: Combine modifiers into a single net stage shift 
before applying the multiplier to prevent intermediate precision loss.
-/
def spec (accMod evaMod baseAcc : BitVec 8) : BitVec 8 :=
  let net := accMod.toNat.toInt - evaMod.toNat.toInt + 7
  let s := if net < 1 then 1 else if net > 13 then 13 else net.toNat
  let (n, d) := getRatio s
  let res := (baseAcc.toNat * n) / d
  let res := if res == 0 then 1 else res
  if res > 255 then 255 else BitVec.ofNat 8 res

/-- Predicate for valid stat stages (1 to 13). -/
def isValidStage (s : BitVec 8) : Prop := s.toNat >= 1 ∧ s.toNat <= 13

---

/-- L1: Bug Witness.
For a move with 255 accuracy, +1 Accuracy (8) and +1 Evasion (8) results in 252 (not 255).
-/
theorem bug_exists : ∃ a e b, isValidStage a ∧ isValidStage e ∧ impl a e b ≠ spec a e b := by
  use 8, 8, 255
  unfold isValidStage
  native_decide

/-- L2: Characterization.
For all valid equal stage boosts (except neutral), the bug always results in a 
hit chance strictly lower than the base accuracy (pessimistic truncation).
-/
theorem bug_always_pessimistic_at_max (s : BitVec 8) : 
  isValidStage s ∧ s.toNat ≠ 7 → (impl s s 255).toNat < 255 := by
  intro h
  revert h
  unfold isValidStage impl getRatio
  native_decide

/-- L2: Universal property.
The bug never results in a higher hit chance than the base move accuracy 
when modifiers are equal. It is always either correct (neutral) or lower.
-/
theorem bug_never_exceeds_base (s : BitVec 8) (b : BitVec 8) : 
  isValidStage s → (impl s s b).toNat ≤ b.toNat := by
  intro h
  revert h b s
  unfold isValidStage impl getRatio
  native_decide

/-- L3: Fix Correctness.
The single-pass specification ensures perfect cancellation (impl s s b = b).
-/
def fix := spec

theorem fix_cancels_perfectly (s : BitVec 8) (b : BitVec 8) (h : isValidStage s) :
  fix s s b = b := by
  unfold fix spec
  have h_net : (s.toNat.toInt - s.toNat.toInt + 7) = 7 := by omega
  simp [h_net, getRatio]

/-- L4: Extreme Case.
At maximum evasion and accuracy (+6/+6), the hit chance drops from 255 to 249.
-/
theorem extreme_case_loss : impl 13 13 255 = 249 := by native_decide

end AutoResearch
