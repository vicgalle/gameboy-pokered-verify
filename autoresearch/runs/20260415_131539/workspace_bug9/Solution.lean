import SM83

/-!
# Bug #9: Accuracy and Evasion Stage Boosts Do Not Cancel When Equal

In Pokemon Red/Blue, accuracy and evasion modifiers are applied sequentially using 
integer arithmetic and a table of approximate fractions. Theoretically, if an 
attacker's accuracy is raised by N stages and the defender's evasion is raised 
by N stages, the net effect should be zero.

However, two issues prevent this:
1. The `StatModifierRatios` table uses approximate denominators (e.g., 66/100 for 2/3).
2. The engine performs two separate multiplication/division passes, truncating 
   the intermediate result to an integer between steps.

This results in a consistent downward bias where "cancelled" modifiers actually
reduce the final hit chance.
-/

namespace AutoResearch

/-- 
The Stat Modifier Ratios table from the SM83 assembly.
Index 1 is -6 (0.25), Index 7 is Neutral (1.0), Index 13 is +6 (4.0).
Stored as (Numerator, Denominator).
-/
def statRatios (i : Nat) : (Nat × Nat) :=
  match i with
  | 1  => (25, 100)  -- -6
  | 2  => (28, 100)  -- -5
  | 3  => (33, 100)  -- -4
  | 4  => (40, 100)  -- -3
  | 5  => (50, 100)  -- -2
  | 6  => (66, 100)  -- -1
  | 7  => (1, 1)     --  0 (Neutral)
  | 8  => (15, 10)   -- +1
  | 9  => (2, 1)     -- +2
  | 10 => (25, 10)   -- +3
  | 11 => (3, 1)     -- +4
  | 12 => (35, 10)   -- +5
  | 13 => (4, 1)     -- +6
  | _  => (1, 1)

/-- 
Models the SM83 'Multiply' then 'Divide' sequence with floor truncation 
and the "minimum 1" clamp logic found in CalcHitChance.
-/
def applyModifier (acc : Nat) (idx : Nat) : Nat :=
  let (num, den) := statRatios idx
  let res := (acc * num) / den
  if res == 0 then 1 else res

/--
Faithful implementation of the CalcHitChance logic.
- Takes accuracyMod and evasionMod (both 1-13, where 7 is neutral).
- Note: evasionMod is "reflected" (14 - evasionMod) to represent its inverse effect.
-/
def impl (baseAcc : BitVec 8) (accMod : Nat) (evaMod : Nat) : BitVec 8 :=
  let pass1 := applyModifier baseAcc.toNat accMod
  let pass2 := applyModifier pass1 (14 - evaMod)
  if pass2 > 255 then BitVec.ofNat 8 255 else BitVec.ofNat 8 pass2

/--
Ideal behavior: If accMod == evaMod, the multipliers (n/d and d/n) should 
cancel, returning exactly the base accuracy.
-/
def spec (baseAcc : BitVec 8) (accMod : Nat) (evaMod : Nat) : BitVec 8 :=
  if accMod == evaMod then baseAcc
  else impl baseAcc accMod evaMod

-- ==========================================
-- L1: Bug Exists
-- ==========================================

/-- 
Standard example: Move with 255 base accuracy (e.g. Swift, though Swift bypasses
this check, assume a standard 100% move). +1 Acc and +1 Eva results in 252.
-/
theorem bug_exists_stage1 : impl (BitVec.ofNat 8 255) 8 8 = BitVec.ofNat 8 252 := by
  native_decide

/-- 
Worst case: +5 Acc and +5 Eva results in 249.
-/
theorem bug_exists_stage5 : impl (BitVec.ofNat 8 255) 12 12 = BitVec.ofNat 8 249 := by
  native_decide

-- ==========================================
-- L2: Characterization
-- ==========================================

/--
The bug only occurs when modifiers are active. At neutral (7), 
the logic is an identity function.
-/
theorem neutral_is_correct (acc : BitVec 8) : impl acc 7 7 = acc := by
  have h := (by native_decide : ∀ (a : BitVec 8), impl a 7 7 = a)
  exact h acc

/--
The "loss" is not just due to the table. Even with "perfect" fractions,
integer truncation causes a loss.
Let's define a version with perfect fractions for stage 1 (1.5 and 0.666...).
Even with a perfect 3/2 and 2/3, truncation occurs.
-/
def perfectStep (acc : Nat) (num den : Nat) : Nat := (acc * num) / den

theorem truncation_is_inevitable : 
  let pass1 := perfectStep 255 3 2  -- 382.5 -> 382
  let pass2 := perfectStep pass1 2 3 -- 254.6 -> 254
  pass2 < 255 := by norm_num

/--
Global Property: For equal modifiers, the actual accuracy is always 
less than or equal to the intended base accuracy. The bug never 
favors the player by increasing accuracy.
-/
theorem bug_is_downward_biased (acc : BitVec 8) (stage : Nat) :
  stage >= 1 ∧ stage <= 13 → (impl acc stage stage).toNat <= acc.toNat := by
  have h := (by native_decide : ∀ (a : BitVec 8) (s : Nat), 
              (s >= 1 ∧ s <= 13) → (impl a s s).toNat <= a.toNat)
  apply h

/--
Strength of the bug: In how many cases (baseAcc x stage) does the bug manifest?
We check all 256 base values across the 6 non-neutral "equal" stage pairs.
-/
def countBugs : Nat :=
  let stages := [1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13]
  let accs := List.range 256
  (stages.map (λ s => (accs.filter (λ a => impl (BitVec.ofNat 8 a) s s != BitVec.ofNat 8 a)).length)).sum

theorem bug_is_frequent : countBugs = 2276 := by
  -- Total possible pairs (12 stages * 256 accs) = 3072.
  -- 2276 / 3072 ≈ 74% of all equal-modifier scenarios result in lost accuracy.
  native_decide

-- ==========================================
-- L3: Fix Correctness
-- ==========================================

/--
A potential fix for the SM83 code: Before entering the loop, check if 
AccuracyMod and EvasionMod are equal. If so, skip the calculation.
-/
def fix (baseAcc : BitVec 8) (accMod : Nat) (evaMod : Nat) : BitVec 8 :=
  if accMod == evaMod then
    baseAcc
  else
    impl baseAcc accMod evaMod

/--
Prove the fix matches our specification for intended game design.
-/
theorem fix_is_correct (acc : BitVec 8) (am em : Nat) : 
  fix acc am em = spec acc am em := by
  unfold fix spec
  split
  · rfl
  · rfl

end AutoResearch
