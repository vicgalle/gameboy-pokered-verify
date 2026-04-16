import SM83
import Harness

namespace AutoResearch

open SM83

/-!
# Bug #1: Focus Energy Critical Hit Bug

In Pokémon Red, Blue, and Yellow (Generation 1), the move Focus Energy is 
supposed to increase the user's critical hit rate. The critical hit rate 
threshold is initially calculated as `BaseSpeed / 2`. 

If Focus Energy (or a Dire Hit) is active, the game is intended to quadruple 
this threshold. However, due to a bug in the code, the game performs two 
right-shifts (`srl a`) instead of left-shifts or additions. This results in 
the threshold being divided by 4, making critical hits 4 times *less* likely 
(and 16 times less likely than intended).
-/

/-- 
Models the buggy critical hit rate calculation in SM83 assembly.
Logic:
1. a = baseSpeed / 2
2. if focused: a = a / 4  (BUG: should be a * 4)
-/
def impl (s : CPUState) (focused : Bool) : CPUState :=
  -- Base crit rate: speed / 2
  let s1 := s.setA (s.a >>> 1)
  if focused then
    -- The Bug: Two additional right shifts (srl a)
    -- This divides the already halved value by 4.
    s1.setA (s1.a >>> 2)
  else
    s1

/-- 
Models the intended critical hit rate calculation.
Logic:
1. a = baseSpeed / 2
2. if focused: a = a * 4
-/
def spec (s : CPUState) (focused : Bool) : CPUState :=
  let s1 := s.setA (s.a >>> 1)
  if focused then
    -- Intended: Quadruple the base critical hit rate.
    s1.setA (s1.a <<< 2)
  else
    s1

/-! ### L1: Concrete Witness -/

/-- 
For a Pokémon with a Base Speed of 64 (0x40), Focus Energy 
results in a threshold of 8 instead of the intended 128.
-/
theorem L1_focus_energy_mismatch : 
  let s := defaultState.setA 64
  (impl s true).a = 8 ∧ (spec s true).a = 128 := by
  simp [impl, spec, defaultState]
  native_decide

/-! ### L2: Universal Characterization -/

/-- 
Universal characterization: For any Pokémon with Speed >= 8, using 
Focus Energy results in a lower critical hit rate than the intended 
specification.
-/
theorem L2_focus_energy_underperforms_spec : 
  ∀ (a : BitVec 8), a.toNat >= 8 → 
  (impl (defaultState.setA a) true).a < (spec (defaultState.setA a) true).a := by
  intro a h
  simp [impl, spec]
  native_decide

/-- 
The core of the bug: Focus Energy makes the critical hit rate strictly 
worse than not using the move at all (for any speed >= 2).
-/
theorem L2_focus_energy_detrimental : 
  ∀ (a : BitVec 8), a.toNat >= 2 → 
  (impl (defaultState.setA a) true).a < (impl (defaultState.setA a) false).a := by
  intro a h
  simp [impl]
  native_decide

/-! ### L3: Fixed Implementation -/

/-- 
A fixed version of the critical hit calculation that correctly
quadruples the rate when Focus Energy is active.
-/
def fix (s : CPUState) (focused : Bool) : CPUState :=
  let s1 := s.setA (s.a >>> 1)
  if focused then
    -- Replace the two right shifts with two left shifts (or a * 4)
    s1.setA (s1.a <<< 2)
  else
    s1

/-! ### L4: Verification and Relational Properties -/

/-- Verification: The fixed implementation matches the specification for all inputs. -/
theorem L4_fix_matches_spec : ∀ s b, (fix s b).a = (spec s b).a := by
  intro s b
  cases b <;> rfl

/-- 
Relational Proof: With the fix, Focus Energy correctly improves 
(or maintains) the critical hit rate compared to not using it, 
provided the speed is within a range that doesn't overflow 8-bit logic.
-/
theorem L4_fix_is_beneficial : ∀ (a : BitVec 8), 
  (a.toNat >= 2 ∧ a.toNat < 128) → 
  (fix (defaultState.setA a) true).a > (fix (defaultState.setA a) false).a := by
  intro a h
  simp [fix]
  native_decide

end AutoResearch

