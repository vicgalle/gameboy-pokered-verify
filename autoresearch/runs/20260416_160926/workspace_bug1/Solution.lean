import SM83
import Harness

namespace AutoResearch

open SM83

/-!
# Bug #1: Focus Energy Critical Hit Bug

In Pokémon Red, Blue, and Yellow (Generation 1), the move Focus Energy is 
intended to increase the user's critical hit rate. The critical hit rate 
threshold is initially calculated as `BaseSpeed / 2`. 

If Focus Energy (or a Dire Hit) is active, the game is intended to quadruple 
this threshold. However, due to a bug in the code, the game performs two 
right-shifts (`srl a`) instead of left-shifts or additions. This results in 
the threshold being divided by 4, making critical hits 4 times *less* likely 
than normal (and 16 times less likely than intended).
-/

/-- 
Models the buggy critical hit rate calculation in SM83 assembly.
Logic:
1. a = baseSpeed / 2 (initial threshold)
2. if focused: a = a / 4  (BUG: two 'srl a' instructions instead of multiplication)
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
2. if focused: a = min(255, a * 4)
-/
def spec (s : CPUState) (focused : Bool) : CPUState :=
  let s1 := s.setA (s.a >>> 1)
  if focused then
    -- Intended: Quadruple the base critical hit rate.
    -- We model this with a 255 saturation cap to reflect intended 8-bit gameplay logic.
    let val := s1.a.toNat * 4
    s1.setA (BitVec.ofNat 8 (if val > 255 then 255 else val))
  else
    s1

/-! ### L1: Concrete Witness -/

/-- 
For a Pokémon with a Base Speed of 100 (0x64), Focus Energy 
results in a threshold of 12 instead of the intended 200.
-/
theorem L1_focus_energy_mismatch : 
  let s := defaultState.setA 100
  (impl s true).a = 12 ∧ (spec s true).a = 200 := by
  simp [impl, spec, defaultState]
  native_decide

/-! ### L2: Universal Characterization -/

/-- 
Universal characterization: For any Pokémon with Speed >= 2, using 
Focus Energy results in a lower critical hit rate than the intended 
specification.
-/
theorem L2_focus_energy_underperforms_spec : 
  ∀ (a : BitVec 8), a.toNat >= 2 → 
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
quadruples the rate when Focus Energy is active, incorporating 
proper saturation at 255.
-/
def fix (s : CPUState) (focused : Bool) : CPUState :=
  let s1 := s.setA (s.a >>> 1)
  if focused then
    let res := s1.a.toNat * 4
    s1.setA (BitVec.ofNat 8 (if res > 255 then 255 else res))
  else
    s1

/-! ### L4: Relational Verification -/

/-- Verification: The fixed implementation matches the specification for all inputs. -/
theorem L4_fix_matches_spec : ∀ s b, (fix s b).a = (spec s b).a := by
  intro s b
  cases b <;> rfl

/-- 
Relational Proof: With the fix, Focus Energy correctly improves 
the critical hit rate compared to not using it, provided the 
initial threshold (Speed/2) is at least 1 (Speed >= 2).
-/
theorem L4_fix_is_beneficial : ∀ (a : BitVec 8), 
  a.toNat >= 2 → 
  (fix (defaultState.setA a) true).a > (fix (defaultState.setA a) false).a := by
  intro a h
  simp [fix]
  native_decide

/-- 
The bug reduces the threshold to exactly 1/16th of the intended value 
for speeds that do not cause saturation (e.g., Speed 32).
-/
theorem L4_bug_magnitude_exact : 
  let s := defaultState.setA 32
  (spec s true).a.toNat = 16 * (impl s true).a.toNat := by
  simp [impl, spec, defaultState]
  native_decide

end AutoResearch

