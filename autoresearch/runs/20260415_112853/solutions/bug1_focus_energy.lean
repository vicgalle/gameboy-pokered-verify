import SM83

/-!
# Bug: Focus Energy Quarters Critical Hit Rate instead of Doubling it

In Pokémon Red/Blue (Gen 1), the move Focus Energy is intended to increase the 
user's critical hit rate. However, a bug in the assembly logic for 
`CriticalHitTest` causes the rate to be divided by 4 instead.

The critical hit threshold (stored in register `b`) is compared against a 
random value. A higher threshold means a higher critical hit probability. 
The bug occurs because the branch handling Focus Energy uses `srl b` (logical 
shift right, dividing by 2) instead of an instruction that increases the value.
-/

namespace AutoResearch

/-- 
Models the saturating left shift behavior found in the SM83 assembly.
In `CriticalHitTest`, instructions like `sla b` followed by a carry check 
cap the value at 255 if an overflow occurs.
-/
def sla_sat (b : BitVec 8) : BitVec 8 :=
  -- If bit 7 is set, shifting left would overflow the 8-bit register.
  if b >>> 7 == 1 then 255 else b <<< 1

/-- 
Models the actual buggy implementation of the critical hit threshold 
calculation from engine/battle/core.asm.
-/
def impl (base_speed : BitVec 8) (is_focus_energy : Bool) (is_high_crit : Bool) : BitVec 8 :=
  -- ld a, [wMonHBaseSpeed]; ld b, a; srl b
  let b0 := base_speed >>> 1
  
  -- bit GETTING_PUMPED, a; jr nz, .focusEnergyUsed
  let b1 := if is_focus_energy then
              -- .focusEnergyUsed: srl b (This is the bug!)
              b0 >>> 1
            else
              -- Normal case: sla b; caps at 255
              sla_sat b0
  
  -- Check for High Critical Moves table
  if is_high_crit then
    -- .HighCritical: sla b; sla b; (both capped at 255)
    sla_sat (sla_sat b1)
  else
    -- Normal Move: srl b
    b1 >>> 1

/-- 
Models the intended (fixed) behavior. 
Using Focus Energy should increase the probability of a critical hit.
Here we model a fix where Focus Energy doubles the threshold relative to the normal case.
-/
def fixed_impl (base_speed : BitVec 8) (is_focus_energy : Bool) (is_high_crit : Bool) : BitVec 8 :=
  let b0 := base_speed >>> 1
  let b1 := if is_focus_energy then
              -- FIX: Focus Energy should multiply the threshold (e.g., doubling)
              sla_sat (sla_sat b0)
            else
              sla_sat b0
  if is_high_crit then
    sla_sat (sla_sat b1)
  else
    b1 >>> 1

/-- 
L1: Bug Existence.
We show that for a standard Pokémon (like Jolteon with 130 base speed), 
using Focus Energy strictly decreases the critical hit threshold.
-/
theorem bug_exists : ∃ (s : BitVec 8) (h : Bool), impl s true h < impl s false h := by
  -- Jolteon (Speed 130) using a regular move
  exists 130, false
  native_decide

/-- 
L2: Universal Characterization.
For every Pokémon with a base speed of at least 2, Focus Energy makes it 
strictly less likely to land a critical hit.
-/
theorem bug_is_always_harmful (s : BitVec 8) (h : Bool) : 
  s >= 2 → impl s true h < impl s false h := by
  intro _
  have h_univ := (by native_decide : ∀ (s : BitVec 8) (h : Bool), s >= 2 → impl s true h < impl s false h)
  exact h_univ s h

/-- 
L3: Fix Correctness.
In the fixed implementation, Focus Energy always results in a threshold 
greater than or equal to the case where it is not used.
-/
theorem fix_is_beneficial (s : BitVec 8) (h : Bool) : 
  fixed_impl s true h >= fixed_impl s false h := by
  have h_univ := (by native_decide : ∀ (s : BitVec 8) (h : Bool), fixed_impl s true h >= fixed_impl s false h)
  exact h_univ s h

/-- 
L4: The "Quartering" Property.
We verify the observation that for regular moves and typical speeds, 
Focus Energy results in exactly 1/4 the threshold of a normal attack.
(s/2 * 2) / 2 = s/2  vs  (s/2 / 2) / 2 = s/8.
-/
theorem focus_energy_quarters_rate (s : BitVec 8) : 
  s >= 8 ∧ s < 128 → (impl s false false).toNat / 4 = (impl s true false).toNat := by
  intro _
  have h_univ := (by native_decide : ∀ (s : BitVec 8), s >= 8 ∧ s < 128 → (impl s false false).toNat / 4 = (impl s true false).toNat)
  exact h_univ s

end AutoResearch
