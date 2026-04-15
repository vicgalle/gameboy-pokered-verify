import SM83

namespace AutoResearch

/-!
# Bug: Focus Energy Quarters Critical Hit Rate instead of Doubling it.

In Pokemon Red/Blue, the CriticalHitTest function contains a logical error where
the 'Focus Energy' status (GETTING_PUMPED) triggers a bit shift to the right (srl) 
instead of a bit shift to the left (sla). This reduces the probability threshold 
by a factor of 4 compared to the intended behavior.
-/

/-- Simulates the SM83 'sla' (Shift Left Arithmetic) instruction with a $FF cap as seen in assembly. -/
def sla (b : BitVec 8) : BitVec 8 :=
  if b.getMsb 0 then 0xFF else b <<< 1

/-- Simulates the SM83 'srl' (Shift Right Logical) instruction. -/
def srl (b : BitVec 8) : BitVec 8 :=
  b >>> 1

/-- 
Faithful model of the buggy assembly in `engine/battle/core.asm`.
- Starts with `baseSpeed / 2`.
- If Focus Energy is active, it performs `srl` (divide by 2).
- If not active, it performs `sla` (multiply by 2).
- Finally, it adjusts for high-critical moves (sla*2) or normal moves (srl).
-/
def impl (baseSpeed : BitVec 8) (isFocusEnergy : Bool) (isHighCrit : Bool) : BitVec 8 :=
  let b0 := srl baseSpeed
  let b1 := if isFocusEnergy then srl b0 else sla b0
  if isHighCrit then
    sla (sla b1)
  else
    srl b1

/-- 
Model of the intended behavior.
Focus Energy should increase (double) the threshold relative to the standard rate.
-/
def spec (baseSpeed : BitVec 8) (isFocusEnergy : Bool) (isHighCrit : Bool) : BitVec 8 :=
  let b0 := srl baseSpeed
  -- The intended fix: Focus Energy should perform an additional 'sla' to increase crit rate.
  let b1 := if isFocusEnergy then sla (sla b0) else sla b0
  if isHighCrit then
    sla (sla b1)
  else
    srl b1

/-- L1: A witness showing the bug exists for a standard base speed (e.g., 100). -/
theorem bug_exists : ∃ speed hc, impl speed true hc < impl speed false hc :=
  ⟨100, false, by native_decide⟩

/-- 
L2: Characterization - Focus Energy always results in a lower or equal threshold 
compared to not using it, which is the opposite of the move's purpose.
-/
theorem focus_energy_always_worse (speed : BitVec 8) (hc : Bool) :
    speed >= 4 → impl speed true hc < impl speed false hc := by
  have h := (by native_decide : ∀ (s : BitVec 8) (hc : Bool), s >= 4 → impl s true hc < impl s false hc)
  exact h speed hc

/-- L2: The bug specifically results in a threshold 4x smaller than the non-focus case (ignoring caps). -/
theorem bug_is_quarter_rate (speed : BitVec 8) :
    speed >= 8 → speed < 64 → impl speed true false = (impl speed false false) >>> 2 := by
  have h := (by native_decide : ∀ (s : BitVec 8), s >= 8 → s < 64 → impl s true false = (impl s false false) >>> 2)
  exact h speed

/-- 
L3: A proposed fix that swaps the buggy `srl` for `sla`. 
Matching the 'spec' ensures Focus Energy increases critical hit probability.
-/
def fix (baseSpeed : BitVec 8) (isFocusEnergy : Bool) (isHighCrit : Bool) : BitVec 8 :=
  let b0 := srl baseSpeed
  -- Fix: use sla instead of srl when focus energy is active
  let b1 := if isFocusEnergy then sla (sla b0) else sla b0
  if isHighCrit then
    sla (sla b1)
  else
    srl b1

theorem fix_correct (s : BitVec 8) (fe : Bool) (hc : Bool) :
    fix s fe hc = spec s fe hc := rfl

end AutoResearch
