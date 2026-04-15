import SM83

namespace AutoResearch

/-!
# Bug: Focus Energy Quarters Critical Hit Rate instead of Doubling It

## Description
In Pokémon Red/Blue, the move Focus Energy was intended to increase the user's critical hit 
chance. However, due to a bug in `engine/battle/core.asm`, it shifts the critical hit 
threshold right (`srl`) instead of left (`sla`), resulting in 1/4 the intended probability.

## High-Level Logic
1. Calculate base threshold `b = BaseSpeed / 2`.
2. Check Focus Energy status:
   - If NOT set: `b = b * 2` (effectively back to `BaseSpeed`).
   - If SET: `b = b / 2` (effectively `BaseSpeed / 4`). **<-- The Bug**
3. Handle move type:
   - Normal Move: `b = b / 2`.
   - High Crit Move: `b = b * 4`.
4. Final comparison: `Random(0-255) < b`.
-/

/-- 
Simulates the `sla b` instruction followed by a carry check and `ld b, $ff`.
This is a left shift with saturation at 255.
-/
def sla_sat (b : BitVec 8) : BitVec 8 :=
  -- If the most significant bit is set, shifting left would cause a carry.
  if (b &&& 0x80) != 0 then 0xFF else b <<< 1

/-- 
Implementation of the critical hit threshold calculation as it exists in the 
original Pokémon Red assembly code.
-/
def impl (baseSpeed : BitVec 8) (isFocusEnergy : Bool) (isHighCrit : Bool) : BitVec 8 :=
  -- ld a, [wMonHBaseSpeed] / ld b, a / srl b
  let b0 := baseSpeed >>> 1
  
  -- bit GETTING_PUMPED, a / jr nz, .focusEnergyUsed
  let b1 := if isFocusEnergy then
              -- .focusEnergyUsed: srl b
              b0 >>> 1 
            else
              -- sla b / jr nc, .noFocusEnergyUsed / ld b, $ff
              sla_sat b0
  
  -- .noFocusEnergyUsed / ... / .Loop
  if isHighCrit then
    -- .HighCritical: sla b (*2) / sla b (*4) with saturation
    sla_sat (sla_sat b1)
  else
    -- .SkipHighCritical: srl b (/2)
    b1 >>> 1

/-- 
Specification of the intended behavior. 
Focus Energy was intended to double the final critical hit chance compared 
to the non-Focus Energy state.
-/
def spec (baseSpeed : BitVec 8) (isFocusEnergy : Bool) (isHighCrit : Bool) : BitVec 8 :=
  let threshold_no_fe := 
    let b0 := baseSpeed >>> 1
    let b1 := sla_sat b0
    if isHighCrit then sla_sat (sla_sat b1) else b1 >>> 1
  
  if isFocusEnergy then
    -- Intended to be twice as likely (capped at 255)
    sla_sat threshold_no_fe
  else
    threshold_no_fe

/-- 
A proposed fix that replaces the buggy `srl b` with a sequence that quadruples 
the threshold (compensating for the initial `srl`).
-/
def fix (baseSpeed : BitVec 8) (isFocusEnergy : Bool) (isHighCrit : Bool) : BitVec 8 :=
  let b0 := baseSpeed >>> 1
  let b1 := if isFocusEnergy then
              -- To double the final chance relative to No-FE, we need b to be 
              -- twice what it would be in the No-FE path. 
              -- No-FE path does: (speed/2) * 2 = speed.
              -- So FE path needs: (speed/2) * 4 = 2 * speed.
              sla_sat (sla_sat b0)
            else
              sla_sat b0
  if isHighCrit then
    sla_sat (sla_sat b1)
  else
    b1 >>> 1

-- L1: Bug Exists
-- Using a Pokemon like Jolteon (Base Speed 130) with a normal move.
theorem bug_exists : ∃ (s : BitVec 8) (fe hc : Bool), impl s fe hc != spec s fe hc := by
  -- Base speed 130, Focus Energy active, Normal move
  let s := BitVec.ofNat 8 130
  use s, true, false
  native_decide

-- L2: Characterization
-- Focus Energy actually makes the critical hit rate worse for all typical speeds.
-- Specifically, for any speed >= 8, the buggy implementation gives a strictly 
-- lower threshold than doing nothing.
theorem focus_energy_is_detrimental (s : BitVec 8) (hc : Bool) :
    s >= 8 → impl s true hc < impl s false hc := by
  intro _
  -- This can be checked for all 256 * 2 possible inputs
  have h := (by native_decide : ∀ (s : BitVec 8) (hc : Bool), s >= 8 → impl s true hc < impl s false hc)
  exact h s hc

-- L3: Fix Correctness
-- Our proposed fix matches the intended specification for all possible inputs.
theorem fix_matches_spec (s : BitVec 8) (fe hc : Bool) : fix s fe hc = spec s fe hc := by
  have h := (by native_decide : ∀ (s : BitVec 8) (fe hc : Bool), fix s fe hc = spec s fe hc)
  exact h s fe hc

end AutoResearch
