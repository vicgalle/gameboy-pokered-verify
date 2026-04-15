import SM83

namespace AutoResearch

/-!
# Bug: Focus Energy Quarters Critical Hit Rate instead of Doubling It

In Pokemon Red/Blue, the `CriticalHitTest` function calculates a threshold `b`. 
A random value is compared against `b`; if the random value is lower, a critical hit occurs.
Focus Energy is intended to increase this threshold (making critical hits more likely).

Due to a bug in the branching logic, using Focus Energy (`focusEnergyUsed`) performs 
a bitwise shift right (`srl`), which halves the threshold, while the non-Focus Energy 
path performs a shift left (`sla`), which doubles it. The result is that Focus Energy 
makes critical hits 4x less likely than if the move hadn't been used.
-/

/-- Performs the `sla b` instruction followed by the carry check cap. -/
def sla_cap (b : BitVec 8) : BitVec 8 :=
  -- If MSB is 1, shifting left sets the carry flag
  if b.getMsb 0 then 0xFF else b <<< 1

/-- 
Models the buggy `CriticalHitTest` threshold calculation from Gen 1 assembly.
Matches the logic in `engine/battle/core.asm`.
-/
def impl (baseSpeed : BitVec 8) (isHighCrit : Bool) (focusEnergy : Bool) : BitVec 8 :=
  -- ld a, [wMonHBaseSpeed] / ld b, a / srl b
  let b := baseSpeed >>> 1
  -- bit GETTING_PUMPED, a / jr nz, .focusEnergyUsed
  let b := if focusEnergy then
    -- .focusEnergyUsed: srl b (The Bug)
    b >>> 1
  else
    -- sla b / jr nc, .noFocusEnergyUsed / ld b, $ff
    sla_cap b
  
  -- .noFocusEnergyUsed / HighCriticalMoves check
  if isHighCrit then
    -- .HighCritical: sla b (cap) / sla b (cap)
    sla_cap (sla_cap b)
  else
    -- srl b (for regular moves)
    b >>> 1

/-- 
Models the intended behavior where Focus Energy quadruples the critical hit 
threshold relative to the starting `srl b` state.
-/
def spec (baseSpeed : BitVec 8) (isHighCrit : Bool) (focusEnergy : Bool) : BitVec 8 :=
  let b := baseSpeed >>> 1
  let b := if focusEnergy then
    -- Intended: Focus Energy should increase the probability
    -- The common fix is to use sla instead of srl
    sla_cap (sla_cap b)
  else
    sla_cap b
  
  if isHighCrit then
    sla_cap (sla_cap b)
  else
    b >>> 1

/-! ### L1: Bug Existence -/

/-- For a Pokemon with 100 Base Speed (e.g. Charizard), Focus Energy reduces the crit threshold. -/
theorem bug_exists : ∃ (speed : BitVec 8) (high : Bool), 
  impl speed high true < impl speed high false := by
  -- Speed 100, Not High Crit
  use 100, false
  native_decide

/-! ### L2: Characterization -/

/-- 
For any non-trivial base speed, using Focus Energy results in a strictly lower 
critical hit threshold than not using it, regardless of the move type.
-/
theorem focus_energy_always_worse (speed : BitVec 8) (high : Bool) :
  speed >= 8 → impl speed high true < impl speed high false := by
  have h := (by native_decide : ∀ (s : BitVec 8) (high : Bool), 
    s >= 8 → impl s high true < impl s high false)
  exact h speed high

/-- In the buggy implementation, Focus Energy + Normal Move results in speed / 8. -/
theorem focus_energy_math_normal (speed : BitVec 8) :
  speed < 128 → impl speed false true = speed >>> 3 := by
  intro h
  have : ∀ (s : BitVec 8), s < 128 → impl s false true = s >>> 3 := by native_decide
  exact this speed h

/-! ### L3: Fix Correctness -/

/-- 
A fixed implementation where `.focusEnergyUsed` performs `sla` instead of `srl`.
Note: To truly double/quadruple properly relative to the baseline, 
we change the single `srl` to `sla`.
-/
def fix (baseSpeed : BitVec 8) (isHighCrit : Bool) (focusEnergy : Bool) : BitVec 8 :=
  let b := baseSpeed >>> 1
  let b := if focusEnergy then
    sla_cap (sla_cap b) -- Fixed: shift left twice to increase rate
  else
    sla_cap b
  
  if isHighCrit then
    sla_cap (sla_cap b)
  else
    b >>> 1

/-- The fix matches the intended specification for all inputs. -/
theorem fix_correct (speed : BitVec 8) (high : Bool) (fe : Bool) :
  fix speed high fe = spec speed high fe := by
  have h := (by native_decide : ∀ (s : BitVec 8) (h : Bool) (f : Bool), 
    fix s h f = spec s h f)
  exact h speed high fe

end AutoResearch
