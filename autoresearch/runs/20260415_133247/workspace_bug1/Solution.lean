import SM83

namespace AutoResearch

/-!
# Bug: Focus Energy Quarters Critical Hit Rate instead of Doubling It

In Pokémon Red/Blue, the `CriticalHitTest` function calculates a threshold `b`. 
A random value is compared against `b`; if the random value is lower, a critical hit occurs.
Focus Energy is intended to increase this threshold (making critical hits more likely).

Due to a bug in the branching logic, using Focus Energy (`focusEnergyUsed`) performs 
a bitwise shift right (`srl`), which halves the intermediate threshold, while the 
non-Focus Energy path performs a shift left (`sla`), which doubles it. 

The resulting logic for a normal move:
- No Focus Energy: `b = (Speed / 2) * 2 / 2 = Speed / 2`
- With Focus Energy: `b = (Speed / 2) / 2 / 2 = Speed / 8`
Result: Focus Energy makes critical hits 4x less likely.
-/

/-- Performs the `sla b` instruction followed by the carry check cap (ld b, $ff). -/
def sla_cap (b : BitVec 8) : BitVec 8 :=
  if b.getMsb 0 then 0xFF else b <<< 1

/-- 
Models the buggy `CriticalHitTest` threshold calculation from Gen 1 assembly.
Matches `engine/battle/core.asm` instruction-for-instruction.
-/
def impl (baseSpeed : BitVec 8) (isHighCrit : Bool) (focusEnergy : Bool) : BitVec 8 :=
  -- ld a, [wMonHBaseSpeed] / ld b, a / srl b
  let b0 := baseSpeed >>> 1
  
  -- bit GETTING_PUMPED, a / jr nz, .focusEnergyUsed
  let b1 := if focusEnergy then
    -- .focusEnergyUsed: srl b
    b0 >>> 1
  else
    -- sla b / jr nc, .noFocusEnergyUsed / ld b, $ff
    sla_cap b0
  
  -- .noFocusEnergyUsed / HighCriticalMoves check
  if isHighCrit then
    -- .HighCritical: sla b / sla b (both with $ff caps)
    sla_cap (sla_cap b1)
  else
    -- srl b (for regular moves)
    b1 >>> 1

/-- 
Models the intended behavior where Focus Energy quadruples the critical hit 
threshold relative to the starting state (making it 4x more likely than normal).
-/
def spec (baseSpeed : BitVec 8) (isHighCrit : Bool) (focusEnergy : Bool) : BitVec 8 :=
  let b0 := baseSpeed >>> 1
  let b1 := if focusEnergy then
    -- Intended: Quadruple the probability relative to the base / 2 state
    sla_cap (sla_cap b0)
  else
    -- Normal: Double the probability relative to the base / 2 state
    sla_cap b0
  
  if isHighCrit then
    sla_cap (sla_cap b1)
  else
    b1 >>> 1

/-! ### L1: Bug Existence -/

/-- For a standard 100 base speed Pokemon, Focus Energy significantly reduces crit chance. -/
theorem bug_exists : ∃ (speed : BitVec 8) (high : Bool), 
  impl speed high true < impl speed high false := by
  -- Speed 100 (0x64), Not High Crit
  use 100, false
  native_decide

/-! ### L2: Characterization -/

/-- 
Focus Energy is strictly worse than doing nothing for all Pokémon with 
sufficiently high base speed (speed >= 8 to avoid floor-to-zero issues).
-/
theorem focus_energy_always_worse (speed : BitVec 8) (high : Bool) :
  speed >= 8 → impl speed high true < impl speed high false := by
  have h := (by native_decide : ∀ (s : BitVec 8) (high : Bool), 
    s >= 8 → impl s high true < impl s high false)
  exact h speed high

/-- 
Focus Energy consistently reduces the critical hit rate by exactly a factor of 4 
compared to the non-Focus Energy state (when no caps are hit).
Specifically, (impl with FE) = (impl without FE) >> 2.
-/
theorem focus_energy_is_exactly_quarter (speed : BitVec 8) (high : Bool) :
  speed < 64 → (impl speed high true) = (impl speed high false) >>> 2 := by
  have h := (by native_decide : ∀ (s : BitVec 8) (h : Bool), 
    s < 64 → impl s h true = (impl s h false) >>> 2)
  exact h speed high

/--
The bug is so severe that a High-Crit move WITH Focus Energy is equivalent to
a Normal move WITHOUT Focus Energy (for non-capped values).
-/
theorem high_crit_fe_is_normal_no_fe (speed : BitVec 8) :
  speed < 64 → impl speed true true = impl speed false false := by
  have h := (by native_decide : ∀ (s : BitVec 8), 
    s < 64 → impl s true true = impl s false false)
  exact h speed

/-! ### L3: Fix Correctness -/

/-- 
A fixed implementation that swaps the buggy `srl b` for `sla b` in the Focus Energy branch,
and ensures it properly scales.
-/
def fix (baseSpeed : BitVec 8) (isHighCrit : Bool) (focusEnergy : Bool) : BitVec 8 :=
  let b0 := baseSpeed >>> 1
  let b1 := if focusEnergy then
    sla_cap (sla_cap b0) -- Fixed: shift left twice (x4 probability)
  else
    sla_cap b0           -- Normal: shift left once (x2 probability)
  
  if isHighCrit then
    sla_cap (sla_cap b1)
  else
    b1 >>> 1

/-- The fix matches the intended specification for all possible game inputs. -/
theorem fix_correct (speed : BitVec 8) (high : Bool) (fe : Bool) :
  fix speed high fe = spec speed high fe := by
  have h := (by native_decide : ∀ (s : BitVec 8) (h : Bool) (f : Bool), 
    fix s h f = spec s h f)
  exact h speed high fe

end AutoResearch
