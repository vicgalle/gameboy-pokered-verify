import SM83

namespace AutoResearch

/-!
# Bug: Focus Energy Quarters Critical Hit Rate instead of Doubling it.

In Pokémon Red/Blue, the `CriticalHitTest` function determines the probability 
threshold `b` for a critical hit. A random value is compared against `b`.
The bug occurs because the code for the 'Focus Energy' status (GETTING_PUMPED)
uses a bit shift right (`srl`) instead of a bit shift left (`sla`).

This formalization models the threshold calculation and proves the bug's effect.
-/

/-- 
Simulates the SM83 `sla` (Shift Left Arithmetic) instruction followed by the 
capping logic seen in the assembly: 
`sla b; jr nc, .ok; ld b, $ff`.
-/
def sla_capped (b : BitVec 8) : BitVec 8 :=
  if b.getMsb 0 then 0xFF else b <<< 1

/-- Simulates the SM83 `srl` (Shift Right Logical) instruction. -/
def srl (b : BitVec 8) : BitVec 8 :=
  b >>> 1

/-- 
The buggy implementation as found in Pokémon Red's `engine/battle/core.asm`.
The threshold `b` starts at `baseSpeed / 2`. 
If Focus Energy is active, it performs another `srl` (division).
If not, it performs `sla` (multiplication).
Then it adjusts for move type (High Critical vs Normal).
-/
def impl (baseSpeed : BitVec 8) (isFocusEnergy : Bool) (isHighCrit : Bool) : BitVec 8 :=
  let b0 := srl baseSpeed
  let b1 := if isFocusEnergy then 
              srl b0 -- BUG: srl used here reduces the rate
            else 
              sla_capped b0
  if isHighCrit then
    sla_capped (sla_capped b1)
  else
    srl b1

/-- 
The intended behavior: Focus Energy should increase the threshold.
Following the logic that Focus Energy should double the standard critical rate.
-/
def spec (baseSpeed : BitVec 8) (isFocusEnergy : Bool) (isHighCrit : Bool) : BitVec 8 :=
  let b0 := srl baseSpeed
  let b1 := if isFocusEnergy then 
              -- Intended: Focus Energy provides an additional multiplier
              sla_capped (sla_capped b0)
            else 
              sla_capped b0
  if isHighCrit then
    sla_capped (sla_capped b1)
  else
    srl b1

/-! ### L1: Bug Existence -/

/-- Focus Energy results in a lower threshold than not using it for a typical speed. -/
theorem bug_exists : ∃ (speed : BitVec 8) (hc : Bool), impl speed true hc < impl speed false hc :=
  ⟨100, false, by native_decide⟩

/-! ### L2: Characterization -/

/-- 
The bug is universal: for all Pokémon with base speed >= 4, 
using Focus Energy strictly reduces your critical hit chance. 
-/
theorem bug_always_reduces (speed : BitVec 8) (hc : Bool) :
    speed >= 4 → impl speed true hc < impl speed false hc := by
  have h := (by native_decide : ∀ (s : BitVec 8) (hc : Bool), s >= 4 → impl s true hc < impl s false hc)
  exact h speed hc

/-- 
For normal moves (not high-crit) and moderate speeds, the threshold with 
Focus Energy is exactly 1/4 of the threshold without it.
-/
theorem bug_is_exactly_quarter_rate (speed : BitVec 8) :
    speed >= 8 ∧ speed < 128 → 
    impl speed false false = (impl speed true false) <<< 2 := by
  have h := (by native_decide : ∀ (s : BitVec 8), s >= 8 ∧ s < 128 → 
    impl s false false = (impl s true false) <<< 2)
  exact h speed

/-! ### L3: Fix Correctness -/

/-- 
A proposed fix that replaces the buggy `srl` branch with the intended 
scaling logic.
-/
def fix (baseSpeed : BitVec 8) (isFocusEnergy : Bool) (isHighCrit : Bool) : BitVec 8 :=
  let b0 := srl baseSpeed
  let b1 := if isFocusEnergy then 
              sla_capped (sla_capped b0)
            else 
              sla_capped b0
  if isHighCrit then
    sla_capped (sla_capped b1)
  else
    srl b1

theorem fix_matches_spec (s : BitVec 8) (fe : Bool) (hc : Bool) :
    fix s fe hc = spec s fe hc := rfl

/-! ### L4: Relational Properties -/

/-- 
In the fixed version (spec), Focus Energy always provides a threshold 
greater than or equal to the standard threshold.
-/
theorem spec_is_consistently_better (speed : BitVec 8) (hc : Bool) :
    spec speed true hc >= spec speed false hc := by
  have h := (by native_decide : ∀ (s : BitVec 8) (hc : Bool), spec s true hc >= spec s false hc)
  exact h speed hc

/--
In the fixed version, for normal moves and non-capped speeds, 
Focus Energy exactly doubles the critical hit threshold.
-/
theorem spec_doubles_rate (speed : BitVec 8) :
    speed >= 2 ∧ speed < 128 → 
    spec speed true false = (spec speed false false) <<< 1 := by
  have h := (by native_decide : ∀ (s : BitVec 8), s >= 2 ∧ s < 128 → 
    spec s true false = (spec s false false) <<< 1)
  exact h speed

end AutoResearch
