import SM83

namespace AutoResearch

/-- 
  Saturating Arithmetic Shift Left (sla) as implemented in the SM83 logic.
  If the shift results in a carry (bit 7 was set), the value is capped at 0xFF.
--/
def slaSat (b : BitVec 8) : BitVec 8 :=
  if b.getMsb 0 then 0xFF else b <<< 1

/-- 
  Model of the CriticalHitTest logic from Pokemon Red.
  Returns the value 'b' which is the threshold compared against a random byte.
  Higher 'b' means a higher chance of a critical hit.
--/
def criticalHitRate (baseSpeed : BitVec 8) (focusEnergy : Bool) (highCritMove : Bool) : BitVec 8 :=
  -- Initial: ld a, [wMonHBaseSpeed]; ld b, a; srl b
  let b0 := baseSpeed >>> 1
  
  -- .calcCriticalHitProbability branch
  let b1 := if focusEnergy then
    -- .focusEnergyUsed: srl b (This is the bug)
    b0 >>> 1
  else
    -- .noFocusEnergyUsed: sla b (Normal behavior)
    slaSat b0
  
  -- Final move type adjustment
  if highCritMove then
    -- .HighCritical: sla b; sla b (Double twice)
    slaSat (slaSat b1)
  else
    -- .SkipHighCritical: srl b (Halve for regular moves)
    b1 >>> 1

/-- 
  The "Spec" or intended behavior.
  If Focus Energy is used, the rate should be increased (doubled) 
  relative to not using it, rather than being halved.
--/
def criticalHitRateSpec (baseSpeed : BitVec 8) (focusEnergy : Bool) (highCritMove : Bool) : BitVec 8 :=
  let b0 := baseSpeed >>> 1
  let b1 := if focusEnergy then
    -- The intended fix: Focus Energy should increase the probability.
    -- In Gen 1, this was likely intended to be a 4x multiplier.
    slaSat (slaSat (slaSat b0))
  else
    slaSat b0
  
  if highCritMove then
    slaSat (slaSat b1)
  else
    b1 >>> 1

/-! ### L1: Bug Existence -/

/-- 
  A concrete witness: For a Pikachu (Base Speed 90), using Focus Energy 
  significantly reduces the critical hit threshold.
--/
theorem bug_exists : ∃ (speed : BitVec 8) (high : Bool), 
  criticalHitRate speed true high < criticalHitRate speed false high := by
  -- Speed 90 (0x5A), Normal Move
  use 90, false
  native_decide

/-! ### L2: Bug Characterization -/

/-- 
  Theorem: For any Pokemon with base speed >= 4, using Focus Energy 
  ALWAYS results in a lower critical hit rate than not using it.
--/
theorem focus_energy_always_detrimental (speed : BitVec 8) (high : Bool) :
    speed >= 4 → criticalHitRate speed true high < criticalHitRate speed false high := by
  have h := (by native_decide : ∀ (s : BitVec 8) (hi : Bool), 
              s >= 4 → criticalHitRate s true hi < criticalHitRate s false hi)
  exact h speed high

/--
  Theorem: The bug exactly quarters the critical hit threshold 
  (ignoring saturation and LSB truncation) when Focus Energy is used.
--/
theorem focus_energy_quarters_rate (speed : BitVec 8) :
    let normal := criticalHitRate speed false false
    let focus := criticalHitRate speed true false
    speed >= 8 ∧ speed < 128 → focus = normal >>> 2 := by
  intro h
  have : ∀ (s : BitVec 8), s >= 8 ∧ s < 128 → 
    criticalHitRate s true false = (criticalHitRate s false false) >>> 2 := by
    native_decide
  apply this speed h

/-! ### L3: Fix Correctness -/

/--
  Defining a "Fixed" version of the assembly logic where 'srl b' 
  is replaced by a doubling operation.
--/
def fixedImpl (baseSpeed : BitVec 8) (focusEnergy : Bool) (highCritMove : Bool) : BitVec 8 :=
  let b0 := baseSpeed >>> 1
  let b1 := if focusEnergy then
    -- Replace 'srl b' with 'sla b' (twice) to actually increase the rate
    slaSat (slaSat b0)
  else
    slaSat b0
  
  if highCritMove then
    slaSat (slaSat b1)
  else
    b1 >>> 1

/--
  Theorem: In the fixed implementation, Focus Energy actually 
  increases (or maintains at cap) the critical hit rate.
--/
theorem fix_is_beneficial (speed : BitVec 8) (high : Bool) :
    speed > 0 → fixedImpl speed true high >= fixedImpl speed false high := by
  have h := (by native_decide : ∀ (s : BitVec 8) (hi : Bool), 
              s > 0 → fixedImpl s true hi >= fixedImpl s false hi)
  exact h speed high

end AutoResearch
