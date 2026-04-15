import SM83

namespace AutoResearch

/-- 
Models the SM83 `sla` instruction followed by the probability-capping logic 
found in `CriticalHitTest`. If the shift left results in a carry (bit 7 was set), 
the routine saturates the value to 0xFF.
-/
def sla8 (b : BitVec 8) : BitVec 8 :=
  if b.getMsb 0 then 0xFF else b <<< 1

/--
Faithful model of the buggy Gen 1 `CriticalHitTest` logic.
This reflects the assembly sequence:
1. `b = baseSpeed / 2`
2. If `Focus Energy` active: `b = b / 2` (The Bug: `srl b` instead of `sla b`)
   Else: `b = sla8 b` (effective `b = baseSpeed`)
3. If `High Critical` move: `b = sla8 (sla8 b)`
   Else: `b = b / 2`
-/
def impl (baseSpeed : BitVec 8) (isFocusEnergy : Bool) (isHighCrit : Bool) : BitVec 8 :=
  -- ld a, [wMonHBaseSpeed] / ld b, a / srl b
  let b1 := baseSpeed >>> 1
  
  -- bit GETTING_PUMPED, a
  let b2 := if isFocusEnergy then
              -- .focusEnergyUsed: srl b
              b1 >>> 1
            else
              -- sla b / jr nc, .noFocusEnergyUsed / ld b, $ff
              sla8 b1
              
  -- HighCriticalMoves check
  if isHighCrit then
    -- .HighCritical: sla b / ... / sla b / ...
    sla8 (sla8 b2)
  else
    -- srl b
    b2 >>> 1

/--
Model of the intended Gen 1 CriticalHitTest logic.
Focus Energy is intended to double the critical hit threshold compared to 
the non-Focus Energy case.
-/
def spec (baseSpeed : BitVec 8) (isFocusEnergy : Bool) (isHighCrit : Bool) : BitVec 8 :=
  let b1 := baseSpeed >>> 1
  -- Intended: Focus Energy should provide a 4x multiplier to b1 
  -- (doubling the 2x multiplier used in the non-Focus Energy case).
  let b2 := if isFocusEnergy then
              sla8 (sla8 b1) 
            else
              sla8 b1
  if isHighCrit then
    sla8 (sla8 b2)
  else
    b2 >>> 1

/-- L1: Prove the bug exists with a concrete witness. -/
theorem bug_exists : ∃ (s : BitVec 8) (h : Bool), (impl s true h).toNat < (impl s false h).toNat := by
  -- Witness: Base speed 100, regular move (h=false)
  -- Without Focus Energy: Threshold is (100/2 * 2) / 2 = 50
  -- With Focus Energy (Bug): Threshold is (100/2 / 2) / 2 = 12
  use 100, false
  native_decide

/-- 
L2: Characterize the bug: Focus Energy never increases the crit rate in the buggy 
implementation; it always results in a threshold less than or equal to the 
original rate. 
-/
theorem bug_never_increases (s : BitVec 8) (h : Bool) : 
    (impl s true h).toNat <= (impl s false h).toNat := by
  have h_all := (by native_decide : ∀ (s : BitVec 8) (h : Bool), (impl s true h).toNat <= (impl s false h).toNat)
  exact h_all s h

/-- 
L2: Universal Property - The bug strictly reduces the critical hit rate for any 
Pokemon with a Base Speed of at least 8. 
-/
theorem bug_strictly_reduces (s : BitVec 8) (h : Bool) : 
    s.toNat >= 8 → (impl s true h).toNat < (impl s false h).toNat := by
  have h_all := (by native_decide : ∀ (s : BitVec 8) (h : Bool), s.toNat >= 8 → (impl s true h).toNat < (impl s false h).toNat)
  exact h_all s h

/-- 
L3: A corrected version of the routine.
Replaces the buggy `srl b` in the Focus Energy branch with the intended doubling logic.
-/
def fix (baseSpeed : BitVec 8) (isFocusEnergy : Bool) (isHighCrit : Bool) : BitVec 8 :=
  let b1 := baseSpeed >>> 1
  let b2 := if isFocusEnergy then
              sla8 (sla8 b1) -- Corrected: Double the intermediate threshold
            else
              sla8 b1
  if isHighCrit then
    sla8 (sla8 b2)
  else
    b2 >>> 1

/-- L3: Verify that the fix faithfully matches the intended specification. -/
theorem fix_correct (s : BitVec 8) (f : Bool) (h : Bool) : 
    fix s f h = spec s f h := by
  unfold fix spec
  cases f <;> rfl

/-- 
L4: Relational proof - Show that under the fix, Focus Energy always results in 
a critical hit rate greater than or equal to the default rate, whereas the 
original implementation fails this property.
-/
theorem fix_improves_rate (s : BitVec 8) (h : Bool) : 
    (fix s true h).toNat >= (fix s false h).toNat := by
  have h_all := (by native_decide : ∀ (s : BitVec 8) (h : Bool), (fix s true h).toNat >= (fix s false h).toNat)
  exact h_all s h

end AutoResearch
