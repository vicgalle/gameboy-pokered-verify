import SM83

namespace AutoResearch

-- Game Boy 'sla' (Shift Left Arithmetic) with bit 7 carry check as seen in CriticalHitTest.
-- If the shift overflows (bit 7 set), the code caps the threshold at $FF.
def sla (x : BitVec 8) : BitVec 8 :=
  if x.getLsb 7 then 0xFF else x <<< 1

-- Model the buggy CriticalHitTest probability threshold calculation.
-- speed: base speed stat, pumped: Focus Energy status, highCrit: move type.
def impl (speed : BitVec 8) (pumped : Bool) (highCrit : Bool) : BitVec 8 :=
  let b0 := speed >>> 1                     -- srl b (initial speed/2)
  let b1 := if pumped then
              b0 >>> 1                      -- .focusEnergyUsed: srl b (BUG: should double)
            else
              sla b0                        -- .noFocusEnergyUsed: sla b
  if highCrit then
    sla (sla b1)                            -- .HighCritical: sla b, sla b
  else
    b1 >>> 1                                -- .SkipHighCritical: srl b

-- Model the intended Gen 1 behavior where Focus Energy quadruples the threshold.
def spec (speed : BitVec 8) (pumped : Bool) (highCrit : Bool) : BitVec 8 :=
  let b0 := speed >>> 1
  let b1 := if pumped then
              sla (sla (sla b0))            -- Intended: Focus Energy provides a 4x multiplier
            else
              sla b0                        -- Normal: Return b0 to speed
  if highCrit then sla (sla b1) else b1 >>> 1

-- L1: Bug Witness - Jolteon (130 Speed) has a 65/256 crit rate normally, but 16/256 with Focus Energy.
theorem bug_exists : impl 130 true false < impl 130 false false := by native_decide

-- L2: Focus Energy is always detrimental or useless under the bug, never beneficial.
theorem bug_detrimental (s : BitVec 8) (h : Bool) : 
  impl s true h <= impl s false h := by
  have := (by native_decide : ∀ s : BitVec 8, ∀ h : Bool, impl s true h <= impl s false h)
  exact this s h

-- L2: For any Pokémon with at least 8 Speed, Focus Energy strictly reduces crit chance.
theorem bug_strictly_worse (s : BitVec 8) : 
  s >= 8 → impl s true false < impl s false false := by
  have := (by native_decide : ∀ s : BitVec 8, s >= 8 → impl s true false < impl s false false)
  exact this s

-- L3: Fix Correctness - The intended spec ensures Focus Energy is always beneficial or equal (capped).
theorem fix_is_beneficial (s : BitVec 8) (h : Bool) : 
  spec s true h >= spec s false h := by
  have := (by native_decide : ∀ s : BitVec 8, ∀ h : Bool, spec s true h >= spec s false h)
  exact this s h

-- L4: Characterize Bug Ratio - For non-capped speeds, the bug quarters the intended rate.
theorem bug_is_exactly_quarter (s : BitVec 8) :
  s >= 8 ∧ s <= 64 → (impl s false false) >>> 2 = impl s true false := by
  have := (by native_decide : ∀ s : BitVec 8, s >= 8 ∧ s <= 64 → (impl s false false) >>> 2 = impl s true false)
  exact this s

-- L4: High Critical Move Interaction - Even with a high-crit move, Focus Energy is worse than no move status.
theorem high_crit_bug_interaction (s : BitVec 8) :
  s >= 4 → impl s true true < impl s false true := by
  have := (by native_decide : ∀ s : BitVec 8, s >= 4 → impl s true true < impl s false true)
  exact this s

-- L4: Relational - The buggy Focus Energy rate is 1/16th of the intended spec rate for normal moves.
theorem bug_vs_spec_discrepancy (s : BitVec 8) :
  s >= 16 ∧ s <= 32 → (spec s true false) >>> 4 = impl s true false := by
  have := (by native_decide : ∀ s : BitVec 8, s >= 16 ∧ s <= 32 → (spec s true false) >>> 4 = impl s true false)
  exact this s

end AutoResearch

