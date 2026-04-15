import SM83

namespace AutoResearch

-- Caps shift-left at 255 if carry would occur
def sla_cap (x : BitVec 8) : BitVec 8 :=
  if x.getLsb 7 then 0xFF else x <<< 1

-- Models the CriticalHitTest logic from Pokemon Red
def critical_hit_threshold (speed : BitVec 8) (focus : Bool) (high : Bool) (buggy : Bool) : BitVec 8 :=
  let b := speed >>> 1
  -- Step 2: Focus Energy handling
  let b := if focus then
    if buggy then b >>> 1 else sla_cap (sla_cap b) -- Bug: srl b instead of doubling
  else sla_cap b
  -- Step 3: High critical move handling
  if !high then b >>> 1
  else sla_cap (sla_cap b)

def impl := fun s f h => critical_hit_threshold s f h true
def spec := fun s f h => critical_hit_threshold s f h false

-- L1: Bug Exists - Focus Energy significantly reduces crit threshold
theorem bug_exists : ∃ s f h, impl s f h ≠ spec s f h :=
  ⟨100, true, false, by native_decide⟩

-- L2: Characterization - Focus Energy always lowers the rate in buggy code
-- Note: A lower threshold 'b' in 'cp b' means fewer 'a < b' successes
theorem focus_energy_reduces_rate (s : BitVec 8) (h : Bool) :
  s > 7 → impl s true h < impl s false h := by
  have h_decide := (by native_decide : ∀ (s : BitVec 8) (h : Bool), s > 7 → impl s true h < impl s false h)
  exact h_decide s h

-- L2: Magnitude - Buggy threshold is exactly 1/4 of the intended "No Focus" threshold (when no overflow)
theorem bug_is_quarter_rate (s : BitVec 8) (h : Bool) :
  s < 64 → impl s true h = (impl s false h) >>> 2 := by
  have h_decide := (by native_decide : ∀ (s : BitVec 8) (h : Bool), s < 64 → impl s true h = (impl s false h) >>> 2)
  exact h_decide s h

-- L3: Fix Correctness
def fix (s : BitVec 8) (f : Bool) (h : Bool) : BitVec 8 := critical_hit_threshold s f h false

theorem fix_matches_spec (s : BitVec 8) (f : Bool) (h : Bool) :
  fix s f h = spec s f h := by rfl

end AutoResearch
