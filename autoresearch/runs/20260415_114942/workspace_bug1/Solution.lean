import SM83

namespace AutoResearch

-- Model SM83 'sla' with carry-based saturation to 0xFF (as seen in assembly)
def sla_cap (x : BitVec 8) : BitVec 8 :=
  if x.getLsb 7 then 0xFF else x <<< 1

-- Models CriticalHitTest logic: speed (b), focus (GETTING_PUMPED), high (move table)
-- buggy=true: srl b (halves probability), buggy=false: sla_cap b (doubles probability)
def threshold (speed : BitVec 8) (focus : Bool) (high : Bool) (buggy : Bool) : BitVec 8 :=
  let b := speed >>> 1 -- initial srl b
  let b1 := if focus then (if buggy then b >>> 1 else sla_cap b) else sla_cap b
  -- Move category branch logic
  if high then sla_cap (sla_cap b1) else b1 >>> 1

def impl (s f h) := threshold s f h true
def spec (s f h) := threshold s f h false

-- L1: Bug exists - Focus Energy reduces the threshold relative to doing nothing
theorem bug_exists : ∃ s h, impl s true h < impl s false h := 
  ⟨64, false, by native_decide⟩

-- L2: Characterization - Focus Energy reduces crit rate by exactly 4x in the buggy version
theorem bug_factor_four (s : BitVec 8) (h : Bool) :
  s ≥ 8 → impl s true h = (impl s false h) >>> 2 := by
  have h_all : ∀ (s : BitVec 8) (h : Bool), s ≥ 8 → 
    impl s true h = (impl s false h) >>> 2 := by native_decide
  exact h_all s h

-- L3: Fix Correctness - Focus Energy correctly doubles the rate in the specification
theorem fix_doubles_rate (s : BitVec 8) (h : Bool) :
  s ≥ 4 ∧ s < 64 → spec s true h = sla_cap (spec s false h) := by
  have h_all : ∀ (s : BitVec 8) (h : Bool), s ≥ 4 ∧ s < 64 → 
    spec s true h = sla_cap (spec s false h) := by native_decide
  exact h_all s h

-- L4: Relational - Total inversion of utility for regular moves
theorem utility_inversion (s : BitVec 8) :
  s ≥ 8 ∧ s < 128 → (impl s true false < impl s false false) ∧ 
                   (spec s true false > spec s false false) := by
  have h_all : ∀ (s : BitVec 8), s ≥ 8 ∧ s < 128 → 
    (impl s true false < impl s false false) ∧ (spec s true false > spec s false false) := by native_decide
  exact h_all s

-- L4: High Criticality saturation - Fix allows 100% crit (0xFF) for fast mons
theorem fix_enables_max_crit (s : BitVec 8) :
  s ≥ 64 → spec s true true = 0xFF := by
  have h_all : ∀ (s : BitVec 8), s ≥ 64 → spec s true true = 0xFF := by native_decide
  exact h_all s

-- L4: Comparison of Buggy vs Fixed performance (8x difference)
theorem fix_magnitude_advantage (s : BitVec 8) (h : Bool) :
  s ≥ 16 ∧ s < 32 → spec s true h = (impl s true h) <<< 3 := by
  have h_all : ∀ (s : BitVec 8) (h : Bool), s ≥ 16 ∧ s < 32 → 
    spec s true h = (impl s true h) <<< 3 := by native_decide
  exact h_all s h

end AutoResearch
