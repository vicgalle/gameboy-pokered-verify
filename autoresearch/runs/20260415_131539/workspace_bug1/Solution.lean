import SM83

namespace AutoResearch

/-!
# Bug: Focus Energy Quarters Critical Hit Rate Instead of Doubling It

## Description
In Pokémon Red/Blue/Yellow, the move Focus Energy is intended to increase a Pokémon's 
critical hit rate. In Generation 1, the critical hit rate is derived from the Pokémon's 
base Speed stat. Focus Energy should double this probability.

However, due to a bug in `engine/battle/core.asm`, the implementation performs a 
logical shift right (`srl b`) instead of a logical shift left (`sla b`) when the 
`GETTING_PUMPED` status (Focus Energy) is active. This results in the critical hit 
threshold being reduced by a factor of 4 relative to not using the move at all.

## Formal Model
- `sla_sat`: Models the assembly's saturating arithmetic shift left (capped at 255).
- `impl`: Models the logic in the `CriticalHitTest` subroutine.
- `spec`: Models the intended doubling effect.
- `fix`: A proposed correction to the assembly.
-/

/-- 
Saturating left shift by 1.
Matches the assembly pattern:
  sla b
  jr nc, .noCarry
  ld b, $ff
.noCarry
-/
def sla_sat (b : BitVec 8) : BitVec 8 :=
  if b.getMsb 0 then 0xFF else b <<< 1

/-- 
Implementation of the critical hit threshold calculation from the original Pokémon Red assembly.
The threshold `b` determines the probability of a critical hit as `b / 256`.
-/
def impl (baseSpeed : BitVec 8) (isFocusEnergy : Bool) (isHighCrit : Bool) : BitVec 8 :=
  -- ld a, [wMonHBaseSpeed] / ld b, a / srl b
  let b0 := baseSpeed >>> 1
  
  -- bit GETTING_PUMPED, a / jr nz, .focusEnergyUsed
  let b1 := if isFocusEnergy then
              -- .focusEnergyUsed: srl b
              -- This is the bug: it divides by 2 instead of multiplying.
              b0 >>> 1 
            else
              -- sla b / jr nc, .noFocusEnergyUsed / ld b, $ff
              -- This is the intended path for non-Focus Energy.
              sla_sat b0
  
  -- .noFocusEnergyUsed / .Loop ...
  if isHighCrit then
    -- .HighCritical: sla b (*2) / sla b (*4) with saturation
    sla_sat (sla_sat b1)
  else
    -- .SkipHighCritical: srl b (/2)
    b1 >>> 1

/-- 
The intended specification: 
Using Focus Energy should result in a critical hit threshold twice as large 
as the threshold without Focus Energy (capped at 255).
-/
def spec (baseSpeed : BitVec 8) (isFocusEnergy : Bool) (isHighCrit : Bool) : BitVec 8 :=
  let b0 := baseSpeed >>> 1
  let threshold_no_fe := 
    let b_base := sla_sat b0
    if isHighCrit then sla_sat (sla_sat b_base) else b_base >>> 1
  
  if isFocusEnergy then
    -- Intended to be twice as likely as no-FE
    sla_sat threshold_no_fe
  else
    threshold_no_fe

/-- 
A proposed fix for the assembly.
To achieve the doubling effect, we replace `srl b` in the `.focusEnergyUsed` 
block with two `sla_sat` operations. This compensates for the fact that the 
non-Focus Energy path performs one `sla_sat`.
-/
def fix (baseSpeed : BitVec 8) (isFocusEnergy : Bool) (isHighCrit : Bool) : BitVec 8 :=
  let b0 := baseSpeed >>> 1
  let b1 := if isFocusEnergy then
              -- Quadruple the starting b0 (speed/2) to reach 2*speed
              sla_sat (sla_sat b0)
            else
              sla_sat b0
  
  if isHighCrit then
    sla_sat (sla_sat b1)
  else
    b1 >>> 1

/-! ## Proofs -/

/-- L1: Bug Exists
For a Pokémon like Jolteon (Base Speed 130) using a normal move,
Focus Energy results in a different threshold than intended.
-/
theorem bug_exists : ∃ (s : BitVec 8) (fe hc : Bool), impl s fe hc != spec s fe hc := by
  -- Speed 130, Focus Energy On, Normal Move
  use 130, true, false
  native_decide

/-- L2: Characterization (Detrimental Nature)
For any Pokémon with a Base Speed of at least 2, using Focus Energy 
strictly reduces the probability of a critical hit compared to doing nothing.
-/
theorem focus_energy_is_detrimental (s : BitVec 8) (hc : Bool) :
    s >= 2 → impl s true hc < impl s false hc := by
  intro _
  have h := (by native_decide : ∀ (s : BitVec 8) (hc : Bool), s >= 2 → impl s true hc < impl s false hc)
  exact h s hc

/-- L2: Magnitude of the Bug
For typical speeds and normal moves, the Focus Energy threshold is exactly 
1/4 of the non-Focus Energy threshold.
-/
theorem bug_is_quarter_threshold (s : BitVec 8) :
    s >= 8 ∧ s < 128 ∧ (s.toNat % 8 = 0) → 
    (impl s false false).toNat = 4 * (impl s true false).toNat := by
  intro _
  have h := (by native_decide : ∀ (s : BitVec 8), (s >= 8 ∧ s < 128 ∧ s.toNat % 8 = 0) → 
    (impl s false false).toNat = 4 * (impl s true false).toNat)
  exact h s

/-- L3: Fix Correctness
Our proposed assembly fix matches the doubling specification for all possible inputs.
-/
theorem fix_correct (s : BitVec 8) (fe hc : Bool) : fix s fe hc = spec s fe hc := by
  have h := (by native_decide : ∀ (s : BitVec 8) (fe hc : Bool), fix s fe hc = spec s fe hc)
  exact h s fe hc

/-- L4: Relational Impact on High-Critical Moves
For High-Critical moves (like Slash), the bug is so severe that using Focus Energy 
reduces the threshold to exactly the Pokémon's base speed, whereas without Focus Energy, 
it would be 4x the base speed (ignoring saturation).
-/
theorem high_crit_impact (s : BitVec 8) :
    s < 64 ∧ (s.toNat % 4 = 0) → 
    impl s true true = s ∧ impl s false true = s <<< 2 := by
  intro _
  have h := (by native_decide : ∀ (s : BitVec 8), (s < 64 ∧ s.toNat % 4 = 0) → 
    impl s true true = s ∧ impl s false true = s <<< 2)
  exact h s

end AutoResearch
