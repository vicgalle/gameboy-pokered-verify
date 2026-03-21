/-
  PokeredBugs/Proofs/StatScaling.lean — Analysis of the damage formula stat scaling.

  ## The Routine
  When either the offensive or defensive stat exceeds 255, both are divided
  by 4 to fit in a single byte. This is done via two srl/rr shift pairs.
  (core.asm lines 4107-4127)

  After scaling:
  - If the offensive stat becomes 0, it is bumped to 1
  - The defensive stat is NOT bumped — it can become 0, causing a freeze
  - Values > 1023 wrap around (only 8 bits stored after the shift)

  ## What We Investigate
  1. Does increasing attack always increase damage? (monotonicity)
  2. Can stat values > 1023 wrap around catastrophically?
  3. Is the defense-zero freeze reachable?
  4. How does truncation affect the attack/defense ratio?
-/
import SM83

namespace PokeredBugs

/-! ### Model: Stat Scaling -/

/-- Scale a 16-bit stat down by /4, returning only the low 8 bits.
    This models two `srl h; rr l` pairs followed by reading only `l`.
    Values > 1023 wrap around because only 8 bits are kept. -/
def scaleDiv4 (stat : UInt16) : UInt8 :=
  let shifted := stat.toNat / 4
  ⟨shifted % 256⟩

/-- The stat scaling routine from core.asm lines 4107-4127.
    Takes 16-bit attack and defense, returns scaled 8-bit values.
    Scaling only triggers when either stat > 255.
    Attack is bumped to 1 if it becomes 0; defense is NOT. -/
def statScaling (attack defense : UInt16) : UInt8 × UInt8 :=
  if attack.toNat ≤ 255 ∧ defense.toNat ≤ 255 then
    (⟨attack.toNat⟩, ⟨defense.toNat⟩)
  else
    let a := scaleDiv4 attack
    let d := scaleDiv4 defense
    let a := if a == 0 then 1 else a
    (a, d)

/-- The damage ratio component: attack / defense (integer division).
    Returns none if defense is 0 (game freezes). -/
def damageRatio (attack defense : UInt16) : Option Nat :=
  let (a, d) := statScaling attack defense
  if d == 0 then none
  else some (a.toNat / d.toNat)

/-! ### Proof 1: Defense Zero Freeze -/

/-- The defensive stat CAN become 0, causing a freeze.
    Example: attack=256, defense=3. After /4: attack=64, defense=0. -/
theorem defense_zero_freeze :
    damageRatio 256 3 = none := by native_decide

/-- Defense values 1, 2, 3 all freeze when scaling is triggered. -/
theorem defense_1_freezes : damageRatio 256 1 = none := by native_decide
theorem defense_2_freezes : damageRatio 256 2 = none := by native_decide
theorem defense_3_freezes : damageRatio 256 3 = none := by native_decide
theorem defense_4_survives : damageRatio 256 4 ≠ none := by native_decide

/-! ### Proof 2: The 1023→1024 Cliff -/

/-- Values > 1023 wrap around after /4 because only 8 bits are stored.
    1024/4 = 256, which wraps to 0 in a byte, then bumped to 1. -/
theorem attack_1023_scales_to_255 : scaleDiv4 1023 = 255 := by native_decide
theorem attack_1024_wraps_to_0 : scaleDiv4 1024 = 0 := by native_decide

/-- Catastrophic damage collapse: attack goes from 1023 to 1024,
    but after scaling the effective attack drops from 255 to 1. -/
theorem damage_cliff_1024 :
    damageRatio 1023 100 = some 10 ∧
    damageRatio 1024 100 = some 0 := by
  native_decide

/-- The wrapping causes periodic damage collapses at every multiple of 1024. -/
theorem periodic_collapse :
    damageRatio 1024 100 = damageRatio 2048 100 := by
  native_decide

/-! ### Proof 3: Monotonicity Violations -/

/-- CRITICAL: Increasing attack does NOT always increase damage.
    attack=1023 → attack=1024 causes damage to DROP from 10 to 0. -/
theorem attack_not_monotone :
    damageRatio 1023 100 = some 10 ∧
    damageRatio 1024 100 = some 0 := by
  native_decide

/-- Even within practical game ranges, 3 Swords Dances gives LESS
    damage than 2 Swords Dances due to wrapping. -/
theorem swords_dance_regression :
    -- 2 SDs: attack=636, defense=200 → ratio=3
    damageRatio 636 200 = some 3 ∧
    -- 3 SDs: attack=1272, defense=200 → ratio=1 (LESS!)
    damageRatio 1272 200 = some 1 := by
  native_decide

/-- The base stat (no Swords Dance) and the 3-SD case give the same ratio.
    Three Swords Dances completely undoes itself. -/
theorem three_sds_equals_zero_sds :
    damageRatio 318 200 = damageRatio 1272 200 := by
  native_decide

/-! ### Proof 4: Exact Wrapping Characterization -/

/-- The scaleDiv4 function maps stat to (stat/4) mod 256. -/
theorem scaling_is_mod256 (stat : UInt16) :
    (scaleDiv4 stat).toNat = stat.toNat / 4 % 256 := by
  simp [scaleDiv4, UInt8.toNat]

/-- The danger zone: attack values where wrapping causes damage to drop.
    Any attack in [1024, 1027] maps to [0, 0] (bumped to 1) after scaling. -/
theorem wrapping_danger_zone :
    scaleDiv4 1024 = 0 ∧ scaleDiv4 1025 = 0 ∧
    scaleDiv4 1026 = 0 ∧ scaleDiv4 1027 = 0 ∧
    scaleDiv4 1028 = 1 := by
  native_decide

/-! ### #eval Demonstrations -/

-- Swords Dance progression: 0 SD, 1 SD, 2 SD, 3 SD
-- Base attack=318, defense=200
#eval (damageRatio 318 200, damageRatio 636 200, damageRatio 954 200, damageRatio 1272 200)

-- The 1023→1024 cliff
#eval (damageRatio 1023 100, damageRatio 1024 100)

-- Defense freeze zone
#eval (damageRatio 300 1, damageRatio 300 2, damageRatio 300 3, damageRatio 300 4)

end PokeredBugs
