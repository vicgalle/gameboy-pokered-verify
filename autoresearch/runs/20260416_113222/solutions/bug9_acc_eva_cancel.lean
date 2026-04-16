import SM83

namespace AutoResearch

/-- Stat modifier lookup table for accuracy/evasion in Pokemon Red's battle system.
    Indices 0-12 correspond to game stages -6 through +6 (index 6 = neutral).
    Each entry is (numerator, denominator) approximating the exact ratio.
    Key approximation error: stage -1 uses 66/100 instead of exact 2/3 ≈ 66.67/100. -/
def lookupMod (stage : Fin 13) : Nat × Nat :=
  match stage.val with
  | 0  => (33, 100)
  | 1  => (36, 100)
  | 2  => (43, 100)
  | 3  => (50, 100)
  | 4  => (60, 100)
  | 5  => (66, 100)
  | 6  => (1, 1)
  | 7  => (100, 66)
  | 8  => (100, 60)
  | 9  => (100, 50)
  | 10 => (100, 43)
  | 11 => (100, 36)
  | _  => (100, 33)

/-- Reflect evasion stage for use in accuracy calculation.
    Assembly: c = 14 - evasionMod (stages 1-13).
    With Fin 13 (indices 0-12): reflected = 12 - evStage.val. -/
def reflectStage (evStage : Fin 13) : Fin 13 :=
  ⟨12 - evStage.val, by omega⟩

/-- Buggy implementation matching the CalcHitChance assembly in engine/battle/core.asm.
    Two separate floor divisions accumulate rounding error:
    step 1: floor(base * accNum / accDen)
    step 2: floor(step1 * evNum / evDen) -/
def impl (baseAcc : BitVec 8) (accStage evStage : Fin 13) : Nat :=
  let base := baseAcc.toNat
  let (an, ad) := lookupMod accStage
  let afterAcc := (base * an) / ad
  let (en, ed) := lookupMod (reflectStage evStage)
  (afterAcc * en) / ed

/-- Correct specification: combine both modifier fractions before a single division.
    No intermediate truncation, so equal and opposite modifiers cancel exactly. -/
def spec (baseAcc : BitVec 8) (accStage evStage : Fin 13) : Nat :=
  let base := baseAcc.toNat
  let (an, ad) := lookupMod accStage
  let (en, ed) := lookupMod (reflectStage evStage)
  (base * an * en) / (ad * ed)

-- Neutral stage (index 6, no modifier applied)
def neutral : Fin 13 := ⟨6, by omega⟩
-- +1 accuracy/evasion stage (index 7)
def stageP1 : Fin 13 := ⟨7, by omega⟩

-- L1: Concrete witness — bug manifests with max accuracy and equal +1 opposing modifiers.
-- The two-pass computation gives 254 instead of the correct 255.
theorem l1_witness : impl (255 : BitVec 8) stageP1 stageP1 ≠ spec (255 : BitVec 8) stageP1 stageP1 := by
  native_decide

-- L1 concrete values proving the exact precision loss
theorem l1_impl_value : impl (255 : BitVec 8) stageP1 stageP1 = 254 := by native_decide
theorem l1_spec_value : spec (255 : BitVec 8) stageP1 stageP1 = 255 := by native_decide

-- L2a: For equal +1/-1 opposing modifiers, spec always recovers the base accuracy unchanged.
-- Reason: (100 * 66) = (66 * 100) = 6600, so the fractions cancel in exact arithmetic.
theorem l2_spec_exact : ∀ b : BitVec 8, spec b stageP1 stageP1 = b.toNat := by
  native_decide

-- L2b: For equal +1/-1 modifiers, impl always underestimates (≤ base accuracy).
-- Intermediate truncation can only remove, never add, to the result.
theorem l2_impl_le_base : ∀ b : BitVec 8, impl b stageP1 stageP1 ≤ b.toNat := by
  native_decide

-- L2c: Universal property: two-pass impl never exceeds single-pass spec for any input.
-- floor(floor(x*a/b)*c/d) ≤ floor(x*a*c/(b*d)) holds for all non-negative integers.
theorem l2_impl_le_spec : ∀ b : BitVec 8, ∀ i j : Fin 13, impl b i j ≤ spec b i j := by
  native_decide

-- L2d: Neutral stages produce exact results (no precision loss with 1/1 multipliers).
theorem l2_neutral_exact : ∀ b : BitVec 8, impl b neutral neutral = b.toNat := by
  native_decide

-- L3: Fixed implementation — single division after combining both modifier ratios.
def implFixed (baseAcc : BitVec 8) (accStage evStage : Fin 13) : Nat :=
  let base := baseAcc.toNat
  let (an, ad) := lookupMod accStage
  let (en, ed) := lookupMod (reflectStage evStage)
  (base * an * en) / (ad * ed)

-- L3: The fix matches the specification for all inputs.
theorem l3_fix_correct : ∀ b : BitVec 8, ∀ i j : Fin 13, implFixed b i j = spec b i j := by
  native_decide

end AutoResearch
