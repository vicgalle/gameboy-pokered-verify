/-
  PokeredBugs/Proofs/AccEvaCancel.lean — Accuracy/Evasion stage non-cancellation.

  ## The Bug
  The CalcHitChance routine (core.asm 5348-5417) applies accuracy and evasion
  stage multipliers sequentially, using the StatModifierRatios table. Two
  factors cause equal accuracy and evasion boosts to not cancel:

  1. Truncated fractions in the table:
       Stage +1: 15/10 = 1.50     Stage -1: 66/100 = 0.66  (exact: 2/3 = 0.6667)
       Stage +5: 35/10 = 3.50     Stage -5: 28/100 = 0.28  (exact: 2/7 = 0.2857)
     Product: 15/10 * 66/100 = 990/1000 = 0.99 ≠ 1.0.

  2. Intermediate truncation between the two passes:
     Even when the fraction product IS exact (stage ±3: 25/10 * 40/100 = 1.0),
     floor division after pass 1 loses precision. 255*25/10 = 637 (not 637.5),
     then 637*40/100 = 254 (not 254.8). Loss of 1 from truncation alone.

  ## Practical Impact
  This bug is LATENT in Gen 1: no Gen 1 move raises accuracy stages or lowers
  evasion stages. The non-cancellation scenario is impossible in normal gameplay.
  It becomes exploitable in later generations with moves like Hone Claws or Coil.

  ## Assembly Context
  CalcHitChance does two passes through StatModifierRatios:
    Pass 1: accuracy = move_accuracy * acc_numerator / acc_denominator
    Pass 2: accuracy = accuracy * eva_numerator / eva_denominator
  (with integer truncation at each division)

  Evasion stage is inverted: index = 14 - evasion_stage_value.
  So evasion +N uses the table entry for stage -N.
-/
import SM83

namespace PokeredBugs

/-! ### Model: Stat Modifier Ratios Table -/

/-- A stage multiplier: numerator and denominator. -/
structure StageRatio where
  num : Nat
  den : Nat
  deriving Repr, DecidableEq

/-- The StatModifierRatios table from data/battle/stat_modifiers.asm.
    Indexed 0-12 corresponding to stages -6 through +6. -/
def statModifierRatios : Array StageRatio := #[
  ⟨25, 100⟩,  -- stage -6: 0.25
  ⟨28, 100⟩,  -- stage -5: 0.28  (exact 2/7 = 0.2857)
  ⟨33, 100⟩,  -- stage -4: 0.33  (exact 1/3 = 0.3333)
  ⟨40, 100⟩,  -- stage -3: 0.40
  ⟨50, 100⟩,  -- stage -2: 0.50
  ⟨66, 100⟩,  -- stage -1: 0.66  (exact 2/3 = 0.6667)
  ⟨1,  1⟩,    -- stage  0: 1.00
  ⟨15, 10⟩,   -- stage +1: 1.50
  ⟨2,  1⟩,    -- stage +2: 2.00
  ⟨25, 10⟩,   -- stage +3: 2.50
  ⟨3,  1⟩,    -- stage +4: 3.00
  ⟨35, 10⟩,   -- stage +5: 3.50
  ⟨4,  1⟩     -- stage +6: 4.00
]

/-- Stage values in RAM: 1-13, where 7 = neutral (stage 0).
    Convert to table index: index = value - 1. -/
def stageToIndex (stageValue : Nat) : Nat := stageValue - 1

/-- Invert evasion stage: 14 - evasion_value. -/
def invertEvasion (evasionValue : Nat) : Nat := 14 - evasionValue

/-- Look up a ratio from the table. -/
def getRatio (index : Nat) : StageRatio :=
  statModifierRatios.getD index ⟨1, 1⟩

/-! ### Model: CalcHitChance Two-Pass Calculation -/

/-- Apply one stage modifier: multiply by numerator, divide by denominator.
    Integer truncation (floor division). Clamp result to at least 1. -/
def applyRatio (accuracy : Nat) (ratio : StageRatio) : Nat :=
  let result := accuracy * ratio.num / ratio.den
  if result == 0 then 1 else result

/-- CalcHitChance: apply accuracy stage, then evasion stage.
    accStage and evaStage are RAM values (1-13, where 7 = neutral). -/
def calcHitChance (moveAccuracy : Nat) (accStage evaStage : Nat) : Nat :=
  let accIndex := stageToIndex accStage
  let evaInverted := invertEvasion evaStage
  let evaIndex := stageToIndex evaInverted
  let accRatio := getRatio accIndex
  let evaRatio := getRatio evaIndex
  -- Two-pass: accuracy first, then evasion
  let pass1 := applyRatio moveAccuracy accRatio
  let pass2 := applyRatio pass1 evaRatio
  -- Cap at 255
  min pass2 255

/-! ### Proof 1: Equal Stages Don't Cancel -/

/-- Stage +1 accuracy, +1 evasion on a 255-accuracy move.
    Should give 255 (perfect cancellation), but gives 252. -/
theorem plus1_doesnt_cancel :
    calcHitChance 255 8 8 = 252 := by native_decide

/-- No boosts at all gives the full 255. -/
theorem neutral_is_255 :
    calcHitChance 255 7 7 = 255 := by native_decide

/-- Equal +1 boosts REDUCE effective accuracy by 3 points! -/
theorem plus1_reduces_accuracy :
    calcHitChance 255 8 8 < calcHitChance 255 7 7 := by native_decide

/-- Equal +4 boosts also don't cancel. -/
theorem plus4_doesnt_cancel :
    calcHitChance 255 11 11 < calcHitChance 255 7 7 := by native_decide

/-- Equal +5 boosts are the worst: 249 instead of 255. -/
theorem plus5_worst_noncancellation :
    calcHitChance 255 12 12 = 249 := by native_decide

/-- Only ±2 and ±6 cancel perfectly. ±3 loses 1 due to truncation. -/
theorem plus2_cancels : calcHitChance 255 9 9 = 255 := by native_decide
theorem plus3_almost : calcHitChance 255 10 10 = 254 := by native_decide
theorem plus6_cancels : calcHitChance 255 13 13 = 255 := by native_decide

/-! ### Proof 2: The Exact Non-Cancellation Table -/

/-- Complete characterization: which equal stages cancel and which don't.
    For a 255-accuracy move: -/
theorem noncancellation_table :
    -- Stages that perfectly cancel (result = 255)
    calcHitChance 255 7  7  = 255 ∧  -- ±0
    calcHitChance 255 9  9  = 255 ∧  -- ±2
    calcHitChance 255 13 13 = 255 ∧  -- ±6
    -- Stages that DON'T cancel (result < 255)
    calcHitChance 255 8  8  = 252 ∧  -- ±1: lose 3
    calcHitChance 255 10 10 = 254 ∧  -- ±3: lose 1
    calcHitChance 255 11 11 = 252 ∧  -- ±4: lose 3
    calcHitChance 255 12 12 = 249 := -- ±5: lose 6!
  by native_decide

/-! ### Proof 3: Impact on Hit Probability -/

/-- With the 1/256 bug, accuracy 255 gives 255/256 hit chance.
    Equal +5 boosts reduce this to 249/256 — a compound penalty. -/
theorem plus5_hit_probability_loss :
    -- Without the non-cancellation: 255/256 = 99.6%
    -- With non-cancellation: 249/256 = 97.3%
    -- That's a 2.3% penalty for "equal" boosts that should cancel!
    calcHitChance 255 7 7 - calcHitChance 255 12 12 = 6 := by native_decide

/-- For lower accuracy moves, the impact is similar.
    Thunderbolt (accuracy ~242): equal ±5 boosts lose 5 points. -/
theorem thunderbolt_noncancellation :
    calcHitChance 242 12 12 = 237 ∧
    calcHitChance 242 7 7 = 242 := by native_decide

/-! ### Proof 4: The Root Cause — Truncated Fractions -/

/-- The non-cancellation happens because the table uses truncated decimals.
    Stage -1 should be 2/3 but is stored as 66/100.
    15/10 * 66/100 = 990/1000 ≠ 1. -/
theorem ratio_product_not_one :
    let r_plus1 := getRatio 7   -- stage +1: 15/10
    let r_minus1 := getRatio 5  -- stage -1: 66/100
    r_plus1.num * r_minus1.num ≠ r_plus1.den * r_minus1.den := by
  native_decide

/-- Stages ±2 and ±6 cancel because their fraction products equal 1:
    2/1 * 50/100 = 100/100. 4/1 * 25/100 = 100/100.
    Stage ±3 (25/10 * 40/100 = 1000/1000) cancels algebraically but
    loses 1 point from integer truncation in the two-pass calculation. -/
theorem exact_fractions_cancel :
    let r2p := getRatio 8; let r2m := getRatio 4
    let r6p := getRatio 12; let r6m := getRatio 0
    r2p.num * r2m.num = r2p.den * r2m.den ∧
    r6p.num * r6m.num = r6p.den * r6m.den := by
  native_decide

/-! ### Proof 5: Order Dependence (Non-Commutativity) -/

/-- Reversing the order of accuracy and evasion application can give
    different results due to integer truncation. -/
def calcHitChanceReversed (moveAccuracy : Nat) (accStage evaStage : Nat) : Nat :=
  let evaInverted := invertEvasion evaStage
  let evaIndex := stageToIndex evaInverted
  let accIndex := stageToIndex accStage
  let evaRatio := getRatio evaIndex
  let accRatio := getRatio accIndex
  -- Reversed: evasion first, then accuracy
  let pass1 := applyRatio moveAccuracy evaRatio
  let pass2 := applyRatio pass1 accRatio
  min pass2 255

/-- The two orderings give different results for some inputs. -/
theorem order_matters :
    calcHitChance 255 12 12 ≠ calcHitChanceReversed 255 12 12 := by
  native_decide

/-- Reversed order gives 248, original gives 249. Both are wrong (should be 255),
    but they're wrong in DIFFERENT ways! -/
theorem order_difference :
    calcHitChance 255 12 12 = 249 ∧
    calcHitChanceReversed 255 12 12 = 248 := by
  native_decide

/-! ### #eval Demonstrations -/

-- Equal stages that should cancel but don't
#eval (calcHitChance 255 7 7, calcHitChance 255 8 8, calcHitChance 255 11 11, calcHitChance 255 12 12)
-- (255, 252, 252, 249)

-- Order dependence
#eval (calcHitChance 255 12 12, calcHitChanceReversed 255 12 12)
-- (249, 248)

end PokeredBugs
