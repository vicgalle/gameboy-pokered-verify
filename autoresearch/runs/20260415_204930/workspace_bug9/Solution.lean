import SM83

namespace AutoResearch

/-- Numerator from the Gen 1 StatModifierRatios table.
    Stage mod index is 1–13; index 7 = neutral (×1). -/
def modNum : Nat → Nat
  | 1  => 25  | 2  => 28  | 3  => 33  | 4  => 40
  | 5  => 50  | 6  => 66  | 7  => 100 | 8  => 150
  | 9  => 200 | 10 => 250 | 11 => 300 | 12 => 350
  | 13 => 400 | _  => 100

/-- Denominator for all table entries. -/
def modDen : Nat := 100

/-- CalcHitChance: two sequential passes, each with floor division.
    accMod, evaMod ∈ {1,...,13}; 7 = neutral.
    Assembly reflects evasion: c = 14 − evaMod before the loop. -/
def impl (baseAcc accMod evaMod : Nat) : Nat :=
  -- Pass 1: scale by accuracy stage ratio
  let afterAcc := (baseAcc * modNum accMod) / modDen
  -- Reflect evasion index (c = 14 − evaMod in the assembly)
  let evaRef   := 14 - evaMod
  -- Pass 2: scale by reflected evasion ratio
  let afterEva := (afterAcc * modNum evaRef) / modDen
  -- Assembly ensures result ≥ 1
  max afterEva 1

/-- Specification: equal accuracy and evasion stage boosts should cancel
    perfectly, leaving effective accuracy equal to the base. -/
def spec (baseAcc accMod evaMod : Nat) : Nat :=
  if accMod = evaMod then baseAcc
  else impl baseAcc accMod evaMod

-- ============================================================
-- L1 : Concrete bug witness
-- ============================================================

/-- Equal ±1 stages: impl gives 252 but spec expects 255. -/
theorem bug_L1 : impl 255 8 8 ≠ spec 255 8 8 := by native_decide

-- ============================================================
-- L2 : Characterize the loss at all 13 stage levels (base = 255)
-- ============================================================

-- Exact values match the assembly-level bug description
theorem impl_equal_plus1 : impl 255 8  8  = 252 := by native_decide
theorem impl_equal_plus5 : impl 255 12 12 = 249 := by native_decide

-- Stages that lose accuracy due to non-exact floor division
theorem loss_at_1  : impl 255 1  1  = 252 := by native_decide
theorem loss_at_2  : impl 255 2  2  = 248 := by native_decide  -- worst case: −7
theorem loss_at_3  : impl 255 3  3  = 252 := by native_decide
theorem loss_at_5  : impl 255 5  5  = 254 := by native_decide
theorem loss_at_6  : impl 255 6  6  = 252 := by native_decide
theorem loss_at_10 : impl 255 10 10 = 254 := by native_decide
theorem loss_at_11 : impl 255 11 11 = 252 := by native_decide

-- Stages where the division is arithmetically exact (no loss)
theorem exact_at_4  : impl 255 4  4  = 255 := by native_decide  -- 40/100 × 250/100 = 1
theorem exact_at_7  : impl 255 7  7  = 255 := by native_decide  -- neutral
theorem exact_at_9  : impl 255 9  9  = 255 := by native_decide  -- 200/100 × 50/100 = 1
theorem exact_at_13 : impl 255 13 13 = 255 := by native_decide  -- 400/100 × 25/100 = 1

-- The bug is strictly a loss (impl never exceeds baseAcc for equal stages)
theorem bug_L1_lt : impl 255 8 8 < spec 255 8 8 := by native_decide
theorem bug_loss_monotone : impl 255 2 2 < impl 255 1 1 := by native_decide

-- ============================================================
-- L3 : Fix — short-circuit when stages are equal
-- ============================================================

/-- Fixed implementation: detect when acc/eva stages cancel and return
    base accuracy directly, avoiding the two-pass truncation error. -/
def fix (baseAcc accMod evaMod : Nat) : Nat :=
  if accMod = evaMod then baseAcc
  else impl baseAcc accMod evaMod

/-- The fix matches the specification by construction. -/
theorem fix_matches_spec (baseAcc accMod evaMod : Nat) :
    fix baseAcc accMod evaMod = spec baseAcc accMod evaMod := by
  simp only [fix, spec]

/-- The fix eliminates the loss at the problematic +1 stage. -/
theorem fix_correct_plus1 : fix 255 8 8 = 255 := by native_decide

/-- The fix eliminates the worst-case −7 loss at stage 2. -/
theorem fix_correct_stage2 : fix 255 2 2 = 255 := by native_decide

end AutoResearch
