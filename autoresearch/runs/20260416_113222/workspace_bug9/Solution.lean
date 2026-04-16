import SM83

namespace AutoResearch

/-- Stat modifier lookup table for accuracy/evasion in Pokemon Red's battle system.
    Indices 0-12 correspond to game stages 1-13 (index 6 = neutral).
    Each entry is (numerator, denominator) approximating the exact ratio.
    Key approximation error: stage index 5 uses 66/100 instead of exact 2/3. -/
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

/-- Reflect evasion stage. Assembly: c = 14 - evasionMod. In 0-indexed Fin 13: 12 - idx. -/
def reflectStage (evStage : Fin 13) : Fin 13 :=
  ⟨12 - evStage.val, by omega⟩

/-- Buggy CalcHitChance: two separate floor divisions accumulate rounding error.
    step 1: floor(base * accNum / accDen)
    step 2: floor(step1 * evNum / evDen) -/
def impl (baseAcc : BitVec 8) (accStage evStage : Fin 13) : Nat :=
  let base := baseAcc.toNat
  let (an, ad) := lookupMod accStage
  let afterAcc := (base * an) / ad
  let (en, ed) := lookupMod (reflectStage evStage)
  (afterAcc * en) / ed

/-- Correct specification: single division after combining both modifier fractions.
    No intermediate truncation, so equal and opposite modifiers cancel exactly. -/
def spec (baseAcc : BitVec 8) (accStage evStage : Fin 13) : Nat :=
  let base := baseAcc.toNat
  let (an, ad) := lookupMod accStage
  let (en, ed) := lookupMod (reflectStage evStage)
  (base * an * en) / (ad * ed)

/-- Fixed implementation: combine fractions first, then one floor division. -/
def implFixed (baseAcc : BitVec 8) (accStage evStage : Fin 13) : Nat :=
  let base := baseAcc.toNat
  let (an, ad) := lookupMod accStage
  let (en, ed) := lookupMod (reflectStage evStage)
  (base * an * en) / (ad * ed)

-- Named stage constants
def neutral  : Fin 13 := ⟨6, by omega⟩  -- stage 7 in game (neutral, no modifier)
def stageP1  : Fin 13 := ⟨7, by omega⟩  -- stage 8 in game (+1 accuracy/evasion)
def stageIdx1 : Fin 13 := ⟨1, by omega⟩  -- stage 2 in game (-5 modifier, equal cancel)

-- ── Structural lemma ──────────────────────
