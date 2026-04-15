import SM83

/-!
# Bug: The "1/256 Miss Chance" (one_in_256)

In Pokémon Red/Blue, move accuracy and critical hit checks compare a random 
byte `r` against a threshold `t`. The check is implemented using the `cp` 
instruction followed by a "no carry" (`nc`) jump/return for failure.

In SM83 assembly, `cp t` (applied to `a`) performs `a - t`.
The Carry flag is set if `a < t` and cleared if `a ≥ t`.
Since the code treats "no carry" as a miss/failure, the condition for 
success is `r < t`.

Even for "100% accuracy" moves or maximum critical hit rates where `t = 255`, 
a random roll of `r = 255` results in `255 < 255` being false, causing 
an unintended 1/256 (0.39%) chance of failure.
-/

namespace AutoResearch

/-- 
Models the threshold calculation for critical hits based on the SM83 
assembly in `CriticalHitTest`.
-/
def calcCritThreshold (baseSpeed : BitVec 8) (isHighCrit : Bool) (isFocusEnergy : Bool) : BitVec 8 :=
  let b0 := baseSpeed >>> 1
  -- Focus Energy Bug: srl instead of sla
  let b1 := if isFocusEnergy then b0 >>> 1 else (if b0.getMsb 0 then 255 else b0 <<< 1)
  -- High Critical Move handling
  if isHighCrit then
    let b2 := if b1.getMsb 0 then 255 else b1 <<< 1
    if b2.getMsb 0 then 255 else b2 <<< 1
  else
    b1 >>> 1

/-- 
The buggy success condition used in both MoveHitTest and CriticalHitTest.
Success occurs only if `roll < threshold`.
-/
def impl (threshold : BitVec 8) (roll : BitVec 8) : Bool :=
  roll < threshold

/-- 
The intended success condition: if threshold is maxed (255), it should 
always succeed. Otherwise, it follows the threshold.
-/
def spec (threshold : BitVec 8) (roll : BitVec 8) : Bool :=
  if threshold == 255 then true else roll < threshold

/-! ### L1: Bug Existence -/

/-- Persian (Base Speed 115) using Slash (High Crit) reaches the 255 cap. -/
theorem persian_slash_threshold_maxed : 
    calcCritThreshold 115 true false = 255 := rfl

/-- Even with the maximum possible threshold, a roll of 255 results in failure. -/
theorem bug_exists : ∃ t r, impl t r = false ∧ spec t r = true :=
  ⟨255, 255, by native_decide⟩

/-! ### L2: Characterization -/

/-- The bug occurs if and only if the threshold is 255 and the roll is 255. -/
theorem bug_iff (t r : BitVec 8) : 
    impl t r ≠ spec t r ↔ (t = 255 ∧ r = 255) := by
  native_decide

/-- 
In any "guaranteed" scenario (t=255), there is exactly 1 value in the 
0-255 range that causes a miss.
-/
theorem one_in_256_chance : 
    (List.range 256).filter (λ r => !impl 255 (BitVec.ofNat 8 r)) = [255] := by
  native_decide

/-! ### L3: Fix Correctness -/

/-- 
A fix for the bug: use "less than or equal" logic. 
In assembly, this would involve checking the Zero flag or using a different 
comparison constant.
-/
def fix (t r : BitVec 8) : Bool :=
  r < t || (t == 255)

theorem fix_correct (t r : BitVec 8) : fix t r = spec t r := by
  have h := (by native_decide : ∀ t r : BitVec 8, fix t r = spec t r)
  exact h t r

/-! ### L4: CPU-Level Verification -/

/-- 
Verifies that the SM83 `cp` instruction indeed clears the carry flag (nc) 
when A (the roll) is equal to B (the threshold).
-/
theorem sm83_cp_logic_nc_on_equal : 
    ∀ (val : BitVec 8), 
      let s := SM83.defaultState.setA val |>.setB val
      let s' := SM83.execCp val s
      s'.cFlag = false := by
  intro val
  -- SM83: cp A, B clears carry if A >= B.
  -- Since A = B, A >= B is true, so Carry = 0.
  simp [SM83.execCp, SM83.CPUState.setA, SM83.CPUState.setB]
  cases val using BitVec.casesOn
  decide

/--
Demonstrates how the Focus Energy bug further reduces the threshold.
Instead of doubling the threshold, it halves it twice.
-/
theorem focus_energy_bug_effect (baseSpeed : BitVec 8) :
    calcCritThreshold baseSpeed false true < calcCritThreshold baseSpeed false false := by
  -- For base speed 100: 
  -- Without focus energy: (100/2)*2/2 = 50
  -- With focus energy bug: (100/2)/2/2 = 12
  native_decide

end AutoResearch
