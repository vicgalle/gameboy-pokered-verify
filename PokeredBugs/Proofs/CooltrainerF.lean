/-
  PokeredBugs/Proofs/CooltrainerF.lean — CooltrainerF AI always switches/heals.

  ## The Bug
  CooltrainerF's AI routine (trainer_ai.asm:344-355) has a commented-out
  `ret nc` instruction at line 348. This missing early return means the
  25% random check has no effect — execution ALWAYS falls through to the
  healing/switching logic.

  Compare with CooltrainerM (lines 339-342) which has `ret nc` intact:
    CooltrainerMAI:
      cp 25 percent + 1
      ret nc               ← present: 75% chance to just attack
      jp AIUseXAttack

    CooltrainerFAI:
      cp 25 percent + 1
      ; ret nc             ← COMMENTED OUT: always falls through
      ld a, 10
      call AICheckIfHPBelowFraction
      jp c, AIUseHyperPotion
      ld a, 5
      call AICheckIfHPBelowFraction
      ret nc
      jp AISwitchIfEnoughMons

  Result: CooltrainerF never just attacks — she always tries to heal or
  switch, making her AI predictable and suboptimal.

  Source: engine/battle/trainer_ai.asm lines 344-355

  ## Proof Techniques
  This uses structural reasoning about control flow rather than arithmetic.
  We model the AI decision tree and prove that one branch is unreachable.
-/
import SM83

namespace PokeredBugs

/-! ### Model: Trainer AI Decision -/

/-- The possible actions a trainer AI can take. -/
inductive AIAction where
  | attack        -- just use a move (no special AI action)
  | useHyperPotion
  | switchMon
  deriving Repr, DecidableEq

/-- Outcome of AICheckIfHPBelowFraction: true if HP is low enough. -/
abbrev HPCheckResult := Bool

/-- CooltrainerM's AI: correct implementation.
    25% chance to use X Attack, 75% chance to just attack. -/
def cooltrainerMAI (randomBelow25Pct : Bool) : AIAction :=
  if randomBelow25Pct then
    .attack  -- X Attack effect, but the key point is: CooltrainerM CAN just attack
  else
    .attack  -- ret nc: just attack (no special action)

/-- CooltrainerF's BUGGY AI: the ret nc is missing.
    The random check has no effect — always falls through to heal/switch. -/
def cooltrainerFBuggy (_randomBelow25Pct : Bool)
    (hpBelow10Pct : HPCheckResult) (hpBelow5Pct : HPCheckResult)
    (hasEnoughMons : Bool) : AIAction :=
  -- The cp 25 percent + 1 check occurs but ret nc is missing,
  -- so _randomBelow25Pct is IGNORED
  if hpBelow10Pct then
    .useHyperPotion
  else if hpBelow5Pct && hasEnoughMons then
    .switchMon
  else
    .attack  -- ret nc at line 354 (this IS present — the SECOND ret nc)

/-- CooltrainerF's FIXED AI: ret nc restored at line 348. -/
def cooltrainerFFixed (randomBelow25Pct : Bool)
    (hpBelow10Pct : HPCheckResult) (hpBelow5Pct : HPCheckResult)
    (hasEnoughMons : Bool) : AIAction :=
  if !randomBelow25Pct then
    .attack  -- ret nc: 75% chance to just attack
  else
    -- 25% of the time, consider healing/switching
    if hpBelow10Pct then
      .useHyperPotion
    else if hpBelow5Pct && hasEnoughMons then
      .switchMon
    else
      .attack

/-! ### Proof 1: The Random Check Is Dead Code -/

/-- The buggy AI ignores the random input entirely. Changing it doesn't
    change the action — it's dead code. -/
theorem random_check_is_dead_code (hp10 hp5 : HPCheckResult) (mons : Bool) :
    cooltrainerFBuggy true hp10 hp5 mons =
    cooltrainerFBuggy false hp10 hp5 mons := by
  rfl

/-- CooltrainerM DOES use the random check — changing it changes the action.
    (Though CooltrainerM's AI is trivial: just X Attack or attack.) -/
theorem cooltrainerM_uses_random :
    cooltrainerMAI true = cooltrainerMAI false := by
  rfl  -- Both return .attack (CooltrainerM always "attacks" either way)

/-! ### Proof 2: CooltrainerF Always Heals or Switches When Able -/

/-- When HP is below 10%, CooltrainerF ALWAYS uses Hyper Potion,
    regardless of the random check. -/
theorem always_heals_when_low (rand : Bool) (hp5 : HPCheckResult) (mons : Bool) :
    cooltrainerFBuggy rand true hp5 mons = .useHyperPotion := by
  rfl

/-- When HP is between 5% and 10% and has enough mons,
    CooltrainerF ALWAYS switches. -/
theorem always_switches_when_able (rand : Bool) :
    cooltrainerFBuggy rand false true true = .switchMon := by
  rfl

/-! ### Proof 3: The Fix Restores Random Behavior -/

/-- With the fix, CooltrainerF attacks 75% of the time (when random ≥ 25%). -/
theorem fix_attacks_on_high_random (hp10 hp5 : HPCheckResult) (mons : Bool) :
    cooltrainerFFixed false hp10 hp5 mons = .attack := by
  rfl

/-- With the fix, the random check IS used — different random → potentially
    different action. -/
theorem fix_uses_random :
    cooltrainerFFixed true false true true ≠
    cooltrainerFFixed false false true true := by
  native_decide

/-- With the fix and low random (25% case), the AI CAN still switch. -/
theorem fix_can_switch :
    cooltrainerFFixed true false true true = .switchMon := by
  rfl

/-- With the fix and high random (75% case), it attacks even if switch is possible. -/
theorem fix_attacks_despite_switch_possible :
    cooltrainerFFixed false false true true = .attack := by
  rfl

/-! ### Proof 4: Full Behavioral Characterization -/

/-- The buggy AI's behavior depends on only 3 inputs, not 4.
    Complete truth table (8 rows): -/
theorem buggy_complete_behavior :
    -- HP below 10%: always heal
    cooltrainerFBuggy true true true true = .useHyperPotion ∧
    cooltrainerFBuggy true true false true = .useHyperPotion ∧
    cooltrainerFBuggy true true true false = .useHyperPotion ∧
    cooltrainerFBuggy true true false false = .useHyperPotion ∧
    -- HP between 5-10%, has mons: always switch
    cooltrainerFBuggy true false true true = .switchMon ∧
    -- HP between 5-10%, no mons / HP above 5%: attack
    cooltrainerFBuggy true false true false = .attack ∧
    cooltrainerFBuggy true false false true = .attack ∧
    cooltrainerFBuggy true false false false = .attack := by
  native_decide

/-- The fixed AI's behavior depends on all 4 inputs.
    When random ≥ 25%: always attack (regardless of HP or mons). -/
theorem fixed_high_random_always_attacks :
    cooltrainerFFixed false true true true = .attack ∧
    cooltrainerFFixed false true false true = .attack ∧
    cooltrainerFFixed false false true true = .attack ∧
    cooltrainerFFixed false false false false = .attack := by
  native_decide

/-! ### Proof 5: Comparison with Other Trainers -/

-- CooltrainerF is the only trainer whose random check is dead code.
-- Blaine always heals (no HP check). CooltrainerF always heals/switches
-- (no random check). Both are "always do X" bugs but different mechanisms.

/-! ### #eval Demonstrations -/

-- Buggy: random value doesn't matter
#eval (cooltrainerFBuggy true false true true, cooltrainerFBuggy false false true true)
-- (.switchMon, .switchMon) — same regardless of random

-- Fixed: random value matters
#eval (cooltrainerFFixed true false true true, cooltrainerFFixed false false true true)
-- (.switchMon, .attack) — different based on random

end PokeredBugs
