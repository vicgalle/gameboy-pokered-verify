import SM83

namespace AutoResearch

/-
  Bug: Blaine's AI Uses Super Potion Regardless of HP
  
  In Pokémon Red/Blue, trainer AI logic for using items typically involves 
  two checks:
  1. A probability check (does the trainer "want" to use an item this turn?)
  2. A health check (does the active Pokémon "need" healing?)
  
  Blaine's AI (Trainer AI $1) specifically omits the health check, 
  leading to scenarios where he uses Super Potions on full-health Pokémon.
-/

/-- 
  The logical state of a Pokémon for AI decision making.
  - hp: current HP
  - maxHP: maximum HP
  - will_roll_item: whether the AI's internal probability check for using an item succeeded.
-/
structure BattleState where
  hp : Nat
  maxHP : Nat
  will_roll_item : Bool

/-- 
  The intended AI behavior (spec):
  Use the potion only if the AI wants to use an item AND the Pokémon's HP is below a threshold.
  In Gen 1, this threshold is usually HP < 25% or HP < 50%. We'll use maxHP / 2.
-/
def spec (s : BattleState) : Bool :=
  s.will_roll_item && (s.hp < s.maxHP / 2)

/-- 
  Blaine's buggy behavior (impl):
  Blaine only checks if the probability roll succeeded, ignoring the Pokémon's current health.
-/
def impl (s : BattleState) : Bool :=
  s.will_roll_item

/- L1: Proof of Existence
   There exists a state (specifically at full HP) where Blaine uses a potion
   but the standard AI logic would not.
-/
theorem bug_exists : ∃ s : BattleState, s.hp = s.maxHP ∧ s.maxHP > 0 ∧ s.will_roll_item = true ∧ impl s ≠ spec s := by
  let s : BattleState := ⟨100, 100, true⟩
  exists s
  simp [impl, spec]
  -- 100 < 100 / 2 is false
  have h : ¬(100 < 100 / 2) := by omega
  simp [h]

/- L2: Universal Characterization - Independence
   Blaine's decision is entirely independent of the Pokémon's current HP.
   This proves he "does not check whether his Pokemon actually needs healing".
-/
theorem blaine_ignores_hp (hp1 hp2 maxHP : Nat) (roll : Bool) :
  impl ⟨hp1, maxHP, roll⟩ = impl ⟨hp2, maxHP, roll⟩ := by
  simp [impl]

/- L2: Divergence condition
   Blaine and the Spec will always diverge whenever the roll is successful
   but the Pokémon is healthy (HP >= MaxHP / 2).
-/
theorem divergence_iff_healthy (s : BattleState) :
  s.will_roll_item = true → (s.hp ≥ s.maxHP / 2 ↔ impl s ≠ spec s) := by
  intro hroll
  simp [impl, spec, hroll]
  constructor
  · intro h_healthy
    simp [h_healthy]
    -- Since h_healthy is hp >= maxHP / 2, hp < maxHP / 2 is false.
    have h_not_lt : ¬(s.hp < s.maxHP / 2) := by omega
    simp [h_not_lt]
  · intro h_diff
    contrapose! h_diff
    -- If hp < maxHP / 2, then spec s is true, so impl s == spec s
    simp [h_diff]

/- L3: The Fix
   A fixed version of Blaine's AI that includes the HP check.
-/
def fix (s : BattleState) : Bool :=
  s.will_roll_item && (s.hp < s.maxHP / 2)

theorem fix_is_correct : ∀ s, fix s = spec s := by
  intro s; rfl

/- L4: Relational - Turn Advantage
   We model "wasted turns". A turn is wasted if a trainer uses a healing item
   on a Pokémon that is already at full HP.
-/
def is_turn_wasted (s : BattleState) (uses_item : Bool) : Bool :=
  uses_item && (s.hp == s.maxHP) && (s.maxHP > 0)

theorem blaine_wastes_turns :
  ∀ s, (s.hp = s.maxHP ∧ s.maxHP > 0 ∧ s.will_roll_item = true) → 
  is_turn_wasted s (impl s) = true := by
  intro s h
  rcases h with ⟨h_full, h_pos, h_roll⟩
  simp [is_turn_wasted, impl, h_full, h_pos, h_roll]

theorem spec_never_wastes_turns :
  ∀ s, is_turn_wasted s (spec s) = false := by
  intro s
  simp [is_turn_wasted, spec]
  by_cases h_roll : s.will_roll_item
  · simp [h_roll]
    by_cases h_full : s.hp = s.maxHP
    · -- If full HP, hp < maxHP / 2 must be false for maxHP > 0
      simp [h_full]
      intro h_pos
      omega
    · simp [h_full]
  · simp [h_roll]

end AutoResearch
