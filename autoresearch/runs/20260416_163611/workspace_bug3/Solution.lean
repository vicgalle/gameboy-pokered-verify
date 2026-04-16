import SM83

namespace AutoResearch

/-
  Bug #3: Blaine AI Super Potion Bug

  Gameplay Description:
  Blaine, the Gym Leader of Cinnabar Island, uses a Super Potion on his Pokémon
  whenever his AI internal "item roll" succeeds. Unlike other trainers, his logic
  omits the health check, causing him to use the item even if his Pokémon is 
  at full HP.

  Technical details:
  - Trainer AI $1 (Blaine) is supposed to check HP before using a healing item.
  - Due to a programming oversight, the code branch for Blaine bypasses the
    routine that compares Current HP against a threshold (usually < 25% or < 50%).
-/

/-- 
  Represents the state of Blaine's Pokémon during a turn.
  - hp: Current health points.
  - maxHP: Maximum health points.
  - will_roll_item: Internal probability check (does Blaine "want" to use an item?).
-/
structure BattleState where
  hp : Nat
  maxHP : Nat
  will_roll_item : Bool
  deriving DecidableEq

/-- 
  The intended AI behavior (spec):
  The AI should only use a Super Potion if the roll is successful AND
  the Pokémon's HP is below a specific threshold (we model this as 50% HP).
-/
def spec (s : BattleState) : Bool :=
  s.will_roll_item && (s.hp < s.maxHP / 2)

/-- 
  Blaine's buggy behavior (impl):
  Blaine uses the item whenever the roll is successful, completely 
  ignoring the Pokémon's current health.
-/
def impl (s : BattleState) : Bool :=
  s.will_roll_item

/- --- L1: Existence of the Bug --- -/

/-- 
  There exists a scenario where Blaine uses a potion on a full-health 
  Pokémon, whereas the specification dictates he should not.
-/
theorem exists_bug_at_full_hp : ∃ s : BattleState, 
  s.hp = s.maxHP ∧ s.maxHP > 0 ∧ s.will_roll_item = true ∧ impl s ≠ spec s := by
  let s : BattleState := ⟨100, 100, true⟩
  exists s
  simp [impl, spec]
  -- 100 < 100 / 2 is 100 < 50, which is false.
  have h : ¬(100 < 100 / 2) := by omega
  simp [h]

/- --- L2: Universal Characterization --- -/

/-- 
  Characterization: Blaine's AI is "HP-blind".
  Given the same roll, his decision is identical regardless of current HP.
-/
theorem blaine_is_hp_blind (hp1 hp2 maxHP : Nat) (roll : Bool) :
  impl ⟨hp1, maxHP, roll⟩ = impl ⟨hp2, maxHP, roll⟩ := by
  simp [impl]

/--
  Characterization: Blaine and the Spec diverge if and only if the roll
  is successful but the Pokémon is "healthy" (HP ≥ 50%).
-/
theorem divergence_condition (s : BattleState) :
  impl s ≠ spec s ↔ (s.will_roll_item = true ∧ s.hp ≥ s.maxHP / 2) := by
  simp [impl, spec]
  by_cases h_roll : s.will_roll_item
  · simp [h_roll]
    -- We want to prove ¬(hp < maxHP/2) ↔ hp >= maxHP/2
    constructor
    · intro h; omega
    · intro h; omega
  · simp [h_roll]

/- --- L3: The Fix --- -/

/-- 
  The corrected logic for Blaine's AI, incorporating the missing health check.
-/
def fix (s : BattleState) : Bool :=
  s.will_roll_item && (s.hp < s.maxHP / 2)

theorem fix_matches_spec : ∀ s, fix s = spec s := by
  intro s; rfl

/- --- L4: Relational Analysis & Efficiency --- -/

/-- 
  Model of "Effective Healing". 
  A Super Potion restores up to 50 HP, capped at Max HP.
-/
def effective_healing (s : BattleState) (use_item : Bool) : Nat :=
  if use_item then
    let new_hp := Nat.min s.maxHP (s.hp + 50)
    new_hp - s.hp
  else 0

/-- 
  Blaine can perform an action that results in zero effective healing 
  despite consuming the item.
-/
theorem blaine_zero_healing_on_full :
  ∀ s, (s.hp = s.maxHP ∧ s.will_roll_item = true) → 
  (impl s = true ∧ effective_healing s (impl s) = 0) := by
  intro s ⟨h_full, h_roll⟩
  simp [impl, effective_healing, h_full, h_roll]

/--
  The specification never uses an item if it would result in zero effective healing
  (assuming maxHP > 0, since a 0 HP Pokémon is fainted and cannot be active).
-/
theorem spec_always_heals_effectively :
  ∀ s, s.maxHP > 1 → spec s = true → effective_healing s (spec s) > 0 := by
  intro s h_pos h_spec
  simp [spec] at h_spec
  match h_spec with
  | ⟨_, h_hp_low⟩ =>
    simp [effective_healing, h_spec.1, h_spec.2]
    -- Since hp < maxHP / 2 and maxHP > 1, then hp < maxHP.
    have h_lt : s.hp < s.maxHP := by
      have h1 : s.maxHP / 2 < s.maxHP := by omega
      exact Nat.lt_trans h_hp_low h1
    -- Since hp < maxHP, Nat.min s.maxHP (s.hp + 50) is at least hp + 1
    have h_min : Nat.min s.maxHP (s.hp + 50) > s.hp := by
      apply Nat.lt_min
      · exact h_lt
      · omega
    omega

/--
  Formally define a "Wasted Turn" as using a healing item when already at full HP.
-/
def is_wasted_turn (s : BattleState) (action : Bool) : Prop :=
  action = true ∧ s.hp = s.maxHP ∧ s.maxHP > 0

theorem blaine_can_waste_turn : ∃ s, is_wasted_turn s (impl s) := by
  exists ⟨100, 100, true⟩
  simp [is_wasted_turn, impl]

theorem spec_never_wastes_turn : ∀ s, ¬is_wasted_turn s (spec s) := by
  intro s
  simp [is_wasted_turn, spec]
  intro h_roll h_hp_low h_full h_max_pos
  -- Contradiction: hp < maxHP/2 and hp = maxHP
  rw [h_full] at h_hp_low
  -- maxHP < maxHP / 2 is impossible for maxHP > 0
  omega

end AutoResearch
