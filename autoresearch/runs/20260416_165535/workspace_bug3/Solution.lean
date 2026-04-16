import SM83

namespace AutoResearch

/-
  Bug: Blaine's AI Uses Super Potion Regardless of HP.
  
  In Pokémon Red/Blue, trainer AI routines generally check if a Pokémon's 
  health is low before using a healing item. However, Blaine's AI routine 
  omits this check, leading him to use a Super Potion even if his 
  Pokémon is at full health.
-/

/--
  Blaine's buggy AI implementation.
  - `hp`: The current health of the Pokémon.
  - `maxHp`: The maximum health of the Pokémon.
  - `trigger`: A boolean representing the probabilistic chance that the AI logic 
    selects the item-use routine.
-/
def impl (hp maxHp : BitVec 8) (trigger : Bool) : Bool :=
  -- The bug: Blaine ignores HP and uses the item whenever the routine triggers.
  trigger

/--
  The intended AI behavior (the Specification).
  The AI should only use the item if the routine triggers AND the health 
  is below a threshold (in this case, "not full").
-/
def spec (hp maxHp : BitVec 8) (trigger : Bool) : Bool :=
  trigger && (hp < maxHp)

/-- L1: Concrete witness of the bug.
  When the AI routine triggers and HP is full, Blaine heals while the spec does not.
-/
theorem bug_exists : ∃ hp maxHp trigger, impl hp maxHp trigger ≠ spec hp maxHp trigger :=
  ⟨100, 100, true, by native_decide⟩

/-- L2: Universal property of Blaine's AI.
  Blaine's action is entirely independent of the Pokémon's health state.
-/
theorem blaine_ignores_health : ∀ hp1 hp2 maxHp : BitVec 8, ∀ trigger : Bool, 
  impl hp1 maxHp trigger = impl hp2 maxHp trigger := by
  intro hp1 hp2 maxHp trigger
  simp [impl]

/-- L2: Safety property of the Specification.
  The intended behavior (spec) never uses a potion if the Pokémon is at full HP.
-/
theorem spec_safe_at_full_hp : ∀ hp maxHp : BitVec 8, hp ≥ maxHp → spec hp maxHp true = false := by
  intro hp maxHp h
  have := (by native_decide : ∀ h1 h2 : BitVec 8, h1 ≥ h2 → (true && (h1 < h2)) = false)
  exact this hp maxHp h

/-- L3: The Fix.
  The fixed implementation incorporates the missing HP check.
-/
def fix (hp maxHp : BitVec 8) (trigger : Bool) : Bool :=
  trigger && (hp < maxHp)

theorem fix_matches_spec : ∀ hp maxHp : BitVec 8, ∀ trigger : Bool, fix hp maxHp trigger = spec hp maxHp trigger := by
  intro hp maxHp trigger
  rfl

/-- L4: Relational Divergence.
  Blaine and the Spec diverge if and only if the AI trigger occurs while health is full (or higher).
-/
theorem divergence_iff_wasteful_trigger : ∀ hp maxHp : BitVec 8, ∀ trigger : Bool,
  (impl hp maxHp trigger ≠ spec hp maxHp trigger) ↔ (trigger = true ∧ hp ≥ maxHp) := by
  intro hp maxHp trigger
  have := (by native_decide : ∀ h1 h2 : BitVec 8, ∀ t : Bool, (t ≠ (t && (h1 < h2))) ↔ (t = true ∧ h1 ≥ h2))
  exact this hp maxHp trigger

/-- L4: Player Advantage.
  At full HP, Blaine performs a useless action (impl = true) whereas the spec 
  (representing every other competent trainer AI) would skip it (spec = false).
-/
theorem blaine_wasted_turn : ∀ hp maxHp : BitVec 8, 
  hp = maxHp → (impl hp maxHp true = true ∧ spec hp maxHp true = false) := by
  intro hp maxHp h
  have := (by native_decide : ∀ h1 h2 : BitVec 8, h1 = h2 → (true = true ∧ (true && (h1 < h2)) = false))
  exact this hp maxHp h

/-- L2: Rationality of Spec.
  The specification only allows action if the Pokémon is damaged.
-/
theorem spec_rationality : ∀ hp maxHp : BitVec 8, ∀ trigger : Bool,
  spec hp maxHp trigger = true → hp < maxHp := by
  intro hp maxHp trigger h
  have := (by native_decide : ∀ h1 h2 : BitVec 8, ∀ t : Bool, (t && (h1 < h2)) = true → h1 < h2)
  exact this hp maxHp trigger h

end AutoResearch
