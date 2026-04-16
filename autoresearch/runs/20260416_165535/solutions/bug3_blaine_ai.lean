import SM83

namespace AutoResearch

/-
  Bug: Blaine's AI Uses Super Potion Regardless of HP.
  In Pokémon Red/Blue, Blaine's AI routine for using a Super Potion fails to check
  the current HP of his Pokémon. While every other trainer AI that uses healing 
  items checks if their Pokémon's HP is below a threshold (or simply not full), 
  Blaine's logic triggers the use of the item regardless of the health state.
  This allows Blaine to waste a Super Potion even when his Pokémon is at full HP.
-/

/--
Blaine's buggy AI implementation.
- `hp`: Current health points.
- `maxHp`: Maximum health points.
- `ai_trigger`: A boolean representing the probabilistic decision of the AI to attempt item use.
-/
def impl (hp maxHp : BitVec 8) (ai_trigger : Bool) : Bool :=
  -- The bug: Blaine uses the item if the AI logic triggers, ignoring HP.
  ai_trigger

/--
Standard AI Specification (Correct).
The AI should only use a healing item if the trigger occurs AND the health is not full.
-/
def spec (hp maxHp : BitVec 8) (ai_trigger : Bool) : Bool :=
  ai_trigger && (hp.toNat < maxHp.toNat)

/-- L1: Concrete witness of the bug.
At full HP (e.g., 50/50), if the AI logic is triggered, Blaine uses the potion 
whereas the spec does not.
-/
theorem bug_exists : ∃ hp maxHp ai_trigger, impl hp maxHp ai_trigger ≠ spec hp maxHp ai_trigger :=
  ⟨50, 50, true, by native_decide⟩

/-- L2: Universal property of Blaine's AI.
Blaine always uses the potion if the move-selection logic triggers, regardless of health.
-/
theorem blaine_always_ignores_hp : ∀ hp maxHp : BitVec 8, impl hp maxHp true = true := by
  intro hp maxHp
  simp [impl]

/-- L2: Property of the spec AI.
The spec never uses a potion if the Pokémon is already at full health (or above).
-/
theorem spec_never_wastes_at_full_hp : ∀ hp maxHp : BitVec 8, hp.toNat ≥ maxHp.toNat → spec hp maxHp true = false := by
  intro hp maxHp h
  -- Using native_decide for exhaustive verification of the BitVec logic.
  have h_spec := (by native_decide : ∀ h1 h2 : BitVec 8, h1.toNat ≥ h2.toNat → spec h1 h2 true = false)
  exact h_spec hp maxHp h

/-- L3: The Fix.
A fixed implementation matches the specification by incorporating an HP check.
-/
def fix (hp maxHp : BitVec 8) (ai_trigger : Bool) : Bool :=
  ai_trigger && (hp.toNat < maxHp.toNat)

theorem fix_is_correct : ∀ hp maxHp ai_trigger, fix hp maxHp ai_trigger = spec hp maxHp ai_trigger := by
  intro hp maxHp ai_trigger
  rfl

/-- L4: Relational Divergence.
Blaine's behavior and the intended behavior diverge specifically when 
the Pokémon does not need healing (hp >= maxHp) and the AI logic is triggered.
-/
theorem blaine_spec_divergence_iff : ∀ hp maxHp : BitVec 8,
  (impl hp maxHp true ≠ spec hp maxHp true) ↔ (hp.toNat ≥ maxHp.toNat) := by
  intro hp maxHp
  have h_div := (by native_decide : ∀ h1 h2 : BitVec 8, (impl h1 h2 true ≠ spec h1 h2 true) ↔ (h1.toNat ≥ h2.toNat))
  exact h_div hp maxHp

/-- L4: Waste characterization.
At full health, Blaine uses a potion (impl = true) while the spec would not (spec = false).
-/
theorem blaine_wastes_potion_at_full_hp : ∀ hp maxHp : BitVec 8,
  hp.toNat = maxHp.toNat → (impl hp maxHp true = true ∧ spec hp maxHp true = false) := by
  intro hp maxHp h
  have h_waste := (by native_decide : ∀ h1 h2 : BitVec 8, h1.toNat = h2.toNat → (impl h1 h2 true = true ∧ spec h1 h2 true = false))
  exact h_waste hp maxHp h

end AutoResearch

