import SM83

namespace AutoResearch

/-!
# Bug: Blaine's AI Uses Super Potion Regardless of HP

Blaine's AI in Pokemon Red/Blue (Cinnabar Gym) is programmed to use Super Potions
with a ~25% probability. However, unlike other trainers, the code fails to call
`AICheckIfHPBelowFraction` (or any HP check), causing Blaine to use potions even
when his Pokémon is at full health.

Assembly logic for Blaine:
BlaineAI:
    cp 25 percent + 1  ; Check random roll
    ret nc             ; If roll >= 64, exit
    jp AIUseSuperPotion ; Use potion (OMITS HP CHECK)
-/

/-- Represents relevant battle state for the AI decision. -/
structure BattleState where
  currHP : BitVec 16
  maxHP : BitVec 16
  randomRoll : BitVec 8

/--
  Model of the buggy implementation.
  The assembly `cp 25 percent + 1` followed by `ret nc` means the AI proceeds
  if `randomRoll < 64` (25% of 256).
-/
def impl (s : BattleState) : Bool :=
  s.randomRoll < 64

/--
  Model of the intended behavior.
  Trainers should check if current HP is below a threshold (usually 1/2 or 1/3)
  before attempting to use a healing item.
-/
def spec (s : BattleState) : Bool :=
  let hp_low := s.currHP.toNat < (s.maxHP.toNat / 2)
  (s.randomRoll < 64) && hp_low

/-- L1: Bug exists - A witness at full HP where the AI uses the potion incorrectly. -/
theorem bug_exists : ∃ s, impl s = true ∧ spec s = false := by
  -- At full health (100/100), HP is not below 50%.
  let s : BattleState := { currHP := 100, maxHP := 100, randomRoll := 0 }
  exists s
  simp [impl, spec]
  native_decide

/-- L2: Independence - Blaine's AI decision is completely independent of HP. -/
theorem blaine_ignores_hp (roll : BitVec 8) (hp1 hp2 max1 max2 : BitVec 16) :
    impl ⟨hp1, max1, roll⟩ = impl ⟨hp2, max2, roll⟩ := by
  simp [impl]

/-- L3: Fix Correctness - Integrating the HP check into the AI logic matches spec. -/
def fixed_ai (s : BattleState) : Bool :=
  let hp_low := s.currHP.toNat < (s.maxHP.toNat / 2)
  if hp_low then impl s else false

theorem fixed_ai_is_spec (s : BattleState) : fixed_ai s = spec s := by
  unfold fixed_ai spec impl
  split <;> simp [*]

/-- L4: Universal Bug Condition - Characterize exactly when the bug triggers. -/
theorem bug_trigger_iff (s : BattleState) :
    impl s ≠ spec s ↔ (s.randomRoll < 64 ∧ s.currHP.toNat ≥ s.maxHP.toNat / 2) := by
  unfold impl spec
  constructor
  · intro h
    cases h_roll : s.randomRoll < 64
    · simp [h_roll] at h -- If roll >= 64, both are false, contradiction
    · simp [h_roll] at h
      simp [h_roll]
      omega
  · intro h
    simp [h.1]
    have h_hp : ¬(s.currHP.toNat < s.maxHP.toNat / 2) := by omega
    simp [h_hp]

/-- L4: Extreme Case - Blaine always wastes a turn if at full HP and roll succeeds. -/
theorem blaine_wastes_potion_at_full_hp (s : BattleState) :
    s.currHP = s.maxHP ∧ s.maxHP.toNat > 0 ∧ s.randomRoll < 64 →
    impl s = true ∧ spec s = false := by
  intro ⟨h_full, h_pos, h_roll⟩
  constructor
  · simp [impl, h_roll]
  · simp [spec, h_roll, h_full]
    omega

end AutoResearch
