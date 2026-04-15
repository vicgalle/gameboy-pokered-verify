import SM83

namespace AutoResearch

/-
  Bug: Blaine's AI Uses Super Potion Regardless of HP
  
  In Pokemon Red/Blue, the AI for trainer Blaine (Cinnabar Gym Leader) contains 
  a logic error where it invokes the Super Potion healing routine based 
  only on a random roll (approx 25% chance), skipping the standard 
  HP-threshold check used by other trainer AI.
-/

/--
  Represents the state of a trainer's active Pokemon relevant to the AI decision.
  In the SM83 engine, HP values are 16-bit (Big Endian in memory).
-/
structure TrainerState where
  hp : BitVec 16
  maxHP : BitVec 16
  roll : BitVec 8

/--
  The actual implementation in Pokemon Red (engine/battle/trainer_ai.asm).
  BlaineAI:
    cp 25 percent + 1 ; Compare random roll to ~25% (64)
    ret nc            ; If roll >= 64, exit
    jp AIUseSuperPotion ; Otherwise, use potion (NO HP CHECK)
-/
def impl (s : TrainerState) : Bool :=
  s.roll < 64

/--
  The intended behavior (Specification).
  AI should check if the random roll succeeds AND if the Pokemon's current HP 
  is below a specific threshold (e.g., 50% or 1/2 of max HP).
-/
def spec (s : TrainerState) : Bool :=
  s.roll < 64 && (s.hp.toNat < s.maxHP.toNat / 2)

-- L1: Bug Existence
-- We provide a concrete witness: A Pokemon at full HP where the random roll 
-- succeeds (roll = 0). Blaine uses the potion, but the spec says he shouldn't.
theorem bug_exists : ∃ s, impl s = true ∧ spec s = false := by
  let s : TrainerState := { hp := 100, maxHP := 100, roll := 0 }
  exists s
  simp [impl, spec]
  -- 0 < 64 is true; 100 < 100/2 is false.
  decide

-- L2: Universal Characterization
-- This theorem proves that Blaine's AI decision is completely independent 
-- of the Pokemon's current HP, which is the core of the bug.
theorem blaine_ignores_health (hp1 hp2 : BitVec 16) (maxHP : BitVec 16) (roll : BitVec 8) :
    impl ⟨hp1, maxHP, roll⟩ = impl ⟨hp2, maxHP, roll⟩ := by
  simp [impl]

-- L3: Fix Correctness
-- To fix the bug, the AI must call a health check (like AICheckIfHPBelowFraction)
-- before committing to using the item.
def fix (s : TrainerState) : Bool :=
  if s.hp.toNat < s.maxHP.toNat / 2 then impl s else false

theorem fix_matches_spec (s : TrainerState) : fix s = spec s := by
  unfold fix spec impl
  split
  · simp [*]
  · simp_all

-- L4: Behavioral Divergence
-- Prove that whenever the Pokemon is at full HP and the roll succeeds, 
-- Blaine's AI is guaranteed to diverge from the correct specification.
theorem bug_triggers_at_full_hp (s : TrainerState) :
    s.hp = s.maxHP ∧ s.maxHP.toNat > 0 ∧ s.roll < 64 → impl s ≠ spec s := by
  intro h
  simp [impl, spec, h.1, h.2.2]
  -- At full HP (hp = maxHP > 0), hp < hp/2 is always false.
  have h_not_low : ¬(s.maxHP.toNat < s.maxHP.toNat / 2) := by
    have h_pos : s.maxHP.toNat > 0 := h.2.1
    omega
  simp [h_not_low]

end AutoResearch
