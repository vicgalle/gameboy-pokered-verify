import SM83

namespace AutoResearch

-- Model Blaine's AI decision logic (engine/battle/trainer_ai.asm)
-- The assembly shows Blaine only checks a 25% random threshold before using a Potion.
-- ASM: BlaineAI: cp 25 percent + 1; ret nc; jp AIUseSuperPotion
def impl (rand : BitVec 8) (hp max : BitVec 16) : Bool :=
  rand < 64 -- 25% chance (approx)

-- Model the correct/intended behavior: AI should check if healing is actually needed.
-- Every other trainer AI uses AICheckIfHPBelowFraction before calling healing logic.
def spec (rand : BitVec 8) (hp max : BitVec 16) : Bool :=
  rand < 64 && hp < max

-- L1: Bug Exists
-- Prove Blaine will use a Potion even when his Pokemon is at full HP (100/100).
theorem bug_exists : ∃ r h m, impl r h m = true ∧ spec r h m = false :=
  ⟨0, 100, 100, by native_decide⟩

-- L2: Characterization - HP Independence
-- Prove that Blaine's decision is mathematically independent of the current HP value.
theorem bug_hp_invariant (r : BitVec 8) (h1 h2 m : BitVec 16) :
    impl r h1 m = impl r h2 m := by
  simp [impl]

-- L2: Characterization - Wasteful Behavior
-- Prove that if the random roll passes, Blaine ALWAYS uses the potion, even at max HP.
theorem bug_always_heals_if_roll_passes (r : BitVec 8) (m : BitVec 16) :
    r < 64 → impl r m m = true := by
  intro h; simp [impl, h]

-- L3: Fix Correctness
-- A fixed version would check both the random threshold and the HP status.
def fix (rand : BitVec 8) (hp max : BitVec 16) : Bool :=
  if rand < 64 then hp < max else false

theorem fix_is_correct (r : BitVec 8) (h m : BitVec 16) : 
    fix r h m = spec r h m := by
  unfold fix spec; split <;> simp_all

end AutoResearch
