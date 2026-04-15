import SM83

namespace AutoResearch

-- Model Blaine's AI (engine/battle/trainer_ai.asm)
-- The assembly jump to AIUseSuperPotion happens immediately after the roll check.
def impl (rand : BitVec 8) (hp max : BitVec 16) : Bool :=
  rand < 65 -- 25% chance

-- Intended behavior: Items should only be used if current HP is strictly less than Max HP.
-- Other AIs call AICheckIfHPBelowFraction, which Blaine skips.
def spec (rand : BitVec 8) (hp max : BitVec 16) : Bool :=
  (rand < 65) && (hp < max)

-- L1: Bug Existence
-- Witness: At full HP (100/100), Blaine still uses the potion on a successful roll.
theorem bug_exists : ∃ r h m, impl r h m = true ∧ spec r h m = false :=
  ⟨0, 100, 100, by native_decide⟩

-- L2: Characterization - State Independence
-- The buggy implementation is entirely independent of the Pokemon's current health.
theorem bug_hp_independence (r : BitVec 8) (h1 h2 m : BitVec 16) :
  impl r h1 m = impl r h2 m := rfl

-- L2: Characterization - Trigger Logic
-- The bug occurs if and only if the AI rolls to heal but the target is already at full health.
theorem bug_trigger_logic (r : BitVec 8) (h m : BitVec 16) :
  (impl r h m = true ∧ spec r h m = false) ↔ (r < 65 ∧ h ≥ m) := by
  unfold impl spec
  constructor
  . intro h_and; simp_all
  . intro h_cond; simp_all

-- L3: Fix Correctness
-- The fix integrates the HP check (AICheckIfHPBelowFraction proxy) before usage.
def fix (r : BitVec 8) (h m : BitVec 16) : Bool := (r < 65) && (h < m)

theorem fix_is_spec (r : BitVec 8) (h m : BitVec 16) :
  fix r h m = spec r h m := rfl

-- L4: Relational - Soundness
-- The fixed AI never heals when the Pokemon is at full health.
theorem fix_safe_at_full_hp (r : BitVec 8) (m : BitVec 16) :
  fix r m m = false := by
  unfold fix; split <;> simp_all

-- L4: Relational - Completeness
-- The fixed AI still performs the heal if the roll succeeds and HP is low.
theorem fix_preserves_valid_healing (r : BitVec 8) (h m : BitVec 16) :
  r < 65 → h < m → fix r h m = true := by
  intros; simp [fix, *]

-- L4: Item Conservation
-- Proves that the fix uses items in a strictly subset of cases compared to the bug.
theorem fix_is_strictly_more_conservative (r : BitVec 8) (h m : BitVec 16) :
  fix r h m → impl r h m := by
  unfold fix impl; intro h_fix; simp_all

-- L4: Waste Probability
-- At full health, the probability of Blaine wasting a potion is exactly 65/256.
theorem blaine_waste_rate (r : BitVec 8) (m : BitVec 16) :
  impl r m m = true ↔ r < 65 := by rfl

end AutoResearch
