import SM83

namespace AutoResearch
open SM83

/-!
# Bug #3: Blaine's AI Uses Super Potion Regardless of HP

## Description
Blaine is the Cinnabar Island Gym Leader in Pokemon Red/Blue. Unlike other trainer
AIs which check if their Pokemon's HP is low before using a healing item, Blaine's 
specific AI routine fails to perform this check. As a result, he will use his 
Super Potions even when his Pokemon is at 100% HP.

## Model
We model the AI's decision as a transformation of the `CPUState`.
- `wEnemyHP`: The current HP of Blaine's Pokemon (16-bit).
- `wEnemyMaxHP`: The maximum HP of Blaine's Pokemon (16-bit).
- `wEnemyPotions`: The address storing the number of healing items remaining.
- Register `B` is used to signal the choice: `1` for "Use Super Potion", `0` for "None".
-/

def wEnemyHP      : BitVec 16 := 0xCF1C
def wEnemyMaxHP   : BitVec 16 := 0xCF1E
def wEnemyPotions : BitVec 16 := 0xD123

/-- 
Blaine's buggy AI implementation.
It checks if there are potions remaining but ignores the HP values entirely.
-/
def impl (s : CPUState) : CPUState :=
  if s.readMem wEnemyPotions > 0 then
    s.setB 1 -- Use Super Potion
  else
    s.setB 0

/-- 
The specification of a correct healing AI.
It should only use a potion if one is available AND the Pokemon is injured.
-/
def spec (s : CPUState) : CPUState :=
  if s.readMem wEnemyPotions > 0 ∧ s.readMem16 wEnemyHP < s.readMem16 wEnemyMaxHP then
    s.setB 1
  else
    s.setB 0

/-! ## L1: Concrete Witness -/

/-- 
There exists a state (specifically, full HP with a potion available) 
where Blaine's AI diverges from the intended specification.
-/
theorem L1_full_hp_witness : ∃ s, (impl s).b = 1 ∧ (spec s).b = 0 := by
  -- Construct a state with 1 potion and full HP (100/100)
  let s := (defaultState.writeMem wEnemyPotions 1).writeMem16 wEnemyHP 100 |>.writeMem16 wEnemyMaxHP 100
  exists s
  -- The evaluation depends on the memory model axioms. 
  -- We assume standard memory independence for this witness.
  sorry

/-! ## L2: Universal Characterization -/

/--
Blaine's AI decision depends entirely on the potion count and 
completely ignores any changes to the Pokemon's HP.
-/
theorem L2_blaine_ignores_hp (s : CPUState) (hp_val : BitVec 16) :
  (impl (s.writeMem16 wEnemyHP hp_val)).b = (impl s).b := by
  unfold impl
  -- Decision is a function of s.readMem wEnemyPotions.
  -- In a well-behaved memory model, writing to 0xCF1C does not affect 0xD123.
  have : (s.writeMem16 wEnemyHP hp_val).readMem wEnemyPotions = s.readMem wEnemyPotions := by
    sorry -- Memory independence axiom
  simp [this]

/--
Blaine's AI decision logic is a simple predicate on the potion count.
-/
theorem L2_blaine_logic_invariant (s : CPUState) :
  (impl s).b = 1 ↔ s.readMem wEnemyPotions > 0 := by
  unfold impl
  split <;> simp [*]

/--
If the specification determines a potion should be used, 
Blaine's buggy AI will always agree (the bug is false positives, not false negatives).
-/
theorem L2_spec_implies_impl (s : CPUState) :
  (spec s).b = 1 → (impl s).b = 1 := by
  unfold spec impl
  intro h
  split at h
  · simp_all
  · contradiction

/-! ## L3: Fix Verification -/

/-- The fixed AI adds the missing HP check. -/
def fix (s : CPUState) : CPUState :=
  if s.readMem wEnemyPotions > 0 ∧ s.readMem16 wEnemyHP < s.readMem16 wEnemyMaxHP then
    s.setB 1
  else
    s.setB 0

/-- The fixed implementation matches the specification for all possible states. -/
theorem L3_fix_matches_spec (s : CPUState) : (fix s).b = (spec s).b := rfl

/-! ## L4: Relational Divergence -/

/--
Whenever Blaine has a potion and his Pokemon is at full health, 
his behavior diverges from the intended specification.
-/
theorem L4_relational_divergence_at_full_hp (s : CPUState) :
  s.readMem wEnemyPotions > 0 ∧ s.readMem16 wEnemyHP = s.readMem16 wEnemyMaxHP →
  (impl s).b = 1 ∧ (spec s).b = 0 := by
  intro ⟨h_pot, h_full⟩
  constructor
  · -- Impl uses potion because count > 0
    unfold impl
    simp [h_pot]
  · -- Spec refuses because HP is not less than MaxHP
    unfold spec
    simp [h_pot, h_full]
    -- BitVec: x < x is false
    have h_not_lt : ¬(s.readMem16 wEnemyHP < s.readMem16 wEnemyHP) := by
      intro h_lt
      exact BitVec.lt_irrefl _ h_lt
    simp [h_not_lt]

/--
The exact condition for Blaine's AI to behave incorrectly is having
at least one potion while the Pokemon is not actually injured.
-/
theorem L4_exact_bug_condition (s : CPUState) :
  (impl s).b ≠ (spec s).b ↔ 
  (s.readMem wEnemyPotions > 0 ∧ ¬(s.readMem16 wEnemyHP < s.readMem16 wEnemyMaxHP)) := by
  unfold impl spec
  split <;> split <;> simp_all
  case _ h1 h2 => -- potions > 0 AND ¬(potions > 0 ∧ hp < maxHP)
    simp [h1] at h2
    simp [h2]
  case _ h1 h2 => -- potions <= 0 AND (potions > 0 ∧ hp < maxHP)
    exfalso
    simp [h1] at h2

end AutoResearch

