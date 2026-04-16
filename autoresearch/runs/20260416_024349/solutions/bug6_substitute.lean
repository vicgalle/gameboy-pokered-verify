import SM83

namespace AutoResearch

/-!
# Substitute Move Bugs in Pokémon Red

Two bugs in SubstituteEffect_:
- Bug 1: `maxHP / 4` truncates to 0 for maxHP ∈ {1,2,3}, creating a 0-HP substitute for free
- Bug 2: Only the carry flag is checked (underflow), not whether result = 0.
         When currentHP = maxHP/4, the user survives at exactly 0 HP.
-/

-- Substitute HP cost: maxHP / 4 via two logical right shifts (srl; rr; srl; rr in assembly)
-- Assumes maxHP ≤ 1023 so result fits in 8 bits (per assembly comment)
def substituteHP (maxHP : BitVec 8) : BitVec 8 :=
  maxHP >>> 2

-- Buggy implementation — mirrors the assembly's carry-only check:
-- succeeds whenever currentHP >= cost (no carry/underflow), even if result = 0
def impl (maxHP : BitVec 8) (currentHP : BitVec 8) : Option (BitVec 8) :=
  let cost := substituteHP maxHP
  if currentHP.toNat >= cost.toNat then
    some (currentHP - cost)
  else
    none

-- Correct specification:
-- (1) cost must be > 0 (fixes Bug 1: no zero-HP substitutes)
-- (2) currentHP must be strictly greater than cost (fixes Bug 2: no zero-HP user)
def spec (maxHP : BitVec 8) (currentHP : BitVec 8) : Option (BitVec 8) :=
  let cost := substituteHP maxHP
  if 0 < cost.toNat && cost.toNat < currentHP.toNat then
    some (currentHP - cost)
  else
    none

-- ===== L1: Concrete Witnesses =====

-- Bug 2: maxHP=8, currentHP=2 (exactly maxHP/4).
-- impl creates the substitute, leaving user at 0 HP.
theorem l1_bug2_zero_hp_user : impl 8 2 = some 0 := by native_decide

-- Spec correctly rejects this case (would leave user at 0 HP)
theorem l1_spec_rejects_zero_hp : spec 8 2 = none := by native_decide

-- Bug 1: maxHP=2, substituteHP=0.
-- The substitute has 0 HP and costs the user nothing.
theorem l1_bug1_zero_cost : substituteHP 2 = 0 := by native_decide

-- impl still "creates" the substitute, leaving the user's HP unchanged
theorem l1_bug1_impl_free_substitute : impl 2 100 = some 100 := by native_decide

-- ===== L2: Universal Characterizations =====

-- Bug 2 triggers exactly when currentHP equals the cost (result is precisely 0)
theorem l2_bug2_trigger : ∀ maxHP currentHP : BitVec 8,
    impl maxHP currentHP = some 0 ↔ currentHP = substituteHP maxHP := by native_decide

-- Bug 1 triggers exactly when maxHP < 4 (cost rounds to zero)
theorem l2_bug1_trigger : ∀ maxHP : BitVec 8,
    substituteHP maxHP = 0 ↔ maxHP.toNat < 4 := by native_decide

-- impl can produce 0-HP outcomes that spec always blocks
theorem l2_bug_divergence : ∀ maxHP currentHP : BitVec 8,
    impl maxHP currentHP = some 0 → spec maxHP currentHP = none := by native_decide

-- spec never produces a 0-HP remaining outcome (invariant it maintains)
theorem l2_spec_no_zero_result : ∀ maxHP currentHP : BitVec 8,
    spec maxHP currentHP ≠ some 0 := by native_decide

-- When impl and spec disagree, impl always returns some value while spec returns none
theorem l2_impl_more_permissive : ∀ maxHP currentHP : BitVec 8,
    spec maxHP currentHP = none → impl maxHP currentHP ≠ none →
    impl maxHP currentHP = some 0 ∨ substituteHP maxHP = 0 := by native_decide

-- ===== L3: Verified Fix =====

-- Fix: require strictly positive cost AND user must have strictly more HP than cost
def implFixed (maxHP : BitVec 8) (currentHP : BitVec 8) : Option (BitVec 8) :=
  let cost := substituteHP maxHP
  if 0 < cost.toNat && cost.toNat < currentHP.toNat then
    some (currentHP - cost)
  else
    none

-- The fix matches the specification exactly for all inputs
theorem l3_fix_correct : ∀ maxHP currentHP : BitVec 8,
    implFixed maxHP currentHP = spec maxHP currentHP := by native_decide

-- The fix never leaves the user at 0 HP
theorem l3_fix_no_zero_hp : ∀ maxHP currentHP : BitVec 8,
    implFixed maxHP currentHP ≠ some 0 := by native_decide

-- The fix only succeeds when the substitute has a positive HP cost (Bug 1 fixed)
theorem l3_fix_positive_cost : ∀ maxHP currentHP : BitVec 8,
    implFixed maxHP currentHP ≠ none → 0 < (substituteHP maxHP).toNat := by native_decide

-- The fix strictly reduces the set of accepted inputs compared to impl
theorem l3_fix_strictly_safer : ∀ maxHP currentHP : BitVec 8,
    implFixed maxHP currentHP ≠ none → impl maxHP currentHP ≠ none := by native_decide

end AutoResearch
