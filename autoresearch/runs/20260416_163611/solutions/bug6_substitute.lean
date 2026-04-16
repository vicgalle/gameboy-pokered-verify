import SM83

namespace AutoResearch

/-!
# Bug #6: Substitute 0 HP Shield and 0 HP User

The move Substitute creates a decoy at the cost of 1/4 of the user's max HP.
Two bugs are present in the SM83 implementation in Pokémon Red:

1. **Zero-HP Substitute**: When Max HP < 4, `cost = maxHP / 4` rounds down to 0. 
   The routine allows this, creating a shield with 0 HP at no cost.
2. **User left at 0 HP**: The code checks `currentHP - cost` for an underflow (carry flag).
   If `currentHP == cost`, the subtraction results in 0 with no carry.
   The move succeeds, leaving the user with 0 HP (a lethal state).
-/

/-- Results of a Substitute move attempt. -/
structure SubResult where
  success : Bool
  userHP  : BitVec 8
  subHP   : BitVec 8
  deriving DecidableEq, Repr

/-- 
Standard integer division of max HP by 4. 
In SM83, this is typically done using two `SRL` (Shift Right Logical) instructions.
-/
def getCost (maxHP : BitVec 8) : BitVec 8 :=
  maxHP >>> 2

/--
The buggy implementation from Pokémon Red.
- Uses `SUB` and only checks the Carry flag (fails only if `currentHP < cost`).
- Does not check if the resulting cost is 0.
-/
def impl (maxHP currentHP : BitVec 8) : SubResult :=
  let cost := getCost maxHP
  -- In SM83, SUB sets the carry flag if currentHP < cost.
  -- The bug is checking only for this carry, allowing currentHP == cost.
  if currentHP.toNat >= cost.toNat then
    { success := true, userHP := currentHP - cost, subHP := cost }
  else
    { success := false, userHP := currentHP, subHP := 0 }

/--
The intended behavior (Spec).
- Substitute should fail if the cost is 0 (Max HP too low).
- Substitute should fail if the user cannot survive the cost (currentHP <= cost).
-/
def spec (maxHP currentHP : BitVec 8) : SubResult :=
  let cost := getCost maxHP
  -- Correct logic: Cost must be > 0 AND user must have strictly more HP than cost.
  if cost.toNat > 0 && currentHP.toNat > cost.toNat then
    { success := true, userHP := currentHP - cost, subHP := cost }
  else
    { success := false, userHP := currentHP, subHP := 0 }

-- L1: Prove Bug 1 exists (Zero-HP Substitute)
-- If Max HP is 2, cost is 0. A substitute is created with 0 HP.
theorem exists_bug_zero_hp_sub : ∃ m c, (impl m c).success = true ∧ (impl m c).subHP = 0 :=
  ⟨2, 10, by native_decide⟩

-- L1: Prove Bug 2 exists (User survives at 0 HP)
-- If Max HP is 4, cost is 1. If Current HP is 1, user is left at 0.
theorem exists_bug_user_at_zero_hp : ∃ m c, (impl m c).success = true ∧ (impl m c).userHP = 0 ∧ (getCost m).toNat > 0 :=
  ⟨4, 1, by native_decide⟩

-- L2: Universal characterization of Bug 2 (User survival at 0 HP)
-- The user ends at 0 HP if and only if their current HP exactly equals the cost.
theorem user_at_zero_hp_iff_hp_eq_cost : ∀ m c, 
    ((impl m c).success = true ∧ (impl m c).userHP = 0) ↔ (c = getCost m) := by
  intro m c
  have := (by native_decide : ∀ m v : BitVec 8,
    (let r := impl m v; r.success = true ∧ r.userHP = 0) ↔ (v = getCost m))
  exact this m c

-- L2: Universal characterization of Bug 1 (Zero-HP Substitute)
-- A successful substitute has 0 HP if and only if the Max HP is less than 4.
theorem zero_hp_sub_iff_low_max_hp : ∀ m c, 
    ((impl m c).success = true ∧ (impl m c).subHP = 0) ↔ (m.toNat < 4) := by
  intro m c
  have := (by native_decide : ∀ m v : BitVec 8,
    (let r := impl m v; r.success = true ∧ r.subHP = 0) ↔ (m.toNat < 4))
  exact this m c

-- L3: Fix the implementation
def fix (maxHP currentHP : BitVec 8) : SubResult :=
  let cost := getCost maxHP
  -- Fix: Use > instead of >=, and ensure cost is not 0.
  if cost.toNat > 0 && currentHP.toNat > cost.toNat then
    { success := true, userHP := currentHP - cost, subHP := cost }
  else
    { success := false, userHP := currentHP, subHP := 0 }

theorem fix_is_correct : ∀ m c, fix m c = spec m c := by
  intro m c; rfl

-- L4: Desync - Show that the buggy implementation permits a state that is impossible in the spec.
-- Specifically: The spec never allows a successful substitute to leave the user at 0 HP.
theorem spec_never_leaves_user_at_zero : ∀ m c, (spec m c).success = true → (spec m c).userHP.toNat > 0 := by
  intro m c
  have := (by native_decide : ∀ m v : BitVec 8, 
    (spec m v).success = true → (spec m v).userHP.toNat > 0)
  exact this m c

-- This property fails for the buggy implementation.
theorem impl_can_leave_user_at_zero : ∃ m c, (impl m c).success = true ∧ (impl m c).userHP.toNat = 0 :=
  ⟨4, 1, by native_decide⟩

end AutoResearch
