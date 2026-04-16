import SM83

namespace AutoResearch

/-!
# Bug #6: Substitute 0 HP Shield and 0 HP User

The move Substitute creates a decoy at the cost of 1/4 of the user's max HP.
Two bugs are present in the SM83 implementation in Pokémon Red:

1. **Zero-HP Substitute**: When Max HP < 4, the cost (maxHP / 4) rounds down to 0. 
   The routine incorrectly allows this, creating a shield with 0 HP at zero cost.
2. **User left at 0 HP**: The routine checks for affordability by testing the Carry flag
   after subtraction (`currentHP - cost`). If `currentHP == cost`, the subtraction 
   results in 0 with no carry (NC), so the move succeeds and leaves the user at 0 HP.
-/

/-- Results of a Substitute move attempt. -/
structure SubResult where
  success : Bool
  userHP  : BitVec 8
  subHP   : BitVec 8
  deriving DecidableEq, Repr

/-- 
Calculates substitute cost: Max HP divided by 4 via integer division. 
In the SM83 engine, this is performed using two bitwise right shifts.
-/
def getCost (maxHP : BitVec 8) : BitVec 8 :=
  maxHP >>> 2

/--
The buggy implementation from Pokémon Red.
- Uses `SUB` and checks only the Carry flag (NC).
- Does not verify that the resulting cost is greater than 0.
- Does not verify that the user's HP remains greater than 0.
-/
def impl (maxHP currentHP : BitVec 8) : SubResult :=
  let cost := getCost maxHP
  -- The bug: checking only for underflow (Carry flag).
  -- If currentHP >= cost, the move proceeds.
  if currentHP.toNat >= cost.toNat then
    { success := true, userHP := currentHP - cost, subHP := cost }
  else
    { success := false, userHP := currentHP, subHP := 0 }

/--
The intended behavior (Spec).
- A Substitute must have at least 1 HP (cost > 0).
- The user must survive the creation (userHP > 0).
-/
def spec (maxHP currentHP : BitVec 8) : SubResult :=
  let cost := getCost maxHP
  -- Correct logic: Substitute HP must be > 0 AND user must have strictly more HP than cost.
  if cost.toNat > 0 && currentHP.toNat > cost.toNat then
    { success := true, userHP := currentHP - cost, subHP := cost }
  else
    { success := false, userHP := currentHP, subHP := 0 }

-- L1: Prove Bug 1 exists (Zero-HP Substitute)
-- If Max HP is 3, cost is 0. A substitute is created with 0 HP.
theorem exists_bug_zero_hp_sub : ∃ m c, (impl m c).success = true ∧ (impl m c).subHP = 0 :=
  ⟨3, 10, by native_decide⟩

-- L1: Prove Bug 2 exists (User survives at 0 HP)
-- If Max HP is 4 (cost 1) and current HP is 1, user is left at 0 HP.
theorem exists_bug_user_at_zero_hp : ∃ m c, (impl m c).success = true ∧ (impl m c).userHP = 0 ∧ (getCost m).toNat > 0 :=
  ⟨4, 1, by native_decide⟩

-- L2: Characterization of Bug 1 (Zero-HP Substitute)
-- A successful substitute has 0 HP if and only if the Max HP is less than 4.
theorem zero_hp_sub_iff_low_max_hp : ∀ m c, 
    ((impl m c).success = true ∧ (impl m c).subHP = 0) ↔ (m.toNat < 4) := by
  intro m c
  have := (by native_decide : ∀ m v : BitVec 8,
    (let r := impl m v; r.success = true ∧ r.subHP = 0) ↔ (m.toNat < 4))
  exact this m c

-- L2: Characterization of Bug 2 (Lethal Substitute)
-- A successful substitute leaves the user at 0 HP if and only if HP exactly equals cost.
theorem user_at_zero_hp_iff_hp_eq_cost : ∀ m c, 
    ((impl m c).success = true ∧ (impl m c).userHP = 0) ↔ (c = getCost m) := by
  intro m c
  have := (by native_decide : ∀ m v : BitVec 8,
    (let r := impl m v; r.success = true ∧ r.userHP = 0) ↔ (v = getCost m))
  exact this m c

-- L2: Agreement on Safe Values
-- The implementation and spec agree if Max HP >= 4 and Current HP > Cost.
theorem agreement_on_safe_values : ∀ m c, 
    (m.toNat >= 4 ∧ c.toNat > (getCost m).toNat) → impl m c = spec m c := by
  intro m c
  have := (by native_decide : ∀ m v : BitVec 8,
    (m.toNat >= 4 ∧ v.toNat > (getCost m).toNat) → impl m v = spec m v)
  exact this m c

-- L3: Corrected implementation
def fix (maxHP currentHP : BitVec 8) : SubResult :=
  let cost := getCost maxHP
  -- Fix: Ensure cost is positive and current HP is strictly greater than cost.
  if cost.toNat > 0 && currentHP.toNat > cost.toNat then
    { success := true, userHP := currentHP - cost, subHP := cost }
  else
    { success := false, userHP := currentHP, subHP := 0 }

theorem fix_is_correct : ∀ m c, fix m c = spec m c := by
  intro m c; rfl

-- L4: Safety Invariant (User HP)
-- The specification guarantees that a successful Substitute never results in 0 User HP.
theorem spec_user_hp_invariant : ∀ m c, (spec m c).success → (spec m c).userHP.toNat > 0 := by
  intro m c
  have := (by native_decide : ∀ m v : BitVec 8, (spec m v).success → (spec m v).userHP.toNat > 0)
  exact this m c

-- L4: Safety Invariant (Shield HP)
-- The specification guarantees that a successful Substitute never results in a 0 HP shield.
theorem spec_sub_hp_invariant : ∀ m c, (spec m c).success → (spec m c).subHP.toNat > 0 := by
  intro m c
  have := (by native_decide : ∀ m v : BitVec 8, (spec m v).success → (spec m v).subHP.toNat > 0)
  exact this m c

-- L4: Divergence (Lethal State)
-- The buggy implementation allows a lethal state transition that the spec forbids.
theorem lethal_state_desync : ∃ m c, (impl m c).success ∧ (impl m c).userHP = 0 ∧ 
                                   ¬((spec m c).success ∧ (spec m c).userHP = 0) :=
  ⟨4, 1, by native_decide⟩

-- L4: Divergence (Zero-HP Shield State)
-- The buggy implementation allows creating a 0-HP shield, which the spec forbids.
theorem zero_shield_desync : ∃ m c, (impl m c).success ∧ (impl m c).subHP = 0 ∧
                                   ¬((spec m c).success ∧ (spec m c).subHP = 0) :=
  ⟨2, 5, by native_decide⟩

end AutoResearch
