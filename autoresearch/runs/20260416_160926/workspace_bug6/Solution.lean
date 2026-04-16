import SM83
import Harness

namespace AutoResearch

open BitVec

/-!
# Bug #6: Substitute HP Calculation Logic

## Description
In Pokémon Red, the move Substitute allows a Pokémon to create a decoy at the 
cost of 1/4 of its maximum HP. There are two critical logic errors in the
implementation:
1. **Zero-HP Substitute**: If Max HP is less than 4, the integer division 
   `MaxHP / 4` rounds down to 0, creating a decoy with 0 HP.
2. **User survives at 0 HP**: The code checks for an underflow after deducting
   HP but does not verify if the resulting HP is exactly 0. If current HP is 
   exactly 1/4 of Max HP, the user survives in battle with 0 HP.

This model verifies both bugs and proves a fix.
-/

/-- 
Cost calculation for Substitute: 1/4 of Max HP.
In the SM83 assembly, this is implemented using two right shifts (`srl`),
which corresponds to unsigned integer division by 4.
-/
def cost (maxHP : BitVec 16) : BitVec 16 :=
  maxHP / 4

/-- 
The buggy implementation of the Substitute routine.
Logic Error 1: Allows cost `c` to be 0 (Zero-HP decoy).
Logic Error 2: Uses `>=` instead of `>` for the HP check, allowing the user 
to reach exactly 0 HP without failing the routine.
-/
def impl (currHP maxHP : BitVec 16) : Option (BitVec 16 × BitVec 16) :=
  let c := cost maxHP
  -- Bug: The check 'jr c, .fail' only detects underflow (currHP < c).
  if currHP >= c then
    some (currHP - c, c)
  else
    none

/-- 
The intended specification for the Substitute routine.
A valid Substitute must cost more than 0 HP and leave the user with at least 1 HP.
-/
def spec (currHP maxHP : BitVec 16) : Option (BitVec 16 × BitVec 16) :=
  let c := cost maxHP
  if c > 0 && currHP > c then
    some (currHP - c, c)
  else
    none

/-! ### L1: Bug Witnesses -/

/-- 
L1 Witness for Error 1: Zero-HP Substitute.
When Max HP is 3, cost is 0. A substitute is created with 0 HP.
-/
theorem l1_zero_hp_sub : ∃ currHP maxHP res, 
  impl currHP maxHP = some res ∧ res.2 = 0 ∧ spec currHP maxHP = none := by
  let currHP : BitVec 16 := 10
  let maxHP : BitVec 16 := 3
  exists currHP, maxHP, (10, 0)
  native_decide

/-- 
L1 Witness for Error 2: User survives at 0 HP.
When current HP equals 1/4 of Max HP, the user survives with 0 HP.
-/
theorem l1_user_dead : ∃ currHP maxHP res, 
  impl currHP maxHP = some res ∧ res.1 = 0 ∧ spec currHP maxHP = none := by
  let currHP : BitVec 16 := 10
  let maxHP : BitVec 16 := 40
  exists currHP, maxHP, (0, 10)
  native_decide

/-! ### L2: Universal Characterization -/

/--
Theorem characterizing the divergence between the buggy implementation
and the specification.
The bug triggers exactly when the user has enough HP to cover the cost 
(currHP >= c) but fails the safety conditions (c > 0 and currHP > c).
-/
theorem l2_bug_condition (currHP maxHP : BitVec 16) :
  impl currHP maxHP ≠ spec currHP maxHP ↔
  let c := cost maxHP
  (currHP >= c ∧ (c = 0 ∨ currHP = c)) := by
  let c := cost maxHP
  simp [impl, spec]
  split <;> split <;> simp [*]
  · -- Both succeed: impl=some, spec=some
    intro h_spec
    intro h_cond
    cases h_cond with
    | inl hc0 => 
      have := h_spec.1
      contradiction
    | inr h_eq =>
      subst h_eq
      exact BitVec.lt_irrefl _ h_spec.2
  · -- Divergence: impl=some, spec=none
    intro h_ge h_nspec
    simp at h_nspec
    simp [h_ge]
    cases h_c0 : decide (c = 0) with
    | isTrue h0 => left; exact h0
    | isFalse h0 =>
      simp [h0] at h_nspec
      right; apply BitVec.le_antisymm h_nspec h_ge
  · -- Divergence: impl=none, spec=some
    intro h_lt h_gt
    have := BitVec.lt_of_le_of_lt h_lt h_gt.2
    exact BitVec.lt_irrefl _ this

/-! ### L3: Fixed Implementation -/

/-- Corrected version of the Substitute routine. -/
def fixed (currHP maxHP : BitVec 16) : Option (BitVec 16 × BitVec 16) :=
  let c := cost maxHP
  if c > 0 && currHP > c then
    some (currHP - c, c)
  else
    none

/-- The fixed implementation matches the specification for all inputs. -/
theorem l3_fix_matches_spec : fixed = spec := rfl

/-! ### L4: Relational/Safety Property -/

/-- 
The specification ensures the Pokémon never reaches a state that should be 
impossible (0 HP without fainting) and never creates a 0-HP decoy.
-/
theorem l4_spec_is_safe (currHP maxHP : BitVec 16) (newHP subHP : BitVec 16) :
  spec currHP maxHP = some (newHP, subHP) → 
  newHP > 0 ∧ subHP > 0 := by
  simp [spec]
  intro h_c0 h_gt h_eq
  injection h_eq with h_new h_sub
  subst h_new h_sub
  constructor
  · -- user survives with > 0 HP
    apply BitVec.lt_of_toNat_lt
    simp [BitVec.toNat_sub_of_le (BitVec.le_of_lt h_gt)]
    have := BitVec.toNat_lt_toNat.mpr h_gt
    omega
  · -- decoy has > 0 HP
    exact h_c0

/-- 
The implementation is unsafe as it allows the user's HP to drop to 0
during a successful move execution.
-/
theorem l4_impl_is_unsafe : ∃ currHP maxHP res,
  impl currHP maxHP = some res ∧ res.1 = 0 := by
  exists 1, 4, (0, 1)
  native_decide

end AutoResearch
