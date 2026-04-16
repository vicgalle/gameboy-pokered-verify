import SM83

namespace AutoResearch

/-!
# Bug #6: Substitute Creates 0 HP Shield and Leaves User at 0 HP

## Description
The move Substitute creates a decoy at the cost of 1/4 of the user's max HP.
Due to rounding and missing boundary checks:
1.  **Zero-HP Substitute**: If Max HP < 4, cost is 0. The routine succeeds, 
    creating a 0 HP substitute for 0 cost.
2.  **User at 0 HP**: If Current HP == (Max HP / 4), the subtraction result 
    is 0. The routine checks for underflow (carry flag) but not for a 0 result, 
    leaving the user at 0 HP.
-/

/--
Buggy implementation of Substitute.
Returns: (User Remaining HP, Substitute HP, Success Flag)
-/
def impl (max_hp current_hp : Nat) : (Nat × Nat × Bool) :=
  let cost := max_hp / 4
  -- In SM83, the carry flag is clear if (A >= B).
  -- The bug succeeds if there is "no carry".
  if current_hp >= cost then
    (current_hp - cost, cost, true)
  else
    (current_hp, 0, false)

/--
Intended implementation of Substitute.
1. Cost must be at least 1 (Max HP >= 4).
2. Current HP must be strictly greater than cost (user must survive with > 0 HP).
-/
def spec (max_hp current_hp : Nat) : (Nat × Nat × Bool) :=
  let cost := max_hp / 4
  if cost > 0 && current_hp > cost then
    (current_hp - cost, cost, true)
  else
    (current_hp, 0, false)

/- --- L1: Concrete Witnesses --- -/

/--
L1: Witness for Bug 1 (Zero-HP Substitute).
A Pokemon with 3 Max HP can create a substitute with 0 HP.
-/
theorem bug_exists_zero_sub : ∃ m c, 
  let (u, s, ok) := impl m c
  ok = true ∧ s = 0 ∧ m > 0 :=
  ⟨3, 5, by rfl⟩

/--
L1: Witness for Bug 2 (User survives at 0 HP).
A Pokemon with 4 Max HP and 1 Current HP survives at 0 HP.
-/
theorem bug_exists_user_zero : ∃ m c,
  let (u, s, ok) := impl m c
  ok = true ∧ u = 0 ∧ c > 0 :=
  ⟨4, 1, by rfl⟩

/- --- L2: Universal Characterizations --- -/

/--
L2: Universal characterization of Bug 1.
Whenever Max HP is between 1 and 3, any Pokemon with HP >= 0 creates a 0-HP substitute.
-/
theorem forall_zero_sub_triggers : ∀ m c : Nat,
  (m > 0 ∧ m < 4) → (impl m c).2.1 = 0 ∧ (impl m c).2.2 = true := by
  intro m c h
  simp [impl]
  have h_cost : m / 4 = 0 := by omega
  simp [h_cost]

/--
L2: Universal characterization of Bug 2.
Whenever current HP equals the non-zero cost, the user is left with 0 HP.
-/
theorem forall_user_zero_triggers : ∀ m c : Nat,
  (m >= 4 ∧ c = m / 4) → (impl m c).1 = 0 ∧ (impl m c).2.2 = true := by
  intro m c h
  have h_cost : m / 4 = c := by omega
  simp [impl, h_cost, Nat.sub_self]
  omega

/- --- L3: Fix and Correctness --- -/

/--
L3: A corrected implementation.
-/
def fix (max_hp current_hp : Nat) : (Nat × Nat × Bool) :=
  let cost := max_hp / 4
  if cost > 0 && current_hp > cost then
    (current_hp - cost, cost, true)
  else
    (current_hp, 0, false)

theorem fix_correct : ∀ m c, fix m c = spec m c := by
  intro m c; rfl

/--
L3: The fix prevents the user from reaching 0 HP on success.
-/
theorem fix_prevents_user_faint : ∀ m c, (fix m c).2.2 = true → (fix m c).1 > 0 := by
  intro m c h
  simp [fix] at h
  split at h
  · next h_cond => 
    simp [fix, h_cond]
    omega
  · contradiction

/--
L3: The fix prevents substitutes from having 0 HP.
-/
theorem fix_prevents_zero_sub_hp : ∀ m c, (fix m c).2.2 = true → (fix m c).2.1 > 0 := by
  intro m c h
  simp [fix] at h
  split at h
  · next h_cond =>
    simp [fix, h_cond]
    omega
  · contradiction

/- --- L4: Relational Divergence --- -/

/--
L4: The implementation and specification differ exactly when:
1. The cost is 0 (rounding bug)
2. The remaining HP would be 0 (fainting bug)
-/
theorem relational_desync : ∀ m c, 
  impl m c ≠ spec m c ↔ (m / 4 = 0) ∨ (c = m / 4 ∧ c > 0) := by
  intro m c
  simp [impl, spec]
  constructor
  · intro h
    match h_cost : m / 4 with
    | 0 => left; rfl
    | cost + 1 =>
      right
      constructor
      · exact h_cost
      · split at h
        · next h_ge =>
          split at h
          · contradiction
          · -- c >= cost but not (cost > 0 && c > cost)
            -- since cost > 0, this means c == cost
            omega
        · -- c < cost: both are (c, 0, false)
          contradiction
  · intro h
    cases h with
    | il => 
      have h_cost : m / 4 = 0 := by assumption
      simp [h_cost]
    | ir r =>
      have h_cost : m / 4 = c := by omega
      have h_pos : c > 0 := by omega
      simp [h_cost, h_pos]

end AutoResearch

