import SM83

namespace AutoResearch

/--
Buggy implementation of the move Substitute.
The routine calculates the substitute cost (Max HP / 4), then subtracts it 
from the current HP. It succeeds if the subtraction doesn't underflow (carry flag).
However, it fails to check if the result is 0 or if the cost itself is 0.
-/
def impl (max_hp current_hp : Nat) : (Nat × Nat × Bool) :=
  let cost := max_hp / 4
  -- Bug: uses >= (no carry) instead of > (strictly more than cost)
  if current_hp >= cost then
    (current_hp - cost, cost, true)
  else
    (current_hp, 0, false)

/--
Corrected behavior of Substitute.
1. The substitute cost must be at least 1 (requires Max HP >= 4).
2. The user must have strictly more HP than the cost to survive (HP > cost).
-/
def spec (max_hp current_hp : Nat) : (Nat × Nat × Bool) :=
  let cost := max_hp / 4
  if cost > 0 && current_hp > cost then
    (current_hp - cost, cost, true)
  else
    (current_hp, 0, false)

-- L1: Prove that Bug 1 exists (Zero-HP Substitute).
-- A Pokemon with 2 Max HP generates a substitute with 0 HP.
theorem bug_exists_zero_sub : ∃ m c, 
  let (_, sub_hp, success) := (impl m c).1, (impl m c).2.1, (impl m c).2.2
  success = true ∧ sub_hp = 0 ∧ m > 0 :=
  ⟨2, 10, by rfl⟩

-- L1: Prove that Bug 2 exists (User left at 0 HP).
-- A Pokemon with 4 Max HP and 1 Current HP survives at 0 HP.
theorem bug_exists_user_zero : ∃ m c,
  let (user_hp, _, success) := (impl m c).1, (impl m c).2.1, (impl m c).2.2
  success = true ∧ user_hp = 0 ∧ c > 0 :=
  ⟨4, 1, by rfl⟩

-- L2: Universal characterization of Bug 1 (Zero-HP Substitute).
-- Any Pokemon with Max HP < 4 creates a 0-HP substitute if the move is allowed.
theorem forall_zero_sub_triggers : ∀ m c : Nat,
  m > 0 → m < 4 → (impl m c).2.1 = 0 ∧ (impl m c).2.2 = true := by
  intro m c _ h_lt
  simp [impl]
  have h_cost : m / 4 = 0 := by omega
  simp [h_cost]
  intro; rfl

-- L2: Universal characterization of Bug 2 (User survives at 0 HP).
-- If the current HP equals the cost (and cost > 0), the Pokemon is left at 0 HP.
theorem forall_user_zero_triggers : ∀ m c : Nat,
  m >= 4 → c = m / 4 → (impl m c).1 = 0 ∧ (impl m c).2.2 = true := by
  intro m c _ h_eq
  simp [impl, h_eq]
  have h_cost : m / 4 = c := by omega
  simp [h_cost, Nat.sub_self]

-- L3: A fix that correctly implements the specification.
def fix (max_hp current_hp : Nat) : (Nat × Nat × Bool) :=
  let cost := max_hp / 4
  if cost > 0 && current_hp > cost then
    (current_hp - cost, cost, true)
  else
    (current_hp, 0, false)

-- Verification that the fix matches the specification for all inputs.
theorem fix_is_correct : ∀ m c, fix m c = spec m c := by
  intro m c; rfl

-- Verification that the fix prevents the "User at 0 HP" bug.
theorem fix_prevents_user_faint : ∀ m c, (fix m c).2.2 = true → (fix m c).1 > 0 := by
  intro m c h
  simp [fix] at h
  split at h
  · next h_cond => 
    simp [fix, h_cond]
    omega
  · contradiction

-- Verification that the fix prevents the "Zero-HP Substitute" bug.
theorem fix_prevents_zero_sub_hp : ∀ m c, (fix m c).2.2 = true → (fix m c).2.1 > 0 := by
  intro m c h
  simp [fix] at h
  split at h
  · next h_cond =>
    simp [fix, h_cond]
    omega
  · contradiction

end AutoResearch

