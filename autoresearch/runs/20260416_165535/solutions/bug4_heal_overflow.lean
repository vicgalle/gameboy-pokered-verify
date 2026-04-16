import SM83

namespace AutoResearch

/-!
# Bug #4: heal_overflow

In the Generation 1 Pokémon games (Red, Blue, Yellow), healing moves such as 
Recover, Softboiled, and Rest perform a check to see if the user's HP is already full. 
The bug occurs because the comparison logic is flawed: the game subtracts the 
current HP from the maximum HP and checks if the result is zero. However, it effectively 
only checks the lower 8 bits of the 16-bit difference.

If the difference between Max HP and Current HP is a non-zero multiple of 256 
(e.g., 256, 512), the lower 8 bits of the difference are 0. The move incorrectly 
concludes that the HP is already full and fails to heal, despite the Pokémon 
being damaged.
-/

/--
The buggy implementation: reports that the Pokémon is "at full HP" if the 
lower 8 bits of the difference between Max HP and Current HP are zero.
-/
def impl (maxHP currentHP : Nat) : Bool :=
  (maxHP - currentHP) % 256 == 0

/--
The intended behavior: reports that the Pokémon is "at full HP" if and only if
Current HP is exactly equal to Max HP.
-/
def spec (maxHP currentHP : Nat) : Bool :=
  maxHP == currentHP

-- L1: Concrete witness of the bug
-- A Pokémon with 512 Max HP and 256 Current HP will trigger the bug.
theorem bug_exists : ∃ m c, c < m ∧ impl m c = true ∧ spec m c = false := by
  exists 512, 256
  simp [impl, spec]
  constructor
  · omega
  · rfl

-- L1: A second witness with specific values
theorem bug_at_300_44 : impl 300 44 = true ∧ spec 300 44 = false := by
  native_decide

-- L2: Universal characterization of when the bug triggers
-- The bug occurs when the HP difference is a positive multiple of 256.
theorem bug_iff_nonzero_multiple_of_256 (m c : Nat) (h_le : c ≤ m) :
  (impl m c = true ∧ spec m c = false) ↔ (m - c > 0 ∧ (m - c) % 256 = 0) := by
  simp [impl, spec]
  constructor
  · intro ⟨h_impl, h_spec⟩
    constructor
    · -- Prove m - c > 0 given m != c and c <= m
      omega
    · -- The modulo condition is exactly what impl checks
      exact h_impl
  · intro ⟨h_pos, h_mod⟩
    constructor
    · exact h_mod
    · -- If m - c > 0, then m cannot be c
      omega

-- L3: Correct implementation (Fix)
def fix (m c : Nat) : Bool :=
  m == c

theorem fix_correct : ∀ m c, fix m c = spec m c := by
  intro m c; rfl

-- L4: Relational property - The buggy implementation is "conservative" regarding healing.
-- If the spec says the move should fail (true), the buggy implementation always agrees.
theorem spec_implies_impl_fail (m c : Nat) :
  spec m c = true → impl m c = true := by
  simp [impl, spec]
  intro h
  rw [h]
  simp

-- L4: Relational property - Agreement on low HP values.
-- If the difference is within the range [0, 255], the buggy and correct versions agree.
theorem agree_on_small_diffs (m c : Nat) (h_le : c ≤ m) (h_diff : m - c < 256) :
  impl m c = spec m c := by
  simp [impl, spec]
  if h_eq : m = c then
    simp [h_eq]
  else
    -- If m != c and c <= m, then m - c > 0
    have h_pos : m - c > 0 := by omega
    -- Since m - c < 256 and m - c > 0, (m - c) % 256 cannot be 0
    have h_mod : (m - c) % 256 = m - c := Nat.mod_eq_of_lt h_diff
    rw [h_mod]
    simp [h_eq]
    intro h_contra
    omega

-- Relational property: For any Max HP below 256, the bug can never trigger.
theorem bug_impossible_for_low_max_hp (m c : Nat) (h_le : c ≤ m) (h_max : m < 256) :
  impl m c = spec m c := by
  have h_diff : m - c < 256 := by omega
  exact agree_on_small_diffs m c h_le h_diff

end AutoResearch
