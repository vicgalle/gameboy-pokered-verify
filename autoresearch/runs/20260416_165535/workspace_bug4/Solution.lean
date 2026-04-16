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
The buggy implementation: reports that the Pokémon is "at full HP" (True) if the 
lower 8 bits of the difference between Max HP and Current HP are zero.
-/
def impl (maxHP currentHP : Nat) : Bool :=
  (maxHP - currentHP) % 256 == 0

/--
The intended behavior: reports that the Pokémon is "at full HP" (True) if and only if
Current HP is exactly equal to Max HP.
-/
def spec (maxHP currentHP : Nat) : Bool :=
  maxHP == currentHP

/-! ### L1: Concrete Witnesses -/

/-- A Pokémon with 512 Max HP and 256 Current HP will trigger the bug. -/
theorem bug_exists : ∃ m c, c < m ∧ impl m c = true ∧ spec m c = false := by
  exists 512, 256
  simp [impl, spec]

/-- A Pokémon with 300 Max HP and 44 Current HP (gap of 256) will trigger the bug. -/
theorem bug_at_300_44 : impl 300 44 = true ∧ spec 300 44 = false := by
  simp [impl, spec]

/-! ### L2: Universal Characterization -/

/-- The bug occurs when and only when the HP difference is a positive multiple of 256. -/
theorem bug_iff_nonzero_multiple_of_256 (m c : Nat) (h_le : c ≤ m) :
  (impl m c = true ∧ spec m c = false) ↔ (m - c > 0 ∧ (m - c) % 256 = 0) := by
  simp [impl, spec]
  constructor
  · intro ⟨h_impl, h_spec⟩
    constructor <;> omega
  · intro ⟨h_pos, h_mod⟩
    constructor <;> omega

/-! ### L3: Fix -/

/-- The corrected implementation of the full HP check. -/
def fix (m c : Nat) : Bool := m == c

theorem fix_is_correct : ∀ m c, fix m c = spec m c := by
  intro m c; rfl

/-! ### L4: Relational Properties -/

/-- Completeness: If the HP is truly full, the buggy implementation always identifies it as full. -/
theorem spec_implies_impl_full (m c : Nat) :
  spec m c = true → impl m c = true := by
  simp [impl, spec]
  intro h; rw [h]; simp

/-- Soundness (Negative): If the bug does NOT trigger, the HP is definitely NOT full. -/
theorem impl_false_implies_not_full (m c : Nat) :
  impl m c = false → spec m c = false := by
  simp [impl, spec]
  intro h h_eq
  rw [h_eq] at h
  simp at h

/-- Periodicity: The bug's behavior repeats every 256 HP points. -/
theorem bug_periodicity (m c : Nat) (h_le : c + 256 ≤ m) :
  impl m c = impl m (c + 256) := by
  simp [impl]
  have h1 : m - c = (m - (c + 256)) + 256 := by omega
  rw [h1]
  -- Use mod property: (x + 256) % 256 = x % 256
  have h_mod (n : Nat) : (n + 256) % 256 = n % 256 := by
    rw [Nat.add_mod, Nat.mod_self]
    simp
  rw [h_mod]

/-- Safety: For Pokémon with low Max HP (under 256), the bug is physically impossible to trigger. -/
theorem bug_impossible_small_hp (m c : Nat) (h_le : c ≤ m) (h_max : m < 256) :
  impl m c = spec m c := by
  simp [impl, spec]
  if h_eq : m = c then
    simp [h_eq]
  else
    -- If m != c and c <= m, then 0 < m - c < 256
    have h_pos : m - c > 0 := by omega
    have h_lt : m - c < 256 := by omega
    -- n % 256 = n when n < 256
    rw [Nat.mod_eq_of_lt h_lt]
    simp [h_pos]

end AutoResearch
