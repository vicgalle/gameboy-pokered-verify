import SM83

namespace AutoResearch

/-
  Bug #7: Bide Accumulated Damage Link Battle Desynchronization

  Gameplay Description:
  Bide stores damage taken over 2-3 turns and returns double that amount.
  When a Pokemon faints, the game is supposed to reset the Bide damage
  accumulator to zero. However, the 'enemy_faint' routine only clears
  the high byte of the 16-bit damage counter, leaving the low byte intact.
  In contrast, the 'player_faint' routine correctly clears both bytes.

  In a link battle, the Game Boy whose Pokemon fainted runs the player_faint 
  logic (correct reset), while the opponent Game Boy runs the enemy_faint 
  logic (buggy reset). This causes the two consoles to diverge if the 
  low byte of the stored damage was non-zero.
-/

/-- 
  Model of the buggy enemy_faint reset behavior (impl).
  Only the high byte of the 16-bit damage value is cleared.
-/
def impl (d : BitVec 16) : BitVec 16 :=
  SM83.mk16 0 (SM83.lo d)

/-- 
  Model of the correct faint reset behavior (spec).
  Both bytes are cleared, resetting the value to zero.
-/
def spec (_d : BitVec 16) : BitVec 16 :=
  0

/-- L1: A concrete witness of the bug. 
    If the damage stored was 1 (0x0001), the buggy reset results in 1, while spec is 0. -/
theorem bug_exists : ∃ d : BitVec 16, impl d ≠ spec d :=
  ⟨1, by native_decide⟩

/-- L2: Universal characterization.
    The buggy reset fails if and only if the low byte of the accumulated damage is non-zero. -/
theorem bug_iff_low_byte_nonzero (d : BitVec 16) :
  impl d ≠ spec d ↔ SM83.lo d ≠ 0 := by
  simp [impl, spec]
  constructor
  · intro h
    contrapose! h
    simp at h
    -- If low byte is 0, the result of mk16 0 0 is indeed 0.
    have h_zero : SM83.mk16 0 0 = 0 := by native_decide
    rw [h, h_zero]
  · intro h
    -- For all non-zero 8-bit values, mk16 0 b is non-zero.
    have helper : ∀ b : BitVec 8, b ≠ 0 → SM83.mk16 0 b ≠ 0 := by
      intro b; native_decide
    apply helper
    exact h

/-- L2: Partial correctness check.
    Even in the buggy implementation, the high byte is always correctly cleared. -/
theorem high_byte_is_always_cleared (d : BitVec 16) :
  SM83.hi (impl d) = 0 := by
  simp [impl]
  -- Universal check over all possible low bytes.
  have helper : ∀ b : BitVec 8, SM83.hi (SM83.mk16 0 b) = 0 := by
    intro b; native_decide
  exact helper (SM83.lo d)

/-- L3: The fix is to ensure both bytes are reset, matching the intended spec. -/
def fix (_d : BitVec 16) : BitVec 16 := 0

theorem fix_is_correct : ∀ d : BitVec 16, fix d = spec d := by
  intro d; rfl

/-- L4: Relational divergence in a Link Battle.
    When a faint event occurs, one console processes it as a player faint (spec)
    while the other processes it as an enemy faint (impl).
    If the damage counter had a non-zero low byte, the consoles permanently desynchronize. -/
theorem link_battle_desync (d : BitVec 16) (h : SM83.lo d ≠ 0) :
  let side_a_player_view := spec d -- Pokemon belongs to side A, runs correct reset
  let side_b_enemy_view := impl d  -- Pokemon is side B's enemy, runs buggy reset
  side_a_player_view ≠ side_b_enemy_view := by
  simp
  -- Use the previously proven characterization.
  rw [bug_iff_low_byte_nonzero]
  exact h

end AutoResearch
