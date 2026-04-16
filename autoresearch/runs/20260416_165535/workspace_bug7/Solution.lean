import SM83

namespace AutoResearch

/-
  Bug #7: Bide Accumulated Damage Link Battle Desynchronization

  Gameplay Description:
  Bide stores damage taken over 2-3 turns and deals double that amount back.
  When a Pokemon faints, the game is supposed to reset the Bide damage
  accumulator (a 16-bit value) to zero. However, the routine for handling
  an enemy fainting only clears the high byte of the counter, leaving the
  low byte intact. The routine for the player's Pokemon fainting correctly
  clears both bytes.

  In a link battle, this causes a desynchronization:
  - Console A (whose Pokemon fainted) runs the correct 'player faint' reset.
  - Console B (opponent) runs the buggy 'enemy faint' reset.
  The two consoles now disagree on the stored Bide damage, causing battle
  states to diverge.
-/

/-- 
  Model of the buggy enemy_faint reset behavior (impl).
  Only the high byte of the 16-bit damage value is cleared to zero.
  The low byte is left unchanged.
-/
def impl (d : BitVec 16) : BitVec 16 :=
  SM83.mk16 0 (SM83.lo d)

/-- 
  Model of the correct faint reset behavior (spec).
  Both bytes of the 16-bit counter are cleared, resetting the value to zero.
-/
def spec (_d : BitVec 16) : BitVec 16 :=
  0

/-- L1: A concrete witness of the bug. 
    If the damage stored was 1 (0x0001), the buggy reset results in 1, while spec is 0. -/
theorem bug_exists : ∃ d : BitVec 16, impl d ≠ spec d :=
  ⟨1, by native_decide⟩

/-- L2: Universal characterization.
    The buggy reset fails to clear the counter if and only if the low byte is non-zero. -/
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
    have helper := (by native_decide : ∀ b : BitVec 8, b ≠ 0 → SM83.mk16 0 b ≠ 0)
    apply helper
    exact h

/-- L2: Even in the buggy implementation, the high byte is always correctly cleared. -/
theorem high_byte_is_always_cleared (d : BitVec 16) :
  SM83.hi (impl d) = 0 := by
  simp [impl]
  have helper := (by native_decide : ∀ b : BitVec 8, SM83.hi (SM83.mk16 0 b) = 0)
  exact helper (SM83.lo d)

/-- L2: The low byte is incorrectly preserved in the implementation. -/
theorem low_byte_is_preserved (d : BitVec 16) :
  SM83.lo (impl d) = SM83.lo d := by
  simp [impl]
  have helper := (by native_decide : ∀ b : BitVec 8, SM83.lo (SM83.mk16 0 b) = b)
  exact helper (SM83.lo d)

/-- L2: The residual value after the buggy reset is exactly the previous low byte. -/
theorem divergence_magnitude (d : BitVec 16) :
  (impl d).toNat = (SM83.lo d).toNat := by
  simp [impl]
  have helper := (by native_decide : ∀ b : BitVec 8, (SM83.mk16 0 b).toNat = b.toNat)
  exact helper (SM83.lo d)

/-- L3: The fix is to ensure the entire register is set to zero, matching the spec. -/
def fix (_d : BitVec 16) : BitVec 16 := 0

theorem fix_is_correct : ∀ d : BitVec 16, fix d = spec d := by
  intro d; rfl

/-- L4: Link Battle Desynchronization.
    When one side's Pokemon faints, the two Game Boys use different routines.
    The side that sees a 'player faint' clears the accumulator (spec), 
    while the side that sees an 'enemy faint' uses the buggy routine (impl). -/
theorem link_battle_desync (d : BitVec 16) (h : SM83.lo d ≠ 0) :
  let side_a_player_view := spec d 
  let side_b_enemy_view := impl d  
  side_a_player_view ≠ side_b_enemy_view := by
  simp
  rw [bug_iff_low_byte_nonzero]
  exact h

/-- Bide deals damage equal to twice the accumulated amount. -/
def bide_damage (d : BitVec 16) : BitVec 16 := d <<< 1

/-- L4: The desynchronization in the counter leads to different damage being dealt 
    on each Game Boy, causing the consoles to diverge permanently. -/
theorem bide_damage_divergence (d : BitVec 16) (h : SM83.lo d ≠ 0) :
  bide_damage (spec d) ≠ bide_damage (impl d) := by
  simp [spec, impl, bide_damage]
  -- Shifted non-zero 8-bit values (in a 16-bit space) never wrap back to 0.
  have helper := (by native_decide : ∀ b : BitVec 8, b ≠ 0 → (0 : BitVec 16) ≠ (SM83.mk16 0 b) <<< 1)
  apply helper
  exact h

end AutoResearch

