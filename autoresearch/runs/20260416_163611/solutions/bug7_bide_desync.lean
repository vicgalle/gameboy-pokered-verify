import SM83

namespace AutoResearch

/-!
# Bug #7: Bide Accumulated Damage Link Battle Desynchronization

## Description
In Pokémon Red/Blue, the Bide move stores damage taken and returns it doubled.
When a Pokémon faints, the game should reset the Bide accumulated damage counter.
However, while the routine for a player's Pokémon fainting clears both bytes of 
the damage counter, the routine for an enemy Pokémon fainting only clears the 
high byte, leaving the low byte intact.

In a link battle, this causes a desynchronization because one Game Boy processes 
the faint as "Player" (full clear) while the other processes it as "Enemy" 
(partial clear).
-/

/--
  Model of the buggy clearing routine (Enemy fainting).
  It clears the high byte but leaves the low byte intact.
-/
def impl (acc : BitVec 16) : BitVec 16 :=
  SM83.mk16 0 (SM83.lo acc)

/--
  Model of the correct clearing routine (Player fainting).
  It correctly clears both bytes (resets to 0).
-/
def spec (acc : BitVec 16) : BitVec 16 :=
  0

-- L1: Concrete witness where the bug occurs
theorem bug_exists : ∃ acc : BitVec 16, impl acc ≠ spec acc := by
  -- If the low byte is non-zero (e.g., 1), the bug manifests
  use 1
  native_decide

-- L2: Universal characterization of when the bug triggers
-- The bug causes a desync if and only if the low byte of the accumulated damage is non-zero.
theorem bug_iff_low_byte_nonzero (acc : BitVec 16) :
  impl acc ≠ spec acc ↔ SM83.lo acc ≠ 0 := by
  have h := (by native_decide : ∀ v : BitVec 16, (SM83.mk16 0 (SM83.lo v) ≠ 0) ↔ (SM83.lo v ≠ 0))
  exact h acc

-- L2: Characterization of the resulting value
-- The buggy value is equal to the original low byte.
theorem bug_result_is_low_byte (acc : BitVec 16) :
  (impl acc).toNat = (SM83.lo acc).toNat := by
  have h := (by native_decide : ∀ v : BitVec 16, (SM83.mk16 0 (SM83.lo v)).toNat = (SM83.lo v).toNat)
  exact h acc

-- L3: Correct fix that matches the intended behavior for all inputs
def fix (acc : BitVec 16) : BitVec 16 := 0

theorem fix_correct : ∀ acc : BitVec 16, fix acc = spec acc := by
  intro acc; rfl

-- L4: Link Battle Desynchronization
-- We model two consoles processing the same faint event.
-- Console A sees it as a Player faint (correct clear).
-- Console B sees it as an Enemy faint (buggy clear).

structure ConsoleState where
  bideAccumulatedDamage : BitVec 16

def player_side_faint (s : ConsoleState) : ConsoleState :=
  ⟨spec s.bideAccumulatedDamage⟩

def enemy_side_faint (s : ConsoleState) : ConsoleState :=
  ⟨impl s.bideAccumulatedDamage⟩

/--
  Relational Property: If the low byte is non-zero, the two consoles diverge 
  permanently after a faint event.
-/
theorem link_battle_desync (acc : BitVec 16) (h : SM83.lo acc ≠ 0) :
  (player_side_faint ⟨acc⟩).bideAccumulatedDamage ≠ (enemy_side_faint ⟨acc⟩).bideAccumulatedDamage := by
  simp [player_side_faint, enemy_side_faint]
  -- Use the previously proven characterization
  rw [bug_iff_low_byte_nonzero]
  exact h

/--
  Consequence: The damage dealt by Bide will differ between the two consoles.
-/
def damage_dealt (acc : BitVec 16) : Nat := 2 * acc.toNat

theorem damage_desync (acc : BitVec 16) (h : SM83.lo acc ≠ 0) :
  let sA := player_side_faint ⟨acc⟩
  let sB := enemy_side_faint ⟨acc⟩
  damage_dealt sA.bideAccumulatedDamage ≠ damage_dealt sB.bideAccumulatedDamage := by
  simp [damage_dealt, player_side_faint, enemy_side_faint, spec]
  -- Side A deals 0 damage
  -- Side B deals 2 * (impl acc).toNat
  have h_val := bug_result_is_low_byte acc
  rw [h_val]
  intro h_zero
  -- If 2 * lo_byte == 0, then lo_byte == 0
  have h_lo_zero : (SM83.lo acc).toNat = 0 := by omega
  have h_lo_bv_zero : SM83.lo acc = 0 := by
    apply BitVec.val_inj.mp
    exact h_lo_zero
  contradiction

/--
  Consistency: If the low byte happened to be zero, no desync occurs.
-/
theorem link_battle_remains_synced_if_lo_zero (acc : BitVec 16) (h : SM83.lo acc = 0) :
  (player_side_faint ⟨acc⟩).bideAccumulatedDamage = (enemy_side_faint ⟨acc⟩).bideAccumulatedDamage := by
  simp [player_side_faint, enemy_side_faint, spec, impl, h]
  have h_mk := (by native_decide : SM83.mk16 0 0 = 0)
  exact h_mk

end AutoResearch
