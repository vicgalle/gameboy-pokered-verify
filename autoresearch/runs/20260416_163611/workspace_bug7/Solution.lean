import SM83

/-!
# Bug #7: Bide Accumulated Damage Link Battle Desynchronization

## Description
Bide is a move that stores damage taken over 2-3 turns and deals double that
amount back to the opponent. When a Pokémon faints, the game should reset 
the 16-bit Bide damage accumulator to zero. 

The bug is that the routine handling an enemy fainting only clears the high 
byte of the 16-bit accumulator, leaving the low byte intact. Conversely, the 
routine handling a player's Pokémon fainting correctly clears both bytes.

In a link battle, a faint event is processed as a "player faint" on one 
Game Boy and an "enemy faint" on the other. This results in the consoles 
disagreeing on the accumulator value, leading to permanent desynchronization 
of the battle state when Bide damage is later calculated.
-/

namespace AutoResearch

/-- 
  The buggy clear routine (used when an enemy Pokémon faints).
  It clears the high byte but leaves the low byte intact.
-/
def impl (acc : BitVec 16) : BitVec 16 :=
  SM83.mk16 0 (SM83.lo acc)

/-- 
  The correct clear routine (used when the player's Pokémon faints).
  It resets the entire 16-bit accumulator to 0.
-/
def spec (acc : BitVec 16) : BitVec 16 :=
  0

/-! ### L1: Existence of Bug -/

theorem bug_exists : ∃ acc : BitVec 16, impl acc ≠ spec acc := by
  -- If the low byte is non-zero, the bug manifests.
  use 1
  native_decide

/-! ### L2: Universal Characterization -/

/-- The bug causes a mismatch if and only if the low byte of the accumulator was non-zero. -/
theorem bug_iff_low_byte_nonzero (acc : BitVec 16) :
  impl acc ≠ spec acc ↔ SM83.lo acc ≠ 0 := by
  have h := (by native_decide : ∀ v : BitVec 16, (SM83.mk16 0 (SM83.lo v) ≠ 0) ↔ (SM83.lo v ≠ 0))
  exact h acc

/-- In the buggy version, the high byte is always guaranteed to be zero after the call. -/
theorem buggy_clears_high_byte (acc : BitVec 16) :
  SM83.hi (impl acc) = 0 := by
  have h := (by native_decide : ∀ v : BitVec 16, SM83.hi (SM83.mk16 0 (SM83.lo v)) = 0)
  exact h acc

/-- In the buggy version, the low byte is always preserved. -/
theorem buggy_preserves_low_byte (acc : BitVec 16) :
  SM83.lo (impl acc) = SM83.lo acc := by
  have h := (by native_decide : ∀ v : BitVec 16, SM83.lo (SM83.mk16 0 (SM83.lo v)) = SM83.lo v)
  exact h acc

/-! ### L3: Fix Verification -/

/-- The fix is to clear the entire 16-bit word. -/
def fix (acc : BitVec 16) : BitVec 16 := 0

theorem fix_is_correct : ∀ acc : BitVec 16, fix acc = spec acc := by
  intro acc; rfl

/-! ### L4: Link Battle Relational Modeling -/

/-- Model of a Game Boy console's state relevant to Bide. -/
structure ConsoleState where
  bideAccumulatedDamage : BitVec 16

/-- 
  In a Link Battle, a faint event occurs. 
  Console A (Player side) runs the correct clear.
  Console B (Enemy side) runs the buggy clear.
-/
def process_faint_link_battle (initial_acc : BitVec 16) : (ConsoleState × ConsoleState) :=
  (⟨spec initial_acc⟩, ⟨impl initial_acc⟩)

/-- 
  The two consoles diverge if the low byte was non-zero.
-/
theorem link_battle_state_divergence (acc : BitVec 16) (h : SM83.lo acc ≠ 0) :
  let (sideA, sideB) := process_faint_link_battle acc
  sideA.bideAccumulatedDamage ≠ sideB.bideAccumulatedDamage := by
  simp [process_faint_link_battle, spec, impl]
  rw [bug_iff_low_byte_nonzero]
  exact h

/-- 
  Bide deals double the accumulated damage.
-/
def bide_damage (acc : BitVec 16) : Nat :=
  2 * acc.toNat

/-- 
  Desynchronization in damage calculation. 
  Side A deals 0 damage (correct), while Side B deals 2 * leftovers.
-/
theorem damage_calc_desync (acc : BitVec 16) (h : SM83.lo acc ≠ 0) :
  let (sideA, sideB) := process_faint_link_battle acc
  bide_damage sideA.bideAccumulatedDamage ≠ bide_damage sideB.bideAccumulatedDamage := by
  simp [process_faint_link_battle, bide_damage, spec, impl]
  -- Side A is 2 * 0 = 0.
  -- Side B is 2 * (impl acc).toNat.
  -- (impl acc).toNat = acc.lo.toNat.
  have h_val := buggy_preserves_low_byte acc
  have h_hi := buggy_clears_high_byte acc
  have h_toNat : (impl acc).toNat = (SM83.lo acc).toNat := by
    have h_total := (by native_decide : ∀ v : BitVec 16, (SM83.mk16 0 (SM83.lo v)).toNat = (SM83.lo v).toNat)
    exact h_total acc
  rw [h_toNat]
  intro h_zero
  -- If 2 * lo.toNat = 0, then lo.toNat = 0, which means lo = 0.
  have h_lo_zero : (SM83.lo acc).toNat = 0 := by omega
  have : SM83.lo acc = 0 := by
    apply BitVec.val_inj.mp
    exact h_lo_zero
  contradiction

/--
  Even if both consoles later receive the same amount of damage 'd', 
  the desynchronization persists because they started from different bases.
-/
theorem accumulation_desync_persistence (acc : BitVec 16) (d : BitVec 16) (h : SM83.lo acc ≠ 0) :
  let (sideA, sideB) := process_faint_link_battle acc
  let sideA_new := sideA.bideAccumulatedDamage + d
  let sideB_new := sideB.bideAccumulatedDamage + d
  sideA_new ≠ sideB_new := by
  simp [process_faint_link_battle, spec, impl]
  intro h_eq
  -- if 0 + d = (acc & 0xFF) + d, then 0 = (acc & 0xFF)
  have h_inner : (0 : BitVec 16) = SM83.mk16 0 (SM83.lo acc) := by
    -- In BitVec 16, x + d = y + d implies x = y
    exact BitVec.add_right_cancel h_eq
  have : SM83.lo acc = 0 := by
    have h_lo := (by native_decide : ∀ v : BitVec 16, 0 = SM83.mk16 0 (SM83.lo v) → SM83.lo v = 0)
    exact h_lo acc h_inner
  contradiction

end AutoResearch
