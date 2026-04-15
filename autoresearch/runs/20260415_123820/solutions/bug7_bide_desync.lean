import SM83

/-!
# Bug #7: bide_desync

## Gameplay Description
Bide is a move that stores damage taken over 2-3 turns and then deals double that
amount back to the opponent. In a link battle between two Game Boys, the accumulated
damage counter can become desynchronized.

When a Pokemon faints, the game should reset the Bide damage accumulator to zero. 
However, `FaintEnemyPokemon` (called when the opponent's mon faints) only clears 
one byte (the high byte) of the player's damage counter. Its counterpart 
`RemoveFaintedPlayerMon` (called when the player's own mon faints) correctly 
clears both bytes.

In a link battle, the same faint event triggers `FaintEnemyPokemon` on one console 
and `RemoveFaintedPlayerMon` on the other. If the accumulated damage was not 
a multiple of 256, the two consoles will disagree on the Bide damage, leading 
to permanent desynchronization of the battle state.
-/

namespace AutoResearch

/-- 
  Models the 16-bit Bide accumulated damage in the Game Boy's big-endian memory format.
  In Pokemon Red, damage is typically stored as [High Byte, Low Byte].
-/
def BideDamage := BitVec 16

/-- 
  The buggy implementation found in `FaintEnemyPokemon`.
  It only clears the high byte: `ld [wPlayerBideAccumulatedDamage], a` 
  where `a` is 0.
-/
def impl (d : BideDamage) : BideDamage :=
  -- Clear the high 8 bits (big-endian), leave the low 8 bits.
  -- Equivalent to d % 256.
  d &&& (BitVec.ofNat 16 0x00FF)

/-- 
  The intended behavior (and the one implemented in `RemoveFaintedPlayerMon`).
  It clears both bytes, setting the damage to 0.
-/
def spec (_ : BideDamage) : BideDamage :=
  BitVec.ofNat 16 0

/-- 
  A proposed fix that clears both the high and low bytes of the 16-bit word.
-/
def fix (d : BideDamage) : BideDamage :=
  let highCleared := d &&& (BitVec.ofNat 16 0x00FF)
  highCleared &&& (BitVec.ofNat 16 0xFF00)

/-! ### Proofs -/

/-- 
  L1: Bug Exists. 
  If the player has accumulated 1 unit of damage (0x0001), 
  the buggy clear leaves it as 1, while the spec requires 0.
-/
theorem bug_exists : exists d, impl d != spec d := by
  -- Witness: 1 damage point (0x0001)
  let d := BitVec.ofNat 16 1
  use d
  native_decide

/-- 
  L2: Characterization.
  The bug triggers (desync occurs) if and only if the low byte of the 
  accumulated damage is non-zero.
-/
theorem bug_iff_low_byte_nonzero (d : BideDamage) : 
  impl d != spec d ↔ (d &&& BitVec.ofNat 16 0x00FF) != BitVec.ofNat 16 0 := by
  simp [impl, spec]

/--
  Alternative L2: The bug triggers for any value not divisible by 256.
-/
theorem bug_iff_not_div_256 (d : BideDamage) :
  impl d != spec d ↔ d.toNat % 256 != 0 := by
  simp [impl, spec]
  -- BitVec 16 is small enough for native_decide to confirm the equivalence
  have h : ∀ (x : BitVec 16), (x &&& BitVec.ofNat 16 255 != BitVec.ofNat 16 0) ↔ x.toNat % 256 != 0 := by
    native_decide
  exact h d

/-- 
  L3: Fix Correctness.
  The fix (clearing both bytes) matches the specification for all possible 16-bit values.
-/
theorem fix_correct (d : BideDamage) : fix d = spec d := by
  unfold fix spec
  -- This checks all 65536 possible values of BitVec 16
  have h : ∀ (x : BitVec 16), (x &&& BitVec.ofNat 16 0x00FF) &&& BitVec.ofNat 16 0xFF00 = BitVec.ofNat 16 0 := by
    native_decide
  exact h d

/-- 
  L4: Link Desynchronization Property.
  In a link battle, the same event (Pokemon faints) causes Console A (Enemy Faint) 
  to result in `impl` and Console B (Player Faint) to result in `spec`.
  This theorem shows that the link state diverges whenever the low byte is non-zero.
-/
theorem link_battle_desync (initial_damage : BideDamage) :
  initial_damage.toNat % 256 != 0 → impl initial_damage != spec initial_damage := by
  intro h_nonzero
  rw [bug_iff_not_div_256]
  exact h_nonzero

end AutoResearch
