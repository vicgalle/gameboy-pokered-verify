import SM83

namespace AutoResearch

/-!
### Bug #7: Bide Accumulated Damage Link Battle Desynchronization

In Pokémon Red/Blue, Bide damage is stored as a 16-bit Big-Endian value.
When a Pokémon faints, the accumulated Bide damage should be reset to zero.
In `FaintEnemyPokemon`, the code only zeroes the high byte (`wPlayerBideAccumulatedDamage`),
leaving the low byte (`wPlayerBideAccumulatedDamage + 1`) intact.
Its link-battle counterpart, `RemoveFaintedPlayerMon`, correctly zeroes both bytes.
This causes the internal state of two Game Boys to diverge during link battles.
-/

/-- Accumulated Bide damage is a 16-bit value. -/
def BideDamage := BitVec 16

/-- 
The buggy routine `FaintEnemyPokemon`.
`xor a; ld [wPlayerBideAccumulatedDamage], a`
This clears the first byte (High Byte in Big-Endian), leaving the low 8 bits.
-/
def impl (damage : BideDamage) : BideDamage :=
  damage &&& 0x00FF

/-- 
The correct routine `RemoveFaintedPlayerMon`.
Zeros the entire 16-bit damage counter.
-/
def spec (damage : BideDamage) : BideDamage :=
  0x0000

--- Proofs ---

/-- L1: Bug Exists.
A concrete witness where the two Game Boys will diverge (e.g., 1 damage accumulated).
-/
theorem bug_exists : ∃ d : BideDamage, impl d ≠ spec d :=
  ⟨1, by native_decide⟩

/-- L2: Characterization.
The consoles desynchronize if and only if the low byte of the Bide damage is non-zero.
`native_decide` checks all 65,536 possible states.
-/
theorem bug_iff_desync (d : BideDamage) :
  impl d ≠ spec d ↔ (d &&& 0x00FF) ≠ 0 := by
  native_decide

/-- L2: Numerical Behavior.
The buggy implementation effectively applies a modulo 256 to the damage counter.
-/
theorem bug_is_modulo_256 (d : BideDamage) :
  impl d = BitVec.ofNat 16 (d.toNat % 256) := by
  native_decide

/-- L3: Fix Correctness.
A routine that zeroes both bytes matches the intended specification.
-/
def fix (damage : BideDamage) : BideDamage :=
  damage &&& 0x0000

theorem fix_is_correct (d : BideDamage) :
  fix d = spec d := by
  native_decide

/-- L4: Relational Divergence.
In a link battle, the 'local' and 'remote' Game Boys process the same faint event
using different functions. If the low byte is non-zero, they diverge.
-/
structure BattleState where
  bide_acc : BideDamage

def transition_local (s : BattleState) : BattleState :=
  ⟨impl s.bide_acc⟩

def transition_remote (s : BattleState) : BattleState :=
  ⟨spec s.bide_acc⟩

theorem link_battle_divergence (s : BattleState) :
  (s.bide_acc &&& 0x00FF) ≠ 0 → transition_local s ≠ transition_remote s := by
  intro h
  simp [transition_local, transition_remote]
  -- Use the characterization from L2
  have h_bug := (bug_iff_desync s.bide_acc).mpr h
  exact h_bug

/-- 
Further L4: If the high byte was non-zero but the low byte was zero,
the consoles actually stay in sync by accident.
-/
theorem accidental_sync (s : BattleState) :
  (s.bide_acc &&& 0x00FF) = 0 → transition_local s = transition_remote s := by
  intro h
  simp [transition_local, transition_remote, impl, spec]
  -- If low byte is 0, and impl clears high byte, the result is 0.
  have : (s.bide_acc &&& 0x00FF) = 0 → (s.bide_acc &&& 0x00FF) = 0 := id
  exact this h

end AutoResearch
