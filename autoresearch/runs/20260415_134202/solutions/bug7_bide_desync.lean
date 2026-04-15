import SM83

/-!
# Bug #7: bide_desync

In Pokemon Red/Blue link battles, Bide accumulated damage is a 16-bit value.
When a Pokemon faints, the game is supposed to reset the Bide damage to zero.
However, the `FaintEnemyPokemon` routine only zeroes the high byte of the player's
Bide damage, leaving the low byte intact.

In a link battle, the side where the Pokemon fainted correctly zeroes both bytes
using `RemoveFaintedPlayerMon`, while the other side (the one that saw the "enemy"
faint) uses the buggy routine. This causes the Bide counters to desynchronize.
-/

namespace AutoResearch

/-- 
Represents the 16-bit Bide accumulated damage as two 8-bit registers (High, Low).
High byte is stored at wPlayerBideAccumulatedDamage, Low byte follows.
-/
structure BideState where
  hi : BitVec 8
  lo : BitVec 8
  deriving DecidableEq, Repr

/-- 
The buggy behavior in `FaintEnemyPokemon`.
It only executes `ld [wPlayerBideAccumulatedDamage], a` where `a` is 0.
This only clears the high byte.
-/
def faintedEnemyPokemon (s : BideState) : BideState :=
  { s with hi := 0 }

/-- 
The correct behavior as found in `RemoveFaintedPlayerMon`.
It clears both the high and low bytes of the Bide damage.
-/
def removeFaintedPlayerMon (s : BideState) : BideState :=
  { hi := 0, lo := 0 }

/-- The intended specification: Bide damage should be completely reset to 0. -/
def spec (s : BideState) : BideState :=
  { hi := 0, lo := 0 }

/-- 
L1: Bug Existence
A witness where the buggy routine fails to match the specification.
If the low byte is non-zero (e.g., 1), the bug manifests.
-/
theorem bug_exists : ∃ s, faintedEnemyPokemon s ≠ spec s := 
  ⟨{ hi := 0, lo := 1 }, by native_decide⟩

/--
L2: Characterization
The bug occurs if and only if the low byte of the accumulated damage is non-zero.
-/
theorem bug_iff_low_byte_nonzero (s : BideState) : 
    faintedEnemyPokemon s ≠ spec s ↔ s.lo ≠ 0 := by
  constructor
  · intro h
    contrapose! h
    unfold faintedEnemyPokemon spec
    simp [h]
  · intro h
    unfold faintedEnemyPokemon spec
    simp [h]

/--
L2: Desynchronization
In a link battle, if a Pokemon faints with a non-zero low-byte Bide counter,
the two consoles will disagree on the state.
One console runs the buggy routine, the other runs the correct routine.
-/
theorem link_battle_desync (s : BideState) : 
    s.lo ≠ 0 → faintedEnemyPokemon s ≠ removeFaintedPlayerMon s := by
  intro h
  unfold faintedEnemyPokemon removeFaintedPlayerMon
  simp [h]

/--
L3: Fix Correctness
A fixed version of the routine would clear both bytes.
-/
def fixedFaintedEnemyPokemon (s : BideState) : BideState :=
  let s' := { s with hi := 0 }
  { s' with lo := 0 }

theorem fix_is_correct (s : BideState) : fixedFaintedEnemyPokemon s = spec s := by
  unfold fixedFaintedEnemyPokemon spec
  simp

/--
L3: Verification that the fainted player routine is already correct.
-/
theorem player_routine_is_correct (s : BideState) : removeFaintedPlayerMon s = spec s := by
  rfl

end AutoResearch
