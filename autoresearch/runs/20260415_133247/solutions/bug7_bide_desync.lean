import SM83

namespace AutoResearch

/-!
# Bug #7: Bide Accumulated Damage Link Battle Desynchronization

In Pokémon Red/Blue, Bide damage is stored as a 16-bit Big-Endian value.
When a Pokémon faints, the accumulated Bide damage should be reset to 0.
However, `FaintEnemyPokemon` only zeroes the high byte of the damage counter.
Its link-battle counterpart, `RemoveFaintedPlayerMon`, correctly zeroes both bytes.
This causes the internal state of the two Game Boys to diverge during link battles.
-/

/-- 
The high-level representation of Bide accumulated damage (16-bit).
In memory, this is stored at `wPlayerBideAccumulatedDamage` (High) and 
`wPlayerBideAccumulatedDamage + 1` (Low).
-/
def BideDamage := BitVec 16

/--
The buggy implementation in `FaintEnemyPokemon`.
The assembly `xor a; ld [wPlayerBideAccumulatedDamage], a` only clears
 the first (high) byte of the 16-bit word.
-/
def faintEnemy (damage : BideDamage) : BideDamage :=
  -- Only the high byte (bits 8-15) is cleared.
  -- The low byte (bits 0-7) remains.
  damage &&& 0x00FF

/--
The correct implementation (spec).
This matches `RemoveFaintedPlayerMon`, which zeroes the entire 16-bit word.
-/
def removePlayer (damage : BideDamage) : BideDamage :=
  0x0000

--- Proofs ---

/-- L1: The bug exists. 
If 1 damage was accumulated, the consoles will disagree after a faint. -/
theorem bug_exists : ∃ d : BideDamage, faintEnemy d ≠ removePlayer d :=
  ⟨1, by native_decide⟩

/-- L2: Characterization.
The consoles desynchronize if and only if the low byte of the Bide damage is non-zero.
`native_decide` verifies all 65,536 possible damage values.
-/
theorem bug_iff_desync (d : BideDamage) :
  faintEnemy d ≠ removePlayer d ↔ (d &&& 0x00FF) ≠ 0 := by
  native_decide

/-- L3: Fix Correctness.
A version that clears both bytes (using `0` as the mask) matches the spec.
-/
def faintEnemy_fixed (damage : BideDamage) : BideDamage :=
  damage &&& 0x0000

theorem fix_is_correct (d : BideDamage) :
  faintEnemy_fixed d = removePlayer d := by
  native_decide

/-- L4: Relational Divergence.
In a Link Battle, Console A (Player) and Console B (Opponent) process the same
faint event differently. If the accumulated damage had a low-byte component,
the battle state permanently diverges.
-/
structure LinkBattleState where
  playerBideAccumulator : BideDamage

def consoleA_transition (s : LinkBattleState) : LinkBattleState :=
  { playerBideAccumulator := faintEnemy s.playerBideAccumulator }

def consoleB_transition (s : LinkBattleState) : LinkBattleState :=
  { playerBideAccumulator := removePlayer s.playerBideAccumulator }

theorem link_battle_desync (s : LinkBattleState) :
  (s.playerBideAccumulator &&& 0x00FF) ≠ 0 →
  consoleA_transition s ≠ consoleB_transition s := by
  intro h
  simp [consoleA_transition, consoleB_transition]
  exact (bug_iff_desync s.playerBideAccumulator).mpr h

/-- 
Additional insight: The high byte is cleared, effectively performing a modulo 256.
-/
theorem bug_is_modulo_256 (d : BideDamage) :
  faintEnemy d = BitVec.ofNat 16 (d.toNat % 256) := by
  native_decide

end AutoResearch
