import SM83

/-!
# Bug #7: bide_desync

In Pokémon Red/Blue, the Bide move stores damage taken in a 16-bit counter.
When a Pokémon faints, this counter should be reset to zero.

The routine `FaintEnemyPokemon` contains a bug where it only zeroes the 
high byte of the player's accumulated Bide damage. Its counterpart, 
`RemoveFaintedPlayerMon` (called when the player's Pokémon faints), 
correctly zeroes both the high and low bytes.

In a link battle, if a Pokémon faints, one Game Boy processes it as an 
"enemy" fainting while the other processes it as a "player" fainting. 
This causes the Bide damage counters to desynchronize between the two consoles 
if the low byte was non-zero.
-/

namespace AutoResearch

/-- 
Represents the 16-bit Bide accumulated damage counter.
Pokémon Red/Blue typically stores 16-bit values in Big Endian in memory.
`wPlayerBideAccumulatedDamage` is the address of the high byte.
-/
structure BideState where
  hi : BitVec 8
  lo : BitVec 8
  deriving DecidableEq, Repr

/-- 
Converts the BideState into a single 16-bit value for arithmetic.
Uses Big Endian representation (Hi byte is MSB).
-/
def BideState.toBitVec16 (s : BideState) : BitVec 16 :=
  s.hi ++ s.lo

/-- 
Buggy behavior in `FaintEnemyPokemon`:
`xor a`
`ld [wPlayerBideAccumulatedDamage], a` 
Only the high byte is cleared.
-/
def faintEnemyBuggy (s : BideState) : BideState :=
  { hi := 0, lo := s.lo }

/-- 
Correct behavior in `RemoveFaintedPlayerMon`:
Both bytes of the 16-bit counter are cleared.
-/
def faintPlayerCorrect (s : BideState) : BideState :=
  { hi := 0, lo := 0 }

/-- The intended specification: the entire 16-bit counter is 0. -/
def spec (s : BideState) : BideState :=
  { hi := 0, lo := 0 }

/-! ### L1: Bug Existence -/

/-- The bug exists: there is a state where the buggy clear does not match the spec. -/
theorem bug_exists : ∃ s, faintEnemyBuggy s ≠ spec s := 
  ⟨{ hi := 0, lo := 1 }, by native_decide⟩

/-! ### L2: Characterization -/

/-- 
The bug triggers (fails to clear memory) if and only if the low byte of 
the Bide damage counter was non-zero.
-/
theorem bug_iff_low_byte_nonzero (s : BideState) : 
    faintEnemyBuggy s ≠ spec s ↔ s.lo ≠ 0 := by
  simp [faintEnemyBuggy, spec]

/-- 
In a link battle, the state desynchronizes between Console A (seeing an enemy faint)
and Console B (seeing a player faint) whenever the low byte is non-zero.
-/
theorem link_battle_desync_condition (s : BideState) :
    faintEnemyBuggy s ≠ faintPlayerCorrect s ↔ s.lo ≠ 0 := by
  simp [faintEnemyBuggy, faintPlayerCorrect]

/-! ### L3: Fix Correctness -/

/-- 
The fix: clear both the high byte and the low byte (wPlayerBideAccumulatedDamage + 1).
-/
def fixedFaintEnemy (s : BideState) : BideState :=
  let s' := { s with hi := 0 }  -- ld [wPlayerBideAccumulatedDamage], a
  { s' with lo := 0 }          -- ld [wPlayerBideAccumulatedDamage + 1], a

/-- Proving the fix matches the intended specification. -/
theorem fix_is_correct (s : BideState) : fixedFaintEnemy s = spec s := by
  simp [fixedFaintEnemy, spec]

/-! ### L4: Relational Divergence -/

/-- 
Models how Bide damage accumulates over time.
Damage is added to the 16-bit state.
-/
def accumulate (s : BideState) (damage : BitVec 16) : BideState :=
  let val := s.toBitVec16 + damage
  { hi := val.extractLsb 15 8, lo := val.extractLsb 7 0 }

/-- 
If the consoles desynchronize after a faint, and then both take the 
same amount of damage, they will continue to hold different Bide values.
-/
theorem desync_persists (s : BideState) (damage : BitVec 16) :
    s.lo ≠ 0 → accumulate (faintEnemyBuggy s) damage ≠ accumulate (faintPlayerCorrect s) damage := by
  intro h_low
  simp [faintEnemyBuggy, faintPlayerCorrect, accumulate, BideState.toBitVec16]
  intro h_eq
  have h_low_zero : s.lo = 0 := by
    -- Extract the low 8 bits from the 16-bit equality
    simp [BitVec.ext_iff] at h_eq
    have h_lo := h_eq (i := 0)
    -- This follows because the low byte of (0++lo + dmg) vs (0++0 + dmg) 
    -- only matches if lo was 0.
    contrapose! h_eq
    native_decide
  exact h_low h_low_zero

/-- 
Final verification: The player-side routine in Pokémon Red is actually 
already correct/bug-free.
-/
theorem player_side_is_already_correct (s : BideState) : 
    faintPlayerCorrect s = spec s := rfl

end AutoResearch
