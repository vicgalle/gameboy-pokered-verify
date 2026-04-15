import SM83

namespace AutoResearch

/-!
# Bug #7: Bide Accumulated Damage Link Battle Desynchronization

## Description
Bide stores damage taken over 2-3 turns and then deals double that amount back. 
When a Pokemon faints, Bide's accumulated damage should be reset to zero. 

In Pokémon Red/Blue, the routine `FaintEnemyPokemon` (called when the enemy faints) 
only clears the high byte of the player's 16-bit Bide damage counter due to a 
coding error. In contrast, the routine `RemoveFaintedPlayerMon` (called when the 
player's Pokemon faints) correctly clears both bytes.

In a link battle, one Game Boy processes a faint as an "enemy faint" while the 
other processes it as a "player faint". This leads to the two consoles having 
different values for the Bide damage counter, causing a permanent desynchronization.

## Formalization
Bide damage is stored in Big-Endian format in Pokémon Red. 
- `wPlayerBideAccumulatedDamage` points to the High Byte.
- `wPlayerBideAccumulatedDamage + 1` points to the Low Byte.
-/

/-- 
Model of the buggy Bide damage reset (`FaintEnemyPokemon`).
Only the high byte is cleared because `ld [wPlayerBideAccumulatedDamage], a`
is used instead of a 16-bit clear. This leaves the low byte intact.
In Big-Endian, clearing the high byte is equivalent to `value % 256`.
-/
def impl (damage : BitVec 16) : BitVec 16 :=
  -- High byte (bits 8-15) becomes 0.
  -- Low byte (bits 0-7) remains.
  damage % 256

/-- 
Model of the correct Bide damage reset (`RemoveFaintedPlayerMon`).
Both bytes are cleared to zero.
-/
def spec (_damage : BitVec 16) : BitVec 16 :=
  0

/-- 
L1: Bug Exists
We provide a concrete witness: if the player has 1 point of accumulated damage,
the buggy routine leaves it as 1, while the correct routine resets it to 0.
-/
theorem bug_exists : ∃ d : BitVec 16, impl d ≠ spec d := by
  -- Witness: 1 damage point (0x0001)
  exists 1
  -- impl(1) = 1, spec(1) = 0
  native_decide

/-- 
L2: Characterization
The desynchronization occurs if and only if the low byte of the accumulated 
damage was non-zero. If the low byte happened to be zero, both routines 
accidentally result in the same value (0).
-/
theorem bug_triggers_iff_low_byte_nonzero (d : BitVec 16) :
    impl d ≠ spec d ↔ d % 256 ≠ 0 := by
  unfold impl spec
  simp

/--
L2: Bounds Property
The bug always results in a value that fits in a single byte (less than 256).
-/
theorem bug_upper_bound (d : BitVec 16) : (impl d).toNat < 256 := by
  have h := (by native_decide : ∀ x : BitVec 16, (impl x).toNat < 256)
  exact h d

/-- 
L3: Fix Correctness
A fix must clear both the high and low bytes.
In SM83 assembly, this would be:
  xor a
  ld [wPlayerBideAccumulatedDamage], a
  ld [wPlayerBideAccumulatedDamage + 1], a
-/
def fix (damage : BitVec 16) : BitVec 16 :=
  let high_cleared := damage % 256
  -- Clearing the remaining low byte results in 0
  high_cleared - (high_cleared % 256)

theorem fix_correct (d : BitVec 16) : fix d = spec d := by
  unfold fix spec
  simp

/-- 
L4: Relational Link Battle Model
We model the state of two Game Boys in a link battle. 
Console A (where the enemy faints) and Console B (where the player faints)
start with the same Bide damage counter but end up in different states.
-/
structure LinkState where
  bideDamage : BitVec 16

/-- Console A processes the event using the buggy FaintEnemyPokemon logic. -/
def consoleA_process (s : LinkState) : LinkState :=
  { bideDamage := impl s.bideDamage }

/-- Console B processes the event using the correct RemoveFaintedPlayerMon logic. -/
def consoleB_process (s : LinkState) : LinkState :=
  { bideDamage := spec s.bideDamage }

/-- 
The battle permanently desynchronizes if the Bide damage 
accumulator has a non-zero low byte at the time of fainting.
-/
theorem link_desync_proof :
    ∃ (s : LinkState), (consoleA_process s).bideDamage ≠ (consoleB_process s).bideDamage := by
  -- Use a state where accumulated damage is 1
  exists { bideDamage := 1 }
  native_decide

end AutoResearch
