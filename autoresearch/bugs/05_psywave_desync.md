# Bug: Psywave Causes Link Battle Desynchronization

## Gameplay Description

Psywave is a Psychic-type move that deals random damage based on the user's level.
The damage is a random value between 1 and 1.5 times the user's level. When used
in a link battle (two players connected via Game Boy link cable), Psywave can cause
the two Game Boys to desynchronize, breaking the battle.

After a desync, the two players see different battle states — different damage
values, different HP, potentially different moves being used. The battle becomes
corrupted and usually must be abandoned.

## Root Cause

In link battles, both Game Boys share a synchronized random number sequence to
ensure both sides compute identical results. The problem is that the Psywave
damage calculation has **two different implementations** — one used when the
player's Pokemon uses Psywave, and another when the opponent's Pokemon uses it.

These two implementations handle the random number generation loop differently.
Specifically, they differ in which random values they accept or reject. When a
value is rejected by one implementation but accepted by the other, the two sides
consume different numbers of random values from the shared sequence. This causes
their random number indices to diverge, and all subsequent random operations
produce different results on each Game Boy.

## Where to Look

- Psywave's damage calculation is in `engine/battle/core.asm`
- Search for "Psywave" or the damage calculation loop
- There should be TWO separate loops — one for when the player uses the move,
  and one for when the enemy uses it
- Compare the two loops carefully: look at what conditions cause a random value
  to be rejected and the loop to retry
- The random number routine (`BattleRandom` or similar) is called within these
  loops
- The key difference is likely in how the value zero (0) is handled

## Severity

High in link battles. The desync permanently corrupts the battle state. However,
Psywave is not a commonly used move, so this rarely occurs in practice.
