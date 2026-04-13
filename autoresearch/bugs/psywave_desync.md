# Psywave Link Battle Desync

In Pokemon Red/Blue link battles, the move Psywave can cause the two Game Boys
to permanently desynchronize. After a Psywave desync occurs, the battle becomes
corrupted — the two players see different things happening.

## Observable behavior

- Occasionally in link battles, using Psywave causes the game state to diverge
- After the desync, all subsequent battle actions are out of sync
- The desync is permanent for the rest of the battle
- The player's Psywave can never deal 0 damage, but the enemy's can

## Assembly context

In link battles, both Game Boys share a synchronized list of random numbers.
Psywave has TWO different implementations — one for when the player attacks
and one for when the enemy attacks.

**Player's Psywave** (`engine/battle/core.asm` ~line 4664):

```
; b = level * 1.5
.loop
    call BattleRandom    ; draw from shared random list
    and a                ; test if zero
    jr z, .loop          ; REJECT 0 — draw again
    cp b                 ; compare against damage cap
    jr nc, .loop         ; reject if >= b
    ld b, a              ; accept: damage in [1, b)
```

**Enemy's Psywave** (`engine/battle/core.asm` ~line 4785):

```
; b = level * 1.5
.loop
    call BattleRandom    ; draw from shared random list
    cp b                 ; compare against damage cap
    jr nc, .loop         ; reject if >= b
    ld b, a              ; accept: damage in [0, b)
```

The player's loop rejects 0 (via `and a; jr z, .loop`) and accepts values in
[1, b). The enemy's loop accepts 0 and takes values in [0, b).

## Why this causes a desync

In a link battle, both Game Boys execute the SAME damage calculation using a
shared random number sequence. When one Game Boy is the "player" and the other
is the "enemy" for a given Psywave attack:

1. Both start reading from the same position in the shared random list
2. If the random value is 0:
   - The "player" side rejects it and draws ANOTHER random number
   - The "enemy" side accepts it immediately
3. Now the two Game Boys are at different positions in the random list
4. All future random draws are different — the battle is permanently desynced

The `and a; jr z, .loop` instruction in the player's loop is the root cause.
It makes the player consume an extra random number whenever a 0 appears.

## Key detail

- `and a` — AND accumulator with itself. Sets Zero flag if a == 0. Does NOT
  consume the value, just tests it.
- `jr z` — Jump if Zero flag set
- The asymmetry is that the player's loop has this extra zero-check while the
  enemy's loop does not

## Relevant files

- `engine/battle/core.asm`, player Psywave loop (~line 4664)
- `engine/battle/core.asm`, enemy Psywave loop (~line 4785)
