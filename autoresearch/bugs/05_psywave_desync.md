# Bug: Psywave Causes Link Battle Desynchronization

## Gameplay Description

Psywave is a Psychic-type move that deals random damage based on the user's level.
The damage is a random value between 1 and 1.5 times the user's level. When used
in a link battle (two players connected via Game Boy link cable), Psywave can cause
the two Game Boys to desynchronize, breaking the battle.

After a desync, the two players see different battle states — different damage
values, different HP, potentially different moves being used. The battle becomes
corrupted and usually must be abandoned.

