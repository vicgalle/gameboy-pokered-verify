# Bug: Bide Accumulated Damage Link Battle Desynchronization

## Gameplay Description

Bide is a move that stores damage taken over 2-3 turns and then deals double that
amount back to the opponent. In a link battle between two Game Boys, the accumulated
damage counter can become desynchronized between the two consoles.

When a Pokemon faints during battle, the game resets the Bide damage accumulator to
zero. However, the routine that handles an enemy fainting only clears one of the two
bytes of the damage counter (the high byte), leaving the low byte intact. The routine
that handles the player's Pokemon fainting correctly clears both bytes.

In a link battle, the same faint event is processed differently on each Game Boy —
one runs the incomplete clear, the other runs the correct clear. After this, the two
consoles disagree on the Bide accumulated damage. Any subsequent use of Bide will deal
different damage on each side, and the battle states permanently diverge.
