# Bug: Substitute Creates 0 HP Shield and Leaves User at 0 HP

## Gameplay Description

The move Substitute creates a decoy that absorbs hits for the user, at a cost of
1/4 of the user's max HP. However, two bugs exist in this routine:

1. **Zero-HP Substitute**: When a Pokemon's max HP is very low (1-3), the cost
   calculation (max HP divided by 4 via integer division) rounds down to 0. This
   creates a Substitute with 0 HP that breaks on the very first hit, while costing
   the user nothing.

2. **User left at 0 HP**: The routine checks whether the user can afford the
   Substitute by testing for an underflow (carry flag), but does not check whether
   the result is exactly zero. When a Pokemon's current HP equals exactly 1/4 of
   its max HP, the subtraction gives 0 with no carry, so the Substitute is created
   and the user survives at 0 HP — a state that should be impossible.
