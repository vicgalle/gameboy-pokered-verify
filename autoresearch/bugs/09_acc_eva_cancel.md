# Bug: Accuracy and Evasion Stage Boosts Do Not Cancel When Equal

## Gameplay Description

In the Pokemon battle system, accuracy and evasion are modified by stage multipliers.
If a Pokemon's accuracy is raised by +1 stage and the opponent's evasion is also raised
by +1 stage, the two modifiers should cancel out, leaving the effective hit chance
unchanged from the base accuracy.

However, due to how the stat modifier ratios are stored and applied, equal accuracy and
evasion boosts do not perfectly cancel. The effective accuracy after equal +/- boosts is
slightly lower than the base value. For a move with 255 base accuracy (the maximum),
equal +1/-1 stages give 252 effective accuracy — a loss of 3 points. Equal +5/-5 is
the worst case, losing 6 accuracy points (249 vs 255).

Two factors cause this: the modifier table stores approximate fractions (e.g., stage -1
is stored as 66/100 instead of the exact 2/3), and intermediate integer truncation
between the two multiplication passes loses additional precision. Even when the fraction
product is mathematically exact, floor division between passes still causes a loss.
