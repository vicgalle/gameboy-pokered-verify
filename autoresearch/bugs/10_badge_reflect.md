# Bug: Badge Boost Stacking Enables Catastrophic Reflect Overflow

## Gameplay Description

Three separate game mechanics interact to produce a catastrophic bug:

1. **Badge stat boosts** are reapplied to ALL stats whenever any stat changes during
   battle (not just once). Each application multiplies the stat by 9/8. So if the
   opponent uses Growl (which lowers attack), the badge boost is reapplied to defense
   too, pushing it higher.

2. **Reflect** doubles the defense stat with no upper bound check.

3. **Stat scaling** in the damage formula wraps values at 1024 (divides by 4, keeps
   only the low byte).

The result: a Cloyster with 458 defense gets the Thunder Badge defense boost. The
opponent uses Growl once, which triggers badge reapplication: defense goes from 458
to 515 (above the 512 overflow threshold). Then Reflect doubles 515 to 1030. After
damage scaling: effective defense becomes 1 instead of 128.

The opponent's Growl — a move intended to make the player weaker — actually enables
a catastrophic overflow that reduces the player's effective defense by a factor of 128.
No action from the player is needed beyond having used Reflect earlier.
