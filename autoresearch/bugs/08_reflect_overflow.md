# Bug: Reflect and Light Screen Overflow Reduces Defense Instead of Doubling It

## Gameplay Description

Reflect is a move that doubles the user's Defense stat for the duration of the battle.
Light Screen does the same for the Special stat. However, when a Pokemon's defense is
high enough (512 or above, achievable through stat-boosting moves like Barrier), the
doubling causes an arithmetic overflow.

The damage calculation routine divides stats by 4 and keeps only the low byte when
either stat exceeds 255. This means values wrap around at 1024. When Reflect doubles
a defense of 512 to 1024, it wraps to 0 — causing a division-by-zero game freeze.
Values above 512 wrap to small numbers, meaning Reflect actively reduces the effective
defense instead of doubling it.

For example, a Cloyster (high base defense) that uses Barrier and then Reflect can end
up taking roughly twice the physical damage it would without Reflect.
