import SM83

namespace AutoResearch

/-!
# Bug: Blaine's AI Uses Super Potion Regardless of HP

## Description
In Pokémon Red/Blue, Blaine's trainer AI (Cinnabar Island Gym Leader) is 
programmed to use a Super Potion based solely on a random roll. Unlike other 
trainers, his code misses the call to `AICheckIfHPBelowFraction`. Consequently, 
Blaine will use a Super Potion even when his Pokémon is at full health, 
wasting a turn.

## Assembly Analysis
The buggy code in `engine/battle/trainer_ai.asm` is:
