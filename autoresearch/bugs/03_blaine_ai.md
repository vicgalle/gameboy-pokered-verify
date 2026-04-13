# Bug: Blaine's AI Uses Super Potion Regardless of HP

## Gameplay Description

Blaine is the Cinnabar Island Gym Leader in Pokemon Red/Blue. During battle, his
AI is programmed to occasionally use a Super Potion on his active Pokemon. However,
unlike every other trainer in the game who uses healing items, Blaine's AI does not
check whether his Pokemon actually needs healing before using the item.

This means Blaine will waste Super Potions even when his Pokemon is at full health,
giving the player a free turn advantage.

## Root Cause

Each trainer's AI script has a section that controls item usage. Most trainers call
a routine that checks whether the Pokemon's current HP is below a certain fraction
of its maximum HP before deciding to use a healing item. Blaine's AI script is
missing this HP check entirely — after passing a random chance gate, it jumps
directly to the "use Super Potion" routine without verifying that healing is needed.

## Where to Look

- Trainer AI scripts are in `engine/battle/trainer_ai.asm`
- Search for Blaine's AI section (look for `Blaine` in the file)
- Compare Blaine's script with other Gym Leaders who also use healing items
  (e.g., Erika, or Elite Four members)
- The HP check routine that Blaine skips is likely named something like
  `AICheckIfHPBelowFraction` or similar
- The healing routine itself (e.g., `AIUseSuperPotion`) is shared by all trainers

## Severity

Moderate. Blaine wastes items and gives the player free turns. The bug is limited
to Blaine's fights specifically.
