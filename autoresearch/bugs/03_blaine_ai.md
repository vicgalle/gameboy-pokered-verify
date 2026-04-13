# Bug: Blaine's AI Uses Super Potion Regardless of HP

## Gameplay Description

Blaine is the Cinnabar Island Gym Leader in Pokemon Red/Blue. During battle, his
AI is programmed to occasionally use a Super Potion on his active Pokemon. However,
unlike every other trainer in the game who uses healing items, Blaine's AI does not
check whether his Pokemon actually needs healing before using the item.

This means Blaine will waste Super Potions even when his Pokemon is at full health,
giving the player a free turn advantage.
