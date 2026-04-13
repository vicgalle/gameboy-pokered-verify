# Blaine AI Super Potion Bug

In Pokemon Red/Blue, Blaine's trainer AI uses a Super Potion without first
checking whether his Pokemon's HP is low enough to need healing. This means
Blaine wastes healing items even at full health.

## Observable behavior

- Blaine sometimes uses a Super Potion when his Pokemon is at full HP
- The potion heals 0 HP in this case — a complete waste of his item and turn
- Other gym leaders with healing items (Erika, etc.) only heal when injured

## Assembly context

In `engine/battle/trainer_ai.asm`, Blaine's AI (~line 387):

```
BlaineAI:
    cp 25 percent + 1    ; 25% random chance to attempt healing
    ret nc               ; 75% of the time, skip healing
    jp AIUseSuperPotion  ; use Super Potion immediately — NO HP CHECK!
```

Compare with Erika's AI (~line 374), which correctly checks HP first:

```
ErikaAI:
    cp 50 percent + 1    ; 50% random chance
    ret nc               ; skip otherwise
    ld a, 10             ; divisor for HP fraction check
    call AICheckIfHPBelowFraction  ; checks if currentHP < maxHP / 10
    ret nc               ; skip if HP is high enough
    jp AIUseSuperPotion  ; only heals if HP is low
```

Every other healing trainer (Erika, Lorelei, Agatha, Sabrina, Champion's Rival)
calls `AICheckIfHPBelowFraction` before using their healing item. Blaine is
the only one who skips this check and jumps directly to `AIUseSuperPotion`.

Super Potion heals 50 HP, capped at max HP. When used at full HP, the
net healing is 0.

## Key detail

- `AICheckIfHPBelowFraction` — a routine that checks if currentHP is below
  maxHP divided by the value in register `a`. Returns carry if HP is low.
- `ret nc` — return if no carry, meaning "skip if HP is NOT low"
- Blaine simply never calls this check

## Relevant files

- `engine/battle/trainer_ai.asm`, BlaineAI (~line 387)
- `engine/battle/trainer_ai.asm`, ErikaAI (~line 374) for comparison
- `engine/battle/trainer_ai.asm`, AICheckIfHPBelowFraction and AIUseSuperPotion
