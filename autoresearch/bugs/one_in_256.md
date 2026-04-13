# 1/256 Accuracy Miss and Critical Hit Miss

In Pokemon Red/Blue, moves with 100% accuracy can still miss 1 out of every
256 uses. The same issue affects critical hit calculations.

## Observable behavior

- A move listed as having 100% accuracy (like Swift) occasionally misses
- Critical hits seem to happen slightly less often than the math suggests
- The probability error is small (1/256 per check) but universal

## Assembly context — Accuracy

The MoveHitTest routine in `engine/battle/core.asm` (~line 5321) generates a
random byte and compares it against the move's accuracy:

```
call BattleRandom     ; random byte in a (0..255)
cp b                  ; compare: sets carry if a < b
jr nc, .moveMissed    ; jump if NO carry, i.e. a >= b
```

The `cp` instruction sets the carry flag when `a < b`. So `jr nc` (jump if no
carry) triggers when `a >= b`. This means the move hits only when
`random < accuracy`, giving accuracy/256 hit chance.

For accuracy=255 (which the game treats as 100% via the `percent` macro where
`100 percent = 255`), the hit chance is 255/256 — not 256/256 as intended.

## Assembly context — Critical hits

The same pattern appears at the end of CriticalHitTest (~line 4534):

```
call BattleRandom
rlc a / rlc a / rlc a   ; rotate random value
cp b                      ; compare against crit rate
ret nc                    ; no crit if a >= b
```

Again, `ret nc` returns (no crit) when `random >= critRate`, so the crit
triggers only when `random < critRate` — off by one.

## Key opcodes

- `cp b` — Compare: subtracts b from a, sets flags but discards result. Carry set if a < b.
- `jr nc` / `ret nc` — Jump/Return if No Carry, i.e. if a >= b after cp.

## Relevant files

- `engine/battle/core.asm`, MoveHitTest accuracy check (~line 5321)
- `engine/battle/core.asm`, CriticalHitTest final comparison (~line 4534)
