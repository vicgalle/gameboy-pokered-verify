# Heal Move Overflow Bug

In Pokemon Red/Blue, the healing moves (Recover, Softboiled, Rest) check
whether the Pokemon is already at full HP before healing. This check is
broken for Pokemon with high max HP values (256+), causing the move to fail
at specific HP gaps.

## Observable behavior

- Chansey (max HP ~703) sometimes gets "But it failed!" when using Softboiled
  at around 64% health
- Snorlax (max HP ~524) sometimes can't use Rest despite being injured
- The bug only affects Pokemon with max HP >= 256
- It seems to happen at very specific HP values

## Assembly context

The full HP check in `engine/battle/move_effects/heal.asm` (~lines 13-20)
compares currentHP to maxHP in 16-bit big-endian format (high byte first):

```
ld a, [de]      ; a = currentHP high byte
cp [hl]         ; compare with maxHP high byte → sets carry/zero flags
inc de
inc hl
ld a, [de]      ; a = currentHP low byte
sbc [hl]        ; a = currentHP_lo - maxHP_lo - borrow (from high byte cp)
jp z, .failed   ; if result is zero: "But it failed!"
```

The problem: `jp z` only checks if the `sbc` result is zero. It does NOT
verify the full 16-bit equality. The code uses `cp` for the high bytes
(which sets the carry flag for borrow) and `sbc` for the low bytes, but
then only checks the zero flag of the low-byte subtraction.

When the high bytes are DIFFERENT but the low-byte subtraction with borrow
happens to give zero, the move incorrectly thinks the Pokemon is at full HP.

## When the bug triggers

The false failure happens when:
- `currentHP_hi != maxHP_hi` (high bytes differ, so NOT at full HP)
- `(currentHP_lo - maxHP_lo - borrow) mod 256 == 0` (low byte sbc gives 0)

This occurs at HP gaps of 255, 511, and 767 — values of the form (256k - 1)
where k >= 1. But only when maxHP >= 256 so the high bytes can actually differ.

For maxHP <= 255, both bytes' high portions are 0, so the check works correctly.

## Key opcodes

- `cp [hl]` — Compare: sets carry if a < [hl], sets zero if a == [hl]
- `sbc [hl]` — Subtract with Carry (borrow): a = a - [hl] - carry_flag
- `jp z` — Jump if Zero flag is set

## Relevant files

- `engine/battle/move_effects/heal.asm`, lines 13-20 (the broken full-HP check)
