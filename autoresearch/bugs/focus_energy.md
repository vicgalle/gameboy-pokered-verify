# Focus Energy Bug

In Pokemon Red/Blue, the move Focus Energy is supposed to increase the user's
critical hit rate. However, players have observed that using Focus Energy
actually DECREASES the critical hit rate — the exact opposite of its purpose.

## Observable behavior

- A Pokemon using Focus Energy gets fewer critical hits than one not using it
- The move is effectively anti-synergistic: it makes crits less likely

## Assembly context

The CriticalHitTest routine in `engine/battle/core.asm` (around line 4478)
computes the critical hit rate from the Pokemon's base speed:

1. Load base speed into register `b`
2. `srl b` — shift right logical, halving it (b = base_speed / 2)
3. Check if Focus Energy is active (GETTING_PUMPED bit in battle status)
4. If Focus Energy is active: `srl b` — shifts RIGHT again (b = base_speed / 4)
5. If Focus Energy is NOT active: `sla b` — shifts LEFT (b = base_speed, restoring it)
6. Later compares `b` against a random number to determine crit

The Focus Energy branch (step 4) does `srl b` (divide by 2) where it should
do `sla b` (multiply by 2). This means Focus Energy quarters the crit rate
instead of restoring/doubling it.

The "no Focus Energy" branch correctly does `sla b` to undo the initial
halving. So without Focus Energy, the effective rate is base_speed (with bit 0
cleared). With Focus Energy (bugged), the effective rate is base_speed / 4.

## Key opcodes

- `srl` — Shift Right Logical: shifts all bits right, bit 0 goes to carry, bit 7 becomes 0. Effectively unsigned divide by 2.
- `sla` — Shift Left Arithmetic: shifts all bits left, bit 7 goes to carry, bit 0 becomes 0. Effectively multiply by 2.

## Relevant files

- `engine/battle/core.asm`, CriticalHitTest routine (~line 4478)
- The bug is in the `.focusEnergyUsed` branch (~line 4514)
