# Bug: Focus Energy Quarters Critical Hit Rate Instead of Doubling It

## Gameplay Description

The move Focus Energy is supposed to increase the user's critical hit rate. In
Generation 1, the critical hit rate is derived from the Pokemon's base Speed stat.
Focus Energy should multiply this rate by a factor, making critical hits more likely.

However, due to a bug, Focus Energy actually **reduces** the critical hit rate instead
of increasing it. Players who use Focus Energy end up getting fewer critical hits
than if they hadn't used the move at all.

## Root Cause

The bug is in the critical hit rate calculation routine. After computing an initial
value from the base Speed, the code applies Focus Energy's modifier using a bitwise
shift instruction. The wrong shift direction is used — a right shift where a left
shift was intended — causing the value to be divided instead of multiplied.

## Where to Look

- The critical hit calculation is in `engine/battle/core.asm`
- Search for the `CriticalHitTest` label
- Look at the shift instructions (`srl`, `sla`, `sra`) applied to the critical
  hit rate value
- The Focus Energy flag is checked via bit operations on a battle status byte

## Severity

This is one of the most well-known bugs in Pokemon Red/Blue. It's particularly
impactful because it makes a strategic move actively harmful to use.
