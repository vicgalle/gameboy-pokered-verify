# Bug: Healing Moves Fail at Certain HP Gaps

## Gameplay Description

Recovery moves like Recover, Softboiled, and Rest are supposed to restore a
Pokemon's HP. However, under specific conditions, these moves incorrectly report
that the Pokemon is already at full HP and fail to heal, even though the Pokemon
has taken damage and genuinely needs healing.

This happens when the difference between the Pokemon's current HP and maximum HP
falls at certain specific values. The move's "are you already at full HP?" check
produces a false positive, blocking the heal.

## Root Cause

The Game Boy's SM83 CPU is an 8-bit processor, but Pokemon HP values can exceed
255 (they are 16-bit values stored as two bytes: a high byte and a low byte). The
routine that checks whether current HP equals max HP performs the comparison one
byte at a time. Due to how the comparison logic and carry flag interact when
processing the two bytes, certain combinations of high and low bytes cause the
"already full" check to incorrectly succeed.

The bug is in the routine that handles healing moves. It compares the 16-bit
current HP against the 16-bit max HP, but the byte-by-byte comparison has an
error in its logic.

## Where to Look

- The healing/recovery logic is in the battle engine files under `engine/battle/`
- Search for routines related to HP recovery, healing moves, or "Recover"
- Look for 16-bit comparison code that checks high byte and low byte separately
- The comparison likely uses `cp` instructions on individual bytes with conditional
  jumps based on carry and zero flags
- Pay attention to how the code handles the case where the high bytes are equal
  but the low bytes differ

## Severity

Moderate. Affects high-HP Pokemon (those with max HP > 255) in specific damage
scenarios. Most commonly seen with Pokemon like Chansey or Snorlax that have
very high HP stats.
