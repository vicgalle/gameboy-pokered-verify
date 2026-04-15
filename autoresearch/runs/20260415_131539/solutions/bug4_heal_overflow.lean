import SM83

namespace AutoResearch

/-!
# Bug: heal_overflow

## Description
In Pokemon Red/Blue, the comparison check for healing moves (Recover, Softboiled, Rest)
is implemented incorrectly for 16-bit HP values. Specifically, the check to see if the 
Pokemon is already at full HP uses a buggy sequence of `cp` and `sbc` instructions.

## Assembly Analysis
