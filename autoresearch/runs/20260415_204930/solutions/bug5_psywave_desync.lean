import SM83
import Harness

namespace AutoResearch

/-!
# Bug #5: Psywave Link Battle Desynchronization

## Root Cause
The player-attacks and enemy-attacks code paths use **different** Psywave loops:

**Player** (`core.asm:4664–4667`):
