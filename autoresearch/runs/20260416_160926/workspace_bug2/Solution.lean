import SM83
import Harness

namespace AutoResearch

/-!
# Bug #2: 1/256 Miss Chance on "100% Accuracy" Moves

In Pokémon Red and Blue, moves with "100% accuracy" (represented by the value 255/255)
can still miss with a probability of 1 in 256. This is caused by the use of a 
strict "less-than" comparison (`cp` followed by `jr nc`) against the random byte.

## Assembly implementation (Gen 1):
