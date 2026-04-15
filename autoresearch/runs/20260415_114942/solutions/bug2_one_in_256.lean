import SM83

namespace AutoResearch

-- Modeling the 1/256 miss/failure bug in Pokemon Red/Blue.
-- In MoveHitTest and CriticalHitTest, a random byte is compared against a threshold.
-- The assembly uses: cp b / ret nc.
-- Carry flag is set if a < b. If a >= b, the carry is clear (nc), and the function returns/fails.

-- Rotate Left Circular (used in CriticalHitTest)
def rlc (x : BitVec 8) : BitVec 8 := (x <<< 1) ||| (x >>> 7)

-- The core comparison logic from the assembly
def check_success (rand : BitVec 8) (threshold : BitVec 8) : Bool :=
  -- CriticalHitTest performs 3 RLCs before comparison
  let a := rlc (rlc (rlc rand))
  a < threshold

-- Even for "100% accuracy" or "Max crit", the threshold is capped at 255 ($FF).
def MAX_THRESHOLD : BitVec 8 := 255

-- Buggy behavior: the logic used in the engine
def impl (rand : BitVec 8) : Bool := check_success rand MAX_THRESHOLD

-- Spec: For a "100% chance" move, it should always succeed regardless of random roll.
def spec (rand : BitVec 8) : Bool := true

-- L1: Bug exists - find the concrete value that causes a miss
theorem bug_exists : ∃ r, impl r ≠ spec r := 
  -- When the random value is 255, rlc-ing it stays 255. 
  -- 255 < 255 is false, causing a failure.
  ⟨255, by native_decide⟩

-- L2: Characterization - the bug occurs exactly once in the 0-255 range
theorem bug_probability_is_1_256 : 
  (List.range 256).filter (λ r => impl (BitVec.ofNat 8 r) == false) = [255] := by
  native_decide

-- L2: Universal property - any threshold <= 255 has at least one failure case
theorem bug_always_exists (threshold : BitVec 8) : ∃ r, check_success r threshold = false := by
  -- For any threshold, a random roll equal to it (or 255 if threshold is max) fails.
  -- We can prove this by checking all 256 possible thresholds.
  have h := (by native_decide : ∀ t : BitVec 8, ∃ r : BitVec 8, check_success r t = false)
  apply h

-- L3: Fix Correctness
-- A potential fix is to allow equality or use 16-bit logic where max is 256.
-- In SM83 assembly, this would mean using 'cp threshold; jr z, .hit; ret nc' 
-- or similar to include the 255 case.
def fix (rand : BitVec 8) : Bool :=
  let a := rlc (rlc (rlc rand))
  a <= 255

theorem fix_correct (r : BitVec 8) : fix r = spec r := by
  have h := (by native_decide : ∀ r : BitVec 8, rlc (rlc (rlc r)) <= 255 = true)
  exact h r

end AutoResearch
