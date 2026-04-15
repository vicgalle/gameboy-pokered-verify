import SM83

namespace AutoResearch

/-!
# Bug: 1/256 Miss Chance (one_in_256)

In Pokémon Red and Blue, the logic for both move accuracy and critical hit chance 
utilizes a 1-byte comparison between a threshold and a random number generated 
in the range [0, 255].

The core issue lies in the SM83 assembly pattern:
1. Generate a random byte `r` in `[0, 255]`.
2. Compare `r` with a threshold `T` using `cp T`.
3. The event (hit or critical hit) succeeds if the Carry Flag is set.
4. The event fails if the Carry Flag is not set (No Carry).

In the SM83 architecture, `cp T` sets the Carry Flag if and only if `r < T` 
(unsigned comparison). When the game calculates a "100% chance" (a threshold 
intended to represent 256/256), it uses the maximum 8-bit value, 255 ($FF). 

However, since the comparison is `r < 255`, the case where `r = 255` results 
in a failure (No Carry), even though the threshold is at its maximum. 
This results in a 1/256 (~0.39%) chance of failure for guaranteed events.
-/

/-- 
Models the SM83 `cp` instruction behavior for success/failure checks.
In the Game Boy Pokémon engine, a successful check is determined by the Carry flag.
`cp threshold` sets Carry if `roll < threshold`.
-/
def sm83_event_success (threshold : BitVec 8) (roll : BitVec 8) : Bool :=
  -- Carry is set if roll < threshold
  roll < threshold

/--
The intended specification for a "guaranteed" event.
A move with 100% accuracy or a maxed crit rate should always succeed.
-/
def spec_guaranteed (roll : BitVec 8) : Bool :=
  true

/-! ### L1: Bug Existence -/

/-- 
L1: Prove that even with a maximum threshold of 255, there exists a 
random roll that causes the check to fail.
-/
theorem bug_exists : ∃ (roll : BitVec 8), sm83_event_success 255 roll = false := by
  -- The roll of 255 is the one that triggers the bug.
  -- 255 < 255 is false, so Carry is not set.
  exists 255
  native_decide

/-! ### L2: Characterization -/

/--
L2: Prove that the failure occurs if and only if the random roll is exactly 255
when the threshold is 255. This demonstrates the 1/256 probability.
-/
theorem bug_characterization (roll : BitVec 8) :
  sm83_event_success 255 roll = false ↔ roll = 255 := by
  unfold sm83_event_success
  -- We leverage native_decide to exhaustively check all 256 BitVec 8 values.
  have h := (by native_decide : ∀ (x : BitVec 8), (x < 255 = false) ↔ x = 255)
  exact h roll

/--
L2: Prove that for the bug to be avoided entirely, the threshold would 
need to be 256 (which is impossible for an 8-bit register).
Any 8-bit threshold will always fail for at least one roll.
-/
theorem failure_always_possible (threshold : BitVec 8) :
  ∃ (roll : BitVec 8), sm83_event_success threshold roll = false := by
  -- For any T, if roll = T, then roll < T is false.
  -- Note: even if T = 0, roll = 0 makes 0 < 0 false.
  exists threshold
  unfold sm83_event_success
  simp [BitVec.lt_irrefl]

/-! ### L3: Fix Correctness -/

/--
A common fix in localized versions or fan-patches is to explicitly check 
if the threshold is 255, bypass the random roll, and force a success.
-/
def fixed_logic (threshold : BitVec 8) (roll : BitVec 8) : Bool :=
  if threshold == 255 then true else roll < threshold

/--
L3: Prove that the fixed logic satisfies the specification for 
guaranteed events (threshold 255).
-/
theorem fix_is_correct (roll : BitVec 8) :
  fixed_logic 255 roll = spec_guaranteed roll := by
  unfold fixed_logic spec_guaranteed
  simp

/--
Alternative Fix: Use an inclusive comparison (roll <= threshold).
In SM83 assembly, this would be implemented as `cp threshold` followed by 
`jr c, .hit` and `jr z, .hit`.
-/
def inclusive_logic (threshold : BitVec 8) (roll : BitVec 8) : Bool :=
  roll <= threshold

/--
L3: Prove that using inclusive comparison also fixes the "guaranteed" 255 case.
-/
theorem inclusive_fix_is_correct (roll : BitVec 8) :
  inclusive_logic 255 roll = true := by
  unfold inclusive_logic
  -- Every 8-bit value is less than or equal to 255.
  have h := (by native_decide : ∀ (x : BitVec 8), x <= 255 = true)
  exact h roll

end AutoResearch
