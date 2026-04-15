import SM83

namespace AutoResearch

/--
Models the comparison logic used in MoveHitTest and CriticalHitTest.
In the SM83 CPU:
`cp b` computes `A - B` and sets flags.
The Carry flag (C) is set if `A < B` (unsigned).
The game logic uses `ret nc` (Return No Carry) after the comparison.
This means the move/crit fails if `A >= B` and continues (succeeds) if `A < B`.
-/
def check_success (threshold rand : BitVec 8) : Bool :=
  rand.toNat < threshold.toNat

/--
The buggy implementation found in Pokémon Red/Blue.
Even when the intended probability is "100%", the engine uses an 8-bit
threshold capped at 255 ($FF). Because the random roll is also 0-255,
rolling a 255 results in `255 < 255` being false.
-/
def impl (threshold rand : BitVec 8) : Bool :=
  check_success threshold rand

/--
The intended behavior: a move or effect with a "100% rate" (represented by 
the maximum threshold 255) should always succeed regardless of the random roll.
-/
def spec (threshold rand : BitVec 8) : Bool :=
  if threshold == 255 then true else check_success threshold rand

/-- 
L1: Bug Existence. 
For a maximum accuracy/crit threshold of 255, a random roll of 255 
causes a failure (miss) where the spec expects success.
-/
theorem bug_exists : ∃ t r, t = 255 ∧ r = 255 ∧ impl t r = false ∧ spec t r = true := by
  exists 255, 255
  simp [impl, spec, check_success]
  native_decide

/-- 
L2: Characterization.
The bug triggers (impl differs from spec) if and only if the threshold
is set to the maximum (255) and the random roll hits exactly 255.
-/
theorem bug_iff (t r : BitVec 8) :
  impl t r ≠ spec t r ↔ (t = 255 ∧ r = 255) := by
  revert t r
  native_decide

/--
L2: Probability Ceiling.
No matter how high the threshold is (up to 255), there is always at least 
one random value (255) that results in failure in the buggy implementation.
This proves that 100% accuracy is impossible.
-/
theorem always_possible_to_miss (t : BitVec 8) : ∃ r, impl t r = false := by
  exists 255
  simp [impl, check_success]
  have h := t.toNat_lt_256
  omega

/--
L2: Monotonicity.
Lowering the threshold always results in a success set that is a subset
of the higher threshold's success set.
-/
theorem success_monotonic (t1 t2 r : BitVec 8) : 
  t1.toNat <= t2.toNat → impl t1 r = true → impl t2 r = true := by
  unfold impl check_success
  intro h1 h2
  simp_all
  omega

/--
L3: Fix Correctness.
A proper fix handles the 255 threshold as a special case for 100% success.
-/
def fix (t r : BitVec 8) : Bool :=
  t == 255 || r.toNat < t.toNat

theorem fix_is_correct (t r : BitVec 8) : fix t r = spec t r := by
  revert t r
  native_decide

/--
L4: Focus Energy Bug Model.
The assembly snippet shows that Focus Energy uses `srl b` (shift right)
instead of `sla b` (shift left), dividing crit chance by 4 instead of
doubling it.
-/
def calc_crit_threshold (base_speed : BitVec 8) (focus_energy : Bool) : BitVec 8 :=
  let b := base_speed >>> 1 -- b = base/2
  if focus_energy then
    b >>> 1 -- Bug: srl b (result is base/4)
  else
    let b2 := b <<< 1 -- sla b (result is base)
    if b2 < b then 255 else b2 -- cap at 255

/-- 
Focus Energy actually lowers your critical hit rate if base_speed > 1.
-/
theorem focus_energy_reduces_crit (speed : BitVec 8) :
  speed.toNat > 1 → 
  (calc_crit_threshold speed true).toNat < (calc_crit_threshold speed false).toNat := by
  revert speed
  native_decide

end AutoResearch
