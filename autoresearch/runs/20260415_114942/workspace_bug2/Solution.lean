-- Formalization of the 1/256 miss bug in Pokémon Red/Blue.
-- In SM83, 'cp b' sets the carry flag if A < B. The game uses 'ret nc' or 'jr nc' 
-- which fails the hit/crit check if A >= B. Even with a max threshold (255), 
-- a random roll of 255 triggers a failure.
import SM83

namespace AutoResearch

-- SM83 RLC (Rotate Left Circular): bit 7 moves to bit 0 and carry.
def rlc (x : BitVec 8) : BitVec 8 := (x <<< 1) ||| (x >>> 7)

-- Modeling the 'cp b' then 'ret nc' logic. Hit/Crit occurs only if rand < threshold.
def is_hit (rand threshold : BitVec 8) : Bool := rand < threshold

-- CriticalHitTest rotates the random byte 3 times before comparison.
def is_crit (rand threshold : BitVec 8) : Bool :=
  let a := rlc (rlc (rlc rand))
  a < threshold

-- The maximum threshold intended for 100% accuracy/crit moves.
def MAX_T : BitVec 8 := 255

-- L1: Bug Existence - Concrete witnesses for the 1/256 failure.
theorem accuracy_bug_exists : ∃ r, is_hit r MAX_T = false := ⟨255, by native_decide⟩
theorem crit_bug_exists : ∃ r, is_crit r MAX_T = false := ⟨255, by native_decide⟩

-- L2: Characterization - The bug triggers if and only if the roll is 255.
theorem accuracy_fail_iff (r : BitVec 8) : is_hit r MAX_T = false ↔ r = 255 := by
  have h := (by native_decide : ∀ r : BitVec 8, (r < 255) = false ↔ r = 255)
  exact h r

theorem crit_fail_iff (r : BitVec 8) : is_crit r MAX_T = false ↔ r = 255 := by
  have h := (by native_decide : ∀ r : BitVec 8, (rlc (rlc (rlc r)) < 255) = false ↔ r = 255)
  exact h r

-- L3: Fix Correctness - Modeling two different fixes.
-- Fix A: Change comparison to <= (effectively making threshold 256).
def fixed_hit (rand threshold : BitVec 8) : Bool :=
  threshold == 255 || rand < threshold

theorem fix_a_perfect : ∀ r, fixed_hit r MAX_T = true := by
  intro r; simp [fixed_hit, MAX_T]

-- Fix B: X-Accuracy bypasses the check entirely as seen in the assembly.
def x_accuracy_logic (x_acc_active : Bool) (rand threshold : BitVec 8) : Bool :=
  if x_acc_active then true else is_hit rand threshold

theorem fix_b_works : ∀ r, x_accuracy_logic true r MAX_T = true := by
  intro r; rfl

-- L4: Relational Property - Symmetry of the bug across subsystems.
-- The 1/256 probability (the count of failing inputs) is invariant under rotation.
theorem rlc_is_bijective : ∀ x y : BitVec 8, rlc x = rlc y → x = y := by
  native_decide

theorem failure_probability_constancy (t : BitVec 8) :
  (List.range 256).filter (λ n => is_hit (BitVec.ofNat 8 n) t == false).length =
  (List.range 256).filter (λ n => is_crit (BitVec.ofNat 8 n) t == false).length := by
  native_decide

end AutoResearch
