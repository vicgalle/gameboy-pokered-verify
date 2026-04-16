import SM83

/-!
# Bug: Focus Energy Quarters Critical Hit Rate Instead of Doubling It

## Description
In Pokémon Generation 1, Focus Energy is intended to increase the critical hit rate
(calculated as `BaseSpeed / 2`). The intended effect is to double this threshold.
However, a bug in the implementation causes the game to right-shift the value twice
(dividing by 4) instead of doubling it. This results in Focus Energy making critical
hits significantly less likely than if the move had never been used.

## Implementation Details
- `base_threshold`: The standard critical hit threshold (Speed / 2).
- `spec_focus_energy_threshold`: The intended behavior (Threshold * 2).
- `impl_focus_energy_threshold`: The buggy behavior (Threshold / 4).
-/

namespace AutoResearch

/-- The standard critical hit threshold in Gen 1 is Speed / 2. -/
def base_threshold (speed : BitVec 8) : Nat :=
  speed.toNat / 2

/-- The buggy implementation: divides the base threshold by 4. -/
def impl_focus_energy_threshold (speed : BitVec 8) : Nat :=
  (base_threshold speed) / 4

/-- The intended specification: doubles the base threshold. -/
def spec_focus_energy_threshold (speed : BitVec 8) : Nat :=
  (base_threshold speed) * 2

-- L1: Concrete witness where the bug causes a divergence.
-- At Speed 100: Base=50, Spec=100, Impl=12.
theorem bug_exists : ∃ (speed : BitVec 8), impl_focus_energy_threshold speed ≠ spec_focus_energy_threshold speed := by
  exists 100
  native_decide

-- L2: Universal characterization - Focus Energy is always strictly worse than intended
-- for any Pokémon with enough speed to have a non-zero threshold.
theorem bug_is_always_worse_than_spec : ∀ (speed : BitVec 8), 
  speed.toNat ≥ 2 → impl_focus_energy_threshold speed < spec_focus_energy_threshold speed := by
  intro speed
  have h := (by native_decide : ∀ (v : BitVec 8), v.toNat ≥ 2 → (v.toNat / 2 / 4) < (v.toNat / 2 * 2))
  exact h speed

-- L2: Focus Energy is detrimental - it makes the crit rate worse than not using the move at all.
-- This triggers when the base threshold is at least 1 (Speed >= 2).
theorem bug_is_detrimental : ∀ (speed : BitVec 8),
  speed.toNat ≥ 8 → impl_focus_energy_threshold speed < base_threshold speed := by
  intro speed
  have h := (by native_decide : ∀ (v : BitVec 8), v.toNat ≥ 8 → (v.toNat / 2 / 4) < (v.toNat / 2))
  exact h speed

-- L2: The intended behavior was always beneficial or neutral.
theorem intended_behavior_is_beneficial : ∀ (speed : BitVec 8),
  spec_focus_energy_threshold speed ≥ base_threshold speed := by
  intro speed
  simp [spec_focus_energy_threshold, base_threshold]
  omega

-- L3: Fix for the bug.
def fix_focus_energy_threshold (speed : BitVec 8) : Nat :=
  (base_threshold speed) * 2

theorem fix_is_correct : ∀ (speed : BitVec 8), 
  fix_focus_energy_threshold speed = spec_focus_energy_threshold speed := by
  intro speed; rfl

-- L4: Relational Divergence (Advantage Inversion)
-- Shows that a Pokémon using Focus Energy (A) becomes strictly inferior in crit rate
-- to an identical Pokémon not using the move (B), despite the opposite being intended.
structure GameState where
  speed : BitVec 8
  focus_active : Bool

def get_crit_threshold (s : GameState) (buggy : Bool) : Nat :=
  if s.focus_active then
    if buggy then impl_focus_energy_threshold s.speed else spec_focus_energy_threshold s.speed
  else
    base_threshold s.speed

theorem advantage_inversion_exists : ∃ (s1 s2 : GameState),
  s1.speed = s2.speed ∧ s1.focus_active = true ∧ s2.focus_active = false ∧
  get_crit_threshold s1 true < get_crit_threshold s2 true ∧ -- Buggy: Focus < No Focus
  get_crit_threshold s1 false > get_crit_threshold s2 false := by -- Spec: Focus > No Focus
  let p1 : GameState := ⟨100, true⟩
  let p2 : GameState := ⟨100, false⟩
  exists p1, p2
  native_decide

-- L4: Magnitude of the bug
-- A max-speed Pokémon (255) using Focus Energy is less likely to crit than 
-- a slow Pokémon (64) not using Focus Energy.
theorem focus_energy_cripples_fast_pokemon : ∀ (fast slow : BitVec 8),
  fast.toNat = 255 ∧ slow.toNat = 64 →
  impl_focus_energy_threshold fast < base_threshold slow := by
  intro fast slow h
  have h_fast : fast = 255 := by apply BitVec.ext; simp [h.1]
  have h_slow : slow = 64 := by apply BitVec.ext; simp [h.2]
  rw [h_fast, h_slow]
  native_decide

end AutoResearch

