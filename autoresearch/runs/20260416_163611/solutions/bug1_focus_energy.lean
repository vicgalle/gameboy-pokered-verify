import SM83

/-!
# Bug: Focus Energy Quarters Critical Hit Rate Instead of Doubling It

## Description
In Pokémon Generation 1, Focus Energy is intended to double the user's critical hit rate.
The critical hit rate is derived from the Pokémon's base Speed stat.
However, due to a bug in the implementation, using Focus Energy actually divides the 
calculated critical hit threshold by 4, effectively quartering the chance of a critical hit
and making the move detrimental to the user.
-/

namespace AutoResearch

/-- The standard critical hit threshold calculation in Gen 1 (Speed / 2). -/
def base_threshold (speed : BitVec 8) : Nat :=
  speed.toNat / 2

/-- 
  The buggy implementation (impl): 
  Focus Energy quarters the critical hit threshold instead of doubling it.
-/
def impl_focus_energy_threshold (speed : BitVec 8) : Nat :=
  (base_threshold speed) / 4

/-- 
  The intended specification (spec): 
  Focus Energy should double the critical hit threshold.
-/
def spec_focus_energy_threshold (speed : BitVec 8) : Nat :=
  (base_threshold speed) * 2

-- L1: Concrete witness where the bug causes a divergence
theorem bug_exists : ∃ (speed : BitVec 8), impl_focus_energy_threshold speed ≠ spec_focus_energy_threshold speed := by
  -- Speed 100: Base=50, Spec=100, Impl=12
  exists 100
  native_decide

-- L2: Focus Energy is always strictly worse than intended for any Pokémon that can crit
theorem forall_nonzero_speed_divergent : ∀ (speed : BitVec 8), 
  speed.toNat ≥ 8 → impl_focus_energy_threshold speed < spec_focus_energy_threshold speed := by
  intro speed
  have h := (by native_decide : ∀ (v : BitVec 8), v.toNat ≥ 8 → (v.toNat / 2 / 4) < (v.toNat / 2 * 2))
  apply h

-- L2: Focus Energy is actually detrimental (makes crit rate worse than not using the move)
-- If Speed is at least 8 (Base threshold >= 4), the bugged threshold (1) is less than the base (4).
theorem bug_is_detrimental : ∀ (speed : BitVec 8),
  speed.toNat ≥ 8 → impl_focus_energy_threshold speed < base_threshold speed := by
  intro speed
  have h := (by native_decide : ∀ (v : BitVec 8), v.toNat ≥ 8 → (v.toNat / 2 / 4) < (v.toNat / 2))
  apply h

-- L3: Fix for the bug
def fix_focus_energy_threshold (speed : BitVec 8) : Nat :=
  (base_threshold speed) * 2

theorem fix_is_correct : ∀ (speed : BitVec 8), 
  fix_focus_energy_threshold speed = spec_focus_energy_threshold speed := by
  intro speed
  rfl

-- L4: Relational Divergence (Advantage Inversion)
-- In the intended game, a Pokémon using Focus Energy has an advantage over one that didn't.
-- In the buggy game, the Pokémon using Focus Energy has a disadvantage.

structure Trainer where
  speed : BitVec 8
  used_focus : Bool

def get_threshold_buggy (t : Trainer) : Nat :=
  if t.used_focus then impl_focus_energy_threshold t.speed else base_threshold t.speed

def get_threshold_spec (t : Trainer) : Nat :=
  if t.used_focus then spec_focus_energy_threshold t.speed else base_threshold t.speed

theorem advantage_inversion_exists : ∃ (p1 p2 : Trainer),
  -- Both have same speed
  p1.speed = p2.speed ∧ 
  -- Player 1 uses Focus Energy, Player 2 does not
  p1.used_focus = true ∧ p2.used_focus = false ∧
  -- In spec, P1 has a better (higher) crit rate
  get_threshold_spec p1 > get_threshold_spec p2 ∧
  -- In impl, P1 has a worse (lower) crit rate
  get_threshold_buggy p1 < get_threshold_buggy p2 := by
  -- Speed 100
  let p1 : Trainer := ⟨100, true⟩
  let p2 : Trainer := ⟨100, false⟩
  exists p1, p2
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · -- Spec: 100 > 50
          native_decide
        · -- Buggy: 12 < 50
          native_decide

end AutoResearch

