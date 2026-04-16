import SM83

namespace AutoResearch

/-!
# Bug: heal_overflow (Gen 1 Recover/Rest/Softboiled Bug)

In Pokémon Red, Blue, and Yellow, recovery moves (Recover, Softboiled, and Rest) 
intended to heal the user can fail if the difference between the Pokemon's 
Maximum HP and Current HP is exactly 255, 511, 767, etc.

Specifically, the move performs a check to see if the user is already at full HP.
Due to a 16-bit subtraction logic error, the move incorrectly flags the Pokemon 
as "already full" if `(MaxHP - CurHP) % 256 == 255`, causing the move to fail.
-/

/-- Pokemon state with current and maximum HP. -/
structure Pokemon where
  curHP : BitVec 16
  maxHP : BitVec 16

/-- 
  Spec: A healing move should fail if and only if the Pokemon is already at full HP.
-/
def spec_is_full (p : Pokemon) : Bool :=
  p.curHP == p.maxHP

/-- 
  Impl: In Pokémon Gen 1, healing moves incorrectly fail if:
  1. Current HP is equal to Max HP (intended), OR
  2. The difference (MaxHP - CurrentHP) mod 256 is 255 (the bug).
-/
def impl_is_full (p : Pokemon) : Bool :=
  let gap := p.maxHP - p.curHP
  (gap == 0) || (gap.toNat % 256 == 255)

/-- 
  Outcome of a healing move: if 'is_full' returns true, healing is skipped (HP remains same).
  Otherwise, HP is restored to max.
-/
def heal_outcome (is_full_fn : Pokemon → Bool) (p : Pokemon) : BitVec 16 :=
  if is_full_fn p then p.curHP else p.maxHP

/-! ### L1: Concrete Witness -/

/-- L1: Prove that there exists a case where the Pokemon is not at full HP, but the bug triggers. -/
theorem bug_exists_witness : ∃ p : Pokemon, p.curHP ≠ p.maxHP ∧ impl_is_full p = true := by
  -- Example: Max HP 255, Cur HP 0. Gap is 255.
  let p : Pokemon := { curHP := 0, maxHP := 255 }
  exists p
  constructor
  · native_decide
  · unfold impl_is_full
    native_decide

/-! ### L2: Universal Characterization -/

/-- L2: Universal characterization of when the bug triggers. -/
theorem bug_trigger_iff (p : Pokemon) :
  (impl_is_full p = true ∧ spec_is_full p = false) ↔ 
  (p.curHP ≠ p.maxHP ∧ (p.maxHP - p.curHP).toNat % 256 = 255) := by
  unfold impl_is_full spec_is_full
  constructor
  · intro ⟨h_impl, h_spec⟩
    simp at h_spec
    refine ⟨h_spec, ?_⟩
    -- Since h_spec is p.curHP ≠ p.maxHP, gap ≠ 0
    have h_gap_nz : (p.maxHP - p.curHP == 0) = false := by
      simp [h_spec]
      intro h_eq; exact h_spec h_eq.symm
    simp [h_gap_nz] at h_impl
    exact h_impl
  · intro ⟨h_spec, h_gap⟩
    simp [h_spec]
    simp [h_gap]

/-- L2: The bug never occurs if the HP gap is small (except for the intended full HP check). -/
theorem no_bug_for_small_gap (p : Pokemon) :
  (p.maxHP - p.curHP).toNat < 255 → impl_is_full p = spec_is_full p := by
  intro h_small
  unfold impl_is_full spec_is_full
  by_cases h : p.curHP = p.maxHP
  · simp [h]
  · simp [h]
    have h_gap_nz : (p.maxHP - p.curHP == 0) = false := by
      simp [h]; intro h_eq; exact h h_eq.symm
    simp [h_gap_nz]
    -- if x < 255, then x % 256 can never be 255
    have : (p.maxHP - p.curHP).toNat % 256 ≠ 255 := by omega
    simp [this]

/-- L2: The bug requires a significant HP gap to manifest. -/
theorem bug_requires_large_gap (p : Pokemon) :
  (impl_is_full p = true ∧ spec_is_full p = false) → 
  (p.maxHP - p.curHP).toNat ≥ 255 := by
  intro h
  rw [bug_trigger_iff] at h
  omega

/-- L2: The bug is periodic in 256-HP increments. -/
theorem bug_is_periodic (p : Pokemon) :
  (p.maxHP - p.curHP).toNat % 256 = 255 → p.curHP ≠ p.maxHP → impl_is_full p = true := by
  intro h_gap h_not_full
  unfold impl_is_full
  simp [h_gap]

/-! ### L3: Fix -/

/-- L3: A fixed implementation that correctly checks only for full HP. -/
def fix_is_full (p : Pokemon) : Bool :=
  p.curHP == p.maxHP

/-- L3: The fix correctly matches the specification for all inputs. -/
theorem fix_is_correct (p : Pokemon) : fix_is_full p = spec_is_full p := by
  rfl

/-! ### L4: Relational Divergence -/

/-- L4: Prove that the buggy implementation leads to different healing outcomes than the spec. -/
theorem healing_desync_exists : ∃ p : Pokemon,
  heal_outcome impl_is_full p ≠ heal_outcome spec_is_full p := by
  let p : Pokemon := { curHP := 0, maxHP := 255 }
  exists p
  unfold heal_outcome
  simp [impl_is_full, spec_is_full]
  native_decide

/-- L4: Proving that when the bug triggers, the implementation fails to restore HP. -/
theorem bug_prevents_healing (p : Pokemon) :
  (p.curHP ≠ p.maxHP ∧ (p.maxHP - p.curHP).toNat % 256 = 255) → 
  heal_outcome impl_is_full p = p.curHP := by
  intro ⟨h_not_full, h_gap⟩
  unfold heal_outcome impl_is_full
  -- Because (p.maxHP - p.curHP).toNat % 256 = 255, impl_is_full returns true
  simp [h_not_full, h_gap]

/-- L4: The specification always heals the Pokemon to Max HP if it's not already full. -/
theorem spec_always_heals_if_not_full (p : Pokemon) :
  p.curHP ≠ p.maxHP → heal_outcome spec_is_full p = p.maxHP := by
  intro h_not_full
  unfold heal_outcome spec_is_full
  simp [h_not_full]

/-- L4: The amount of HP gained is exactly zero when the bug is triggered. -/
theorem healing_failed_delta (p : Pokemon) :
  (impl_is_full p = true ∧ spec_is_full p = false) → 
  (heal_outcome impl_is_full p).toNat - p.curHP.toNat = 0 := by
  intro ⟨h_impl, _⟩
  unfold heal_outcome
  simp [h_impl]

end AutoResearch
