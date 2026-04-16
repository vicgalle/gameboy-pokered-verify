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
  let diff := p.maxHP - p.curHP
  (diff == 0) || (diff.toNat % 256 == 255)

/-- 
  Outcome of a healing move: if 'is_full' returns true, healing is skipped (HP remains same).
  Otherwise, HP is restored to max.
-/
def heal_outcome (is_full_fn : Pokemon → Bool) (p : Pokemon) : BitVec 16 :=
  if is_full_fn p then p.curHP else p.maxHP

/-! ### L1: Concrete Witness -/

/-- L1: Prove that there exists a case where the Pokemon is not at full HP, but the bug triggers. -/
theorem bug_exists_witness : ∃ p : Pokemon, p.curHP ≠ p.maxHP ∧ impl_is_full p = true := by
  -- Example: Max HP 511 (0x01FF), Cur HP 256 (0x0100). 
  -- Difference is 255 (0x00FF).
  let p : Pokemon := { curHP := 256, maxHP := 511 }
  exists p
  constructor
  · -- Check that 256 != 511
    native_decide
  · -- Check that the buggy implementation thinks it is full
    unfold impl_is_full
    -- (511 - 256) % 256 = 255 % 256 = 255
    native_decide

/-! ### L2: Universal Characterization -/

/-- L2: Universal characterization of when the bug triggers for non-full Pokemon. -/
theorem bug_forall_trigger (p : Pokemon) :
  p.curHP ≠ p.maxHP → (impl_is_full p = true ↔ (p.maxHP - p.curHP).toNat % 256 = 255) := by
  intro h_not_full
  unfold impl_is_full
  -- If curHP != maxHP, then the subtraction (maxHP - curHP) cannot be 0.
  have h_diff_nz : (p.maxHP - p.curHP == 0) = false := by
    simp
    intro h_z
    -- BitVec property: x - y = 0 implies x = y
    have : p.maxHP = p.curHP := BitVec.eq_of_sub_eq_zero h_z
    exact h_not_full this.symm
  simp [h_diff_nz]
  exact Bool.decide_eq_true_iff _

/-- L2: The bug never occurs if the HP gap is small (except for the intended full HP check). -/
theorem bug_free_low_gap (p : Pokemon) :
  (p.maxHP - p.curHP).toNat < 255 → impl_is_full p = spec_is_full p := by
  intro h_low
  unfold impl_is_full spec_is_full
  by_cases h_full : p.maxHP = p.curHP
  · simp [h_full]
  · simp [h_full]
    -- Since max != cur, diff != 0
    have h_nz : (p.maxHP - p.curHP == 0) = false := by
      simp; intro h_z; exact h_full (BitVec.eq_of_sub_eq_zero h_z)
    simp [h_nz]
    -- If x < 255, then x % 256 can never be 255
    have h_mod : (p.maxHP - p.curHP).toNat % 256 ≠ 255 := by
      have h_lt : (p.maxHP - p.curHP).toNat < 256 := by omega
      rw [Nat.mod_eq_of_lt h_lt]
      omega
    simp [h_mod]

/-! ### L3: Fix -/

/-- L3: A fixed implementation that correctly checks only for full HP. -/
def fix_is_full (p : Pokemon) : Bool :=
  p.curHP == p.maxHP

theorem fix_is_correct (p : Pokemon) : ∀ p, fix_is_full p = spec_is_full p := by
  intro p; rfl

/-! ### L4: Relational Divergence -/

/-- L4: Prove that the buggy implementation leads to different healing outcomes than the spec. -/
theorem healing_desync : ∃ p : Pokemon,
  heal_outcome impl_is_full p ≠ heal_outcome spec_is_full p := by
  let p : Pokemon := { curHP := 256, maxHP := 511 }
  exists p
  unfold heal_outcome
  simp [impl_is_full, spec_is_full]
  native_decide

/-- L4: Proving that when the bug triggers, the implementation fails to restore HP. -/
theorem bug_prevents_healing (p : Pokemon) :
  p.curHP ≠ p.maxHP ∧ (p.maxHP - p.curHP).toNat % 256 = 255 → 
  heal_outcome impl_is_full p = p.curHP := by
  intro ⟨_, h_bug⟩
  unfold heal_outcome impl_is_full
  -- Because (p.maxHP - p.curHP).toNat % 256 = 255, impl_is_full returns true
  simp [h_bug]

end AutoResearch
