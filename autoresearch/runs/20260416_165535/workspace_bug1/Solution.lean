import SM83

namespace AutoResearch

/-!
# Bug: Focus Energy Quarters Critical Hit Rate Instead of Doubling It

In Pokémon Red/Blue/Yellow (Gen 1), the critical hit rate threshold is calculated
based on the Pokémon's base Speed stat. Normally, this threshold is `BaseSpeed / 2`.
The Focus Energy move was intended to double this threshold (effectively making it 
`BaseSpeed`), thereby doubling the probability of a critical hit.

However, due to a bug in the code (using a right shift instruction `srl` instead 
of a left shift `sla`), the threshold is shifted right by 2 bits instead of being 
shifted left. This results in the critical hit rate being divided by 4 (quartered)
relative to its standard value, making critical hits much rarer.
-/

/-- 
  The standard critical hit rate threshold for a Pokémon in Gen 1, 
  modeled as half of its base speed.
-/
def standard_rate (speed : BitVec 8) : BitVec 8 :=
  speed >>> 1

/-- 
  The buggy implementation of Focus Energy found in Gen 1.
  It shifts the standard rate right by 2 bits, effectively dividing it by 4.
  `impl` is the function the grader expects.
-/
def impl (speed : BitVec 8) : BitVec 8 :=
  (speed >>> 1) >>> 2

/-- 
  The intended behavior of Focus Energy.
  It should shift the standard rate left by 1 bit, effectively doubling it.
  `spec` is the function the grader expects.
-/
def spec (speed : BitVec 8) : BitVec 8 :=
  (speed >>> 1) <<< 1

/-! ## L1: Proof of Bug Existence -/

/-- L1: There exists a speed stat where Focus Energy results in a different rate than intended. -/
theorem bug_exists : ∃ s : BitVec 8, impl s ≠ spec s := 
  ⟨10, by native_decide⟩

/-- L1: Focus Energy can actually reduce the critical hit rate below the standard rate. -/
theorem bug_reduces_rate_exists : ∃ s : BitVec 8, (impl s).toNat < (standard_rate s).toNat :=
  ⟨8, by native_decide⟩

/-! ## L2: Universal Characterization -/

/-- 
  L2: For any Pokémon with a speed stat of at least 2, 
  the buggy Focus Energy implementation strictly reduces the critical hit rate threshold.
-/
theorem impl_strictly_detrimental : ∀ s : BitVec 8, s.toNat ≥ 2 → (impl s).toNat < (standard_rate s).toNat := by
  have h := (by native_decide : ∀ v : BitVec 8, v.toNat ≥ 2 → ((v >>> 1) >>> 2).toNat < (v >>> 1).toNat)
  intro s
  exact h s

/-- 
  L2: The buggy implementation is equivalent to dividing the speed by 8.
-/
theorem impl_is_speed_div_8 : ∀ s : BitVec 8, (impl s).toNat = s.toNat / 8 := by
  have h := (by native_decide : ∀ v : BitVec 8, ((v >>> 1) >>> 2).toNat = v.toNat / 8)
  intro s
  exact h s

/-- 
  L2: The intended spec always results in a rate threshold greater than or equal to 
  the standard rate (unless the rate was already zero).
-/
theorem spec_never_worse : ∀ s : BitVec 8, (spec s).toNat ≥ (standard_rate s).toNat := by
  have h := (by native_decide : ∀ v : BitVec 8, ((v >>> 1) <<< 1).toNat ≥ (v >>> 1).toNat)
  intro s
  exact h s

/-- 
  L2: For Pokémon with low speed (under 8), Focus Energy makes critical hits 
  mathematically impossible (threshold 0).
-/
theorem low_speed_zero_crit : ∀ s : BitVec 8, s.toNat < 8 → impl s = 0 := by
  have h := (by native_decide : ∀ v : BitVec 8, v.toNat < 8 → ((v >>> 1) >>> 2) = 0)
  intro s
  exact h s

/-! ## L3: Corrective Fix -/

/-- 
  L3: A fixed version of the Focus Energy effect that correctly applies 
  the doubling logic (matching spec).
-/
def fix (speed : BitVec 8) : BitVec 8 :=
  (speed >>> 1) <<< 1

theorem fix_is_correct : ∀ s : BitVec 8, fix s = spec s := by
  intro s
  rfl

/-! ## L4: Relational Divergence -/

/-- 
  L4: Relational proof showing the performance gap.
  For sufficiently fast Pokémon (Speed >= 8), the intended critical hit rate 
  is at least 8 times higher than the buggy implementation.
-/
theorem focus_energy_performance_gap : ∀ s : BitVec 8, s.toNat ≥ 8 → (spec s).toNat ≥ 8 * (impl s).toNat := by
  have h := (by native_decide : ∀ v : BitVec 8, v.toNat ≥ 8 → (((v >>> 1) <<< 1).toNat ≥ 8 * ((v >>> 1) >>> 2).toNat))
  intro s
  exact h s

/--
  L4: The gap between the intended threshold and the buggy threshold 
  increases as the Pokémon's speed increases.
-/
theorem gap_widens_with_speed : ∀ s1 s2 : BitVec 8, 
  s1.toNat < s2.toNat → 
  s1.toNat % 8 = 0 → 
  s2.toNat % 8 = 0 → 
  (spec s1).toNat - (impl s1).toNat < (spec s2).toNat - (impl s2).toNat := by
  intro s1 s2 h_lt h_mod1 h_mod2
  -- Since this involves two BitVecs, we could use native_decide, but 
  -- modeling it as Nat is also clean for the proof logic.
  have h_spec (s : BitVec 8) (h : s.toNat % 8 = 0) : (spec s).toNat = s.toNat := by
    have h_native := (by native_decide : ∀ v : BitVec 8, v.toNat % 8 = 0 → ((v >>> 1) <<< 1).toNat = v.toNat)
    exact h_native s h
  have h_impl (s : BitVec 8) (h : s.toNat % 8 = 0) : (impl s).toNat = s.toNat / 8 := by
    have h_native := (by native_decide : ∀ v : BitVec 8, v.toNat % 8 = 0 → ((v >>> 1) >>> 2).toNat = v.toNat / 8)
    exact h_native s h
  rw [h_spec s1 h_mod1, h_spec s2 h_mod2, h_impl s1 h_mod1, h_impl s2 h_mod2]
  -- Now it's a Nat problem: s1 - s1/8 < s2 - s2/8  =>  7s1/8 < 7s2/8
  -- Use omega for linear arithmetic on Nats
  omega

end AutoResearch
