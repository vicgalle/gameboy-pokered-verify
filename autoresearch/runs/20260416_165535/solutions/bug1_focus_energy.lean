import SM83

namespace AutoResearch

/-!
# Bug: Focus Energy Quarters Critical Hit Rate Instead of Doubling It

In Pokémon Red/Blue/Yellow (Gen 1), the critical hit rate is primarily derived from 
a Pokémon's base Speed stat. The standard probability threshold is approximately 
`BaseSpeed / 2`. 

Focus Energy was intended to double this threshold (increasing the chance), but due 
to a coding error—specifically using a right shift (division) instead of a 
left shift or multiplication—it quarters the threshold instead, drastically 
reducing the player's chance of landing a critical hit.
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
-/
def impl (speed : BitVec 8) : BitVec 8 :=
  (standard_rate speed) >>> 2

/-- 
  The intended behavior of Focus Energy.
  It should shift the standard rate left by 1 bit, effectively doubling it.
-/
def spec (speed : BitVec 8) : BitVec 8 :=
  (standard_rate speed) <<< 1

/-! ## L1: Proof of Bug Existence -/

/-- There exists a speed stat where Focus Energy results in a different rate than intended. -/
theorem bug_exists : ∃ s : BitVec 8, impl s ≠ spec s := 
  ⟨10, by native_decide⟩

/-- Focus Energy can actually reduce the critical hit rate below the standard rate. -/
theorem bug_reduces_rate_exists : ∃ s : BitVec 8, (impl s).toNat < (standard_rate s).toNat :=
  ⟨8, by native_decide⟩

/-! ## L2: Universal Characterization -/

/-- 
  For any Pokémon with a high enough speed stat (>= 8), 
  the buggy Focus Energy implementation always strictly reduces the critical hit rate.
-/
theorem impl_always_detrimental : ∀ s : BitVec 8, s.toNat ≥ 8 → (impl s).toNat < (standard_rate s).toNat := by
  have h := (by native_decide : ∀ v : BitVec 8, v.toNat ≥ 8 → ((v >>> 1) >>> 2).toNat < (v >>> 1).toNat)
  intro s
  exact h s

/-- 
  The intended spec always results in a rate threshold greater than or equal to the standard rate.
-/
theorem spec_always_beneficial : ∀ s : BitVec 8, (spec s).toNat ≥ (standard_rate s).toNat := by
  have h := (by native_decide : ∀ v : BitVec 8, ((v >>> 1) <<< 1).toNat ≥ (v >>> 1).toNat)
  intro s
  exact h s

/-! ## L3: Corrective Fix -/

/-- 
  A fixed version of the Focus Energy effect that correctly applies 
  the doubling logic (spec).
-/
def fix (speed : BitVec 8) : BitVec 8 :=
  (speed >>> 1) <<< 1

theorem fix_is_correct : ∀ s : BitVec 8, fix s = spec s := by
  intro s
  rfl

/-! ## L4: Relational Divergence -/

/-- 
  Relational proof: The intended critical hit rate (spec) is at least 8 times 
  higher than the buggy implementation (impl) for sufficiently fast Pokémon, 
  demonstrating the massive impact of the bug.
-/
theorem focus_energy_performance_gap : ∀ s : BitVec 8, s.toNat ≥ 8 → (spec s).toNat ≥ 8 * (impl s).toNat := by
  have h := (by native_decide : ∀ v : BitVec 8, v.toNat ≥ 8 → (((v >>> 1) <<< 1).toNat ≥ 8 * ((v >>> 1) >>> 2).toNat))
  intro s
  exact h s

end AutoResearch
