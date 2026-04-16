import SM83
import Harness

namespace AutoResearch

open SM83

/-!
# Bug #5: psywave_desync

## Gameplay Description
Psywave is a move that deals random damage based on the user's level. 
In Pokémon Red/Blue, the damage calculation uses the local random number generator (RNG)
without synchronizing the result across the link cable. This means that if the 
internal random seeds of the two Game Boys have drifted apart, each machine 
will calculate a different damage value, leading to a desynchronization.

## Formalization
We model the `psywave_impl` (the buggy version) and `psywave_spec` (the fixed version).
The desynchronization is verified by showing that identical initial battle conditions
with different local RNG seeds result in divergent states.
-/

-- Memory Addresses (simplified for modeling)
def wCurLevel : BitVec 16 := BitVec.ofNat 16 0xD123
def hRandomAdd : BitVec 16 := BitVec.ofNat 16 0xFF04
def wDamage : BitVec 16 := BitVec.ofNat 16 0xD500

/-- 
The buggy Psywave implementation as found in Gen 1.
It reads the local level and the local RNG register to compute damage.
The lack of network sync for `hRandomAdd` is the root cause of the desync.
The formula for Psywave is approximately: Damage = (Random % (1.5 * Level)) + 1.
-/
def psywave_impl (s : CPUState) : CPUState :=
  let level := (s.readMem wCurLevel).toNat
  let rand := (s.readMem hRandomAdd).toNat
  -- Damage formula: (random % floor(1.5 * level)) + 1
  let max_val := level + (level / 2)
  let damage := if max_val == 0 then 1
                else (rand % max_val) + 1
  s.writeMem wDamage (BitVec.ofNat 8 damage)

/-- 
The corrected Psywave implementation for link battles.
A properly synchronized battle would use a shared random value transmitted 
over the link cable to ensure both machines compute the exact same damage,
regardless of their local `hRandomAdd` state.
-/
def psywave_spec (s : CPUState) (shared_rand : BitVec 8) : CPUState :=
  let level := (s.readMem wCurLevel).toNat
  let max_val := level + (level / 2)
  let damage := if max_val == 0 then 1
                else (shared_rand.toNat % max_val) + 1
  s.writeMem wDamage (BitVec.ofNat 8 damage)

-- Level 1: Concrete Witness of Desynchronization
-- Prove that two machines with level 50 but different seeds calculate different damage.
theorem L1_psywave_desync_witness :
  ∃ (s1 s2 : CPUState),
    s1.readMem wCurLevel = BitVec.ofNat 8 50 ∧
    s2.readMem wCurLevel = BitVec.ofNat 8 50 ∧
    s1.readMem hRandomAdd = BitVec.ofNat 8 10 ∧
    s2.readMem hRandomAdd = BitVec.ofNat 8 20 ∧
    (psywave_impl s1).readMem wDamage != (psywave_impl s2).readMem wDamage := by
  let s1 := defaultState.writeMem wCurLevel (BitVec.ofNat 8 50) |>.writeMem hRandomAdd (BitVec.ofNat 8 10)
  let s2 := defaultState.writeMem wCurLevel (BitVec.ofNat 8 50) |>.writeMem hRandomAdd (BitVec.ofNat 8 20)
  exists s1, s2
  simp [psywave_impl, wCurLevel, hRandomAdd, wDamage]
  native_decide

-- Level 2: Universal Characterization of the Bug
-- If the level is identical and the RNG seeds differ modulo the damage cap, 
-- and no byte overflow occurs (level <= 100), a desync occurs.
theorem L2_psywave_desync_condition (s1 s2 : CPUState) :
  let level := (s1.readMem wCurLevel).toNat
  let r1 := (s1.readMem hRandomAdd).toNat
  let r2 := (s2.readMem hRandomAdd).toNat
  let m := level + (level / 2)
  (s1.readMem wCurLevel = s2.readMem wCurLevel) ∧
  (m > 0) ∧ (m < 255) ∧
  (r1 % m != r2 % m) →
  (psywave_impl s1).readMem wDamage != (psywave_impl s2).readMem wDamage := by
  intro h
  let ⟨h_level, h_m_pos, h_m_bound, h_rand_diff⟩ := h
  simp [psywave_impl, h_level, h_m_pos]
  intro h_contra
  -- If BitVecs are equal, their values mod 256 are equal.
  have h_eq_mod : (r1 % (s1.readMem wCurLevel).toNat + (s1.readMem wCurLevel).toNat / 2 + 1) % 256 = 
                  (r2 % (s1.readMem wCurLevel).toNat + (s1.readMem wCurLevel).toNat / 2 + 1) % 256 := by
    apply congrArg BitVec.toNat h_contra
  
  -- Since m < 255, (r % m) + 1 is in [1, 255], so % 256 is identity.
  let m_val := (s1.readMem wCurLevel).toNat + (s1.readMem wCurLevel).toNat / 2
  have h_m_val : m_val = m := rfl
  have b1 : (r1 % m + 1) < 256 := by omega
  have b2 : (r2 % m + 1) < 256 := by omega
  
  rw [Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2] at h_eq_mod
  exact h_rand_diff (Nat.add_right_cancel h_eq_mod)

-- Level 3: Verification of the Fix
-- The specification guarantees that both machines reach the same state if they share the random input,
-- regardless of their internal RNG state.
theorem L3_psywave_spec_integrity (s1 s2 : CPUState) (shared_rand : BitVec 8) :
  s1.readMem wCurLevel = s2.readMem wCurLevel →
  (psywave_spec s1 shared_rand).readMem wDamage = (psywave_spec s2 shared_rand).readMem wDamage := by
  intro h_level
  simp [psywave_spec, h_level]

-- Level 4: Relational Divergence Proof
-- Contrast the behavior: in conditions where the implementation allows divergence due to 
-- entropy drift (hRandomAdd), the specification enforces convergence (desync prevention).
theorem L4_psywave_relational_desync_prevention (s1 s2 : CPUState) (shared : BitVec 8) :
  let m := (s1.readMem wCurLevel).toNat + (s1.readMem wCurLevel).toNat / 2
  (s1.readMem wCurLevel = s2.readMem wCurLevel) ∧ (m > 0) ∧ (m < 255) ∧
  ((s1.readMem hRandomAdd).toNat % m != (s2.readMem hRandomAdd).toNat % m) →
  ((psywave_impl s1).readMem wDamage != (psywave_impl s2).readMem wDamage) ∧
  ((psywave_spec s1 shared).readMem wDamage == (psywave_spec s2 shared).readMem wDamage) := by
  intro h
  constructor
  · apply L2_psywave_desync_condition s1 s2 h
  · simp [L3_psywave_spec_integrity s1 s2 shared h.1]

end AutoResearch
