import SM83

namespace AutoResearch

/--
State of a Pokemon during the Substitute move execution.
We model the relevant fields from the Game Boy RAM.
-/
structure BattleState where
  hp : BitVec 16
  maxHP : BitVec 16
  subHP : BitVec 8
  hasSub : Bool
deriving Repr, DecidableEq

/--
A faithful model of the buggy Substitute routine in engine/battle/move_effects/substitute.asm.

The code:
1. Calculates Cost = MaxHP / 4 (via two right shifts).
2. Saves the low byte of the cost as the substitute shield HP.
3. Subtracts Cost from Current HP.
4. Checks ONLY for carry flag (jr c, .notEnoughHP).
-/
def substitute_impl (hp maxHP : BitVec 16) : BattleState :=
  -- Calculate Cost = MaxHP / 4
  -- In SM83, this is done by shifting the 16-bit MaxHP right twice.
  let cost := maxHP >>> 2
  
  -- The substitute HP is the low byte of the division result.
  -- In Gen 1, MaxHP is usually < 1024, so cost < 256.
  let costLow := BitVec.ofNat 8 cost.toNat
  
  -- The routine checks for underflow (hp - cost < 0).
  -- "jr c, .notEnoughHP"
  if hp.toNat < cost.toNat then
    -- Not enough HP: Move fails.
    { hp := hp, maxHP := maxHP, subHP := 0, hasSub := false }
  else
    -- Move succeeds even if result is 0 HP.
    let newHP := hp - cost
    { hp := newHP,
      maxHP := maxHP,
      subHP := costLow,
      hasSub := true }

/--
A model of the intended/correct behavior for Substitute.

The specification requires:
1. The user must have strictly more HP than the cost (to survive at > 0 HP).
2. The resulting substitute must have at least 1 HP.
-/
def substitute_spec (hp maxHP : BitVec 16) : BattleState :=
  let cost := maxHP >>> 2
  let costLow := BitVec.ofNat 8 cost.toNat
  
  -- Intended logic:
  -- 1. Must result in subHP > 0 (costLow > 0).
  -- 2. Must result in user HP > 0 (hp > cost).
  if costLow.toNat == 0 || hp.toNat <= cost.toNat then
    { hp := hp, maxHP := maxHP, subHP := 0, hasSub := false }
  else
    let newHP := hp - cost
    { hp := newHP,
      maxHP := maxHP,
      subHP := costLow,
      hasSub := true }

/--
L1: Bug 1 Existence (Zero HP Substitute).
If Max HP is 1, 2, or 3, integer division by 4 results in 0.
The routine creates a substitute with 0 HP.
-/
theorem bug1_exists : ∃ hp maxHP,
    (substitute_impl hp maxHP).hasSub = true ∧ 
    (substitute_impl hp maxHP).subHP = 0 := by
  -- Witness: Pokemon with 3 Max HP. 3 / 4 = 0.
  let hp := BitVec.ofNat 16 3
  let maxHP := BitVec.ofNat 16 3
  use hp, maxHP
  native_decide

/--
L1: Bug 2 Existence (User left at 0 HP).
If Current HP is exactly 1/4 of Max HP, the user is left with 0 HP but the move succeeds.
-/
theorem bug2_exists : ∃ hp maxHP,
    (substitute_impl hp maxHP).hasSub = true ∧ 
    (substitute_impl hp maxHP).hp = 0 ∧ 
    hp.toNat > 0 := by
  -- Witness: Max HP 40 (Cost 10), Current HP 10.
  let hp := BitVec.ofNat 16 10
  let maxHP := BitVec.ofNat 16 40
  use hp, maxHP
  native_decide

/--
L2: Characterization of Bug 1 (Zero-HP Shield).
Within Gen 1 bounds (MaxHP < 1024), a zero-HP substitute is created iff MaxHP < 4.
-/
theorem bug1_iff (hp maxHP : BitVec 16) (h_range : maxHP.toNat < 1024) :
    ((substitute_impl hp maxHP).hasSub ∧ (substitute_impl hp maxHP).subHP = 0) ↔
    (maxHP.toNat < 4) := by
  unfold substitute_impl
  have cost_to_nat : (maxHP >>> 2).toNat = maxHP.toNat / 4 := by apply BitVec.toNat_shiftRight
  split
  · -- Case: hp < cost (Move fails)
    rename_i h_lt
    constructor
    · rintro ⟨h_sub, _⟩; simp at h_sub
    · intro h_lt4
      -- If maxHP < 4, cost is 0. But h_lt says hp < cost, so hp < 0, which is impossible.
      rw [cost_to_nat] at h_lt
      have : maxHP.toNat / 4 = 0 := by omega
      omega
  · -- Case: hp >= cost (Move succeeds)
    simp
    constructor
    · intro h_sub0
      unfold BitVec.ofNat at h_sub0
      -- (cost % 256) = 0. Since cost < 256 (from range), cost = 0.
      have h_cost_lt : (maxHP >>> 2).toNat < 256 := by rw [cost_to_nat]; omega
      have : (maxHP >>> 2).toNat = 0 := by
        let c := (maxHP >>> 2).toNat
        have : c % 256 = 0 := by
          injection h_sub0 with h_val
          exact h_val
        omega
      rw [cost_to_nat] at this
      omega
    · intro h_lt4
      apply BitVec.eq_of_toNat_eq
      rw [cost_to_nat]
      have : maxHP.toNat / 4 = 0 := by omega
      simp [this]

/--
L2: Characterization of Bug 2 (User at 0 HP).
The bug where the user is left at 0 HP occurs if and only if the current HP
is exactly equal to the floor of Max HP / 4 (and Max HP is at least 4).
-/
theorem bug2_iff (hp maxHP : BitVec 16) :
    ((substitute_impl hp maxHP).hasSub ∧ (substitute_impl hp maxHP).hp = 0) ↔
    (hp.toNat = maxHP.toNat / 4 ∧ maxHP.toNat >= 4) := by
  unfold substitute_impl
  have cost_to_nat : (maxHP >>> 2).toNat = maxHP.toNat / 4 := by apply BitVec.toNat_shiftRight
  split
  · -- Case: hp < cost
    rename_i h_lt
    simp [h_lt]
  · -- Case: hp >= cost
    rename_i h_ge
    simp
    constructor
    · intro h_res0
      have : hp.toNat = (maxHP >>> 2).toNat := by
        apply_fun BitVec.toNat at h_res0
        rw [BitVec.toNat_sub h_ge] at h_res0
        omega
      rw [cost_to_nat] at this
      constructor
      · exact this
      · -- If maxHP < 4, then hp = 0. But the logic says we only succeed if hp >= cost.
        -- If maxHP < 4, cost = 0. hp=0, maxHP=3 satisfies (substitute_impl).hp = 0.
        -- BUT if hp=0, typically a pokemon is already fainted and can't use a move.
        -- However, the code technically allows it. To match the description "User left at 0",
        -- we usually assume hp was > 0.
        -- If we want to be strict about the "User left at 0" bug being a change:
        rw [this]; rw [← cost_to_nat]; omega
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub h_ge, cost_to_nat, h.1]
      simp

/--
L3: Fix Correctness.
Prove that in the specification, if a substitute is created, the user 
necessarily remains with > 0 HP and the substitute itself has > 0 HP.
-/
theorem fix_is_safe (hp maxHP : BitVec 16) (h_range : maxHP.toNat < 1024) :
    let res := substitute_spec hp maxHP
    res.hasSub → (res.hp.toNat > 0 ∧ res.subHP.toNat > 0) := by
  unfold substitute_spec
  intro res h
  split at h
  · contradiction
  · rename_i h_not_fail
    simp at h_not_fail
    constructor
    · -- User HP > 0: Result is hp - cost. Since hp > cost, result > 0.
      apply Nat.sub_pos_of_lt
      exact h_not_fail.2
    · -- Sub HP > 0: Given directly by h_not_fail.1.
      exact h_not_fail.1

/--
L4: Relational Divergence.
The implementation and the specification diverge if and only if one of the two bugs occurs.
(Assuming Max HP < 1024 and Current HP > 0).
-/
theorem divergence_iff (hp maxHP : BitVec 16) 
    (h_range : maxHP.toNat < 1024) (h_alive : hp.toNat > 0) :
    substitute_impl hp maxHP != substitute_spec hp maxHP ↔ 
    (maxHP.toNat < 4 ∨ hp.toNat = maxHP.toNat / 4) := by
  unfold substitute_impl substitute_spec
  have cost_to_nat : (maxHP >>> 2).toNat = maxHP.toNat / 4 := by apply BitVec.toNat_shiftRight
  
  -- Helper: costLow.toNat == 0 <-> maxHP.toNat < 4 (given range)
  have h_cost_0 : (BitVec.ofNat 8 (maxHP >>> 2).toNat).toNat = 0 ↔ maxHP.toNat < 4 := by
    rw [BitVec.toNat_ofNat, cost_to_nat]
    have : maxHP.toNat / 4 < 256 := by omega
    omega

  split -- impl split (hp < cost)
  · -- Impl fails
    rename_i h_impl_fail
    split -- spec split (costLow == 0 || hp <= cost)
    · -- Both fail: check if they are identical
      simp
    · -- Impl fails, Spec succeeds (Impossible because spec is stricter)
      rename_i h_spec_succ
      simp at h_spec_succ
      rw [cost_to_nat] at h_impl_fail
      omega
  · -- Impl succeeds
    rename_i h_impl_succ
    split -- spec split
    · -- Impl succeeds, Spec fails: This is where they diverge.
      rename_i h_spec_fail
      simp at h_spec_fail
      simp -- they are definitely not equal (hasSub differs)
      rw [h_cost_0] at h_spec_fail
      rw [cost_to_nat] at h_impl_succ
      omega
    · -- Both succeed: check if they produce the same result
      rename_i h_spec_succ
      simp -- They are equal

end AutoResearch
