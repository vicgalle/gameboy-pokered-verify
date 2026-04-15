import SM83

namespace AutoResearch

/--
State of a Pokemon during the Substitute move execution.
-/
structure BattleState where
  hp : BitVec 16
  maxHP : BitVec 16
  subHP : BitVec 8
  hasSub : Bool
deriving Repr, DecidableEq

/--
A faithful model of the buggy Substitute routine in Pokémon Red/Blue.
The code calculates the cost as (MaxHP / 4) and then subtracts it from Current HP.
It only branches to 'notEnoughHP' if the carry flag is set (Current HP < Cost).
If Current HP == Cost, the carry flag is not set, and the move succeeds, leaving the user at 0 HP.
Additionally, if Max HP < 4, the cost rounds down to 0, creating a 0-HP substitute.
-/
def substitute_impl (hp maxHP : BitVec 16) : BattleState :=
  -- The cost calculation: maxHP >> 2 (16-bit)
  let cost := maxHP >>> 2
  -- The low byte of the cost is stored as the substitute's HP.
  -- In Gen 1, Max HP < 1024, so cost < 256. The low byte is the whole cost.
  let costLow := BitVec.ofNat 8 cost.toNat
  
  -- The SM83 logic: subtract and check only the carry flag (jr c, .notEnoughHP).
  -- Carry is set if hp < cost.
  if hp.toNat < cost.toNat then
    -- .notEnoughHP: No substitute created, user HP unchanged.
    { hp := hp, maxHP := maxHP, subHP := 0, hasSub := false }
  else
    -- Success: Deduct HP and set the substitute flag.
    let newHP := hp - cost
    { hp := newHP,
      maxHP := maxHP,
      subHP := costLow,
      hasSub := true }

/--
A model of the intended/correct behavior for Substitute.
The user must have strictly more HP than the cost to survive, 
and the cost must be at least 1 HP to create a valid shield.
-/
def substitute_spec (hp maxHP : BitVec 16) : BattleState :=
  let cost := maxHP >>> 2
  let costLow := BitVec.ofNat 8 cost.toNat
  
  -- Correct conditions:
  -- 1. Cost must be > 0 (prevents 0-HP substitute bug).
  -- 2. HP must be > cost (prevents user-at-0-HP bug).
  if cost.toNat == 0 || hp.toNat <= cost.toNat then
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
  -- Witness: Pokemon at full HP with 3 Max HP.
  let hp := BitVec.ofNat 16 3
  let maxHP := BitVec.ofNat 16 3
  use hp, maxHP
  -- Proof: 3 / 4 = 0. 3 >= 0 succeeds. SubHP = 0.
  native_decide

/--
L1: Bug 2 Existence (User at 0 HP).
If Current HP is exactly 1/4 of Max HP, the user is left with 0 HP but the move succeeds.
-/
theorem bug2_exists : ∃ hp maxHP,
    (substitute_impl hp maxHP).hasSub = true ∧ 
    (substitute_impl hp maxHP).hp = 0 := by
  -- Witness: Max HP 40 (Cost 10), Current HP 10.
  let hp := BitVec.ofNat 16 10
  let maxHP := BitVec.ofNat 16 40
  use hp, maxHP
  -- Proof: 10 - 10 = 0. No carry. user HP becomes 0.
  native_decide

/--
L2: Characterization of Bug 2.
The bug where the user is left at 0 HP occurs if and only if the current HP
is exactly equal to the floor of Max HP / 4 (and HP > 0).
-/
theorem bug2_iff (hp maxHP : BitVec 16) :
    (substitute_impl hp maxHP).hasSub ∧ (substitute_impl hp maxHP).hp = 0 ↔
    (hp.toNat = maxHP.toNat / 4 ∧ hp.toNat > 0) := by
  unfold substitute_impl
  have cost_def : (maxHP >>> 2).toNat = maxHP.toNat / 4 := by apply BitVec.toNat_shiftRight
  split
  · -- Case: hp < cost (Fail)
    rename_i h_lt
    simp [h_lt]
  · -- Case: hp >= cost (Success)
    rename_i h_ge
    simp
    constructor
    · intro h_res0
      have : hp.toNat = (maxHP >>> 2).toNat := by
        apply_fun BitVec.toNat at h_res0
        rw [BitVec.toNat_sub h_ge] at h_res0
        omega
      rw [cost_def] at this
      constructor
      · exact this
      · rw [this]; rw [← cost_def]; omega
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub h_ge, cost_def, h.1]
      simp

/--
L3: Fix Correctness.
Prove that in the specification, if a substitute is created, the user 
necessarily remains with > 0 HP and the substitute itself has > 0 HP.
(Assuming Max HP is within Gen 1 bounds, i.e., < 1024).
-/
theorem fix_is_safe (hp maxHP : BitVec 16) (h_range : maxHP.toNat < 1024) :
    let res := substitute_spec hp maxHP
    res.hasSub → (res.hp.toNat > 0 ∧ res.subHP.toNat > 0) := by
  unfold substitute_spec
  intro res h
  split at h
  · contradiction -- cost == 0 || hp <= cost: hasSub would be false
  · rename_i h_not_fail
    simp at h_not_fail -- cost.toNat != 0 AND hp.toNat > cost.toNat
    let cost := maxHP >>> 2
    have cost_def : cost.toNat = maxHP.toNat / 4 := by apply BitVec.toNat_shiftRight
    constructor
    · -- Prove User HP > 0: Since hp > cost, hp - cost > 0
      apply Nat.sub_pos_of_lt
      exact BitVec.toNat_lt_toNat.mp (by omega)
    · -- Prove Substitute HP > 0: Since 0 < cost < 256, costLow > 0
      have h_cost_pos : cost.toNat > 0 := by omega
      have h_cost_max : cost.toNat < 256 := by rw [cost_def]; omega
      -- subHP is (cost % 256). For 0 < cost < 256, this is cost.
      unfold BitVec.ofNat
      simp [h_cost_max, h_cost_pos]
      omega

end AutoResearch
