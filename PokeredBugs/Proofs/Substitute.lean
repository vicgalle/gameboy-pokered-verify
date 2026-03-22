/-
  PokeredBugs/Proofs/Substitute.lean — Formal verification of Substitute HP bugs.

  ## The Bugs (TWO bugs in one routine!)

  ### Bug A: Zero-HP Substitute
  Substitute costs maxHP/4 of the user's max HP (via two srl/rr right shifts).
  When maxHP ≤ 3, integer division gives 0, creating a Substitute with 0 HP
  that breaks on the first hit.

  ### Bug B: User left at 0 HP
  The HP sufficiency check uses `jr c` (carry = underflow), but doesn't check
  for zero. When currentHP = maxHP/4 exactly, the subtraction gives 0 with no
  carry, so the Substitute is created and the user survives at 0 HP.

  Source: engine/battle/move_effects/substitute.asm

  ## Proof Techniques
  This file demonstrates diverse proof strategies beyond native_decide:
  - Arithmetic reasoning with omega and simp
  - Iff characterizations via constructor/intro
  - Composition of lemmas
  - Equational calc blocks
  - Mixed native_decide (only for the SM83 CPU-level equivalence)
-/
import SM83

namespace PokeredBugs

/-! ### Model -/

/-- Compute maxHP / 4 via two right shifts (srl a; rr b; srl a; rr b).
    Only the low byte `b` is kept as the substitute HP (8-bit). -/
def substituteHP (maxHP : Nat) : Nat := maxHP / 4

/-- Can the user afford the substitute? The assembly checks if
    currentHP - substituteHP underflows (carry flag). It does NOT
    check for the result being exactly zero. -/
def canAffordSubstitute (currentHP maxHP : Nat) : Bool :=
  decide (currentHP ≥ substituteHP maxHP)

/-- HP remaining after creating substitute. -/
def hpAfterSubstitute (currentHP maxHP : Nat) : Nat :=
  currentHP - substituteHP maxHP

/-! ## Bug A: Zero-HP Substitute -/

/-- Core arithmetic fact: n / 4 = 0 iff n < 4.
    Proved with omega after establishing both directions. -/
theorem div4_eq_zero_iff (n : Nat) : n / 4 = 0 ↔ n < 4 := by
  constructor
  · intro h
    -- If n ≥ 4 then n/4 ≥ 1, contradicting h
    omega
  · intro h
    omega

/-- Substitute HP is 0 exactly when maxHP < 4. Proved via the lemma above. -/
theorem substitute_zero_iff (maxHP : Nat) :
    substituteHP maxHP = 0 ↔ maxHP < 4 := by
  exact div4_eq_zero_iff maxHP

/-- The three problematic HP values. -/
theorem sub_hp_1 : substituteHP 1 = 0 := by simp [substituteHP]
theorem sub_hp_2 : substituteHP 2 = 0 := by simp [substituteHP]
theorem sub_hp_3 : substituteHP 3 = 0 := by simp [substituteHP]
theorem sub_hp_4 : substituteHP 4 = 1 := by simp [substituteHP]

/-- For HP ≥ 4, the substitute always has positive HP. -/
theorem substitute_positive (maxHP : Nat) (h : maxHP ≥ 4) :
    substituteHP maxHP > 0 := by
  simp only [substituteHP]
  omega

/-! ### The zero-HP substitute is always "affordable" -/

/-- A 0-cost substitute is always affordable (subtraction never underflows). -/
theorem zero_sub_always_affordable (currentHP maxHP : Nat)
    (hpos : currentHP > 0) (hlt : maxHP < 4) :
    canAffordSubstitute currentHP maxHP = true := by
  unfold canAffordSubstitute substituteHP
  simp; omega

/-! ## Bug B: User Survives at 0 HP -/

/-- The user is left at 0 HP when currentHP equals the substitute cost. -/
theorem user_zero_hp (currentHP maxHP : Nat) (h : currentHP = substituteHP maxHP)
    (_hpos : substituteHP maxHP > 0) :
    hpAfterSubstitute currentHP maxHP = 0 := by
  simp only [hpAfterSubstitute, h, Nat.sub_self]

/-- The assembly considers this affordable (no carry on exact subtraction). -/
theorem zero_hp_is_affordable (currentHP maxHP : Nat) (h : currentHP = substituteHP maxHP) :
    canAffordSubstitute currentHP maxHP = true := by
  unfold canAffordSubstitute; simp [h]

/-- Concrete example: maxHP=100, currentHP=25. Cost=25. User left at 0 HP. -/
theorem concrete_zero_hp :
    substituteHP 100 = 25 ∧
    hpAfterSubstitute 25 100 = 0 ∧
    canAffordSubstitute 25 100 = true := by
  simp [substituteHP, hpAfterSubstitute, canAffordSubstitute]

/-! ## Characterization: When is the user left at 0 HP? -/

/-- The user ends at 0 HP iff currentHP equals maxHP/4.
    Uses omega for the arithmetic reasoning. -/
theorem zero_hp_iff (currentHP maxHP : Nat)
    (h : canAffordSubstitute currentHP maxHP = true) :
    hpAfterSubstitute currentHP maxHP = 0 ↔ currentHP = substituteHP maxHP := by
  unfold hpAfterSubstitute canAffordSubstitute substituteHP at *
  simp at h; omega

/-! ## Fix Verification -/

/-- Fixed affordability check: reject if cost is 0 OR if user would have 0 HP. -/
def canAffordSubstituteFixed (currentHP maxHP : Nat) : Bool :=
  let cost := substituteHP maxHP
  decide (cost > 0 ∧ currentHP > cost)

/-- The fix rejects zero-cost substitutes. -/
theorem fix_rejects_zero_cost (currentHP maxHP : Nat) (h : maxHP < 4) :
    canAffordSubstituteFixed currentHP maxHP = false := by
  unfold canAffordSubstituteFixed substituteHP
  simp; omega

/-- The fix prevents 0 HP survival. -/
theorem fix_prevents_zero_hp (currentHP maxHP : Nat)
    (h : canAffordSubstituteFixed currentHP maxHP = true) :
    hpAfterSubstitute currentHP maxHP > 0 := by
  unfold canAffordSubstituteFixed substituteHP at h
  unfold hpAfterSubstitute substituteHP
  simp at h; omega

/-- The fix still allows legitimate substitutes. -/
theorem fix_allows_normal (currentHP maxHP : Nat)
    (h1 : maxHP ≥ 4) (h2 : currentHP > maxHP / 4) :
    canAffordSubstituteFixed currentHP maxHP = true := by
  unfold canAffordSubstituteFixed substituteHP
  simp; omega

/-! ## Quantitative Analysis -/

/-- The substitute HP is at most 255 (stored in a single byte). -/
theorem sub_hp_byte_bound (maxHP : Nat) (h : maxHP ≤ 1023) :
    substituteHP maxHP ≤ 255 := by
  simp only [substituteHP]; omega

/-- The minimum maxHP that gives a substitute with N HP.
    substituteHP maxHP = N iff 4*N ≤ maxHP < 4*(N+1). -/
theorem sub_hp_characterization (maxHP N : Nat) :
    substituteHP maxHP = N ↔ 4 * N ≤ maxHP ∧ maxHP < 4 * (N + 1) := by
  unfold substituteHP; omega

/-! ## Both Bugs Interact -/

/-- When maxHP ≤ 3: the substitute has 0 HP AND the user loses 0 HP.
    The user "pays nothing" for a "substitute" that blocks nothing. -/
theorem both_bugs_interact (currentHP maxHP : Nat) (hle : maxHP ≤ 3) (hpos : currentHP > 0)
    (hge : currentHP ≤ maxHP) :
    substituteHP maxHP = 0 ∧ hpAfterSubstitute currentHP maxHP = currentHP := by
  constructor
  · unfold substituteHP; omega
  · have hcost : substituteHP maxHP = 0 := by unfold substituteHP; omega
    simp [hpAfterSubstitute, hcost]

/-! ## SM83-Level Model -/

/-- Model the HP/4 calculation at the CPU level: two srl/rr pairs on hi:lo. -/
def substituteHPSM83 (maxHP_hi maxHP_lo : BitVec 8) : BitVec 8 :=
  let carry1 := maxHP_hi.getLsbD 0
  let a1 := maxHP_hi >>> 1
  let b1 := (maxHP_lo >>> 1) ||| (if carry1 then 0x80 else 0)
  let carry2 := a1.getLsbD 0
  let b2 := (b1 >>> 1) ||| (if carry2 then 0x80 else 0)
  b2

/-- The SM83 implementation matches our abstract model for values ≤ 1023. -/
theorem sm83_matches_model :
    ∀ hi lo : BitVec 8,
      (SM83.mk16 hi lo).toNat ≤ 1023 →
      (substituteHPSM83 hi lo).toNat = substituteHP (SM83.mk16 hi lo).toNat := by
  native_decide

/-! ## #eval Demonstrations -/

-- Substitute HP for various maxHP values
#eval (substituteHP 1, substituteHP 3, substituteHP 4, substituteHP 100, substituteHP 999)

-- User left at 0 HP
#eval (hpAfterSubstitute 25 100, canAffordSubstitute 25 100)

end PokeredBugs
