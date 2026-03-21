/-
  PokeredBugs/Proofs/BlaineAI.lean — Formal verification of the Blaine AI Super Potion bug.

  ## The Bug
  Blaine's AI uses a Super Potion without checking if his Pokémon's HP is low
  enough to need healing. Every other trainer who uses a healing item first calls
  `AICheckIfHPBelowFraction` to verify HP is below some threshold.

  Source: engine/battle/trainer_ai.asm in pret/pokered

  ## Assembly Context

  Blaine's AI (lines 387-390):
    BlaineAI:
      cp 25 percent + 1     ; 25% chance to trigger
      ret nc
      jp AIUseSuperPotion    ; BUG: no HP check!

  Compare with Erika (lines 374-380), who uses the same item correctly:
    ErikaAI:
      cp 50 percent + 1
      ret nc
      ld a, 10
      call AICheckIfHPBelowFraction  ; ← HP below 1/10th of max?
      ret nc                          ; ← skip if HP is fine
      jp AIUseSuperPotion

  AICheckIfHPBelowFraction returns carry if currentHP < maxHP / a.
  Blaine skips this entirely, so he uses a Super Potion even at full HP.

  Super Potion heals 50 HP, capped at max HP (AIRecoverHP handles overflow).

  ## What We Prove
  1. The bug exists: Blaine heals at full HP (wasting the item)
  2. Characterization: Blaine heals unconditionally regardless of HP
  3. Fix correctness: adding the HP check makes Blaine only heal when needed
  4. Wasted healing: when HP is close to max, most of the 50 HP is wasted
-/
import SM83

namespace PokeredBugs

/-! ### Model -/

/-- Trainer AI healing decision state. We abstract away the random check
    (the `cp 25 percent + 1; ret nc` part) since the bug is downstream of it.
    This models the state AFTER the random check has passed. -/
structure AIHealState where
  currentHP : UInt16
  maxHP : UInt16
  deriving Repr, DecidableEq

/-- Super Potion heals 50 HP, capped at max HP. Models AIRecoverHP. -/
def superPotionHeal (s : AIHealState) : UInt16 :=
  let healed := s.currentHP.toNat + 50
  let capped := min healed s.maxHP.toNat
  ⟨capped⟩

/-- AICheckIfHPBelowFraction: returns true if currentHP < maxHP / divisor.
    This is what Blaine's code is MISSING. -/
def hpBelowFraction (s : AIHealState) (divisor : Nat) : Bool :=
  if divisor == 0 then false
  else s.currentHP.toNat < s.maxHP.toNat / divisor

/-- Blaine's actual AI: after the random check passes, ALWAYS use Super Potion.
    No HP check at all. -/
def blaineActual (s : AIHealState) : Option UInt16 :=
  some (superPotionHeal s)

/-- What Blaine's AI should do (like Erika): check if HP is below 1/10th max,
    only then use Super Potion. Returns none if no healing needed. -/
def blaineCorrect (s : AIHealState) (divisor : Nat := 10) : Option UInt16 :=
  if hpBelowFraction s divisor then
    some (superPotionHeal s)
  else
    none

/-- Was the heal wasted? True if the Pokémon was already at full HP. -/
def healWasted (s : AIHealState) : Bool :=
  s.currentHP == s.maxHP

/-- How much HP was effectively gained (could be less than 50 due to cap). -/
def hpGained (s : AIHealState) : Nat :=
  (superPotionHeal s).toNat - s.currentHP.toNat

/-! ### Proof 1: The Bug Exists -/

/-- Blaine uses a Super Potion even when his Pokémon is at full HP. -/
theorem blaine_heals_at_full_hp :
    ∃ s : AIHealState,
      s.currentHP = s.maxHP ∧ blaineActual s = some (superPotionHeal s) := by
  exact ⟨⟨200, 200⟩, rfl, rfl⟩

/-- With the correct AI, healing at full HP would be skipped. -/
theorem correct_ai_skips_full_hp :
    ∀ s : AIHealState, s.currentHP = s.maxHP → s.maxHP.toNat > 0 →
      blaineCorrect s = none := by
  intro s h hpos
  simp only [blaineCorrect, hpBelowFraction]
  split
  · -- divisor = 0 case (divisor is 10, this is False)
    simp_all
  · -- currentHP < maxHP / 10
    simp_all
    omega

/-! ### Proof 2: Blaine Heals Unconditionally -/

/-- Blaine's actual AI always returns some (always heals), regardless of HP. -/
theorem blaine_always_heals (s : AIHealState) :
    (blaineActual s).isSome = true := by
  rfl

/-- The correct AI does NOT always heal — it skips when HP is sufficient. -/
theorem correct_ai_sometimes_skips :
    ∃ s : AIHealState, (blaineCorrect s).isNone = true := by
  exact ⟨⟨200, 200⟩, rfl⟩

/-! ### Proof 3: Blaine Disagrees With Correct AI -/

/-- There exist HP states where Blaine heals but the correct AI wouldn't. -/
theorem blaine_wastes_potion :
    ∃ s : AIHealState,
      blaineActual s ≠ none ∧ blaineCorrect s = none := by
  refine ⟨⟨200, 200⟩, ?_, ?_⟩
  · simp [blaineActual]
  · rfl

/-- For ANY Pokémon at ≥ 1/10th max HP, Blaine heals but shouldn't. -/
theorem blaine_wastes_when_healthy (s : AIHealState)
    (h : ¬ hpBelowFraction s 10) :
    blaineActual s ≠ none ∧ blaineCorrect s = none := by
  constructor
  · simp [blaineActual]
  · simp [blaineCorrect, h]

/-! ### Proof 4: Fix Correctness -/

/-- The fixed Blaine AI (with HP check) matches what other trainers do.
    When HP is low enough, it heals with the same result. -/
theorem blaine_fix_heals_when_needed (s : AIHealState)
    (h : hpBelowFraction s 10) :
    blaineCorrect s = some (superPotionHeal s) := by
  simp [blaineCorrect, h]

/-- The fixed AI never heals when HP is sufficient. -/
theorem blaine_fix_skips_when_healthy (s : AIHealState)
    (h : ¬ hpBelowFraction s 10) :
    blaineCorrect s = none := by
  simp [blaineCorrect, h]

/-! ### Proof 5: Quantifying Waste -/

/-- Helper: UInt16 constructed from a small Nat round-trips through toNat. -/
private theorem uint16_mk_toNat (n : Nat) (h : n < 65536) :
    ({ toBitVec := (↑n : BitVec 16) } : UInt16).toNat = n := by
  simp [UInt16.toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- At full HP, the heal gains 0 HP — complete waste of the item. -/
theorem full_hp_zero_gain (s : AIHealState) (h : s.currentHP = s.maxHP)
    (hBound : s.maxHP.toNat ≤ 999) :
    hpGained s = 0 := by
  simp only [hpGained, superPotionHeal]
  have hcap : min (s.currentHP.toNat + 50) s.maxHP.toNat = s.maxHP.toNat := by
    rw [h]; omega
  simp only [hcap]
  rw [uint16_mk_toNat _ (by omega), h]; omega

/-- When HP is within 50 of max, the effective heal is less than 50. -/
theorem partial_waste (s : AIHealState)
    (h1 : s.currentHP.toNat + 50 > s.maxHP.toNat)
    (h2 : s.currentHP.toNat < s.maxHP.toNat)
    (hBound : s.maxHP.toNat ≤ 999) :
    hpGained s < 50 := by
  simp only [hpGained, superPotionHeal]
  have hcap : min (s.currentHP.toNat + 50) s.maxHP.toNat = s.maxHP.toNat := by omega
  simp only [hcap]
  rw [uint16_mk_toNat _ (by omega)]
  omega

/-! ### Comparison with Other Trainers -/

/-- Erika's AI: checks HP < maxHP/10 before using Super Potion. -/
def erikaAI (s : AIHealState) : Option UInt16 :=
  blaineCorrect s 10

/-- Lorelei's AI: checks HP < maxHP/5 before using Super Potion (more aggressive). -/
def loreleiAI (s : AIHealState) : Option UInt16 :=
  blaineCorrect s 5

/-- Agatha's AI: checks HP < maxHP/4 before using Super Potion (most aggressive). -/
def agathaAI (s : AIHealState) : Option UInt16 :=
  blaineCorrect s 4

/-- Blaine is the ONLY trainer that heals unconditionally. Every other
    trainer's heal function can return none. -/
theorem blaine_unique_unconditional :
    (∀ s, (blaineActual s).isSome = true) ∧
    (∃ s, (erikaAI s).isNone = true) ∧
    (∃ s, (loreleiAI s).isNone = true) ∧
    (∃ s, (agathaAI s).isNone = true) := by
  exact ⟨fun _ => rfl, ⟨⟨200, 200⟩, rfl⟩, ⟨⟨200, 200⟩, rfl⟩, ⟨⟨200, 200⟩, rfl⟩⟩

end PokeredBugs
