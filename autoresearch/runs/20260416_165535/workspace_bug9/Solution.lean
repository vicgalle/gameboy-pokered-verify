import SM83

namespace AutoResearch

/-- 
  Accuracy/Evasion stage multipliers from Pokémon Red/Blue.
  The table uses denominators of 100 to represent floating point multipliers.
  Indices 0 to 12 represent stages -6 to +6.
-/
def mod_table (idx : Nat) : Nat :=
  match idx with
  | 0  => 25  -- -6: 25/100
  | 1  => 28  -- -5: 28/100
  | 2  => 33  -- -4: 33/100
  | 3  => 40  -- -3: 40/100
  | 4  => 50  -- -2: 50/100
  | 5  => 66  -- -1: 66/100
  | 6  => 100 --  0: 100/100
  | 7  => 150 -- +1: 150/100
  | 8  => 200 -- +2: 200/100
  | 9  => 250 -- +3: 250/100
  | 10 => 300 -- +4: 300/100
  | 11 => 350 -- +5: 350/100
  | 12 => 400 -- +6: 400/100
  | _  => 100

/-- 
  The buggy implementation (impl).
  Accuracy and evasion modifiers are applied as two sequential multiplication and division passes.
  Integer truncation (floor division) occurs after each pass.
  If the opponent has evasion boosts, the attacker receives a corresponding accuracy penalty.
-/
def impl (base : Nat) (acc_stage eva_stage : Nat) : Nat :=
  -- Pass 1: Apply accuracy stage multiplier
  let acc_idx := if acc_stage > 12 then 12 else acc_stage
  let h1 := (base * mod_table acc_idx) / 100
  -- Pass 2: Apply evasion multiplier (opponent's evasion is the inverse stage for attacker)
  -- For example, if opponent evasion is +1 (idx 7), the penalty multiplier is at idx 5 (-1).
  let eva_idx := if eva_stage > 12 then 0 else (12 - eva_stage)
  (h1 * mod_table eva_idx) / 100

/-- 
  The intended specification (spec).
  Accuracy and evasion stages should cancel out before applying any multiplier.
  The net stage is calculated first, clamped to [-6, +6], then applied once.
-/
def spec (base : Nat) (acc_stage eva_stage : Nat) : Nat :=
  let net : Int := (acc_stage : Int) - (eva_stage : Int)
  let final_idx_int := net + 6
  let clamped_idx := if final_idx_int < 0 then 0 else if final_idx_int > 12 then 12 else final_idx_int.toNat
  (base * mod_table clamped_idx) / 100

-- L1: Concrete witness showing the bug exists for equal +1 stages (index 7).
-- For a move with 255 base accuracy, the effective accuracy becomes 252.
theorem bug_exists : ∃ s : Fin 13, impl 255 s.val s.val ≠ spec 255 s.val s.val := by
  exists 7
  native_decide

-- L2: Verification of the +1/+1 accuracy loss (255 becomes 252).
theorem plus_one_accuracy_loss : impl 255 7 7 = 252 ∧ spec 255 7 7 = 255 := by
  constructor <;> rfl

-- L2: Verification of the worst-case accuracy loss at +5/+5 (255 becomes 249).
theorem worst_case_accuracy_loss : impl 255 11 11 = 249 ∧ spec 255 11 11 = 255 := by
  constructor <;> rfl

-- L2: Neutral stage equivalence. When both stages are at base (0), they are equal.
theorem neutral_is_exact : ∀ b : Nat, impl b 6 6 = spec b 6 6 := by
  intro b
  simp [impl, spec, mod_table]

-- L2: Universal property for equal stages.
-- The buggy implementation never exceeds the intended accuracy for base 255.
theorem equal_stages_never_exceed_spec : ∀ s : Fin 13, impl 255 s.val s.val <= spec 255 s.val s.val := by
  have h := (by native_decide : ∀ s : Fin 13, impl 255 s.val s.val <= spec 255 s.val s.val)
  intro s; exact h s

-- L2: Precision loss due to intermediate truncation specifically.
-- Shows that even when the fraction product is mathematically exact (2.5 * 0.4 = 1.0),
-- the two-step floor division results in a loss (254 instead of 255).
theorem truncation_loss_at_plus_three : impl 255 9 9 = 254 ∧ (255 * mod_table 9 * mod_table 3) / 10000 = 255 := by
  constructor <;> rfl

-- L3: The fix: calculate net stage first to ensure modifiers cancel perfectly.
def fix (base : Nat) (acc_stage eva_stage : Nat) : Nat :=
  let net : Int := (acc_stage : Int) - (eva_stage : Int)
  let idx := net + 6
  let clamped := if idx < 0 then 0 else if idx > 12 then 12 else idx.toNat
  (base * mod_table clamped) / 100

theorem fix_is_correct : ∀ b s1 s2, fix b s1 s2 = spec b s1 s2 := by
  intro b s1 s2; rfl

-- L4: Relational Divergence - Boost Penalty Characterization.
-- For a move with 255 base accuracy, most non-neutral equal boosts result in accuracy loss.
theorem boost_divergence_is_common : 
  ∀ s : Fin 13, (s.val = 7 ∨ s.val = 9 ∨ s.val = 10 ∨ s.val = 11) → 
  impl 255 s.val s.val < spec 255 s.val s.val := by
  have h := (by native_decide : ∀ s : Fin 13, (s.val = 7 ∨ s.val = 9 ∨ s.val = 10 ∨ s.val = 11) → impl 255 s.val s.val < spec 255 s.val s.val)
  intro s; exact h s

-- L4: Truncation witness - Even with a base of 1, the two-pass system fails to cancel +1/-1.
theorem truncation_loss_witness : impl 1 7 7 = 0 ∧ spec 1 7 7 = 1 := by
  constructor <;> rfl

end AutoResearch
