import SM83

namespace AutoResearch

/-- 
  Accuracy/Evasion stage multipliers from Pokémon Red/Blue.
  The table uses denominators of 100.
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
  Stages are 0-12, where 6 is neutral.
-/
def impl (base : Nat) (acc_stage eva_stage : Nat) : Nat :=
  -- Pass 1: Apply accuracy stage multiplier
  let h1 := (base * mod_table acc_stage) / 100
  -- Pass 2: Apply evasion multiplier (opponent's evasion is the inverse stage for attacker)
  -- If opponent evasion is +1 (idx 7), the penalty multiplier is at idx 5 (-1).
  let eva_mod_idx := 12 - (if eva_stage > 12 then 12 else eva_stage)
  (h1 * mod_table eva_mod_idx) / 100

/-- 
  The intended specification (spec).
  Accuracy and evasion stages should cancel out before applying any multiplier.
-/
def spec (base : Nat) (acc_stage eva_stage : Nat) : Nat :=
  let net : Int := (acc_stage : Int) - (eva_stage : Int)
  let clamped_idx := if net < -6 then 0 else if net > 6 then 12 else (net + 6).toNat
  (base * mod_table clamped_idx) / 100

-- L1: Concrete witness showing the bug exists for equal +1 stages (index 7).
theorem bug_exists : ∃ s : Fin 13, impl 255 s.val s.val ≠ spec 255 s.val s.val := by
  exists 7
  native_decide

-- L2: Verification of the +1/+1 accuracy loss (255 becomes 252).
theorem plus_one_accuracy_loss : impl 255 7 7 = 252 ∧ spec 255 7 7 = 255 := by
  constructor <;> rfl

-- L2: Verification of the worst-case accuracy loss at +5/+5 (255 becomes 249).
theorem worst_case_accuracy_loss : impl 255 11 11 = 249 ∧ spec 255 11 11 = 255 := by
  constructor <;> rfl

-- L2: Universal property - for any equal stages, the buggy version never exceeds the intended accuracy.
-- This confirms the bug always results in a loss or parity, never a gain.
theorem equal_stages_never_exceed_spec : ∀ s : Fin 13, impl 255 s.val s.val <= spec 255 s.val s.val := by
  have h := (by native_decide : ∀ s : Fin 13, impl 255 s.val s.val <= spec 255 s.val s.val)
  intro s; exact h s

-- L2: Precision loss due to intermediate truncation specifically.
-- Shows that even if the product was exact (2.5 * 0.4 = 1.0), the split steps lose points.
theorem truncation_causes_loss_at_plus_three : impl 255 9 9 = 254 ∧ (255 * mod_table 9 * mod_table 3) / 10000 = 255 := by
  constructor <;> rfl

-- L3: The fix: calculate net stage first to ensure modifiers cancel perfectly.
def fix (base : Nat) (acc_stage eva_stage : Nat) : Nat :=
  let net : Int := (acc_stage : Int) - (eva_stage : Int)
  let clamped_idx := if net < -6 then 0 else if net > 6 then 12 else (net + 6).toNat
  (base * mod_table clamped_idx) / 100

theorem fix_is_correct : ∀ b s1 s2, fix b s1 s2 = spec b s1 s2 := by
  intro b s1 s2; rfl

-- L4: Characterization - The implementation and specification diverge for most boosts.
theorem boost_divergence_is_common : ∃ s : Fin 13, s.val > 6 ∧ s.val < 12 ∧ impl 255 s.val s.val < spec 255 s.val s.val := by
  exists 7
  native_decide

end AutoResearch
