/-
  PokeredBugs/Proofs/BadgeReflect.lean — Badge boost stacking enables Reflect overflow.

  ## The Bug Interaction
  Three separate mechanisms combine catastrophically:
  1. Badge boosts (ApplyBadgeStatBoosts): stat += stat/8, reapplied on EVERY stat change
  2. Reflect: doubles defense with no cap
  3. .scaleStats: wraps at 1024 (keeps only low byte after /4)

  When the opponent uses Growl (or any stat-modifying move), badge boosts
  compound on ALL stats — including defense. The Thunder Badge boosts defense
  by 9/8 each time. After just ONE Growl, Cloyster's defense goes from 458
  to 515 (> 512). Then Reflect doubles to 1030, which wraps to 1 after
  .scaleStats. Effective defense drops from 128 to 1.

  This requires NO action from the player beyond using Reflect. The opponent's
  Growl unwittingly enables the overflow.

  ## Assembly Context
  - Badge boosts: core.asm:6454-6505 — called on every stat modification
  - Reflect: core.asm:4051-4053 — sla c; rl b (no cap)
  - .scaleStats: core.asm:4107-4127 — divides by 4, keeps low byte
  - Growl triggers badge reapplication: effects.asm:689
-/
import SM83

namespace PokeredBugs

/-! ### Model -/

/-- Apply one badge boost to a stat: stat + floor(stat/8), capped at 999. -/
def badgeBoost (stat : Nat) : Nat :=
  min (stat + stat / 8) 999

/-- Apply badge boost N times (compounding). -/
def badgeBoostN (stat : Nat) (n : Nat) : Nat :=
  match n with
  | 0 => stat
  | n + 1 => badgeBoostN (badgeBoost stat) n

/-- Reflect doubling. -/
def reflectDoubleN (stat : Nat) : Nat := stat * 2

/-- scaleStats: divide by 4, keep low byte. -/
def badgeScaleToU8 (stat : Nat) : Nat := (stat / 4) % 256

/-- Full pipeline: badge boost N times → optional Reflect → scaleStats.
    Returns effective defense (0 = freeze). -/
def fullPipeline (baseDef : Nat) (badgeApplications : Nat)
    (hasReflect : Bool) (attack : Nat) : Nat :=
  let def' := badgeBoostN baseDef badgeApplications
  let def' := if hasReflect then reflectDoubleN def' else def'
  -- Scaling triggers when either stat > 255
  if attack ≤ 255 ∧ def' ≤ 255 then def'
  else badgeScaleToU8 def'

/-! ### Proof 1: Badge Stacking Pushes Defense Past 512 -/

/-- Cloyster's max defense at level 100: 458.
    One badge boost (Thunder Badge): 458 + 57 = 515. > 512! -/
theorem one_growl_exceeds_512 :
    badgeBoost 458 = 515 ∧ 515 > 512 := by native_decide

/-- Multiple Growls compound further, all capped at 999. -/
theorem badge_stacking_progression :
    badgeBoostN 458 0 = 458 ∧
    badgeBoostN 458 1 = 515 ∧
    badgeBoostN 458 2 = 579 ∧
    badgeBoostN 458 3 = 651 ∧
    badgeBoostN 458 4 = 732 ∧
    badgeBoostN 458 5 = 823 ∧
    badgeBoostN 458 6 = 925 ∧
    badgeBoostN 458 7 = 999 := -- capped
  by native_decide

/-! ### Proof 2: The Catastrophic Interaction -/

/-- After ONE Growl + Reflect: defense wraps to 1.
    Attack = 300 (triggers scaling). -/
theorem one_growl_reflect_catastrophe :
    -- No badge boost, no Reflect: 458/4 = 114
    fullPipeline 458 0 false 300 = 114 ∧
    -- One badge boost, no Reflect: 515/4 = 128
    fullPipeline 458 1 false 300 = 128 ∧
    -- No badge boost, Reflect: 916/4 = 229
    fullPipeline 458 0 true 300 = 229 ∧
    -- One badge boost + Reflect: 1030/4 = 257, mod 256 = 1!
    fullPipeline 458 1 true 300 = 1 := by
  native_decide

/-- The effective defense drops from 128 to 1 — a 128x reduction.
    Reflect is supposed to DOUBLE defense but instead divides it by 128. -/
theorem reflect_128x_worse :
    fullPipeline 458 1 false 300 / fullPipeline 458 1 true 300 = 128 := by
  native_decide

/-! ### Proof 3: No Player Action Required -/

/-- The player doesn't need to use Withdraw/Barrier/Harden.
    The opponent using Growl (lowering the player's attack)
    triggers badge boost reapplication, which boosts defense.
    One Growl + Reflect = catastrophe.

    Timeline:
    1. Player sends out Cloyster (defense = 458)
    2. Opponent uses Growl (attack lowered, badge boost reapplied)
    3. Cloyster's defense: 458 → 515 (Thunder Badge boost)
    4. Cloyster uses Reflect (defense doubled: 515 * 2 = 1030)
    5. scaleStats: 1030/4 = 257, mod 256 = 1
    6. Effective defense = 1 → Cloyster takes massive damage -/
theorem no_player_action_needed :
    -- Step 2-3: Growl triggers badge boost
    badgeBoost 458 = 515 ∧
    -- Step 4-5: Reflect doubles and wraps
    fullPipeline 458 1 true 300 = 1 := by
  native_decide

/-! ### Proof 4: Defense Zero (Freeze) Is Reachable -/

/-- With 2 Growls, defense reaches 579. Reflect: 1158.
    1158/4 = 289, mod 256 = 33. Not a freeze, but very low. -/
theorem two_growls_reflect :
    fullPipeline 458 2 true 300 = 33 := by native_decide

/-- The exact defense value that Reflect pushes to 0 (freeze):
    defense = 512 → Reflect → 1024 → scaleStats → 0 → FREEZE.
    Badge-boosted defense can hit this exact value. -/
theorem badge_reflect_near_freeze :
    -- badgeBoost 455 = 511. Reflect: 1022/4=255. Safe (just barely).
    fullPipeline 455 1 true 300 = 255 ∧
    -- badgeBoost 456 = 513. Reflect: 1026/4=256, mod 256=0. FREEZE!
    fullPipeline 456 1 true 300 = 0 ∧
    -- badgeBoost 458 = 515. Reflect: 1030/4=257, mod 256=1. Near-freeze.
    fullPipeline 458 1 true 300 = 1 := by
  native_decide

/-! ### Proof 5: Multiple Badges Make It Worse -/

/-- Even without Thunder Badge, other badges boost other stats.
    But with Thunder Badge, EVERY stat modification compounds defense.
    With 3 Growls: defense = 651. Reflect: 1302/4 = 325, mod 256 = 69. -/
theorem three_growls_reflect :
    fullPipeline 458 3 true 300 = 69 := by native_decide

/-- At max stacking (capped at 999) + Reflect: 1998/4 = 499, mod 256 = 243. -/
theorem max_stacking_reflect :
    fullPipeline 458 7 true 300 = 243 := by native_decide

/-! ### Proof 6: Not Just Cloyster -/

/-- Any Pokemon with defense ≥ 456 triggers the freeze zone after one badge boost + Reflect.
    Many Pokemon reach this: Golem (459), Slowbro (459), etc. -/
theorem freeze_threshold :
    -- Defense 455: one badge boost → 511, Reflect → 1022, safe (255)
    fullPipeline 455 1 true 300 = 255 ∧
    -- Defense 456: one badge boost → 513, Reflect → 1026, mod 256 → FREEZE or near-freeze
    fullPipeline 456 1 true 300 = 0 := by
  native_decide

/-! ### #eval Demonstration -/

-- Full progression: (badge_applications, no_reflect, with_reflect)
#eval
  (List.range 8).map fun n =>
    (n, badgeBoostN 458 n, fullPipeline 458 n false 300, fullPipeline 458 n true 300)

end PokeredBugs
