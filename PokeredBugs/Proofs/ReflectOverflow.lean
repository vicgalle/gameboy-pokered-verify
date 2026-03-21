/-
  PokeredBugs/Proofs/ReflectOverflow.lean — Reflect/Light Screen overflow bug.

  ## The Bug
  Reflect doubles defense via `sla c; rl b` (16-bit left shift) with NO cap.
  The stat stage system caps modified stats at 999, but Reflect is applied
  AFTER stat stages, bypassing the cap.

  When defense ≥ 512 (achievable via Barrier/Harden + high base defense),
  the doubled value exceeds 1023. The `.scaleStats` routine divides by 4
  and keeps only the low byte (mod 256), causing wrapping.

  Source: core.asm lines 4044-4053 (Reflect), 4107-4127 (.scaleStats)
  Comment at line 4084: "reflect and light screen boosts do not cap the
  stat at MAX_STAT_VALUE, so weird things will happen during stats scaling"
-/
import SM83

namespace PokeredBugs

/-! ### Model (using Nat with explicit truncation for clarity) -/

/-- Scale stat by /4, keep only low byte. Models the srl/rr pair + ld b,l. -/
def scaleToU8 (stat : Nat) : Nat := (stat / 4) % 256

/-- The .scaleStats routine. Both stats divided by 4 when either > 255.
    Offensive stat bumped to 1 if zero; defensive stat is NOT. -/
def scaleStatsPair (attack defense : Nat) : Nat × Nat :=
  if attack ≤ 255 ∧ defense ≤ 255 then
    (attack, defense)
  else
    let a := scaleToU8 attack
    let d := scaleToU8 defense
    let a := if a == 0 then 1 else a
    -- defensive stat NOT bumped!
    (a, d)

/-- Effective defense after optional Reflect, given attacker's stat.
    Returns 0 if the game would freeze (division by zero). -/
def effectiveDefense (attack defense : Nat) (hasReflect : Bool) : Nat :=
  let def' := if hasReflect then defense * 2 else defense
  (scaleStatsPair attack def').2

/-! ### Proof 1: Reflect Causes Freeze at Defense = 512 -/

/-- Defense 512 with Reflect: 1024/4 = 256, mod 256 = 0. FREEZE. -/
theorem reflect_512_freezes :
    effectiveDefense 300 512 true = 0 := by native_decide

/-- Without Reflect: 512/4 = 128. Fine. -/
theorem no_reflect_512_ok :
    effectiveDefense 300 512 false = 128 := by native_decide

/-! ### Proof 2: Reflect REDUCES Effective Defense When Defense ≥ 512 -/

/-- Cloyster with one Barrier: defense ~696. Attack = 300 (triggers scaling).
    Without Reflect: 696/4 = 174. With Reflect: 1392/4 = 348, mod 256 = 92.
    Reflect nearly HALVES the effective defense! -/
theorem cloyster_barrier_reflect :
    effectiveDefense 300 696 false = 174 ∧
    effectiveDefense 300 696 true = 92 := by native_decide

/-- Reflect makes Cloyster take MORE damage. -/
theorem reflect_hurts_cloyster :
    effectiveDefense 300 696 true < effectiveDefense 300 696 false := by
  native_decide

/-- Max stat-boosted defense (999) with Reflect: 1998/4 = 499, mod 256 = 243.
    Without: 999/4 = 249. Reflect costs 6 defense points. -/
theorem max_defense_reflect :
    effectiveDefense 300 999 false = 249 ∧
    effectiveDefense 300 999 true = 243 := by native_decide

/-! ### Proof 3: Concrete Gameplay Scenarios -/

/-- Cloyster: base defense 180, level 100 max DVs ≈ 464.
    After 1 Barrier (+2 stages = 2x): 464 * 2 = 928 (< 999 cap).
    928 ≥ 512, so Reflect causes wrapping. -/
theorem cloyster_1barrier_reflect :
    effectiveDefense 300 928 false = 232 ∧
    effectiveDefense 300 928 true = 208 := by native_decide

/-- After 2 Barriers (+4 stages = 3x): min(464*3, 999) = 999. -/
theorem cloyster_2barrier_reflect :
    effectiveDefense 300 999 false = 249 ∧
    effectiveDefense 300 999 true = 243 := by native_decide

/-- Even modest defense triggers: defense=520 with Reflect.
    Without: 520/4=130. With: 1040/4=260, mod 256=4. Catastrophic! -/
theorem modest_defense_catastrophe :
    effectiveDefense 300 520 false = 130 ∧
    effectiveDefense 300 520 true = 4 := by native_decide

/-! ### Proof 4: The Threshold -/

/-- Below 512: Reflect always helps (doubles effective defense). -/
theorem reflect_helps_below_512 :
    effectiveDefense 300 400 true > effectiveDefense 300 400 false ∧
    effectiveDefense 300 500 true > effectiveDefense 300 500 false := by
  native_decide

/-- At 512: Reflect freezes. -/
theorem reflect_512_is_boundary :
    effectiveDefense 300 511 true > 0 ∧
    effectiveDefense 300 512 true = 0 := by native_decide

/-- Above 512: Reflect hurts (wrapping reduces effective defense). -/
theorem reflect_hurts_above_512 :
    effectiveDefense 300 600 true < effectiveDefense 300 600 false ∧
    effectiveDefense 300 700 true < effectiveDefense 300 700 false ∧
    effectiveDefense 300 928 true < effectiveDefense 300 928 false := by
  native_decide

/-! ### Proof 5: Sawtooth Pattern -/

/-- Effective defense with Reflect follows a sawtooth: rises to 255
    at defense=511, crashes to 0 at 512, then slowly recovers. -/
theorem reflect_sawtooth :
    effectiveDefense 300 400 true = 200 ∧   -- 800/4=200
    effectiveDefense 300 511 true = 255 ∧   -- 1022/4=255
    effectiveDefense 300 512 true = 0 ∧     -- 1024/4=256→0 FREEZE
    effectiveDefense 300 520 true = 4 ∧     -- 1040/4=260→4
    effectiveDefense 300 600 true = 44 ∧    -- 1200/4=300→44
    effectiveDefense 300 700 true = 94 ∧    -- 1400/4=350→94
    effectiveDefense 300 800 true = 144 ∧   -- 1600/4=400→144
    effectiveDefense 300 999 true = 243 :=  -- 1998/4=499→243
  by native_decide

/-! ### #eval Demonstration -/

-- Defense progression: (defense, no_reflect, with_reflect)
#eval
  let vals := #[400, 464, 500, 511, 512, 520, 600, 696, 800, 928, 999]
  vals.map fun d => (d, effectiveDefense 300 d false, effectiveDefense 300 d true)

end PokeredBugs
