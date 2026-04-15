import SM83

namespace AutoResearch

/--
The Badge Boost logic in SM83 assembly (engine/battle/core.asm).
It multiplies a stat by 9/8 (stat + stat/8) and caps the result at 999.
-/
def applyBadgeBoost (stat : BitVec 16) : BitVec 16 :=
  let boost := stat >>> 3
  let res := stat + boost
  -- MAX_STAT_VALUE in Pokemon Red/Blue is 999
  if res.toNat > 999 then BitVec.ofNat 16 999 else res

/--
Models the 'Badge Stacking' bug where badge boosts are reapplied
every time any stat modification occurs in battle.
-/
def badgeStacking (baseStat : BitVec 16) (applications : Nat) : BitVec 16 :=
  match applications with
  | 0 => baseStat
  | n + 1 => applyBadgeBoost (badgeStacking baseStat n)

/--
The buggy Damage Scaling logic from Gen 1.
To fit stats into the damage formula, the game reduces them to 8-bit values.
If the stat (including Reflect/Light Screen doubling) is >= 256, it divides by 4.
Crucially, it then takes only the low byte of the result, allowing values >= 1024 to wrap.
-/
def impl (statInRam : BitVec 16) (reflectActive : Bool) : BitVec 8 :=
  -- Reflect doubles the defense stat during damage calculation
  let d := if reflectActive then statInRam <<< 1 else statInRam
  -- The game checks if the high byte of the stat is non-zero
  if (d >>> 8).toNat != 0 then
    -- It divides by 4 and then truncates to 8 bits (the bug)
    BitVec.ofNat 8 (d.toNat / 4)
  else
    -- Otherwise, it uses the low byte as-is
    BitVec.ofNat 8 d.toNat

/--
The intended Damage Scaling logic.
This version prevents the catastrophe by capping the effective defense at 255
instead of allowing it to wrap around to small numbers.
-/
def spec (statInRam : BitVec 16) (reflectActive : Bool) : BitVec 8 :=
  let d := if reflectActive then statInRam.toNat * 2 else statInRam.toNat
  let scaled := if d >= 256 then d / 4 else d
  if scaled > 255 then BitVec.ofNat 8 255
  else BitVec.ofNat 8 scaled

/- 
  L1: Bug Existence (Witness) 
  Verify the specific case described: Cloyster with 458 base defense.
  One application of the badge boost pushes defense to 515.
  Using Reflect on 515 defense (1030) results in effective defense 1.
-/
theorem bug_exists : 
  let cloyster_base := BitVec.ofNat 16 458
  let boosted := applyBadgeBoost cloyster_base
  -- Without Reflect: (515 / 4) = 128
  impl boosted false = BitVec.ofNat 8 128 ∧
  -- With Reflect: (1030 / 4) = 257. Wrapped: 257 % 256 = 1
  impl boosted true = BitVec.ofNat 8 1 := by
  native_decide

/- 
  L2: Characterization of the Reflect Overflow
  Prove that the opponent's Growl (which triggers the badge re-application)
  can cause a 'catastrophic' reduction in defense if Reflect is active.
-/
theorem growl_enables_catastrophe :
  let base := BitVec.ofNat 16 458
  let before_growl := base
  let after_growl := applyBadgeBoost base -- Growl triggers the first application
  -- Before Growl, Reflect provides a strong defense (229)
  (impl before_growl true).toNat = 229 ∧
  -- After Growl, Reflect results in a near-zero defense (1)
  (impl after_growl true).toNat = 1 := by
  native_decide

/-
  L3: Fix Correctness
  Show that the fixed logic (spec) avoids the wrap-around, ensuring
  that a boosted Cloyster with Reflect has the maximum possible effective defense (255)
  rather than 1.
-/
theorem fix_prevents_overflow :
  let cloyster_boosted := BitVec.ofNat 16 515
  (spec cloyster_boosted true).toNat = 255 ∧
  (impl cloyster_boosted true).toNat = 1 := by
  native_decide

/-
  L4: Multi-Stacking Property
  Show that multiple stat changes (multiple Growls) continue to shift the 
  effective defense as the stat keeps growing and wrapping.
-/
theorem stacking_variability :
  let base := BitVec.ofNat 16 458
  let boost1 := badgeStacking base 1
  let boost2 := badgeStacking base 2
  -- First boost: 1030 / 4 = 257 -> 1
  (impl boost1 true).toNat = 1 ∧
  -- Second boost: 515 + 64 = 579. 579 * 2 = 1158. 1158 / 4 = 289 -> 33
  (impl boost2 true).toNat = 33 := by
  native_decide

end AutoResearch
