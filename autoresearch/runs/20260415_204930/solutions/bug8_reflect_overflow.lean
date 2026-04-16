import SM83
import Harness

namespace AutoResearch

/-!
  Bug: Reflect/Light Screen Overflow in Pokemon Red

  Reflect doubles the user's Defense stat. However, the Gen 1 damage formula
  computes effective defense as `(stat / 4) mod 256` when stat > 255.

  When Defense = 512, Reflect doubles it to 1024:
    effectiveStat(1024) = (1024 / 4) mod 256 = 256 mod 256 = 0

  Compare to without Reflect:
    effectiveStat(512) = (512 / 4) mod 256 = 128

  So Reflect reduces effective defense from 128 to 0 — catastrophic!
-/

-- Gen 1 effective stat formula used in damage calculation:
-- if stat > 255: use (stat / 4) mod 256; else use stat directly
def effectiveStat (stat : BitVec 16) : BitVec 8 :=
  if stat.toNat > 255 then
    BitVec.ofNat 8 (stat.toNat / 4)
  else
    BitVec.ofNat 8 stat.toNat

-- Buggy: Reflect doubles the raw stat value, causing overflow in the effective formula
def impl (baseDef : BitVec 16) : BitVec 8 :=
  effectiveStat (baseDef * 2)

-- Spec: Reflect should double the effective defense (correct intended behavior)
def spec (baseDef : BitVec 16) : BitVec 8 :=
  let eff := (effectiveStat baseDef).toNat
  BitVec.ofNat 8 (min (eff * 2) 255)

-- L1: Concrete witness — Defense 512 with Reflect gives 0 effective defense
-- impl 512: effectiveStat(1024) = (1024/4) mod 256 = 256 mod 256 = 0
theorem l1_impl_zero : impl 512 = 0 := by native_decide

-- spec 512: min(128*2, 255) = 255
theorem l1_spec_full : spec 512 = 255 := by native_decide

theorem l1_impl_ne_spec : impl (512 : BitVec 16) ≠ spec (512 : BitVec 16) := by
  native_decide

-- L2: Reflect actively harms Pokemon with Defense ≥ 512
theorem l2_reflect_reduces_defense :
    ∃ baseDef : BitVec 16, impl baseDef < effectiveStat baseDef := by
  exact ⟨512, by native_decide⟩

-- L2: Exact diagnostic values confirming the overflow bug
theorem l2_diagnostic :
    effectiveStat 512 = 128 ∧ impl 512 = 0 ∧ spec 512 = 255 := by
  native_decide

-- L2: Another victim — Defense 768 (Barrier + Reflect on Cloyster)
-- effectiveStat(768) = 768/4 mod 256 = 192
-- impl(768) = effectiveStat(1536) = 1536/4 mod 256 = 384 mod 256 = 128  (worse!)
theorem l2_cloyster_scenario :
    impl 768 < effectiveStat 768 := by native_decide

-- L3: Fixed implementation — double the effective defense directly, avoiding overflow
def implFixed (baseDef : BitVec 16) : BitVec 8 :=
  let eff := (effectiveStat baseDef).toNat
  BitVec.ofNat 8 (min (eff * 2) 255)

-- L3: Fix matches spec for all inputs (same definition by construction)
theorem l3_fix_correct :
    ∀ baseDef : BitVec 16, implFixed baseDef = spec baseDef :=
  fun _ => rfl

-- L3: Verify fix resolves the specific Defense 512 case
theorem l3_fix_at_512 : implFixed 512 = 255 := by native_decide

-- L3: Fix is always at least as good as no Reflect for the 512 witness
theorem l3_fix_helps : implFixed 512 > effectiveStat 512 := by native_decide

end AutoResearch
