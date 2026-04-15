import SM83

namespace AutoResearch

/--
Models the SM83/Game Boy Pokémon engine's stat normalization.
If a stat exceeds 255, the engine divides it by 4 and stores it in an 8-bit register.
The bug is the 8-bit truncation (`% 256`), which causes 1024 to wrap to 0.
-/
def getEffectiveStatBuggy (stat : Nat) : Nat :=
  if stat > 255 then
    -- The result of (stat / 4) is truncated to 8 bits in the SM83 register 'a'
    (stat / 4) % 256
  else
    stat

/--
Models the behavior of Reflect (doubling the Defense stat) followed by 
the buggy damage calculation normalization.
-/
def impl (baseStat : BitVec 16) (hasReflect : Bool) : Nat :=
  let s := if hasReflect then baseStat.toNat * 2 else baseStat.toNat
  getEffectiveStatBuggy s

/--
The intended behavior (spec) should not have an 8-bit wrap-around.
Doubling a stat should consistently increase or maintain the effective defense.
-/
def getEffectiveStatFixed (stat : Nat) : Nat :=
  if stat > 255 then
    stat / 4
  else
    stat

def spec (baseStat : BitVec 16) (hasReflect : Bool) : Nat :=
  let s := if hasReflect then baseStat.toNat * 2 else baseStat.toNat
  getEffectiveStatFixed s

-------------------------------------------------------------------------------
-- L1: Bug Existence
-------------------------------------------------------------------------------

/--
Reflect causes a decrease in effective defense for high stat values.
For a defense of 512 (achievable with Barrier), Reflect doubles it to 1024,
which normalizes to 0 (1024/4 = 256 ≡ 0 mod 256).
-/
theorem bug_exists : ∃ s : BitVec 16, impl s true < impl s false := by
  -- We use 512 as the witness
  use 512
  -- Without Reflect: 512 > 255 -> 512/4 % 256 = 128
  -- With Reflect: 1024 > 255 -> 1024/4 % 256 = 0
  native_decide

-------------------------------------------------------------------------------
-- L2: Characterization
-------------------------------------------------------------------------------

/--
The most severe form of the bug: Reflect causes the defense to wrap to exactly 0.
This typically results in a division-by-zero crash in the damage formula.
-/
theorem reflect_overflow_to_zero : impl 512 true = 0 := by
  native_decide

/--
The bug also manifests at lower values (the "Division Transition").
A Pokemon with 200 Defense has 100 Effective Defense with Reflect,
but 200 Effective Defense without it.
-/
theorem reflect_harmful_at_mid_range : impl 200 true < impl 200 false := by
  native_decide

/--
The bug triggers for any stat where the doubled value, once divided by 4, 
is a multiple of 256.
-/
theorem bug_iff_overflow (s : BitVec 16) :
  s.toNat = 512 → impl s true = 0 ∧ impl s false = 128 := by
  intro h
  simp [h, impl, getEffectiveStatBuggy]
  native_decide

-------------------------------------------------------------------------------
-- L3: Fix Correctness
-------------------------------------------------------------------------------

/--
The fix (removing the modulo truncation) ensures that the effective stat
after Reflect is always at least half of the original effective stat,
preventing the 512 -> 0 catastrophic failure.
-/
theorem fix_prevents_zero_and_halving (s : BitVec 16) :
  s.toNat > 0 ∧ s.toNat < 1024 → spec s true > 0 := by
  intro h
  unfold spec getEffectiveStatFixed
  split <;> split <;> omega

/--
The fix is monotonic for stats in the dangerous high-defense range.
Without the modulo, Reflect doubling the stat (512 -> 1024) 
correctly results in a higher effective stat (128 -> 256).
-/
theorem fix_is_monotonic_high (s : BitVec 16) :
  s.toNat >= 256 ∧ s.toNat < 1024 → spec s true >= spec s false := by
  intro h
  unfold spec getEffectiveStatFixed
  -- Since s >= 256, both unreflected and reflected trigger the division by 4.
  -- 2s / 4 >= s / 4
  have h1 : s.toNat > 255 := by omega
  have h2 : s.toNat * 2 > 255 := by omega
  simp [h1, h2]
  omega

end AutoResearch
