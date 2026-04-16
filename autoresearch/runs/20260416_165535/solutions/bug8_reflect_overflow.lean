import SM83

namespace AutoResearch

/-!
# Bug: Reflect and Light Screen Overflow

Reflect and Light Screen are moves that double the user's Defense and Special stats,
respectively. However, the Pokemon Red/Blue damage calculation routine has an
arithmetic overflow bug when handling high stats.

When any stat exceeds 255, the routine divides the stats by 4 and keeps only the
low byte (effectively `(stat / 4) % 256`). When a Pokemon's stat is doubled by
Reflect/Light Screen to a value of 1024 or higher, this calculation wraps around.
Specifically, a stat of 512 doubled to 1024 becomes `(1024 / 4) % 256 = 256 % 256 = 0`.
This leads to a division-by-zero freeze or significantly reduced effective defense.
-/

/--
The buggy implementation of Reflect stat doubling.
If the doubled stat exceeds 255, the engine applies the divide-by-4 and 
low-byte (modulo 256) logic. We multiply back by 4 to compare the 
'effective' defense stat to the original on the same scale.
-/
def impl (s : BitVec 16) : BitVec 16 :=
  let doubled := s <<< 1
  if doubled > 255 then
    -- The engine divides by 4, then keeps the low byte (&&& 255).
    ((doubled >>> 2) &&& 255) <<< 2
  else
    doubled

/--
The specification (intended) behavior: the stat is correctly doubled.
Even if the game has a maximum stat limit (e.g., 999), it should not wrap 
around to zero or small values.
-/
def spec (s : BitVec 16) : BitVec 16 :=
  s <<< 1

-- L1: Concrete Witness - A defense stat of 512 results in 0 effective defense.
theorem exists_bug_freeze : impl 512 = 0 := by
  native_decide

-- L1: Concrete Witness - A defense stat of 600 ends up lower than it started.
-- (600 -> 1200. 1200/4 = 300. 300 % 256 = 44. 44 * 4 = 176.)
theorem exists_bug_reduction : ∃ s : BitVec 16, impl s < s := 
  ⟨600, by native_decide⟩

-- L2: Universal characterization of the weakening effect.
-- For stats high enough to cause doubling to reach 1024, Reflect reduces your defense.
theorem forall_weakens_above_512 : ∀ s : BitVec 16, s >= 512 ∧ s < 1024 → impl s < s := by
  have h := (by native_decide : ∀ s : BitVec 16, s >= 512 ∧ s < 1024 → 
    (let d := s <<< 1; if d > 255 then ((d >>> 2) &&& 255) <<< 2 else d) < s)
  intro s hs
  exact h s hs

-- L2: Universal characterization of safe range.
-- For stats below 512, Reflect still increases or maintains the stat (even with granularity loss).
theorem forall_safe_below_512 : ∀ s : BitVec 16, s < 512 → impl s >= s := by
  have h := (by native_decide : ∀ s : BitVec 16, s < 512 → 
    (let d := s <<< 1; if d > 255 then ((d >>> 2) &&& 255) <<< 2 else d) >= s)
  intro s hs
  exact h s hs

-- L3: A fix that doubles correctly without the byte-mask wrap-around.
def fix (s : BitVec 16) : BitVec 16 := s <<< 1

theorem fix_correct : ∀ s : BitVec 16, fix s = spec s := 
  fun _ => rfl

-- L4: Relational property - The buggy implementation and specification diverge 
-- significantly as soon as the doubled stat hits the 1024 overflow threshold.
theorem impl_spec_desync : ∀ s : BitVec 16, s >= 512 ∧ s < 32768 → impl s < spec s := by
  have h := (by native_decide : ∀ s : BitVec 16, s >= 512 ∧ s < 32768 → 
    (let d := s <<< 1; if d > 255 then ((d >>> 2) &&& 255) <<< 2 else d) < (s <<< 1))
  intro s hs
  exact h s hs

end AutoResearch
