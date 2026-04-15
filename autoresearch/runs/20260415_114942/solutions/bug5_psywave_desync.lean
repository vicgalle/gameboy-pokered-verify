import SM83

namespace AutoResearch

-- Psywave damage is based on B = Level * 1.5.
-- Assembly calculation: ld a, [hl]; ld b, a; srl a; add b
def getB (lvl : BitVec 8) : BitVec 8 :=
  lvl + (lvl >>> 1)

-- Player-side logic (lines 4664-4667): 
-- Loops until A != 0. Does NOT check the upper bound B.
def playerAccepts (r : BitVec 8) : Bool :=
  r != 0

-- Enemy-side logic (lines 4785-4788):
-- Loops until A < B. Does NOT check if A is 0.
def enemyAccepts (lvl r : BitVec 8) : Bool :=
  r < getB lvl

-- L1: Bug Exists (Desynchronization Witness)
-- In a link battle, if one Game Boy treats a move as "Player" and the other as "Enemy",
-- they diverge if they use different acceptance criteria for the random damage.
theorem bug_exists : ∃ (lvl r : BitVec 8), playerAccepts r ≠ enemyAccepts lvl r := 
  ⟨10, 20, by native_decide⟩ -- Level 10, B=15. 20 is accepted by player but rejected by enemy.

-- L2: Characterization - Zero-Damage Discrepancy
-- The enemy can deal 0 damage, but the player cannot (as per asm line 4784).
theorem player_rejects_zero : ∀ lvl, playerAccepts 0 = false := by intro; rfl

theorem enemy_accepts_zero (lvl : BitVec 8) : lvl > 0 → enemyAccepts lvl 0 = true := by
  have h := (by native_decide : ∀ (l : BitVec 8), l > 0 → 0 < l + (l >>> 1))
  intro hl; simp [enemyAccepts, getB, h hl]

-- L2: Characterization - Upper-Bound Discrepancy
-- The player can deal damage significantly exceeding the 1.5x level cap.
theorem player_allows_excessive_damage : ∃ (lvl r : BitVec 8), r > getB lvl ∧ playerAccepts r :=
  ⟨10, 100, by native_decide⟩

-- L3: Fix Correctness
-- The fix is to unify the logic to the intended range: 1 <= damage < B.
def spec (lvl r : BitVec 8) : Bool :=
  r > 0 && r < getB lvl

def fix (lvl r : BitVec 8) : Bool :=
  if r == 0 then false else r < getB lvl

theorem fix_correct (lvl r : BitVec 8) : fix lvl r = spec lvl r := by
  simp [fix, spec]
  split <;> simp_all

end AutoResearch
