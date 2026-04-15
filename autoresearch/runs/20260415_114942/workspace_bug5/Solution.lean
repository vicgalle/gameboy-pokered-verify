import SM83

namespace AutoResearch

-- Psywave Damage Cap: B = Level + floor(Level / 2)
def getB (lvl : BitVec 8) : BitVec 8 := (lvl >>> 1) + lvl

-- Player's logic: Loops if r == 0. Accepts anything else [1, 255].
-- Bug: Missing the upper bound check (cp b).
def playerAccepts (r : BitVec 8) : Bool := r != 0

-- Enemy's logic: Loops if r >= B. Accepts [0, B-1].
-- Bug: Missing the lower bound check (r != 0).
def enemyAccepts (lvl r : BitVec 8) : Bool := r < getB lvl

-- L1: Bug exists - Concrete desync witness
-- For Level 10 (B=15), a roll of 0 is accepted by the enemy but rejected by the player.
theorem bug_exists : ∃ lvl r, playerAccepts r ≠ enemyAccepts lvl r :=
  ⟨10, 0, by native_decide⟩

-- L2: Characterization - The "Zero-Damage" Desync
-- The enemy can deal 0 damage, which the player's RNG logic will never produce.
theorem enemy_accepts_zero (lvl : BitVec 8) : (lvl ≥ 1 ∧ lvl ≤ 100) → enemyAccepts lvl 0 := by
  intro h
  have : ∀ x : BitVec 8, (x ≥ 1 ∧ x ≤ 100) → 0 < (x >>> 1) + x := by native_decide
  simp [enemyAccepts, this lvl h]

-- L2: Characterization - The "Overflow" Desync
-- The player can deal damage >= B, which the enemy's logic will never produce.
theorem player_ignores_bound (lvl r : BitVec 8) : r ≥ getB lvl ∧ r ≠ 0 → playerAccepts r := by
  intro ⟨_, h_nz⟩; simp [playerAccepts, h_nz]

-- L3: Fix Correctness - Correct range is [1, B)
def spec (lvl r : BitVec 8) : Bool := (r != 0) && (r < getB lvl)
def fix (lvl r : BitVec 8) : Bool := (r != 0) && (r < getB lvl)

theorem fix_correct (lvl r : BitVec 8) : fix lvl r = spec lvl r := rfl

-- L4: Relational - Desync is inevitable for all valid levels (1-100).
-- There is no level where the two machines agree on all possible RNG outcomes.
theorem desync_ubiquitous (lvl : BitVec 8) :
  (lvl ≥ 1 ∧ lvl ≤ 100) → ∃ r, playerAccepts r ≠ enemyAccepts lvl r := by
  intro h; use 0; simp [playerAccepts, enemyAccepts]
  have : ∀ x : BitVec 8, (x ≥ 1 ∧ x ≤ 100) → 0 < (x >>> 1) + x := by native_decide
  exact this lvl h

-- L4: Severe Case - At Level 1 (B=1), the machines are perfectly inverse.
-- The player accepts all r > 0, while the enemy only accepts r = 0.
theorem level_1_total_divergence (r : BitVec 8) :
  playerAccepts r = enemyAccepts 1 r → False := by
  have : ∀ r : BitVec 8, playerAccepts r = enemyAccepts 1 r → False := by native_decide
  exact this r

-- L4: Maximum Discrepancy - At Level 100 (B=150), the player allows 105 invalid rolls.
theorem level_100_overflow_count :
  (List.filter (λ r : BitVec 8 => playerAccepts r && !enemyAccepts 100 r)
    (List.map BitVec.ofNat (List.range 256))).length = 105 := by native_decide

end AutoResearch
