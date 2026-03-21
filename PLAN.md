# pokered-verify: Formal Verification of Pokémon Red Bugs in Lean 4

## Vision

Use Lean 4 to formally verify known bugs in the `pret/pokered` disassembly, driven by an LLM agent (Claude Code) that translates assembly routines into Lean and produces machine-checked proofs — with Lean's type checker as the trusted oracle.

The key insight: Lean's structured error feedback (goal states, type mismatches, tactic failures) gives the agent rich, compositional information for iterative proof repair — fundamentally better than pass/fail test output.

---

## Phase 1: SM83 CPU Model (START HERE)

**Goal:** Formalize a subset of the Game Boy's Sharp SM83 CPU in Lean 4 — enough to express the pokered bug routines.

### 1.1 Project Setup

- [ ] Initialize Lean 4 project with `lake init pokered-verify`
- [ ] Set up directory structure:
  ```
  pokered-verify/
  ├── SM83/
  │   ├── Basic.lean        -- BitVec helpers, UInt8/UInt16 ops
  │   ├── State.lean        -- CPUState structure
  │   ├── Flags.lean        -- Flag register (Z, N, H, C) semantics
  │   ├── Load.lean         -- LD opcodes
  │   ├── Arithmetic.lean   -- ADD, SUB, INC, DEC, CP
  │   ├── Logic.lean        -- AND, OR, XOR, CPL, bit shifts
  │   ├── Control.lean      -- JP, JR, CALL, RET, conditions
  │   └── Memory.lean       -- Memory model (read/write, basic bank awareness)
  ├── PokeredBugs/
  │   ├── Specs/            -- Intended behavior definitions
  │   ├── Translations/     -- Faithful asm-to-Lean translations
  │   └── Proofs/           -- Bug theorems and fix verifications
  ├── Harness/
  │   └── BugClaim.lean     -- Structured type for bug claims
  └── lakefile.lean
  ```
- [ ] Clone `pret/pokered` as reference (read-only, for source .asm files)

### 1.2 Core State Definition

Define the CPU state. Start minimal — expand as bugs require more registers/memory.

```lean
structure CPUState where
  a : BitVec 8
  f : BitVec 8        -- Flags: bit 7=Z, 6=N, 5=H, 4=C
  b : BitVec 8
  c : BitVec 8
  d : BitVec 8
  e : BitVec 8
  h : BitVec 8
  l : BitVec 8
  sp : BitVec 16
  pc : BitVec 16
  mem : BitVec 16 → BitVec 8
  halted : Bool
  deriving Repr
```

Provide accessors for register pairs:

```lean
def CPUState.bc (s : CPUState) : BitVec 16 := s.b ++ s.c
def CPUState.de (s : CPUState) : BitVec 16 := s.d ++ s.e
def CPUState.hl (s : CPUState) : BitVec 16 := s.h ++ s.l
```

Flag helpers:

```lean
def CPUState.zFlag (s : CPUState) : Bool := s.f.getMsb 0   -- bit 7
def CPUState.nFlag (s : CPUState) : Bool := s.f.getMsb 1   -- bit 6
def CPUState.hFlag (s : CPUState) : Bool := s.f.getMsb 2   -- bit 5
def CPUState.cFlag (s : CPUState) : Bool := s.f.getMsb 3   -- bit 4
```

### 1.3 Priority Opcodes

Not the full ~500 opcode ISA. Just the opcodes used by our target bug routines. Based on analysis of pokered's battle engine, these are the critical ones:

**Tier 1 — needed for almost every bug:**
- `ld` variants: `ld r,r`, `ld r,n`, `ld r,[hl]`, `ld [hl],r`, `ld a,[nn]`, `ld [nn],a`
- `inc` / `dec` (8-bit and 16-bit)
- `add a,r` / `sub r` / `cp r` / `cp n`
- `and` / `or` / `xor`
- `jr nz/z/nc/c, offset`
- `jp nn` / `call nn` / `ret` / `ret nz/z`
- `push` / `pop`

**Tier 2 — needed for specific bugs:**
- `srl` / `sla` / `sra` (bit shifts — Focus Energy bug)
- `swap` (nibble swap)
- `bit n,r` / `set n,r` / `res n,r`
- `rlca` / `rrca`

**Tier 3 — nice to have:**
- `halt`, `di`, `ei`
- `daa` (decimal adjust — BCD arithmetic)
- `scf` / `ccf` (carry flag manipulation)

### 1.4 Validation

For each opcode, write `#eval` tests against known behavior:

```lean
-- ADD A, 0xFF when A = 0x01 should give A = 0x00, Z=1, H=1, C=1
#eval
  let s := defaultState |>.setA 0x01
  let s' := execAddA s 0xFF
  (s'.a, s'.zFlag, s'.hFlag, s'.cFlag)
  -- expected: (0x00, true, true, true)
```

Cross-reference against:
- Game Boy opcode tables (flag effects per instruction)
- Gekkio's "Game Boy: Complete Technical Reference"
- Running the same operation in a known-good emulator (BGB, SameBoy)

### 1.5 Milestone

**Done when:** We can write a Lean function that faithfully models a short (~10 instruction) pokered routine and `#eval` it to get the same result as running it on an emulator.

---

## Phase 2: First Bug Proof (Focus Energy)

**Goal:** Formally verify the Focus Energy critical hit bug — the simplest known pokered bug.

### Why this bug first

- The root cause is a single wrong opcode (`srl` vs `sla`)
- No memory access beyond registers
- No loops or branching
- The spec is trivial: "multiply crit rate by 4"
- The proof is essentially `srl ≠ sla`

### 2.1 Translate the Assembly

From `engine/battle/core.asm`:
```asm
; Focus Energy should quadruple the critical hit rate
; BUG: srl divides by 2 instead of sla multiplying by 2
    srl b    ; bug: shift right (÷2) instead of left (×2)
```

Into Lean:
```lean
def focusEnergyActual (critRate : BitVec 8) : BitVec 8 :=
  critRate >>> 1    -- srl b: shift right, what the code does

def focusEnergySpec (critRate : BitVec 8) : BitVec 8 :=
  critRate <<< 2    -- sla b twice: shift left, what was intended
```

### 2.2 Prove the Bug Exists

```lean
theorem focus_energy_bug :
    ∃ rate : BitVec 8, focusEnergyActual rate ≠ focusEnergySpec rate := by
  exact ⟨4, by native_decide⟩
```

### 2.3 Prove Complete Characterization

```lean
-- For all nonzero rates, actual ≠ spec
theorem focus_energy_always_wrong (rate : BitVec 8) (h : rate ≠ 0) :
    focusEnergyActual rate ≠ focusEnergySpec rate := by
  ...
```

### 2.4 Prove the Fix Correct

```lean
def focusEnergyFixed (critRate : BitVec 8) : BitVec 8 :=
  critRate <<< 2

theorem focus_energy_fix_correct (rate : BitVec 8) :
    focusEnergyFixed rate = focusEnergySpec rate := by
  rfl
```

### 2.5 Milestone

**Done when:** All three theorems (bug exists, characterization, fix correct) typecheck in Lean.

---

## Phase 3: BugClaim Harness

**Goal:** Define a structured type that the LLM agent must fill in for each bug.

### 3.1 The BugClaim Structure

```lean
structure BugClaim where
  name : String
  description : String
  -- The asm routine as a Lean function
  implementation : InputType → OutputType
  -- What it should do
  spec : InputType → OutputType
  -- Existential: at least one input triggers the bug
  witness : InputType
  witnessProof : spec witness ≠ implementation witness
  -- Universal characterization (optional): exactly when the bug triggers
  characterization : Option (∀ x, spec x ≠ implementation x ↔ triggerCondition x)
  -- Fix verification (optional): proposed fix matches spec for all inputs
  fixVerification : Option (∀ x, fixed x = spec x)
```

This gives the agent a clear contract: fill in these fields, and Lean checks the rest.

### 3.2 Difficulty Levels

Each bug gets tagged with what we're proving:

| Level | What the agent produces | Lean checks |
|-------|------------------------|-------------|
| L1    | Concrete witness | `spec w ≠ impl w` (decidable, trivial) |
| L2    | Complete characterization | `∀ x, bug triggers ↔ condition` |
| L3    | Fix correctness | `∀ x, fixed x = spec x` |
| L4    | Relational (desync) | `∀ s, host s = guest s` |

---

## Phase 4: More Bugs

**Goal:** Work through 8–10 pokered bugs spanning different categories.

### Target Bugs (in order of difficulty)

1. **Focus Energy** (L1–L3) — wrong shift direction
   - Source: `engine/battle/core.asm`
   - Category: wrong bitwise op

2. **1/256 accuracy miss** (L1–L3) — `<` vs `≤` on 8-bit comparison
   - Source: `engine/battle/core.asm`
   - Category: off-by-one / boundary

3. **1/256 crit miss** (L1–L3) — same pattern as accuracy
   - Source: `engine/battle/core.asm`
   - Category: off-by-one / boundary

4. **Substitute 0 HP** (L2–L3) — HP/4 subtraction can leave 0
   - Source: `engine/battle/core.asm`
   - Category: arithmetic underflow

5. **Heal overflow at 255/511** (L2–L3) — scaling loses information
   - Source: `engine/battle/core.asm`
   - Category: integer division truncation

6. **CooltrainerF AI always switches** (L2–L3) — missing branch
   - Source: `engine/battle/trainer_ai.asm`
   - Category: dead code / missing early return

7. **Blaine AI Super Potion** (L2–L3) — missing HP check
   - Source: `engine/battle/trainer_ai.asm`
   - Category: missing precondition

8. **Psywave link desync** (L4) — different damage range host vs guest
   - Source: `engine/battle/core.asm`
   - Category: relational / symmetry violation

9. **Counter damage persists across turns** (L4) — state not cleared
   - Source: `engine/battle/core.asm`
   - Category: stale state

10. **Reflect/Light Screen overflow** (L2–L3) — stat boost uncapped
    - Source: `engine/battle/core.asm`
    - Category: arithmetic overflow

---

## Phase 5: Agent Loop (Claude Code Integration)

**Goal:** Automate the translation and proof process with Claude Code as the agent, Lean as the verifier.

### 5.1 Agent Prompt Template

For each bug, the agent receives:
- The `.asm` source (exact lines from pokered)
- The informal bug description (from wiki/Smogon)
- The `BugClaim` structure to fill in
- The SM83 CPU model (imported)

### 5.2 Feedback Loop

```
Claude Code reads .asm + bug description
    ↓
Generates .lean file filling in BugClaim
    ↓
Runs `lake build` → Lean type checker
    ↓
If error:
  - Parse Lean's error output (goal state, type mismatch, tactic failure)
  - Feed structured error back to agent
  - Agent revises the specific failing component
  - Retry (max N iterations)
    ↓
If success:
  - Record: bug name, iterations needed, proof size, difficulty level
  - Move to next bug
```

### 5.3 Metrics to Collect

For the paper:
- Success rate: how many bugs verified out of N attempted
- Iterations: how many Lean feedback loops per bug
- Failure modes: where does the agent get stuck?
- Difficulty correlation: do L1 bugs take fewer iterations than L3?
- Translation fidelity: did the agent correctly model the asm?
- Ablation: same pipeline with Python pass/fail vs Lean structured feedback

---

## Phase 6: Paper

### Target Venues

- **Primary:** ITP, CPP, or AITP workshop paper (6–8 pages)
- **Stretch:** ICLR/NeurIPS workshop on LLMs + formal reasoning
- **Alternative:** ASE/ICSE tool paper (software engineering angle)

### Key Claims

1. First Lean 4 formalization of the SM83 instruction set (reusable artifact)
2. First formal verification of bugs in a shipped commercial game
3. LLM agent + proof assistant feedback loop successfully verifies N/M known bugs
4. Lean's compositional error feedback enables iterative proof repair that flat test feedback cannot
5. Universal fix verification catches issues that testing alone misses

### Paper Outline

1. Introduction (the pitch: formal methods meet software archaeology)
2. Background (SM83, pokered disassembly, Lean 4)
3. SM83 Formalization (the CPU model, validation approach)
4. Bug Taxonomy and Formalization (the BugClaim framework, examples)
5. Agent-Verifier Loop (architecture, prompt design, feedback parsing)
6. Evaluation (success rates, iteration counts, ablation study)
7. Discussion (what worked, what didn't, threats to validity)
8. Related Work (formal verification, LLM theorem proving, retro computing)

---

## Immediate Next Steps

**This week:**
1. `lake init pokered-verify`
2. Define `CPUState` in `SM83/State.lean`
3. Implement flag helpers in `SM83/Flags.lean`
4. Implement Tier 1 arithmetic opcodes: `add a,r`, `sub r`, `cp r`, `inc r`, `dec r`
5. Write `#eval` validation tests for each opcode against known flag behavior
6. Implement bit shift opcodes (`srl`, `sla`) — needed for Focus Energy
7. Prove Focus Energy bug (Phase 2) as the first end-to-end validation

**The Focus Energy proof is the "hello world" — if that works end to end, the architecture is sound.**
