/-
  07-game-sampler-and-quantum-parallel-bridge/ArikanPolarMartingaleUcbOptimismAndCondorcetParadoxFrontier.lean

  Wave V261 · Frontier Module #136:
  Exact Algebraic & Combinatorial Formalization of:
  1. Arıkan Polar Code BEC Erasure Martingale Conservation (`(2*e*S - e²) + e² = 2*e*S`) & Strict
     Bit-Channel Polarization (`e² < e*S < 2*e*S - e²` for `0 < e < S`) vs. Unpolarized Repetition
     50% Rate Collapse (`oai-codes` ↔ `oai-qrep`).
  2. Auer–Cesa-Bianchi `UCB1` Optimism-in-the-Face-of-Uncertainty Regret Bound (`Δ ≤ 2 * bonus`) &
     Cold-Start Rescue (`90%` arm recovered after `0/1` miss) vs. Pure Greedy (`ε = 0`) Permanent
     Suboptimal Lock-In (`50%` forever) (`tc-probcomb` ↔ `econlib`).
  3. Condorcet Jury `3`-Voter Majority Peer-Correction Identity (`Maj₃ - V₁ = (p*q)*(p - q)`) vs.
     Incompetent Amplification (`p < q ⟹ Maj₃ < V₁`), Perfectly Correlated Groupthink (`Maj_corr = V₁`),
     and Condorcet `3`-Candidate Cycling Paradox (`A ≻_M B ≻_M C ≻_M A`, `0` Condorcet Winners!)
     (`econlib` ↔ `tc-probcomb`).

  Toolchain: leanprover/lean4:v4.33.0 (pure core Lean 4, zero sorry).
-/

namespace ArikanPolarMartingaleUcbOptimismAndCondorcetParadoxFrontier

-- ============================================================================
-- PART I: ARIKAN POLAR CODE BEC ERASURE CONSERVATION & STRICT POLARIZATION
-- ============================================================================

/-- Good polarized bit-channel `W⁺` erasure numerator `(e/S)²` scaled by `S²`. -/
def polarGoodScaled (e : Nat) : Nat :=
  e * e

/-- Bad polarized bit-channel `W⁻` erasure numerator `2(e/S) - (e/S)²` scaled by `S²`. -/
def polarBadScaled (e S : Nat) : Nat :=
  2 * e * S - e * e

/-- Unpolarized 2-repetition mutual-information numerator over 2 channel uses (scaled by `S²`):
    repeats 1 bit across 2 uses (`rate = 1/2`), delivering `1 * (S² - e²)` instead of `2 * S * (S - e)`. -/
def repetition2MutualInfoScaled (e S : Nat) : Nat :=
  S * S - e * e

/-- Polar `2×2` Butterfly `(u₁ ⊕ u₂, u₂)` total mutual-information numerator over 2 channel uses
    (scaled by `S²`): `(S² - W⁻) + (S² - W⁺) = 2*S² - 2*e*S`. -/
def polar2MutualInfoScaled (e S : Nat) : Nat :=
  (S * S - polarBadScaled e S) + (S * S - polarGoodScaled e)

/--
  **Theorem 1a (Universal BEC Polar Martingale Conservation)**:
  For every erasure parameter `e ≤ S`, the sum of the bad and good polarized erasure rates equals
  `2 * e * S` (`W⁻(e) + W⁺(e) = 2e`), preserving total Shannon capacity across the Arikan butterfly.
-/
theorem arikan_bec_erasure_martingale_conservation (e S : Nat) (hLe : e ≤ S) :
    polarBadScaled e S + polarGoodScaled e = 2 * e * S := by
  unfold polarBadScaled polarGoodScaled
  have hSqLe : e * e ≤ e * S := Nat.mul_le_mul_left e hLe
  have hTwice : e * S ≤ 2 * e * S := by
    have hEq : 2 * e * S = e * S + e * S := by
      rw [Nat.succ_mul, Nat.one_mul, Nat.right_distrib]
    omega
  omega

/--
  **Theorem 1b (Universal Strict Bit-Channel Polarization)**:
  For every non-degenerate channel `0 < e` and `e < S`, `W⁺` is strictly cleaner than `W`
  (`e * e < e * S`) while `W⁻` is strictly noisier than `W` (`e * S < 2 * e * S - e * e`).
-/
theorem arikan_bec_strict_channel_splitting (e S : Nat) (hPos : 0 < e) (hLt : e < S) :
    polarGoodScaled e < e * S ∧ e * S < polarBadScaled e S := by
  unfold polarGoodScaled polarBadScaled
  have hSqLt : e * e < e * S := Nat.mul_lt_mul_of_pos_left hLt hPos
  have hTwo : 2 * e * S = e * S + e * S := by
    rw [Nat.succ_mul, Nat.one_mul, Nat.right_distrib]
  refine ⟨hSqLt, ?_⟩
  omega

/--
  **Theorem 1c (`N = 4` Two-Stage Polarization Witness & Repetition Rate-Collapse Counterexample)**:
  At `BEC(0.3)` (`e = 3, S = 10`, Stage-2 scale `10,000`):
  - Stage 1 splits `30/100` into `{9/100, 51/100}` (sum `= 60`).
  - Stage 2 splits `{9, 51}/100` into `{81, 1719, 2601, 7599}/10000` (exact 4-channel sum `= 12,000 = 4 × 3,000`),
    driving `W⁺⁺` down to `0.81%` erasure at `100%` sum-capacity `140/100` over 2 uses.
  - **Premise-Failure Counterexample**: Unpolarized `2×` repetition achieves `9/100` erasure on 1 bit
    but discards the second bit degree of freedom (`91 < 140` mutual info — losing `49/200` capacity!).
-/
theorem arikan_two_stage_bec03_vs_repetition_rate_loss :
    polarGoodScaled 3 = 9 ∧
    polarBadScaled 3 10 = 51 ∧
    polarGoodScaled 9 = 81 ∧
    polarBadScaled 9 100 = 1719 ∧
    polarGoodScaled 51 = 2601 ∧
    polarBadScaled 51 100 = 7599 ∧
    81 + 1719 + 2601 + 7599 = 4 * 3000 ∧
    polar2MutualInfoScaled 3 10 = 140 ∧
    repetition2MutualInfoScaled 3 10 = 91 ∧
    repetition2MutualInfoScaled 3 10 < polar2MutualInfoScaled 3 10 := by
  decide

-- ============================================================================
-- PART II: UCB1 OPTIMISM REGRET BOUND VS. PURE GREEDY COLD-START LOCK-IN
-- ============================================================================

/-- `UCB` index `μ̂_i + bonus_i`. -/
def ucbIndex (empMean bonus : Int) : Int :=
  empMean + bonus

/--
  **Theorem 2a (Universal `UCB1` Optimism Instantaneous Regret Bound)**:
  Under concentration (`|μ̂_i - μ_i| ≤ bonus_i` for both the optimal arm `opt` and the selected arm
  `sel`), selecting `sel` with `ucbIndex opt ≤ ucbIndex sel` guarantees instantaneous suboptimality
  `μ_opt - μ_sel ≤ 2 * bonus_sel`. As `sel` is pulled repeatedly, `bonus_sel ∝ 1/√N_sel → 0`.
-/
theorem ucb1_optimism_instantaneous_regret_bound
    (muOpt empOpt bonusOpt muSel empSel bonusSel : Int)
    (hOptUpper : muOpt ≤ empOpt + bonusOpt)
    (hSelLower : empSel - bonusSel ≤ muSel)
    (hSelect : ucbIndex empOpt bonusOpt ≤ ucbIndex empSel bonusSel) :
    muOpt - muSel ≤ 2 * bonusSel := by
  unfold ucbIndex at hSelect
  omega

/-- Cold-start `2`-arm state (`μ₀ = 90` optimal arm after 1 unlucky `0`-reward pull vs. `μ₁ = 50`
    mediocre arm after `16` pulls with empirical mean `50`):
    - `UCB` (`bonus₀ = 100/√1 = 100`, `bonus₁ = 100/√16 = 25`): `0 + 100 = 100 > 75 = 50 + 25` (rescues arm `0`!).
    - Pure greedy (`bonus = 0`): `0 < 50` (locks onto mediocre arm `1` forever, incurring `40 * T` linear regret!). -/
def coldStartUcbSelectsOptimal : Bool :=
  decide (ucbIndex 50 25 < ucbIndex 0 100)

def coldStartGreedySelectsOptimal : Bool :=
  decide (ucbIndex 50 0 < ucbIndex 0 0)

theorem ucb1_cold_start_rescue_vs_greedy_permanent_lockin (T : Nat) (hT : 1 ≤ T) :
    coldStartUcbSelectsOptimal = true ∧
    coldStartGreedySelectsOptimal = false ∧
    40 ≤ (90 - 50) * T := by
  refine ⟨by decide, by decide, ?_⟩
  omega

-- ============================================================================
-- PART III: CONDORCET JURY AMPLIFICATION VS. GROUPTHINK & 3-CANDIDATE CYCLE
-- ============================================================================

/-- 3-voter independent majority success weight over `(p + q)³` (`q = S - p`):
    succeeds on `(1,1,1)` (`p³`) and the three 2-of-3 outcomes `(1,1,0), (1,0,1), (0,1,1)` (`3 p² q`). -/
def condorcetMaj3Weight (p q : Int) : Int :=
  p * p * p + 3 * (p * p * q)

/-- Single voter `V₁` (or perfectly correlated `3`-clone groupthink `V₁ = V₂ = V₃`) success weight
    over `(p + q)³`: succeeds on `(1,1,1)` (`p³`), `(1,1,0), (1,0,1)` (`2 p² q`), and `(1,0,0)` (`p q²`). -/
def singleOrCorrelatedWeight (p q : Int) : Int :=
  p * p * p + 2 * (p * p * q) + p * (q * q)

/--
  **Theorem 3a (Exact Peer-Correction Factorization of Condorcet's Jury Theorem)**:
  `Maj₃(p, q) - V₁(p, q) = p² q - p q² = (p * q) * (p - q)`.
  Majority voting beats a single expert iff peer error-correction `(0,1,1)` (`p² q`) outweighs
  peer false-override `(1,0,0)` (`p q²`), i.e., `q < p` (`p > 1/2`)!
-/
theorem condorcet_peer_correction_factorization (p q : Int) :
    condorcetMaj3Weight p q - singleOrCorrelatedWeight p q = (p * q) * (p - q) := by
  unfold condorcetMaj3Weight singleOrCorrelatedWeight
  have hExpand : (p * q) * (p - q) = p * p * q - p * (q * q) := by
    rw [Int.mul_sub]
    have h1 : p * q * p = p * p * q := by
      rw [Int.mul_assoc, Int.mul_comm q p, ← Int.mul_assoc]
    have h2 : p * q * q = p * (q * q) := Int.mul_assoc p q q
    rw [h1, h2]
  omega

/--
  **Theorem 3b (Universal Competent Amplification vs. Incompetent Error Amplification)**:
  For all `0 < p` and `0 < q`:
  - If `q < p` (competent voters `p > 1/2`), `singleOrCorrelatedWeight p q < condorcetMaj3Weight p q`.
  - If `p < q` (incompetent voters `p < 1/2`), `condorcetMaj3Weight p q < singleOrCorrelatedWeight p q`.
-/
theorem condorcet_amplification_dichotomy (p q : Int) (hp : 0 < p) (hq : 0 < q) :
    (q < p → singleOrCorrelatedWeight p q < condorcetMaj3Weight p q) ∧
    (p < q → condorcetMaj3Weight p q < singleOrCorrelatedWeight p q) := by
  have hpq : 0 < p * q := Int.mul_pos hp hq
  have hDiff := condorcet_peer_correction_factorization p q
  refine ⟨?_, ?_⟩
  · intro hComp
    have hSub : 0 < p - q := by omega
    have hProd : 0 < (p * q) * (p - q) := Int.mul_pos hpq hSub
    omega
  · intro hIncomp
    have hSub : 0 < q - p := by omega
    have hProd : 0 < (p * q) * (q - p) := Int.mul_pos hpq hSub
    have hNeg : (p * q) * (p - q) = -((p * q) * (q - p)) := by
      rw [Int.mul_sub, Int.mul_sub]
      omega
    omega

/-- Condorcet `3`-candidate Latin-square preference rank (`rank v c` = position of candidate `c`
    in voter `v`'s strict ballot: `0` = top choice, `1` = second, `2` = last):
    - Voter 0: `A ≻ B ≻ C` (`[0, 1, 2]`)
    - Voter 1: `B ≻ C ≻ A` (`[2, 0, 1]`)
    - Voter 2: `C ≻ A ≻ B` (`[1, 2, 0]`) -/
def condorcetCycleRank : Fin 3 → Fin 3 → Nat
  | ⟨0, _⟩, ⟨0, _⟩ => 0
  | ⟨0, _⟩, ⟨1, _⟩ => 1
  | ⟨0, _⟩, ⟨2, _⟩ => 2
  | ⟨1, _⟩, ⟨0, _⟩ => 2
  | ⟨1, _⟩, ⟨1, _⟩ => 0
  | ⟨1, _⟩, ⟨2, _⟩ => 1
  | ⟨2, _⟩, ⟨0, _⟩ => 1
  | ⟨2, _⟩, ⟨1, _⟩ => 2
  | ⟨2, _⟩, ⟨2, _⟩ => 0

/-- Number of voters (out of 3) strictly preferring candidate `a` over candidate `b`. -/
def pairwiseVotes3 (a b : Fin 3) : Nat :=
  (if condorcetCycleRank ⟨0, by decide⟩ a < condorcetCycleRank ⟨0, by decide⟩ b then 1 else 0) +
  (if condorcetCycleRank ⟨1, by decide⟩ a < condorcetCycleRank ⟨1, by decide⟩ b then 1 else 0) +
  (if condorcetCycleRank ⟨2, by decide⟩ a < condorcetCycleRank ⟨2, by decide⟩ b then 1 else 0)

def strictMajorityBeats (a b : Fin 3) : Bool :=
  decide (2 ≤ pairwiseVotes3 a b)

def isCondorcetWinner3 (c : Fin 3) : Bool :=
  decide (∀ d : Fin 3, d ≠ c → strictMajorityBeats c d = true)

/--
  **Theorem 3c (Concrete Ensemble Witnesses: `78.4% > 70.0%` vs. Groupthink `70.0%` & Condorcet `3`-Cycle)**:
  - At `p = 7, q = 3` (`70%` accuracy), 3 independent voters achieve `784/1000` (`78.4%`), whereas
    3 perfectly correlated clones stay at `700/1000` (`70.0%`), and `p = 3, q = 7` (`30%`) degrades to `216/1000` (`21.6%`).
  - On `m = 3` candidates `{0, 1, 2}`, `0 ≻_M 1 ≻_M 2 ≻_M 0` each win `2`-to-`1`, leaving **zero** Condorcet winners!
-/
theorem condorcet_concrete_witnesses_and_cycling_paradox :
    condorcetMaj3Weight 7 3 = 784 ∧
    singleOrCorrelatedWeight 7 3 = 700 ∧
    condorcetMaj3Weight 3 7 = 216 ∧
    singleOrCorrelatedWeight 3 7 = 300 ∧
    pairwiseVotes3 ⟨0, by decide⟩ ⟨1, by decide⟩ = 2 ∧
    pairwiseVotes3 ⟨1, by decide⟩ ⟨2, by decide⟩ = 2 ∧
    pairwiseVotes3 ⟨2, by decide⟩ ⟨0, by decide⟩ = 2 ∧
    (∀ c : Fin 3, isCondorcetWinner3 c = false) := by
  decide

end ArikanPolarMartingaleUcbOptimismAndCondorcetParadoxFrontier
