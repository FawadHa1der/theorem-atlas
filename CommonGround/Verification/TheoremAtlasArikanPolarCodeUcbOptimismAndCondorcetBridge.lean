/-
  CommonGround/Verification/TheoremAtlasArikanPolarCodeUcbOptimismAndCondorcetBridge.lean

  Wave V261 · Suite #662:
  Cross-Domain Kernel Bridge Unifying:
  - Arıkan Polar Code BEC Erasure Martingale Conservation (`(2*e*S - e²) + e² = 2*e*S`) & Strict
    Channel Splitting (`e² < e*S < 2*e*S - e²`) vs. Unpolarized Repetition `50%` Rate Collapse
    (`91 < 140` Mutual Info at `BEC(0.3)`) (`oai-codes` ↔ `oai-qrep`)
  - Auer–Cesa-Bianchi `UCB1` Optimism Instantaneous Regret Bound (`μ_opt - μ_sel ≤ 2 * bonus_sel`)
    & Cold-Start Rescue (`100 > 75`) vs. Pure Greedy (`ε = 0`) Permanent Lock-In (`0 < 50`)
    (`tc-probcomb` ↔ `econlib`)
  - Condorcet Jury `3`-Voter Peer-Correction Identity (`Maj₃ - V₁ = (p*q)*(p - q)`, `784 > 700`)
    vs. Correlated Groupthink (`700`) & Condorcet `3`-Candidate Cycling Paradox (`0` Winners!)
    (`econlib` ↔ `tc-probcomb`)

  Toolchain: leanprover/lean4:v4.33.0 (zero sorry).
-/

namespace CommonGround.Verification.TheoremAtlasArikanPolarCodeUcbOptimismAndCondorcetBridge

def polarGoodScaled (e : Nat) : Nat :=
  e * e

def polarBadScaled (e S : Nat) : Nat :=
  2 * e * S - e * e

def polar2MutualInfoScaled (e S : Nat) : Nat :=
  (S * S - polarBadScaled e S) + (S * S - polarGoodScaled e)

def repetition2MutualInfoScaled (e S : Nat) : Nat :=
  S * S - e * e

def ucbIndex (empMean bonus : Int) : Int :=
  empMean + bonus

def condorcetMaj3Weight (p q : Int) : Int :=
  p * p * p + 3 * (p * p * q)

def singleOrCorrelatedWeight (p q : Int) : Int :=
  p * p * p + 2 * (p * p * q) + p * (q * q)

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

def pairwiseVotes3 (a b : Fin 3) : Nat :=
  (if condorcetCycleRank ⟨0, by decide⟩ a < condorcetCycleRank ⟨0, by decide⟩ b then 1 else 0) +
  (if condorcetCycleRank ⟨1, by decide⟩ a < condorcetCycleRank ⟨1, by decide⟩ b then 1 else 0) +
  (if condorcetCycleRank ⟨2, by decide⟩ a < condorcetCycleRank ⟨2, by decide⟩ b then 1 else 0)

def isCondorcetWinner3 (c : Fin 3) : Bool :=
  decide (∀ d : Fin 3, d ≠ c → 2 ≤ pairwiseVotes3 c d)

/--
  **Bridge 1 (`oai-codes` ↔ `oai-qrep`)**:
  Arıkan BEC martingale conservation (`W⁻ + W⁺ = 2*e*S`) and strict two-way polarization
  (`W⁺ < e*S < W⁻`) vs. unpolarized `2×` repetition capacity loss (`91 < 140` at `BEC(0.3)`).
-/
theorem arikan_polar_bec_conservation_and_strict_splitting_bridge
    (e S : Nat) (hPos : 0 < e) (hLt : e < S) :
    polarBadScaled e S + polarGoodScaled e = 2 * e * S ∧
    polarGoodScaled e < e * S ∧
    e * S < polarBadScaled e S ∧
    repetition2MutualInfoScaled 3 10 < polar2MutualInfoScaled 3 10 := by
  unfold polarBadScaled polarGoodScaled
  have hSqLt : e * e < e * S := Nat.mul_lt_mul_of_pos_left hLt hPos
  have hTwo : 2 * e * S = e * S + e * S := by
    rw [Nat.succ_mul, Nat.one_mul, Nat.right_distrib]
  refine ⟨by omega, hSqLt, by omega, by decide⟩

/--
  **Bridge 2 (`tc-probcomb` ↔ `econlib`)**:
  Universal `UCB1` optimism instantaneous regret bound (`μ_opt - μ_sel ≤ 2 * bonus_sel`) paired
  with cold-start recovery of a `90%` arm after a single `0/1` miss (`100 > 75`) vs. pure greedy
  (`bonus = 0`) permanent lock-in (`0 < 50`).
-/
theorem ucb1_optimism_regret_vs_greedy_cold_start_lockin_bridge
    (muOpt empOpt bonusOpt muSel empSel bonusSel : Int)
    (hOptUpper : muOpt ≤ empOpt + bonusOpt)
    (hSelLower : empSel - bonusSel ≤ muSel)
    (hSelect : ucbIndex empOpt bonusOpt ≤ ucbIndex empSel bonusSel) :
    muOpt - muSel ≤ 2 * bonusSel ∧
    ucbIndex 50 25 < ucbIndex 0 100 ∧
    ucbIndex 0 0 < ucbIndex 50 0 := by
  unfold ucbIndex at hSelect ⊢
  refine ⟨by omega, by decide, by decide⟩

/--
  **Bridge 3 (`econlib` ↔ `tc-probcomb`)**:
  Exact Condorcet peer-correction factorization (`Maj₃ - V₁ = (p*q)*(p - q)`), `784 > 700`
  competent amplification vs. correlated groupthink (`700`), and Condorcet `3`-candidate cycling
  paradox (`0` Condorcet winners!).
-/
theorem condorcet_peer_correction_vs_groupthink_and_cycle_bridge (p q : Int) :
    condorcetMaj3Weight p q - singleOrCorrelatedWeight p q = (p * q) * (p - q) ∧
    singleOrCorrelatedWeight 7 3 < condorcetMaj3Weight 7 3 ∧
    condorcetMaj3Weight 3 7 < singleOrCorrelatedWeight 3 7 ∧
    (∀ c : Fin 3, isCondorcetWinner3 c = false) := by
  refine ⟨?_, by decide, by decide, by decide⟩
  unfold condorcetMaj3Weight singleOrCorrelatedWeight
  have hExpand : (p * q) * (p - q) = p * p * q - p * (q * q) := by
    rw [Int.mul_sub]
    have h1 : p * q * p = p * p * q := by
      rw [Int.mul_assoc, Int.mul_comm q p, ← Int.mul_assoc]
    have h2 : p * q * q = p * (q * q) := Int.mul_assoc p q q
    rw [h1, h2]
  omega

/--
  **Master Triad Theorem (`Suite #662`)**:
  Simultaneously certifies Arıkan BEC channel polarization, `UCB1` optimism regret dominance,
  and Condorcet peer-correction amplification vs. groupthink & `3`-candidate cycling.
-/
theorem master_arikan_polar_ucb1_optimism_and_condorcet_bridge
    (e S : Nat) (hPos : 0 < e) (hLt : e < S)
    (muOpt empOpt bonusOpt muSel empSel bonusSel : Int)
    (hOptUpper : muOpt ≤ empOpt + bonusOpt)
    (hSelLower : empSel - bonusSel ≤ muSel)
    (hSelect : ucbIndex empOpt bonusOpt ≤ ucbIndex empSel bonusSel)
    (p q : Int) :
    (polarBadScaled e S + polarGoodScaled e = 2 * e * S ∧ polarGoodScaled e < e * S) ∧
    (muOpt - muSel ≤ 2 * bonusSel ∧ ucbIndex 50 25 < ucbIndex 0 100) ∧
    (condorcetMaj3Weight p q - singleOrCorrelatedWeight p q = (p * q) * (p - q) ∧
     (∀ c : Fin 3, isCondorcetWinner3 c = false)) := by
  have h1 := arikan_polar_bec_conservation_and_strict_splitting_bridge e S hPos hLt
  have h2 := ucb1_optimism_regret_vs_greedy_cold_start_lockin_bridge
    muOpt empOpt bonusOpt muSel empSel bonusSel hOptUpper hSelLower hSelect
  have h3 := condorcet_peer_correction_vs_groupthink_and_cycle_bridge p q
  exact ⟨⟨h1.1, h1.2.1⟩, ⟨h2.1, h2.2.1⟩, ⟨h3.1, h3.2.2.2⟩⟩

end CommonGround.Verification.TheoremAtlasArikanPolarCodeUcbOptimismAndCondorcetBridge
