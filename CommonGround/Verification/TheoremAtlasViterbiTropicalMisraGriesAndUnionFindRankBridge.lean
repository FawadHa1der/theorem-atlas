/-
  CommonGround/Verification/TheoremAtlasViterbiTropicalMisraGriesAndUnionFindRankBridge.lean

  Wave V260 · Suite #661:
  Cross-Domain Kernel Bridge Unifying:
  - Viterbi Tropical `(min, +)` Right-Distributivity (`min(a+c, b+c) = min(a,b) + c`) & Exact MAP
    Optimum (`4`) vs. Myopic Beam-`1` Greedy Garden-Path Trap (`11 = 2.75×` Cost!) (`cslib` ↔ `oai-codes`)
  - Boyer–Moore / Misra–Gries `(k + 1)`-Tuple Cancellation Zero-False-Negative Heavy-Hitter Bound
    (`(k+1)*freq > N ⟹ 1 ≤ cnt`) vs. Unverified `[1,2,1,2,9]` `20%` Survivor Hallucination (`tc-probcomb` ↔ `cslib`)
  - Tarjan Union-by-Rank Exponential Subtree Lower Bound (`2^rank ≤ size ⟹ rank ≤ ⌊log₂ N⌋`, Depth `≤ 3`)
    vs. Unranked Sequential Union `O(N)` Chain Degeneration (Depth `= 7`) (`cslib` ↔ `apsp3sum`)

  Toolchain: leanprover/lean4:v4.33.0 (zero sorry).
-/

namespace CommonGround.Verification.TheoremAtlasViterbiTropicalMisraGriesAndUnionFindRankBridge

def trellisStep1Cost : Bool → Nat
  | false => 1
  | true  => 3

def trellisStep2Cost : Bool → Bool → Nat
  | false, false => 10
  | false, true  => 10
  | true,  false => 1
  | true,  true  => 5

def totalTrellisNll (s₁ s₂ : Bool) : Nat :=
  trellisStep1Cost s₁ + trellisStep2Cost s₁ s₂

def boyerMooreStep (st : Nat × Nat) (x : Nat) : Nat × Nat :=
  if st.2 == 0 then (x, 1)
  else if st.1 == x then (st.1, st.2 + 1)
  else (st.1, st.2 - 1)

def boyerMoorePass1 (xs : List Nat) : Nat × Nat :=
  xs.foldl boyerMooreStep (0, 0)

def streamFreq (xs : List Nat) (x : Nat) : Nat :=
  xs.foldl (fun acc y => acc + if y == x then 1 else 0) 0

def mergedUnionRank (rkA rkB : Nat) : Nat :=
  if rkA < rkB then rkB
  else if rkB < rkA then rkA
  else rkA + 1

def findDepth8 : Nat → (Fin 8 → Fin 8) → Fin 8 → Nat
  | 0, _, _ => 0
  | fuel + 1, parent, x =>
    if parent x == x then 0 else 1 + findDepth8 fuel parent (parent x)

def naiveChainParent8 (x : Fin 8) : Fin 8 :=
  if h : x.val < 7 then ⟨x.val + 1, by omega⟩ else x

def rankedTreeParent8 : Fin 8 → Fin 8
  | ⟨0, _⟩ => ⟨1, by omega⟩
  | ⟨1, _⟩ => ⟨3, by omega⟩
  | ⟨2, _⟩ => ⟨3, by omega⟩
  | ⟨3, _⟩ => ⟨7, by omega⟩
  | ⟨4, _⟩ => ⟨5, by omega⟩
  | ⟨5, _⟩ => ⟨7, by omega⟩
  | ⟨6, _⟩ => ⟨7, by omega⟩
  | ⟨7, _⟩ => ⟨7, by omega⟩

/--
  **Bridge 1 (`cslib` ↔ `oai-codes`)**:
  Universal tropical `(min, +)` right-distributivity paired with exact Viterbi MAP sequence optimum
  (`4`) vs. myopic token-greedy Beam-`1` garden-path trap (`11`).
-/
theorem viterbi_tropical_distrib_vs_myopic_greedy_trap_bridge (a b c : Int) :
    min (a + c) (b + c) = min a b + c ∧
    totalTrellisNll true false = 4 ∧
    (∀ s₁ s₂ : Bool, 4 ≤ totalTrellisNll s₁ s₂) ∧
    (trellisStep1Cost false < trellisStep1Cost true ∧
     ∀ s₂ : Bool, totalTrellisNll false s₂ = 11) := by
  refine ⟨by omega, by decide, by decide, ⟨by decide, by decide⟩⟩

/--
  **Bridge 2 (`tc-probcomb` ↔ `cslib`)**:
  Universal Misra–Gries `(k + 1)`-tuple cancellation zero-false-negative guarantee (`1 ≤ cntX`)
  paired with Boyer–Moore majority recovery (`[2,1,2,3,2] ↦ 2`) vs. unverified `20%` tail survivor
  hallucination (`[1,2,1,2,9] ↦ 9`).
-/
theorem misra_gries_heavy_hitter_vs_unverified_survivor_bridge
    (k N D R freqX cntX : Nat)
    (hPart : N = (k + 1) * D + R) (hDec : freqX ≤ cntX + D) (hHeavy : N < (k + 1) * freqX) :
    1 ≤ cntX ∧
    boyerMoorePass1 [2, 1, 2, 3, 2] = (2, 1) ∧
    boyerMoorePass1 [1, 2, 1, 2, 9] = (9, 1) ∧
    2 * streamFreq [1, 2, 1, 2, 9] 9 < 5 := by
  refine ⟨?_, by decide, by decide, by decide⟩
  have hMul : (k + 1) * freqX ≤ (k + 1) * (cntX + D) := Nat.mul_le_mul_left (k + 1) hDec
  rw [Nat.mul_add] at hMul
  by_cases hZero : cntX = 0
  · subst hZero; omega
  · omega

/--
  **Bridge 3 (`cslib` ↔ `apsp3sum`)**:
  Universal Tarjan union-by-rank exponential subtree bound (`2^rank ≤ size`) paired with logarithmic
  `≤ 3` depth on `N = 8` vs. naive unranked chain depth `= 7`.
-/
theorem union_by_rank_exponential_size_vs_naive_chain_bridge
    (szA rkA szB rkB : Nat) (hA : 2 ^ rkA ≤ szA) (hB : 2 ^ rkB ≤ szB) :
    2 ^ (mergedUnionRank rkA rkB) ≤ szA + szB ∧
    (∀ x : Fin 8, findDepth8 8 rankedTreeParent8 x ≤ 3) ∧
    findDepth8 8 naiveChainParent8 ⟨0, by decide⟩ = 7 := by
  refine ⟨?_, by decide, by decide⟩
  unfold mergedUnionRank
  split
  · omega
  · split
    · omega
    · have hEq : rkA = rkB := by omega
      subst hEq
      rw [Nat.pow_succ]
      omega

/--
  **Master Triad Theorem (`Suite #661`)**:
  Simultaneously certifies Viterbi tropical `(min, +)` dynamic programming, Misra–Gries heavy-hitter
  zero-false-negative cancellation, and Tarjan union-by-rank `2^rank ≤ size` logarithmic height.
-/
theorem master_viterbi_tropical_misra_gries_and_union_find_rank_bridge
    (a b c : Int)
    (k N D R freqX cntX : Nat)
    (hPart : N = (k + 1) * D + R) (hDec : freqX ≤ cntX + D) (hHeavy : N < (k + 1) * freqX)
    (szA rkA szB rkB : Nat) (hA : 2 ^ rkA ≤ szA) (hB : 2 ^ rkB ≤ szB) :
    (min (a + c) (b + c) = min a b + c ∧ totalTrellisNll true false = 4) ∧
    (1 ≤ cntX ∧ boyerMoorePass1 [1, 2, 1, 2, 9] = (9, 1)) ∧
    (2 ^ (mergedUnionRank rkA rkB) ≤ szA + szB ∧ findDepth8 8 naiveChainParent8 ⟨0, by decide⟩ = 7) := by
  have h1 := viterbi_tropical_distrib_vs_myopic_greedy_trap_bridge a b c
  have h2 := misra_gries_heavy_hitter_vs_unverified_survivor_bridge k N D R freqX cntX hPart hDec hHeavy
  have h3 := union_by_rank_exponential_size_vs_naive_chain_bridge szA rkA szB rkB hA hB
  exact ⟨⟨h1.1, h1.2.1⟩, ⟨h2.1, h2.2.2.1⟩, ⟨h3.1, h3.2.2⟩⟩

end CommonGround.Verification.TheoremAtlasViterbiTropicalMisraGriesAndUnionFindRankBridge
