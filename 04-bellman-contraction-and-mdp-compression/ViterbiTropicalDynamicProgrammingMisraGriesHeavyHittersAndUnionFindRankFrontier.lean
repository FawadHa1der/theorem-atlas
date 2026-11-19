/-
  04-bellman-contraction-and-mdp-compression/ViterbiTropicalDynamicProgrammingMisraGriesHeavyHittersAndUnionFindRankFrontier.lean

  Wave V260 · Frontier #135:
  Viterbi Tropical Min-Plus Dynamic Programming Principle of Optimality vs. Myopic Greedy
  Garden-Path Trap, Boyer–Moore / Misra–Gries `(k + 1)`-Tuple Heavy-Hitter Cancellation
  Guarantee vs. Unverified Survivor False Positives, and Tarjan Union-by-Rank Exponential
  Subtree Invariant (`size ≥ 2^rank`) vs. Naive `O(N)` Linear Chain Degeneration.

  Toolchain: `leanprover/lean4:v4.33.0` — zero `sorry`, zero `admit`, zero external axioms.
-/

namespace CommonGround.Frontier.ViterbiTropicalMisraGriesAndUnionFindRank

/-! ## Part I: Viterbi Tropical Min-Plus Distributivity & Dynamic Programming vs. Greedy Trap -/

/-- **Universal Tropical `(min, +)` Right-Distributivity (Bellman / Viterbi Principle of Optimality)**:
    Adding any transition + emission log-cost `c` distributes across pathwise `min`, enabling
    exact `O(T · |S|²)` dynamic programming instead of `O(|S|^T)` exhaustive trajectory search. -/
theorem tropical_min_add_right_distrib_universal (a b c : Int) :
    min (a + c) (b + c) = min a b + c := by
  omega

/-- Step-1 negative log-likelihood costs on `{S₀ = false, S₁ = true}` (`S₀` looks `3×` better locally). -/
def trellisStep1Cost : Bool → Nat
  | false => 1
  | true  => 3

/-- Step-2 transition + emission costs `(prev, curr) ↦ cost` (`S₀` leads into a `+10` dead-end!). -/
def trellisStep2Cost : Bool → Bool → Nat
  | false, false => 10
  | false, true  => 10
  | true,  false => 1
  | true,  true  => 5

/-- Full 2-step sequence negative log-likelihood `cost₁(s₁) + cost₂(s₁, s₂)`. -/
def totalTrellisNll (s₁ s₂ : Bool) : Nat :=
  trellisStep1Cost s₁ + trellisStep2Cost s₁ s₂

/-- Viterbi DP value at `t = 2` for ending state `s₂`: `min_{s₁} (V₁(s₁) + cost₂(s₁, s₂))`. -/
def viterbiStep2Val (s₂ : Bool) : Nat :=
  min (trellisStep1Cost false + trellisStep2Cost false s₂)
      (trellisStep1Cost true  + trellisStep2Cost true  s₂)

/-- **Viterbi Exact Global MAP Optimum (`4`) vs. Myopic Beam-`1` Greedy Garden-Path Trap (`11`)**:
    1. Exact Viterbi DP recovers global minimum `min(viterbiStep2Val false, viterbiStep2Val true) = 4`
       at `(true, false)` (`3 + 1 = 4`), bounding every `(s₁, s₂) ∈ Bool²` from below;
    2. Myopic token-greedy decoding commits at `t = 1` to `s₁ = false` (`1 < 3`), trapping continuation
       at `totalTrellisNll false s₂ = 11 > 4` (`2.75×` higher sequence NLL for every `s₂`!). -/
theorem viterbi_global_optimum_vs_myopic_greedy_garden_path_trap :
    min (viterbiStep2Val false) (viterbiStep2Val true) = 4 ∧
    totalTrellisNll true false = 4 ∧
    (∀ s₁ s₂ : Bool, 4 ≤ totalTrellisNll s₁ s₂) ∧
    (trellisStep1Cost false < trellisStep1Cost true) ∧
    (∀ s₂ : Bool, totalTrellisNll false s₂ = 11 ∧ 4 < totalTrellisNll false s₂) := by
  refine ⟨by decide, by decide, ?_, by decide, ?_⟩
  · decide
  · decide

/-! ## Part II: Boyer–Moore / Misra–Gries Heavy-Hitter Cancellation vs. Unverified Survivor Trap -/

/-- **Universal Misra–Gries `(k + 1)`-Way Cancellation Zero-False-Negative Theorem**:
    Suppose a stream of length `N` undergoes `D` simultaneous `(k + 1)`-distinct decrements leaving
    nonnegative residual counter sum `R` (`N = (k + 1) * D + R`). Since any item `x` loses at most
    `1` count per `(k + 1)`-cancellation (`freqX ≤ cntX + D`), EVERY heavy hitter satisfying
    `(k + 1) * freqX > N` MUST survive at the end of Pass 1 with strictly positive counter `1 ≤ cntX`! -/
theorem misra_gries_heavy_hitter_positive_survivor_universal
    (k N D R freqX cntX : Nat)
    (hPart : N = (k + 1) * D + R)
    (hDec  : freqX ≤ cntX + D)
    (hHeavy : N < (k + 1) * freqX) :
    1 ≤ cntX := by
  have hMul : (k + 1) * freqX ≤ (k + 1) * (cntX + D) := Nat.mul_le_mul_left (k + 1) hDec
  rw [Nat.mul_add] at hMul
  by_cases hZero : cntX = 0
  · subst hZero
    omega
  · omega

/-- Single-step Boyer–Moore (`k = 1`) majority state `(candidate, count)` update. -/
def boyerMooreStep (st : Nat × Nat) (x : Nat) : Nat × Nat :=
  if st.2 == 0 then (x, 1)
  else if st.1 == x then (st.1, st.2 + 1)
  else (st.1, st.2 - 1)

/-- Run Pass-1 Boyer–Moore majority vote over a finite stream `List Nat`. -/
def boyerMoorePass1 (xs : List Nat) : Nat × Nat :=
  xs.foldl boyerMooreStep (0, 0)

/-- Exact occurrence count of `x` in stream `xs` (Pass-2 verification). -/
def streamFreq (xs : List Nat) (x : Nat) : Nat :=
  xs.foldl (fun acc y => acc + if y == x then 1 else 0) 0

/-- **Positive Majority Recovery (`[2,1,2,3,2] ↦ 2`) vs. Unverified `20%` Survivor Hallucination (`[1,2,1,2,9] ↦ 9`)**:
    1. On majority stream `[2, 1, 2, 3, 2]` (`freq(2) = 3/5 > 50%`), Pass 1 returns `(2, 1)` and
       Pass 2 confirms `2 * 3 > 5`;
    2. On non-majority stream `[1, 2, 1, 2, 9]` (`N = 5`), pairs `(1, 2)` cancel twice so Pass 1
       returns `(9, 1)` (`cnt = 1 > 0`!) even though `9` occurs only `1/5 = 20% ≤ 50%` — proving why
       omitting Pass-2 verification produces false-positive heavy hitters! -/
theorem boyer_moore_majority_recovery_vs_unverified_tail_survivor_trap :
    boyerMoorePass1 [2, 1, 2, 3, 2] = (2, 1) ∧
    2 * streamFreq [2, 1, 2, 3, 2] 2 > 5 ∧
    boyerMoorePass1 [1, 2, 1, 2, 9] = (9, 1) ∧
    streamFreq [1, 2, 1, 2, 9] 9 = 1 ∧
    2 * streamFreq [1, 2, 1, 2, 9] 9 < 5 := by
  decide

/-! ## Part III: Tarjan Union-by-Rank Exponential Subtree Invariant vs. `O(N)` Unranked Chain -/

/-- Resulting root rank when merging two disjoint roots of ranks `rkA` and `rkB` by Tarjan's rule. -/
def mergedUnionRank (rkA rkB : Nat) : Nat :=
  if rkA < rkB then rkB
  else if rkB < rkA then rkA
  else rkA + 1

/-- **Universal Tarjan Union-by-Rank Exponential Subtree Lower Bound (`size ≥ 2^rank`)**:
    Merging ANY two disjoint trees satisfying `2^rkA ≤ szA` and `2^rkB ≤ szB` preserves
    `2^(mergedUnionRank rkA rkB) ≤ szA + szB`, guaranteeing `rank ≤ ⌊log₂ N⌋` globally! -/
theorem union_by_rank_size_ge_two_pow_rank_universal
    (szA rkA szB rkB : Nat)
    (hA : 2 ^ rkA ≤ szA)
    (hB : 2 ^ rkB ≤ szB) :
    2 ^ (mergedUnionRank rkA rkB) ≤ szA + szB := by
  unfold mergedUnionRank
  split
  · omega
  · split
    · omega
    · have hEq : rkA = rkB := by omega
      subst hEq
      rw [Nat.pow_succ]
      omega

/-- Pointer-chase depth to root in a parent array `Fin 8 → Fin 8` bounded by fuel `8`. -/
def findDepth8 : Nat → (Fin 8 → Fin 8) → Fin 8 → Nat
  | 0, _, _ => 0
  | fuel + 1, parent, x =>
    if parent x == x then 0 else 1 + findDepth8 fuel parent (parent x)

/-- Naive unranked sequential union `0 → 1 → 2 → 3 → 4 → 5 → 6 → 7` (linear chain depth `7 = N - 1`!). -/
def naiveChainParent8 (x : Fin 8) : Fin 8 :=
  if h : x.val < 7 then ⟨x.val + 1, by omega⟩ else x

/-- Balanced union-by-rank tree on `8` elements (`0,1→1`; `2,3→3`; `1,3→3`; `4,5→5`; `6,7→7`; `5,7→7`; `3,7→7`),
    achieving logarithmic worst-case depth `3 = log₂ 8` even BEFORE path compression! -/
def rankedTreeParent8 : Fin 8 → Fin 8
  | ⟨0, _⟩ => ⟨1, by omega⟩
  | ⟨1, _⟩ => ⟨3, by omega⟩
  | ⟨2, _⟩ => ⟨3, by omega⟩
  | ⟨3, _⟩ => ⟨7, by omega⟩
  | ⟨4, _⟩ => ⟨5, by omega⟩
  | ⟨5, _⟩ => ⟨7, by omega⟩
  | ⟨6, _⟩ => ⟨7, by omega⟩
  | ⟨7, _⟩ => ⟨7, by omega⟩

/-- **Balanced Union-by-Rank Logarithmic Depth (`≤ 3`) vs. Unranked Chain Linear Degeneration (`= 7`)**:
    Across `N = 8` elements, every node in `rankedTreeParent8` reaches the root in `≤ 3 = log₂ 8`
    pointer hops, whereas naive unranked attachment forces `findDepth8 = 7 = N - 1` hops from node `0`! -/
theorem ranked_union_log_depth_vs_naive_chain_linear_degeneration :
    (∀ x : Fin 8, findDepth8 8 rankedTreeParent8 x ≤ 3) ∧
    findDepth8 8 rankedTreeParent8 ⟨0, by omega⟩ = 3 ∧
    findDepth8 8 naiveChainParent8 ⟨0, by omega⟩ = 7 := by
  refine ⟨?_, by decide, by decide⟩
  decide

end CommonGround.Frontier.ViterbiTropicalMisraGriesAndUnionFindRank
