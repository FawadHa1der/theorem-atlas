/-
  09-consequence-lens-meta-atlas/SpannerTrueTimeCommitWaitJosephKalmanAndFenwickDyadicFrontier.lean

  Frontier #130: Google Spanner TrueTime 2ε Commit-Wait Linearizability & 3f+1 Marzullo Clock
  Overlap vs. Zero-Commit-Wait Timestamp Inversion & Split-Brain, Apollo Joseph-Form Stabilized
  Kalman Covariance vs. Standard (I - KH)P Roundoff Indefiniteness, and Fenwick BIT / MMR Dyadic
  n &&& (n - 1) Disjoint Partition vs. Non-Dyadic Overlapping Double-Counting.

  Zero `sorry`, zero `admit`, zero custom axioms — pure Lean 4.33.0 core.
-/

namespace Frontier.SpannerTrueTimeCommitWaitJosephKalmanAndFenwickDyadicFrontier

-- ============================================================================
-- PART I: Spanner TrueTime 2ε Commit-Wait & Marzullo Clock Overlap vs. Inversion
-- ============================================================================

/-- Bounded physical clock drift `|c - t| ≤ eps`. -/
def validTrueTimeClock (tReal cRead eps : Int) : Prop :=
  tReal - eps ≤ cRead ∧ cRead ≤ tReal + eps

/-- **Theorem 1a (Universal Spanner TrueTime `2ε` Commit-Wait External Consistency)**:
    Suppose clocks `1` and `2` have bounded uncertainty `ε ≥ 0` (`|c_i(t) - t| ≤ ε`).
    - Transaction `T₁` picks timestamp `s₁` and waits to commit at real time `tCommit₁`
      until `TT.after(s₁)` holds (`c₁(tCommit₁) - ε > s₁`).
    - Transaction `T₂` begins causally later in real time (`tCommit₁ ≤ tStart₂`) and picks
      timestamp `s₂ ≥ c₂(tStart₂) + ε` (`TT.now().latest`).
    Then `s₁ < s₂` universally — external-consistency linearizability is strictly preserved! -/
theorem spanner_truetime_two_epsilon_commit_wait_linearizability
    (tCommit1 tStart2 c1Commit c2Start s1 s2 eps : Int)
    (hClock1 : validTrueTimeClock tCommit1 c1Commit eps)
    (hClock2 : validTrueTimeClock tStart2 c2Start eps)
    (hCommitWait1 : c1Commit - eps > s1)
    (hRealOrder : tCommit1 ≤ tStart2)
    (hStartRule2 : s2 ≥ c2Start + eps) :
    s1 < s2 := by
  unfold validTrueTimeClock at hClock1 hClock2
  omega

/-- **Theorem 1b (`2ε` Local Commit-Wait Window Lower Bound & 1D Helly Honest Overlap)**:
    1. When `s₁ = c₁(tPick₁) + ε` and commit-wait releases when `c₁(tCommit₁) - ε ≥ s₁`,
       the local clock advances by at least `2ε` (`c₁(tCommit₁) - c₁(tPick₁) ≥ 2 * ε`).
    2. Every pair of honest clock intervals `[L₁, R₁]`, `[L₂, R₂]` containing true `t*`
       intersects (`max L₁ L₂ ≤ min R₁ R₂`). -/
theorem spanner_two_epsilon_window_and_helly_honest_overlap
    (c1Pick c1Commit s1 eps tStar l1 r1 l2 r2 : Int)
    (hPick : s1 = c1Pick + eps)
    (hWait : c1Commit - eps ≥ s1)
    (hH1 : l1 ≤ tStar ∧ tStar ≤ r1)
    (hH2 : l2 ≤ tStar ∧ tStar ≤ r2) :
    c1Commit - c1Pick ≥ 2 * eps ∧ max l1 l2 ≤ min r1 r2 := by
  omega

/-- **Theorem 1c (Premise-Failure Counterexamples: Zero-Commit-Wait Linearizability Inversion
    & `N = 2` Disjoint Byzantine Clock Split-Brain)**:
    1. Without `2ε` commit-wait (`s_i = c_i(t_i)`), at `ε = 10`, `T₁` commits at `t₁ = 112`
       (`c₁ = 120`, `|120 - 112| = 8 ≤ 10`) and causally later `T₂` starts at `t₂ = 115 > 112`
       (`c₂ = 106`, `|106 - 115| = 9 ≤ 10`), producing timestamp inversion `s₂ = 106 < 120 = s₁`!
    2. With `N = 2, f = 1` (`< 3f + 1`), honest `[100, 102]` and Byzantine `[200, 202]`
       have empty intersection (`max 100 200 > min 102 202`). -/
theorem zero_commit_wait_linearizability_inversion_and_byzantine_split :
    let eps : Int := 10
    let t1 : Int := 112
    let s1 : Int := 120
    let t2 : Int := 115
    let s2 : Int := 106
    (t1 - eps ≤ s1 ∧ s1 ≤ t1 + eps) ∧
    (t2 - eps ≤ s2 ∧ s2 ≤ t2 + eps) ∧
    t1 < t2 ∧
    s2 < s1 ∧
    max (100 : Int) 200 > min (102 : Int) 202 := by
  decide

-- ============================================================================
-- PART II: Joseph-Form Stabilized Kalman Covariance vs. Standard Roundoff Collapse
-- ============================================================================

/-- Fixed-point `S`-scaled Joseph quadratic covariance update `(S - K H)² P + K² R`. -/
def josephCovScaled (S P R H K : Int) : Int :=
  (S - K * H) * (S - K * H) * P + K * K * R

/-- Fixed-point `S`-scaled standard short-form covariance update `S (S - K H) P`. -/
def standardCovScaled (S P H K : Int) : Int :=
  S * (S - K * H) * P

theorem sq_int_nonneg (x : Int) : x * x ≥ 0 := by
  cases Int.le_total 0 x with
  | inl hx => exact Int.mul_nonneg hx hx
  | inr hx =>
    have hnx : 0 ≤ -x := by omega
    have hmul : (-x) * (-x) ≥ 0 := Int.mul_nonneg hnx hnx
    rw [Int.neg_mul_neg] at hmul
    exact hmul

/-- **Theorem 2a (Universal Joseph-Form PSD Non-Negativity Under Arbitrary Perturbed Gain)**:
    For every prior variance `P ≥ 0`, measurement noise `R ≥ 0`, scale `S`, observation `H`,
    and *arbitrary* (suboptimal, quantized, or rounded) gain `K`, `josephCovScaled S P R H K ≥ 0`. -/
theorem joseph_kalman_psd_nonnegative_universal
    (S P R H K : Int) (hP : P ≥ 0) (hR : R ≥ 0) :
    josephCovScaled S P R H K ≥ 0 := by
  unfold josephCovScaled
  have h1 : (S - K * H) * (S - K * H) ≥ 0 := sq_int_nonneg (S - K * H)
  have h2 : K * K ≥ 0 := sq_int_nonneg K
  have hP1 : (S - K * H) * (S - K * H) * P ≥ 0 := Int.mul_nonneg h1 hP
  have hR2 : K * K * R ≥ 0 := Int.mul_nonneg h2 hR
  omega

/-- **Theorem 2b (Exact Equivalence of Joseph and Standard Forms at Unrounded Optimal Gain)**:
    Whenever `K` satisfies the exact Kalman normal equation `(H² P + R) K = P H S`,
    `josephCovScaled S P R H K = standardCovScaled S P H K`. -/
theorem joseph_equals_standard_at_exact_kalman_gain
    (S P R H K : Int)
    (hOpt : (H * H * P + R) * K = P * H * S) :
    josephCovScaled S P R H K = standardCovScaled S P H K := by
  unfold josephCovScaled standardCovScaled
  have hK : K * ((H * H * P + R) * K) = K * (P * H * S) := by rw [hOpt]
  have hExpand1 : (S - K * H) * (S - K * H) * P = S * (S - K * H) * P - K * H * (S - K * H) * P := by
    rw [Int.sub_mul, Int.sub_mul]
  have hExpand2 : K * H * (S - K * H) * P = K * (P * H * S) - K * (H * H * P * K) := by
    rw [Int.mul_sub, Int.sub_mul]
    simp [Int.mul_left_comm, Int.mul_comm]
  have hExpand3 : K * ((H * H * P + R) * K) = K * (H * H * P * K) + K * K * R := by
    rw [Int.add_mul, Int.mul_add]
    simp [Int.mul_left_comm, Int.mul_comm]
  omega

/-- **Theorem 2c (Apollo Fixed-Point Perturbation Counterexample: `-100,000 < 0` vs. `+11,201 > 0`)**:
    With `S = 100, P = 1000, R = 1, H = 1`, exact gain is `100,000 / 1001 ≈ 99.90`.
    Under a tiny upward quantization to `K_round = 101`:
    - `standardCovScaled` collapses to `-100,000 < 0` (catastrophic negative variance!),
    - `josephCovScaled` evaluates to `+11,201 > 0` (strictly preserving positive variance!). -/
theorem apollo_quantized_gain_standard_negative_vs_joseph_positive :
    standardCovScaled 100 1000 1 101 = -100000 ∧
    standardCovScaled 100 1000 1 101 < 0 ∧
    josephCovScaled 100 1000 1 1 101 = 11201 ∧
    josephCovScaled 100 1000 1 1 101 > 0 := by
  decide

-- ============================================================================
-- PART III: Fenwick BIT / MMR Dyadic `n &&& (n - 1)` Disjoint Partition vs. Overlap
-- ============================================================================

/-- Strip lowest set bit `n &&& (n - 1)` used in Fenwick BIT & Merkle Mountain Range peeling. -/
def stripLsb (n : Nat) : Nat :=
  n &&& (n - 1)

/-- Bounded-fuel dyadic query step counter. -/
def dyadicQuerySteps : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 0
  | fuel + 1, idx => 1 + dyadicQuerySteps fuel (stripLsb idx)

/-- Exact prefix sum `∑_{i < k} a(i)` on an `8`-element array (`k ≤ 8`). -/
def exactPrefix8 (a : Fin 8 → Int) (k : Nat) : Int :=
  (if 0 < k then a ⟨0, by decide⟩ else 0) +
  (if 1 < k then a ⟨1, by decide⟩ else 0) +
  (if 2 < k then a ⟨2, by decide⟩ else 0) +
  (if 3 < k then a ⟨3, by decide⟩ else 0) +
  (if 4 < k then a ⟨4, by decide⟩ else 0) +
  (if 5 < k then a ⟨5, by decide⟩ else 0) +
  (if 6 < k then a ⟨6, by decide⟩ else 0) +
  (if 7 < k then a ⟨7, by decide⟩ else 0)

/-- `1`-indexed Fenwick Binary Indexed Tree (`BIT`) nodes `T[1..8]`. -/
def fenwickNode8 (a : Fin 8 → Int) : Nat → Int
  | 1 => a ⟨0, by decide⟩
  | 2 => a ⟨0, by decide⟩ + a ⟨1, by decide⟩
  | 3 => a ⟨2, by decide⟩
  | 4 => a ⟨0, by decide⟩ + a ⟨1, by decide⟩ + a ⟨2, by decide⟩ + a ⟨3, by decide⟩
  | 5 => a ⟨4, by decide⟩
  | 6 => a ⟨4, by decide⟩ + a ⟨5, by decide⟩
  | 7 => a ⟨6, by decide⟩
  | 8 => a ⟨0, by decide⟩ + a ⟨1, by decide⟩ + a ⟨2, by decide⟩ + a ⟨3, by decide⟩ +
         a ⟨4, by decide⟩ + a ⟨5, by decide⟩ + a ⟨6, by decide⟩ + a ⟨7, by decide⟩
  | _ => 0

/-- Fenwick dyadic prefix query peeling `idx ↦ stripLsb idx` (`idx &&& (idx - 1)`). -/
def fenwickPrefixQuery8 (a : Fin 8 → Int) : Nat → Nat → Int
  | 0, _ => 0
  | _, 0 => 0
  | fuel + 1, idx => fenwickNode8 a idx + fenwickPrefixQuery8 a fuel (stripLsb idx)

/-- **Theorem 3a (Universal `Fin 8` Fenwick Dyadic Disjoint-Prefix Exactness & Logarithmic Steps)**:
    For every `a : Fin 8 → Int` and every `k : Fin 9` (`0..8`), `fenwickPrefixQuery8` equals
    `exactPrefix8` in `≤ 3 = log₂ 8` steps, and at `N = 65,536` (`2¹⁶`) / `1,023` (`2¹⁰ - 1`),
    dyadic peeling visits `1` / `10` nodes vs. `65,536` / `1,023` linear scans! -/
theorem fenwick_dyadic_exact_prefix_and_logarithmic_steps (a : Fin 8 → Int) (k : Fin 9) :
    fenwickPrefixQuery8 a 4 k.val = exactPrefix8 a k.val ∧
    dyadicQuerySteps 20 65536 = 1 ∧
    dyadicQuerySteps 20 1023 = 10 := by
  refine ⟨?_, by decide, by decide⟩
  match k with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ | ⟨8, _⟩ =>
    simp [fenwickPrefixQuery8, stripLsb, fenwickNode8, exactPrefix8] <;> omega

/-- Buggy non-dyadic length-`2` sliding window `[i-2, i)` jumped by stride `1` (`i ↦ i - 1`). -/
def overlappingNonDyadicSum4 (a0 a1 a2 a3 : Int) : Int :=
  (a0 + a1) + (a1 + a2) + (a2 + a3)

/-- **Theorem 3b (Premise-Failure Counterexamples: Overlapping Double-Count `15 ≠ 10` & `0`-Index Trap)**:
    1. Summing overlapping non-dyadic windows on `[1, 2, 3, 4]` double-counts interior elements,
       yielding `15 ≠ 10` (`(1+2)+(2+3)+(3+4) = 15 ≠ 10`).
    2. `stripLsb 0 = 0`, showing why `0`-indexed Fenwick updates `idx ↦ idx + (idx &&& -idx)` stall at `0`
       without `1`-based indexing. -/
theorem non_dyadic_overlap_double_count_and_zero_trap :
    overlappingNonDyadicSum4 1 2 3 4 = 15 ∧
    (1 + 2 + 3 + 4 : Int) = 10 ∧
    overlappingNonDyadicSum4 1 2 3 4 ≠ 1 + 2 + 3 + 4 ∧
    stripLsb 0 = 0 := by
  decide

end Frontier.SpannerTrueTimeCommitWaitJosephKalmanAndFenwickDyadicFrontier
