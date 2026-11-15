/-
Copyright (c) 2026 Common Ground Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Verification Suite #617: Ville–Doob Maximal Supermartingale Bound, Han–Shearer Submodular Entropy Inequality, Heteroskedastic Martingale Orthogonality, Bregman Three-Point Projection, Arbitrary-$m$ Csiszár Data Processing & Chernoff Tilt

Pure-core Lean 4.33.0 verification suite (`0` imports, `0` `sorry`) unifying:
- **Ville / Doob Maximal Supermartingale Inequality vs. Submartingale Violation**
  (`ville_doob_maximal_supermartingale_threshold_bound_vs_submartingale_violation`),
- **Han / Shearer Leave-One-Out Submodular Inequality vs. 3-Way Conjunctive Synergy Violation**
  (`han_shearer_submodular_leave_one_out_vs_three_way_synergy_violation`),
- **Heteroskedastic Martingale Variance Orthogonality vs. Persistent Autocorrelated Drift Doubling**
  (`azuma_martingale_orthogonal_variance_decomposition_vs_persistent_drift_doubling`),
- **Mahalanobis–Bregman Three-Point Pythagorean Projection vs. Non-Convex Two-Well Failure**
  (`bregman_mahalanobis_three_point_pythagorean_projection_vs_nonconvex_two_well_split`),
- **Arbitrary-$m$ Csiszár $\chi^2$ Pair-Merging Data Processing & Proportional Sufficiency**
  (`arbitrary_m_csiszar_pair_merging_data_processing_and_proportional_sufficiency`),
- **Chernoff Exponential-Tilt Markov Dominance vs. Untuned Linear Markov Slack**
  (`chernoff_exponential_tilt_markov_dominance_vs_untuned_markov_slack`).
-/

namespace CommonGround.Verification.CsiszarFreedmanMartingaleVilleShearerBridge

def sq617 (z : Int) : Int := z * z

theorem sq617_nonneg (z : Int) : 0 ≤ sq617 z := by
  unfold sq617
  by_cases h : 0 ≤ z
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -z := by omega
    have hm : 0 ≤ (-z) * (-z) := Int.mul_nonneg hn hn
    grind

/-! ## 1. Ville / Doob Maximal Supermartingale Inequality vs. Submartingale Violation -/

def hit1 (lam z : Int) : Int :=
  if lam ≤ z then 1 else 0

theorem mul_hit1_le (lam z : Int) (_hlam : 0 < lam) (hz : 0 ≤ z) :
    lam * hit1 lam z ≤ z := by
  unfold hit1
  by_cases h : lam ≤ z
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

/-- Number of equiprobable paths `ω ∈ {HH, HT, TH, TT}` along which `max_{0 ≤ t ≤ 2} X_t(ω) ≥ lam`. -/
def countMaxGe2Step (x0 uH uT uHH uHT uTH uTT lam : Int) : Int :=
  (if lam ≤ x0 || lam ≤ uH || lam ≤ uHH then 1 else 0) +
  (if lam ≤ x0 || lam ≤ uH || lam ≤ uHT then 1 else 0) +
  (if lam ≤ x0 || lam ≤ uT || lam ≤ uTH then 1 else 0) +
  (if lam ≤ x0 || lam ≤ uT || lam ≤ uTT then 1 else 0)

theorem branch_maximal_bound (u1 u2a u2b lam : Int)
    (hlam : 0 < lam) (ha : 0 ≤ u2a) (hb : 0 ≤ u2b) (hsuper : u2a + u2b ≤ 2 * u1) :
    lam * ((if lam ≤ u1 || lam ≤ u2a then 1 else 0) +
           (if lam ≤ u1 || lam ≤ u2b then 1 else 0)) ≤ 2 * u1 := by
  by_cases h1 : lam ≤ u1
  · have hb1 : (lam ≤ u1 || lam ≤ u2a) = true := by simp [h1]
    have hb2 : (lam ≤ u1 || lam ≤ u2b) = true := by simp [h1]
    rw [hb1, hb2]
    simp
    omega
  · have h1f : decide (lam ≤ u1) = false := decide_eq_false h1
    have eqA : (if (decide (lam ≤ u1) || decide (lam ≤ u2a)) = true then (1 : Int) else 0) = hit1 lam u2a := by
      rw [h1f]
      unfold hit1
      by_cases haL : lam ≤ u2a
      · simp [haL]
      · simp [haL]
    have eqB : (if (decide (lam ≤ u1) || decide (lam ≤ u2b)) = true then (1 : Int) else 0) = hit1 lam u2b := by
      rw [h1f]
      unfold hit1
      by_cases hbL : lam ≤ u2b
      · simp [hbL]
      · simp [hbL]
    change lam * ((if (decide (lam ≤ u1) || decide (lam ≤ u2a)) = true then 1 else 0) +
                  (if (decide (lam ≤ u1) || decide (lam ≤ u2b)) = true then 1 else 0)) ≤ 2 * u1
    rw [eqA, eqB]
    have hma := mul_hit1_le lam u2a hlam ha
    have hmb := mul_hit1_le lam u2b hlam hb
    have hdist : lam * (hit1 lam u2a + hit1 lam u2b) = lam * hit1 lam u2a + lam * hit1 lam u2b := by grind
    omega

/-- Ville / Doob Maximal Supermartingale Inequality vs. Submartingale Counterexample:
    1. For ANY non-negative 2-step supermartingale `(x0, uH, uT, uHH, uHT, uTH, uTT)` satisfying
       `uHH + uHT ≤ 2 * uH`, `uTH + uTT ≤ 2 * uT`, `uH + uT ≤ 2 * x0`, and ANY `lam > 0`,
       `lam * countMaxGe2Step ... lam ≤ 4 * x0` (`λ · P(max_{t≤2} X_t ≥ λ) ≤ 𝔼[X_0]`),
    2. Submartingale failure: `(x0 = 1, uH = 0, uT = 3, uHH = 0, uHT = 0, uTH = 3, uTT = 3)` has
       `uH + uT = 3 > 2 = 2 * x0` and at `lam = 3` gives `lam * countMaxGe2Step = 3 * 2 = 6 > 4 = 4 * x0`! -/
theorem ville_doob_maximal_supermartingale_threshold_bound_vs_submartingale_violation :
    (∀ x0 uH uT uHH uHT uTH uTT lam : Int,
      0 < lam → 0 ≤ x0 → 0 ≤ uHH → 0 ≤ uHT → 0 ≤ uTH → 0 ≤ uTT →
      uHH + uHT ≤ 2 * uH → uTH + uTT ≤ 2 * uT → uH + uT ≤ 2 * x0 →
      lam * countMaxGe2Step x0 uH uT uHH uHT uTH uTT lam ≤ 4 * x0) ∧
    (3 * countMaxGe2Step 1 0 3 0 0 3 3 3 = 6 ∧ 4 * (1 : Int) < 6) := by
  refine ⟨?_, by decide⟩
  intro x0 uH uT uHH uHT uTH uTT lam hlam _ hHH hHT hTH hTT hsH hsT hs0
  unfold countMaxGe2Step
  by_cases hx0 : lam ≤ x0
  · simp [hx0]
    omega
  · have hx0f : decide (lam ≤ x0) = false := decide_eq_false hx0
    change lam * (
      (if (decide (lam ≤ x0) || decide (lam ≤ uH) || decide (lam ≤ uHH)) = true then 1 else 0) +
      (if (decide (lam ≤ x0) || decide (lam ≤ uH) || decide (lam ≤ uHT)) = true then 1 else 0) +
      (if (decide (lam ≤ x0) || decide (lam ≤ uT) || decide (lam ≤ uTH)) = true then 1 else 0) +
      (if (decide (lam ≤ x0) || decide (lam ≤ uT) || decide (lam ≤ uTT)) = true then 1 else 0)) ≤ 4 * x0
    rw [hx0f]
    simp only [Bool.false_or]
    have hbH := branch_maximal_bound uH uHH uHT lam hlam hHH hHT hsH
    have hbT := branch_maximal_bound uT uTH uTT lam hlam hTH hTT hsT
    have hdist4 : ∀ c1 c2 c3 c4 : Int, lam * (c1 + c2 + c3 + c4) = lam * (c1 + c2) + lam * (c3 + c4) := by
      intro c1 c2 c3 c4
      grind
    rw [hdist4]
    change lam * ((if (decide (lam ≤ uH) || decide (lam ≤ uHH)) = true then 1 else 0) + (if (decide (lam ≤ uH) || decide (lam ≤ uHT)) = true then 1 else 0)) ≤ 2 * uH at hbH
    change lam * ((if (decide (lam ≤ uT) || decide (lam ≤ uTH)) = true then 1 else 0) + (if (decide (lam ≤ uT) || decide (lam ≤ uTT)) = true then 1 else 0)) ≤ 2 * uT at hbT
    omega

/-! ## 2. Han / Shearer Leave-One-Out Submodular Inequality vs. 3-Way Synergy Gate -/

/-- Coverage / cut-incidence rank of a subset `mask ∈ {0..7}` of `3` vertices on `K₃`:
    `0` on `∅`, `2` on singletons & pairs & `{0,1,2}`? More simply, vertex-neighborhood coverage
    on the path `0 - 1 - 2` (`f(∅)=0, f({0})=2, f({1})=3, f({2})=2, f({0,1})=3, f({0,2})=3, f({1,2})=3, f({0,1,2})=3`). -/
def pathNeighborhoodRank (mask : Nat) : Int :=
  if mask == 0 then 0
  else if mask == 1 || mask == 4 then 2
  else 3

/-- 3-way conjunctive synergy gate (`f(S) = 1` iff `S = {0,1,2}` else `0`): supermodular, NOT submodular! -/
def threeWaySynergy (mask : Nat) : Int :=
  if mask == 7 then 1 else 0

/-- Han / Shearer Leave-One-Out Submodular Inequality vs. 3-Way Conjunctive Synergy Failure:
    1. Universal 3-coordinate Shearer theorem: for ANY set function `f : Nat → Int` on `2^{0,1,2}`
       with `f 0 = 0`, `f 7 + f 1 ≤ f 3 + f 5` (`{0,1} ∪ {0,2} = {0,1,2}`, `{0,1} ∩ {0,2} = {0}`),
       and `f 7 + f 0 ≤ f 1 + f 6` (`{0} ∪ {1,2} = {0,1,2}`, `{0} ∩ {1,2} = ∅`),
       `2 * f 7 ≤ f 3 + f 5 + f 6` (`2 f({0,1,2}) ≤ f({0,1}) + f({0,2}) + f({1,2})`),
    2. Concrete submodular witness (`pathNeighborhoodRank`): `2 * 3 = 6 ≤ 3 + 3 + 3 = 9`,
    3. Supermodular 3-way synergy counterexample (`threeWaySynergy`): `f 7 + f 0 = 1 > 0 = f 1 + f 6`,
       and `2 * f 7 = 2 > 0 = f 3 + f 5 + f 6`! -/
theorem han_shearer_submodular_leave_one_out_vs_three_way_synergy_violation :
    (∀ f : Nat → Int,
      f 0 = 0 →
      f 7 + f 1 ≤ f 3 + f 5 →
      f 7 + f 0 ≤ f 1 + f 6 →
      2 * f 7 ≤ f 3 + f 5 + f 6) ∧
    (pathNeighborhoodRank 0 = 0 ∧
     pathNeighborhoodRank 7 + pathNeighborhoodRank 1 ≤ pathNeighborhoodRank 3 + pathNeighborhoodRank 5 ∧
     pathNeighborhoodRank 7 + pathNeighborhoodRank 0 ≤ pathNeighborhoodRank 1 + pathNeighborhoodRank 6 ∧
     2 * pathNeighborhoodRank 7 ≤ pathNeighborhoodRank 3 + pathNeighborhoodRank 5 + pathNeighborhoodRank 6) ∧
    (threeWaySynergy 0 = 0 ∧
     threeWaySynergy 1 + threeWaySynergy 6 < threeWaySynergy 7 + threeWaySynergy 0 ∧
     threeWaySynergy 3 + threeWaySynergy 5 + threeWaySynergy 6 < 2 * threeWaySynergy 7) := by
  refine ⟨?_, by decide, by decide⟩
  intro f h0 hsub1 hsub2
  omega

/-! ## 3. Heteroskedastic Martingale Orthogonality vs. Persistent Autocorrelated Drift Doubling -/

/-- Heteroskedastic Martingale Variance Orthogonality vs. Persistent Autocorrelated Drift Doubling:
    1. When conditional step-2 increments satisfy `dHH + dHT = 0` and `dTH + dTT = 0` (even when step-2
       volatility `|dHH| ≠ |dTH|` depends arbitrarily on step 1!), total 2-step energy decomposes
       orthogonally with zero cross-covariance:
       `(dH + dHH)² + (dH + dHT)² + (dT + dTH)² + (dT + dTT)² = (2 dH² + 2 dT²) + (dHH² + dHT² + dTH² + dTT²)`,
    2. Under persistent autocorrelation `d2 = d1` (`dHH = dHT = dH`, `dTH = dTT = dT`), total energy
       becomes `4 dH² + 4 dT² = 2 * ((2 dH² + 2 dT²))`, strictly exceeding orthogonal sum whenever `dH ≠ 0`! -/
theorem azuma_martingale_orthogonal_variance_decomposition_vs_persistent_drift_doubling :
    (∀ dH dT dHH dHT dTH dTT : Int,
      dHH + dHT = 0 → dTH + dTT = 0 →
      sq617 (dH + dHH) + sq617 (dH + dHT) + sq617 (dT + dTH) + sq617 (dT + dTT) =
        (2 * sq617 dH + 2 * sq617 dT) + (sq617 dHH + sq617 dHT + sq617 dTH + sq617 dTT)) ∧
    (∀ d : Int, d ≠ 0 →
      (2 * sq617 d + 2 * sq617 (-d)) + (sq617 d + sq617 (-d) + sq617 d + sq617 (-d)) <
        sq617 (d + d) + sq617 (d + d) + sq617 (-d + -d) + sq617 (-d + -d)) := by
  refine ⟨?_, ?_⟩
  · intro dH dT dHH dHT dTH dTT hH hT
    have e1 : dHT = -dHH := by omega
    have e2 : dTT = -dTH := by omega
    subst e1; subst e2
    unfold sq617
    grind
  · intro d hd
    have hpos : 0 < d * d := by
      by_cases hp : 0 < d
      · exact Int.mul_pos hp hp
      · have hn : 0 < -d := by omega
        have hm : 0 < (-d) * (-d) := Int.mul_pos hn hn
        grind
    have hdiff :
        (sq617 (d + d) + sq617 (d + d) + sq617 (-d + -d) + sq617 (-d + -d)) -
          ((2 * sq617 d + 2 * sq617 (-d)) + (sq617 d + sq617 (-d) + sq617 d + sq617 (-d))) =
        8 * (d * d) := by
      unfold sq617
      grind
    omega

/-! ## 4. Mahalanobis–Bregman Three-Point Pythagorean Projection vs. Non-Convex Two-Well Failure -/

def bregDiag2 (w1 w2 x1 x2 y1 y2 : Int) : Int :=
  w1 * sq617 (x1 - y1) + w2 * sq617 (x2 - y2)

/-- Mahalanobis–Bregman Three-Point Identity & Convex Pythagorean Inequality vs. Non-Convex Two-Well Split:
    1. Exact three-point identity: `D(z, x) - D(z, y) - D(y, x) = 2 (w₁(z₁ - y₁)(y₁ - x₁) + w₂(z₂ - y₂)(y₂ - x₂))`,
    2. Variational optimality `w₁(z₁ - y₁)(x₁ - y₁) + w₂(z₂ - y₂)(x₂ - y₂) ≤ 0` implies generalized
       Pythagorean projection dominance `D(z, y) + D(y, x) ≤ D(z, x)`,
    3. Non-convex two-well failure (`C = {-2, +2}`, `x = 0`, `y = 2`, `z = -2`): `y = 2` is a closest point of `C`
       to `x = 0`, yet `D(-2, 2) + D(2, 0) = 16 + 4 = 20 > 4 = D(-2, 0)`! -/
theorem bregman_mahalanobis_three_point_pythagorean_projection_vs_nonconvex_two_well_split :
    (∀ w1 w2 x1 x2 y1 y2 z1 z2 : Int,
      bregDiag2 w1 w2 z1 z2 x1 x2 - bregDiag2 w1 w2 z1 z2 y1 y2 - bregDiag2 w1 w2 y1 y2 x1 x2 =
        2 * (w1 * (z1 - y1) * (y1 - x1) + w2 * (z2 - y2) * (y2 - x2))) ∧
    (∀ w1 w2 x1 x2 y1 y2 z1 z2 : Int,
      w1 * (z1 - y1) * (x1 - y1) + w2 * (z2 - y2) * (x2 - y2) ≤ 0 →
      bregDiag2 w1 w2 z1 z2 y1 y2 + bregDiag2 w1 w2 y1 y2 x1 x2 ≤ bregDiag2 w1 w2 z1 z2 x1 x2) ∧
    (bregDiag2 1 1 (-2) 0 0 0 < bregDiag2 1 1 (-2) 0 2 0 + bregDiag2 1 1 2 0 0 0) := by
  refine ⟨?_, ?_, by decide⟩
  · intro w1 w2 x1 x2 y1 y2 z1 z2
    unfold bregDiag2 sq617
    grind
  · intro w1 w2 x1 x2 y1 y2 z1 z2 hvar
    have hid :
        bregDiag2 w1 w2 z1 z2 x1 x2 - bregDiag2 w1 w2 z1 z2 y1 y2 - bregDiag2 w1 w2 y1 y2 x1 x2 =
          -2 * (w1 * (z1 - y1) * (x1 - y1) + w2 * (z2 - y2) * (x2 - y2)) := by
      unfold bregDiag2 sq617
      grind
    omega

/-! ## 5. Arbitrary-$m$ Csiszár Pair-Merging Data Processing & Proportional Sufficiency -/

def sumMergedChi2 (m : Nat) (p1 p2 q1 q2 : Nat → Int) : Int :=
  match m with
  | 0 => 0
  | k + 1 => sumMergedChi2 k p1 p2 q1 q2 + q1 k * q2 k * sq617 (p1 k + p2 k)

def sumFineChi2 (m : Nat) (p1 p2 q1 q2 : Nat → Int) : Int :=
  match m with
  | 0 => 0
  | k + 1 => sumFineChi2 k p1 p2 q1 q2 + (q1 k + q2 k) * (q2 k * sq617 (p1 k) + q1 k * sq617 (p2 k))

def sumLikelihoodDefectSq (m : Nat) (p1 p2 q1 q2 : Nat → Int) : Int :=
  match m with
  | 0 => 0
  | k + 1 => sumLikelihoodDefectSq k p1 p2 q1 q2 + sq617 (q1 k * p2 k - q2 k * p1 k)

/-- Arbitrary-$m$ Csiszár Pair-Merging Data Processing & Proportional Sufficiency:
    For ANY number `m : Nat` of merged atom pairs `(p1 k, p2 k)` under `(q1 k, q2 k)`,
    `sumMergedChi2 m + sumLikelihoodDefectSq m = sumFineChi2 m` and `sumMergedChi2 m ≤ sumFineChi2 m`,
    with zero total defect when `q1 k * p2 k = q2 k * p1 k` on all `k < m`! -/
theorem arbitrary_m_csiszar_pair_merging_data_processing_and_proportional_sufficiency :
    (∀ m : Nat, ∀ p1 p2 q1 q2 : Nat → Int,
      sumMergedChi2 m p1 p2 q1 q2 + sumLikelihoodDefectSq m p1 p2 q1 q2 =
        sumFineChi2 m p1 p2 q1 q2 ∧
      sumMergedChi2 m p1 p2 q1 q2 ≤ sumFineChi2 m p1 p2 q1 q2) ∧
    (∀ m : Nat, ∀ p1 p2 q1 q2 : Nat → Int,
      (∀ k : Nat, k < m → q1 k * p2 k = q2 k * p1 k) →
      sumMergedChi2 m p1 p2 q1 q2 = sumFineChi2 m p1 p2 q1 q2) := by
  refine ⟨?_, ?_⟩
  · intro m p1 p2 q1 q2
    induction m with
    | zero =>
      simp [sumMergedChi2, sumLikelihoodDefectSq, sumFineChi2]
    | succ k ih =>
      have hmStep : sumMergedChi2 (k + 1) p1 p2 q1 q2 =
          sumMergedChi2 k p1 p2 q1 q2 + q1 k * q2 k * sq617 (p1 k + p2 k) := rfl
      have hdStep : sumLikelihoodDefectSq (k + 1) p1 p2 q1 q2 =
          sumLikelihoodDefectSq k p1 p2 q1 q2 + sq617 (q1 k * p2 k - q2 k * p1 k) := rfl
      have hfStep : sumFineChi2 (k + 1) p1 p2 q1 q2 =
          sumFineChi2 k p1 p2 q1 q2 + (q1 k + q2 k) * (q2 k * sq617 (p1 k) + q1 k * sq617 (p2 k)) := rfl
      have hloc :
          q1 k * q2 k * sq617 (p1 k + p2 k) + sq617 (q1 k * p2 k - q2 k * p1 k) =
            (q1 k + q2 k) * (q2 k * sq617 (p1 k) + q1 k * sq617 (p2 k)) := by
        unfold sq617
        grind
      have hpos := sq617_nonneg (q1 k * p2 k - q2 k * p1 k)
      rw [hmStep, hdStep, hfStep]
      have ihEq := ih.1
      constructor <;> omega
  · intro m p1 p2 q1 q2 hprop
    induction m with
    | zero => rfl
    | succ k ih =>
      have hmStep : sumMergedChi2 (k + 1) p1 p2 q1 q2 =
          sumMergedChi2 k p1 p2 q1 q2 + q1 k * q2 k * sq617 (p1 k + p2 k) := rfl
      have hfStep : sumFineChi2 (k + 1) p1 p2 q1 q2 =
          sumFineChi2 k p1 p2 q1 q2 + (q1 k + q2 k) * (q2 k * sq617 (p1 k) + q1 k * sq617 (p2 k)) := rfl
      have hk : q1 k * p2 k = q2 k * p1 k := hprop k (by omega)
      have hloc :
          q1 k * q2 k * sq617 (p1 k + p2 k) =
            (q1 k + q2 k) * (q2 k * sq617 (p1 k) + q1 k * sq617 (p2 k)) := by
        have hid :
            q1 k * q2 k * sq617 (p1 k + p2 k) + (q1 k * p2 k - q2 k * p1 k) * (q1 k * p2 k - q2 k * p1 k) =
              (q1 k + q2 k) * (q2 k * sq617 (p1 k) + q1 k * sq617 (p2 k)) := by
          unfold sq617
          grind
        have hz : q1 k * p2 k - q2 k * p1 k = 0 := by omega
        rw [hz] at hid
        omega
      have ihk : sumMergedChi2 k p1 p2 q1 q2 = sumFineChi2 k p1 p2 q1 q2 :=
        ih (fun j hj => hprop j (by omega))
      rw [hmStep, hfStep, ihk, hloc]

/-! ## 6. Chernoff Exponential-Tilt Markov Dominance vs. Untuned Linear Markov Slack -/

def sumExceeding (n : Nat) (w g : Nat → Int) (B : Int) : Int :=
  match n with
  | 0 => 0
  | k + 1 => sumExceeding k w g B + (if B ≤ g k then w k else 0)

def sumWeighted (n : Nat) (w g : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | k + 1 => sumWeighted k w g + w k * g k

/-- Chernoff Exponential-Tilt Markov Dominance vs. Untuned Linear Markov Slack:
    1. Universal non-negative tilted Markov bound: for ANY `n : Nat`, weights `w k ≥ 0`, tilted
       exponential feature `g k ≥ 0`, and threshold `B > 0`,
       `B * sumExceeding n w g B ≤ sumWeighted n w g`,
    2. Exponential-tilt sharpening on `3` fair coin flips (`S_3 = 3` all-heads tail, true mass `1 / 8`):
       - Untuned linear Markov (`g(s) = s`, `B = 3`) gives `(3/2) / 3 = 1/2` (`4 / 8`),
       - Base-`2` exponential Chernoff tilt (`g(s) = 2^s`, `B = 8`) gives `(1 + 3·2 + 3·4 + 8) / (8 · 8) = 27 / 64 < 32 / 64 = 1/2` (`27 < 32`),
       - Base-`3` exponential Chernoff tilt (`g(s) = 3^s`, `B = 27`) gives `(1 + 9 + 27 + 27) / (8 · 27) = 64 / 216 = 8 / 27 < 27 / 64`! -/
theorem chernoff_exponential_tilt_markov_dominance_vs_untuned_markov_slack :
    (∀ n : Nat, ∀ w g : Nat → Int, ∀ B : Int,
      0 < B →
      (∀ k : Nat, k < n → 0 ≤ w k ∧ 0 ≤ g k) →
      B * sumExceeding n w g B ≤ sumWeighted n w g) ∧
    (let mLinearNum := 0 * 1 + 1 * 3 + 2 * 3 + 3 * 1 -- 12 / (8 * 3) = 1/2
     let mTilt2Num := 1 * 1 + 2 * 3 + 4 * 3 + 8 * 1  -- 27 / (8 * 8) = 27/64
     let mTilt3Num := 1 * 1 + 3 * 3 + 9 * 3 + 27 * 1 -- 64 / (8 * 27) = 8/27
     mLinearNum * 8 > mTilt2Num * 3 ∧ mTilt2Num * 27 > mTilt3Num * 8) := by
  refine ⟨?_, by decide⟩
  intro n w g B hB hnonneg
  induction n with
  | zero =>
    simp [sumExceeding, sumWeighted]
  | succ k ih =>
    have heStep : sumExceeding (k + 1) w g B =
        sumExceeding k w g B + (if B ≤ g k then w k else 0) := rfl
    have hwStep : sumWeighted (k + 1) w g = sumWeighted k w g + w k * g k := rfl
    have hk := hnonneg k (by omega)
    have ihk := ih (fun j hj => hnonneg j (by omega))
    have hterm : B * (if B ≤ g k then w k else 0) ≤ w k * g k := by
      by_cases hge : B ≤ g k
      · rw [if_pos hge]
        have hdiff : w k * g k - B * w k = w k * (g k - B) := by grind
        have hgb : 0 ≤ g k - B := by omega
        have hp : 0 ≤ w k * (g k - B) := Int.mul_nonneg hk.1 hgb
        omega
      · rw [if_neg hge]
        have hp : 0 ≤ w k * g k := Int.mul_nonneg hk.1 hk.2
        omega
    have hdist : B * (sumExceeding k w g B + (if B ≤ g k then w k else 0)) =
        B * sumExceeding k w g B + B * (if B ≤ g k then w k else 0) := by grind
    rw [heStep, hwStep, hdist]
    omega

end CommonGround.Verification.CsiszarFreedmanMartingaleVilleShearerBridge
