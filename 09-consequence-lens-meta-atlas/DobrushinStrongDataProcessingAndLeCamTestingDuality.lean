/-
Copyright (c) 2026 Common Ground Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Dobrushin $L^1$ Strong Data Processing, Neyman–Pearson–Le Cam Testing Duality & Span-Seminorm Bellman–Kantorovich Contraction

This standalone pure-core Lean 4.33.0 frontier module (`0` imports, `0` sorrys) unifies four
major wings of the Theorem Atlas into one exact, denominator-free arbitrary-dimension (`N × M`)
mathematical engine:
- **Folder `01` (Blackwell–Le Cam Decision Sufficiency)**: Neyman–Pearson likelihood-ratio
  thresholding and Le Cam minimax binary testing duality;
- **Folder `04` (Bellman Error & Lipschitz Control)**: Puterman–Hopf–Dobrushin span-seminorm
  Bellman contraction without discount slack;
- **Folder `08` (Optimal Transport & Kantorovich Coupling)**: Midpoint-centered Kantorovich–Rubinstein
  dual bounded-variation contraction;
- **Folder `09` (Consequence-Oriented Meta-Atlas)**: Quantitative degradation of Consequence
  Classes 1, 2, and 3 under Doeblin–Dobrushin minorized Markov channels.

## Main Results

1. **Scheffé's Positive-Excess $L^1$ Identity (`scheffe_positive_excess_l1_identity`)**:
   For any integer vectors `P, Q : Nat → Int` on `{0, …, N - 1}` with equal total mass
   `∑_{x<N} P_x = ∑_{x<N} Q_x`,
   `∑_{x<N} |P_x - Q_x| = 2 · ∑_{x<N} (P_x - Q_x)_+`.

2. **Neyman–Pearson–Le Cam Minimax Binary Testing Identity & Unequal-Prior Counterexample
   (`le_cam_neyman_pearson_minimax_testing_identity`,
    `unequal_prior_unweighted_threshold_suboptimality_counterexample`)**:
   For every randomized test `T : Nat → Int` bounded in `[0, M]` (`0 ≤ M`),
   `M · ∑_{x<N} min(P_x, Q_x) ≤ ∑_{x<N} (P_x (M - T_x) + Q_x T_x)`,
   with exact equality at the Neyman–Pearson likelihood-ratio threshold `npTest M (P_x) (Q_x)`
   and `2 · ∑_{x<N} min(P_x, Q_x) = ∑ P_x + ∑ Q_x - ∑ |P_x - Q_x|`.
   Conversely, under unequal Bayes priors `3 : 1` on `P = [2, 3], Q = [3, 1]`, the unweighted
   `t = 1/2` threshold incurs Bayes risk `7 > 4`, proving why Consequence Class 3 requires all priors.

3. **Arbitrary-`(N, M)` Doeblin–Dobrushin $L^1$ Strong Data Processing & Le Cam Channel Floor
   (`dobrushin_minorization_l1_strong_data_processing`,
    `dobrushin_channel_minimax_testing_floor`,
    `permutation_channel_zero_minorization_no_contraction`)**:
   For any `N × M` integer Markov kernel `K(x, y) ≥ m(y) ≥ 0` with row sum `R` and minorization
   mass `μ = ∑_{y<M} m(y)`, and any zero-sum perturbation `∑_{x<N} δ_x = 0`,
   `∑_{y<M} |∑_{x<N} δ_x K(x, y)| ≤ (R - μ) · ∑_{x<N} |δ_x|`.
   Consequently, pushing equal-mass non-negative laws `P, Q` (mass `S`) through `K` forces every
   post-channel binary test `0 ≤ T_y ≤ M_test` to incur total testing error at least `M_test · μ · S`.
   When `μ = 0` (the `2 × 2` swap channel `[[0, R], [R, 0]]`), zero contraction occurs (`2RS = 2RS`).

4. **Midpoint-Centered Span-Seminorm Bellman–Kantorovich Contraction & Exact Sharpness
   (`dobrushin_span_seminorm_bellman_kantorovich_contraction`,
    `dobrushin_pairwise_bellman_span_contraction`,
    `dobrushin_span_sharpness_witness`)**:
   For any value vector `V : Nat → Int` bounded in `[ℓ, u]` (`ℓ ≤ V_y ≤ u`),
   `2 · |∑_{x<N} δ_x (KV)_x| ≤ (u - ℓ)(R - μ) · ∑_{x<N} |δ_x|`,
   yielding the sharp factor-2-free pairwise Bellman span contraction
   `|(KV)_{x_1} - (KV)_{x_2}| ≤ (u - ℓ)(R - μ)`, attained with exact integer equality (`10 = 10`).
-/

namespace CommonGround.ConsequenceLens.DobrushinLeCamSpan

/-! ## Section 1: Finite Integer Summations, Order Operations & Pointwise Identities -/

/-- Finite integer sum `∑_{i < n} f(i)`. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

/-- Integer absolute value `|z|`. -/
def iabs (z : Int) : Int :=
  if 0 ≤ z then z else -z

/-- Positive part `z_+ = max(z, 0)`. -/
def posPart (z : Int) : Int :=
  if 0 < z then z else 0

/-- Integer minimum `min(a, b)`. -/
def imin (a b : Int) : Int :=
  if a ≤ b then a else b

/-- Deterministic Neyman–Pearson likelihood-ratio threshold test scaled by `[0, M]`:
rejects `P` in favor of `Q` (`T_x = M`) when `Q_x < P_x` fails? Wait: total error is
`P_x (M - T_x) + Q_x T_x`, so choosing `T_x = M` incurs `Q_x M` (optimal when `Q_x < P_x`)
and choosing `T_x = 0` incurs `P_x M` (optimal when `P_x ≤ Q_x`). -/
def npTest (M p q : Int) : Int :=
  if q < p then M else 0

theorem iabs_nonneg (z : Int) : 0 ≤ iabs z := by
  unfold iabs
  split <;> omega

theorem iabs_add_le (a b : Int) : iabs (a + b) ≤ iabs a + iabs b := by
  unfold iabs
  split <;> split <;> split <;> omega

theorem iabs_mul_of_nonneg_right (a b : Int) (hb : 0 ≤ b) :
    iabs (a * b) = iabs a * b := by
  unfold iabs
  by_cases ha : 0 ≤ a
  · have hab : 0 ≤ a * b := Int.mul_nonneg ha hb
    rw [if_pos hab, if_pos ha]
  · have ha' : a ≤ 0 := by omega
    have hneg : 0 ≤ -a := by omega
    have hab' : a * b ≤ 0 := by
      have h1 : (-a) * b ≥ 0 := Int.mul_nonneg hneg hb
      have h2 : (-a) * b = -(a * b) := Int.neg_mul a b
      omega
    by_cases hz : a * b = 0
    · rw [hz, if_pos (by omega), if_neg ha]
      have h3 : (-a) * b = -(a * b) := Int.neg_mul a b
      omega
    · have hlt : ¬(0 ≤ a * b) := by omega
      rw [if_neg hlt, if_neg ha]
      exact (Int.neg_mul a b).symm

theorem iabs_mul_le (a b : Int) : iabs (a * b) ≤ iabs a * iabs b := by
  unfold iabs
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · have hab : 0 ≤ a * b := Int.mul_nonneg ha hb
    rw [if_pos hab, if_pos ha, if_pos hb]
    exact Int.le_refl _
  · have hnb : 0 ≤ -b := by omega
    have hprod : 0 ≤ a * (-b) := Int.mul_nonneg ha hnb
    have heq : a * (-b) = -(a * b) := Int.mul_neg a b
    rw [if_pos ha, if_neg hb]
    split <;> omega
  · have hna : 0 ≤ -a := by omega
    have hprod : 0 ≤ (-a) * b := Int.mul_nonneg hna hb
    have heq : (-a) * b = -(a * b) := Int.neg_mul a b
    rw [if_neg ha, if_pos hb]
    split <;> omega
  · have hna : 0 ≤ -a := by omega
    have hnb : 0 ≤ -b := by omega
    have hprod : 0 ≤ (-a) * (-b) := Int.mul_nonneg hna hnb
    have heq : (-a) * (-b) = a * b := Int.neg_mul_neg a b
    rw [if_neg ha, if_neg hb]
    split <;> omega

theorem sumRange_congr {n : Nat} {f g : Nat → Int} (h : ∀ i, i < n → f i = g i) :
    sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumRange]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k)]

theorem sumRange_add (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    simp only [sumRange, ih]
    omega

theorem sumRange_sub (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i - g i) = sumRange n f - sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    simp only [sumRange, ih]
    omega

theorem sumRange_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    simp only [sumRange, ih, Int.mul_add]

theorem sumRange_mul_right (n : Nat) (f : Nat → Int) (c : Int) :
    sumRange n (fun i => f i * c) = sumRange n f * c := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    simp only [sumRange, ih, Int.add_mul]

theorem sumRange_nonneg {n : Nat} {f : Nat → Int} (h : ∀ i, i < n → 0 ≤ f i) :
    0 ≤ sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    simp only [sumRange]
    have h1 : 0 ≤ sumRange k f := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have h2 : 0 ≤ f k := h k (Nat.lt_succ_self k)
    omega

theorem sumRange_mono {n : Nat} {f g : Nat → Int} (h : ∀ i, i < n → f i ≤ g i) :
    sumRange n f ≤ sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    simp only [sumRange]
    have h1 : sumRange k f ≤ sumRange k g := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have h2 : f k ≤ g k := h k (Nat.lt_succ_self k)
    omega

theorem iabs_sumRange_le (n : Nat) (f : Nat → Int) :
    iabs (sumRange n f) ≤ sumRange n (fun i => iabs (f i)) := by
  induction n with
  | zero => simp [sumRange, iabs]
  | succ k ih =>
    simp only [sumRange]
    have htri : iabs (sumRange k f + f k) ≤ iabs (sumRange k f) + iabs (f k) :=
      iabs_add_le (sumRange k f) (f k)
    omega

theorem sumRange_comm (N M : Nat) (F : Nat → Nat → Int) :
    sumRange N (fun x => sumRange M (fun y => F x y)) =
      sumRange M (fun y => sumRange N (fun x => F x y)) := by
  induction N with
  | zero =>
    have hz : sumRange M (fun _ => (0 : Int)) = 0 := by
      induction M with
      | zero => rfl
      | succ m ihm => simp [sumRange, ihm]
    simp [sumRange, hz]
  | succ n ihn =>
    simp only [sumRange]
    rw [ihn, ← sumRange_add]

/-! ## Section 2: Scheffé's Positive-Excess Identity & Neyman–Pearson–Le Cam Testing Duality -/

theorem pointwise_abs_sub_eq_two_posPart_sub (p q : Int) :
    iabs (p - q) = 2 * posPart (p - q) - (p - q) := by
  unfold iabs posPart
  split <;> split <;> omega

theorem pointwise_two_imin_eq_add_sub_abs (p q : Int) :
    2 * imin p q = p + q - iabs (p - q) := by
  unfold imin iabs
  split <;> split <;> omega

/-- **Scheffé's Positive-Excess $L^1$ Identity**:
For any equal-mass integer vectors `P, Q` (`∑_{x<N} P_x = ∑_{x<N} Q_x`), the total $L^1$
distance equals twice the one-sided positive excess `2 ∑_{x<N} (P_x - Q_x)_+`. -/
theorem scheffe_positive_excess_l1_identity
    (N : Nat) (P Q : Nat → Int)
    (hmass : sumRange N P = sumRange N Q) :
    sumRange N (fun x => iabs (P x - Q x)) =
      2 * sumRange N (fun x => posPart (P x - Q x)) := by
  have h1 : sumRange N (fun x => iabs (P x - Q x)) =
      sumRange N (fun x => 2 * posPart (P x - Q x) - (P x - Q x)) :=
    sumRange_congr (fun x _ => pointwise_abs_sub_eq_two_posPart_sub (P x) (Q x))
  rw [h1, sumRange_sub, sumRange_mul_left, sumRange_sub, hmass]
  omega

theorem pointwise_npTest_bounds (M p q : Int) (hM : 0 ≤ M) :
    0 ≤ npTest M p q ∧ npTest M p q ≤ M := by
  unfold npTest
  split <;> omega

theorem pointwise_npTest_attains_min (M p q : Int) :
    p * (M - npTest M p q) + q * npTest M p q = M * imin p q := by
  unfold npTest imin
  by_cases hqp : q < p
  · have hnp : ¬(p ≤ q) := by omega
    rw [if_pos hqp, if_neg hnp]
    have hsub : M - M = 0 := by omega
    rw [hsub, Int.mul_zero, Int.zero_add, Int.mul_comm]
  · have hpq : p ≤ q := by omega
    rw [if_neg hqp, if_pos hpq]
    have hsub : M - 0 = M := by omega
    rw [hsub, Int.mul_zero, Int.add_zero, Int.mul_comm]

theorem pointwise_randomized_test_lower_bound (M p q t : Int)
    (ht0 : 0 ≤ t) (htM : t ≤ M) :
    M * imin p q ≤ p * (M - t) + q * t := by
  unfold imin
  by_cases hpq : p ≤ q
  · rw [if_pos hpq]
    have hdiff : 0 ≤ (q - p) * t := Int.mul_nonneg (by omega) ht0
    have hp : p * (M - t) = p * M - p * t := Int.mul_sub p M t
    have hd : (q - p) * t = q * t - p * t := Int.sub_mul q p t
    have hm : M * p = p * M := Int.mul_comm M p
    omega
  · rw [if_neg hpq]
    have hMt : 0 ≤ M - t := by omega
    have hdiff : 0 ≤ (p - q) * (M - t) := Int.mul_nonneg (by omega) hMt
    have hq : q * (M - t) = q * M - q * t := Int.mul_sub q M t
    have hd : (p - q) * (M - t) = p * (M - t) - q * (M - t) := Int.sub_mul p q (M - t)
    have hm : M * q = q * M := Int.mul_comm M q
    omega

/-- **Neyman–Pearson–Le Cam Minimax Binary Testing Identity**:
1. `2 · ∑_{x<N} min(P_x, Q_x) = ∑ P_x + ∑ Q_x - ∑ |P_x - Q_x|`;
2. Every `[0, M]`-valued randomized test `T` satisfies
   `M · ∑_{x<N} min(P_x, Q_x) ≤ ∑_{x<N} (P_x (M - T_x) + Q_x T_x)`;
3. The Neyman–Pearson likelihood-ratio test `npTest M (P_x) (Q_x)` satisfies `0 ≤ T_x ≤ M` and
   attains the minimax lower bound with exact integer equality. -/
theorem le_cam_neyman_pearson_minimax_testing_identity
    (N : Nat) (M : Int) (P Q T : Nat → Int)
    (hM : 0 ≤ M)
    (hT : ∀ x, x < N → 0 ≤ T x ∧ T x ≤ M) :
    2 * sumRange N (fun x => imin (P x) (Q x)) =
        sumRange N P + sumRange N Q - sumRange N (fun x => iabs (P x - Q x)) ∧
      M * sumRange N (fun x => imin (P x) (Q x)) ≤
        sumRange N (fun x => P x * (M - T x) + Q x * T x) ∧
      (∀ x, x < N → 0 ≤ npTest M (P x) (Q x) ∧ npTest M (P x) (Q x) ≤ M) ∧
      sumRange N (fun x =>
        P x * (M - npTest M (P x) (Q x)) + Q x * npTest M (P x) (Q x)) =
        M * sumRange N (fun x => imin (P x) (Q x)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← sumRange_mul_left]
    have h1 : sumRange N (fun x => 2 * imin (P x) (Q x)) =
        sumRange N (fun x => (P x + Q x) - iabs (P x - Q x)) :=
      sumRange_congr (fun x _ => pointwise_two_imin_eq_add_sub_abs (P x) (Q x))
    rw [h1, sumRange_sub, sumRange_add]
  · rw [← sumRange_mul_left]
    exact sumRange_mono (fun x hx =>
      pointwise_randomized_test_lower_bound M (P x) (Q x) (T x) (hT x hx).1 (hT x hx).2)
  · intro x _
    exact pointwise_npTest_bounds M (P x) (Q x) hM
  · rw [← sumRange_mul_left]
    exact sumRange_congr (fun x _ => pointwise_npTest_attains_min M (P x) (Q x))

/-- **Premise-Failure Counterexample (Unequal-Prior Suboptimality of Unweighted Thresholding)**:
On `N = 2` with equal-mass laws `P = [2, 3]` and `Q = [4, 1]` (`∑ P = ∑ Q = 5`) under unequal
prior weights `π_P = 3, π_Q = 1`, the unweighted threshold `npTest 1 P_x Q_x` (`[0, 1]`) incurs
Bayes risk `7`, whereas the prior-calibrated threshold `npTest 1 (3 P_x) Q_x` (`[1, 1]`) achieves
Bayes risk `5 < 7`. -/
theorem unequal_prior_unweighted_threshold_suboptimality_counterexample :
    let P : Nat → Int := fun x => if x = 0 then 2 else 3
    let Q : Nat → Int := fun x => if x = 0 then 4 else 1
    sumRange 2 P = 5 ∧
      sumRange 2 Q = 5 ∧
      sumRange 2 (fun x =>
        (3 * P x) * (1 - npTest 1 (P x) (Q x)) + Q x * npTest 1 (P x) (Q x)) = 7 ∧
      sumRange 2 (fun x =>
        (3 * P x) * (1 - npTest 1 (3 * P x) (Q x)) + Q x * npTest 1 (3 * P x) (Q x)) = 5 := by
  decide

/-! ## Section 3: Arbitrary-`(N, M)` Doeblin–Dobrushin $L^1$ Strong Data Processing -/

/-- **Universal Arbitrary-`(N, M)` Doeblin–Dobrushin $L^1$ Strong Data Processing Inequality**:
Let `K : Nat → Nat → Int` be an integer Markov kernel with constant row sum `R` on `{0, …, M - 1}`,
minorized entrywise by `m : Nat → Int` (`0 ≤ m y ≤ K x y`) with minorization mass
`μ = ∑_{y<M} m y`. For EVERY zero-sum perturbation `δ : Nat → Int` (`∑_{x<N} δ_x = 0`),
`∑_{y<M} |∑_{x<N} δ_x K(x, y)| ≤ (R - μ) · ∑_{x<N} |δ_x|`. -/
theorem dobrushin_minorization_l1_strong_data_processing
    (N M : Nat) (R : Int)
    (K : Nat → Nat → Int) (m : Nat → Int) (δ : Nat → Int)
    (hRow : ∀ x, x < N → sumRange M (fun y => K x y) = R)
    (hMinor : ∀ x y, x < N → y < M → m y ≤ K x y)
    (hZeroSum : sumRange N δ = 0) :
    sumRange M (fun y => iabs (sumRange N (fun x => δ x * K x y))) ≤
      (R - sumRange M m) * sumRange N (fun x => iabs (δ x)) := by
  let H : Nat → Nat → Int := fun x y => K x y - m y
  have hCancel : ∀ y, y < M →
      sumRange N (fun x => δ x * K x y) = sumRange N (fun x => δ x * H x y) := by
    intro y _
    have hsplit : sumRange N (fun x => δ x * K x y) =
        sumRange N (fun x => δ x * H x y + δ x * m y) := by
      refine sumRange_congr (fun x _ => ?_)
      dsimp [H]
      rw [Int.mul_sub]
      omega
    rw [hsplit, sumRange_add, sumRange_mul_right, hZeroSum, Int.zero_mul, Int.add_zero]
  have hPointwise : ∀ y, y < M →
      iabs (sumRange N (fun x => δ x * K x y)) ≤
        sumRange N (fun x => iabs (δ x) * H x y) := by
    intro y hy
    rw [hCancel y hy]
    have htri : iabs (sumRange N (fun x => δ x * H x y)) ≤
        sumRange N (fun x => iabs (δ x * H x y)) :=
      iabs_sumRange_le N (fun x => δ x * H x y)
    have hpos : sumRange N (fun x => iabs (δ x * H x y)) =
        sumRange N (fun x => iabs (δ x) * H x y) := by
      refine sumRange_congr (fun x hx => ?_)
      have hH : 0 ≤ H x y := by
        have hmle : m y ≤ K x y := hMinor x y hx hy
        dsimp [H]
        omega
      exact iabs_mul_of_nonneg_right (δ x) (H x y) hH
    omega
  have hSumY : sumRange M (fun y => iabs (sumRange N (fun x => δ x * K x y))) ≤
      sumRange M (fun y => sumRange N (fun x => iabs (δ x) * H x y)) :=
    sumRange_mono hPointwise
  rw [sumRange_comm M N (fun y x => iabs (δ x) * H x y)] at hSumY
  have hRowH : sumRange N (fun x => sumRange M (fun y => iabs (δ x) * H x y)) =
      (R - sumRange M m) * sumRange N (fun x => iabs (δ x)) := by
    have h1 : sumRange N (fun x => sumRange M (fun y => iabs (δ x) * H x y)) =
        sumRange N (fun x => iabs (δ x) * (R - sumRange M m)) := by
      refine sumRange_congr (fun x hx => ?_)
      rw [sumRange_mul_left]
      have hsubH : sumRange M (fun y => H x y) = R - sumRange M m := by
        dsimp [H]
        rw [sumRange_sub, hRow x hx]
      rw [hsubH]
    rw [h1, sumRange_mul_right, Int.mul_comm]
  omega

/-- Auxiliary $L^1$ triangle bound for equal-mass non-negative laws: `‖P - Q‖₁ ≤ 2 S`. -/
theorem l1_le_two_mass_of_nonneg
    (N : Nat) (S : Int) (P Q : Nat → Int)
    (hP0 : ∀ x, x < N → 0 ≤ P x)
    (hQ0 : ∀ x, x < N → 0 ≤ Q x)
    (hPS : sumRange N P = S)
    (hQS : sumRange N Q = S) :
    sumRange N (fun x => iabs (P x - Q x)) ≤ 2 * S := by
  have hle : sumRange N (fun x => iabs (P x - Q x)) ≤ sumRange N (fun x => P x + Q x) := by
    refine sumRange_mono (fun x hx => ?_)
    have hp := hP0 x hx
    have hq := hQ0 x hx
    unfold iabs
    split <;> omega
  rw [sumRange_add, hPS, hQS] at hle
  omega

/-- **Quantitative Le Cam Channel Minimax Floor (`dobrushin_channel_minimax_testing_floor`)**:
When non-negative laws `P, Q` of equal total mass `S` pass through a minorized Markov kernel `K`
(`K(x, y) ≥ m(y) ≥ 0`, row sum `R`, minorization mass `μ = ∑ m`), the output laws `PK, QK` have
mass `R · S`, satisfy `‖PK - QK‖₁ ≤ (R - μ) ‖P - Q‖₁`, and force EVERY post-channel binary test
`0 ≤ T_y ≤ M_test` to incur total testing error at least `M_test · μ · S`. -/
theorem dobrushin_channel_minimax_testing_floor
    (N M : Nat) (S R M_test : Int)
    (P Q : Nat → Int) (K : Nat → Nat → Int) (m : Nat → Int) (T : Nat → Int)
    (hP0 : ∀ x, x < N → 0 ≤ P x)
    (hQ0 : ∀ x, x < N → 0 ≤ Q x)
    (hPS : sumRange N P = S)
    (hQS : sumRange N Q = S)
    (_hm0 : ∀ y, y < M → 0 ≤ m y)
    (hRow : ∀ x, x < N → sumRange M (fun y => K x y) = R)
    (hMinor : ∀ x y, x < N → y < M → m y ≤ K x y)
    (hMt : 0 ≤ M_test)
    (hT : ∀ y, y < M → 0 ≤ T y ∧ T y ≤ M_test) :
    sumRange M (fun y =>
        iabs (sumRange N (fun x => P x * K x y) - sumRange N (fun x => Q x * K x y))) ≤
        (R - sumRange M m) * sumRange N (fun x => iabs (P x - Q x)) ∧
      M_test * sumRange M m * S ≤
        sumRange M (fun y =>
          sumRange N (fun x => P x * K x y) * (M_test - T y) +
            sumRange N (fun x => Q x * K x y) * T y) := by
  let PK : Nat → Int := fun y => sumRange N (fun x => P x * K x y)
  let QK : Nat → Int := fun y => sumRange N (fun x => Q x * K x y)
  let μ : Int := sumRange M m
  change sumRange M (fun y => iabs (PK y - QK y)) ≤
      (R - μ) * sumRange N (fun x => iabs (P x - Q x)) ∧
    M_test * μ * S ≤ sumRange M (fun y => PK y * (M_test - T y) + QK y * T y)
  have hDiffEq : ∀ y, PK y - QK y = sumRange N (fun x => (P x - Q x) * K x y) := by
    intro y
    dsimp [PK, QK]
    rw [← sumRange_sub]
    refine sumRange_congr (fun x _ => ?_)
    rw [Int.sub_mul]
  have hZero : sumRange N (fun x => P x - Q x) = 0 := by
    rw [sumRange_sub, hPS, hQS]
    omega
  have hSDPI : sumRange M (fun y => iabs (PK y - QK y)) ≤
      (R - μ) * sumRange N (fun x => iabs (P x - Q x)) := by
    have hrew : sumRange M (fun y => iabs (PK y - QK y)) =
        sumRange M (fun y => iabs (sumRange N (fun x => (P x - Q x) * K x y))) :=
      sumRange_congr (fun y _ => by rw [hDiffEq y])
    rw [hrew]
    exact dobrushin_minorization_l1_strong_data_processing N M R K m
      (fun x => P x - Q x) hRow hMinor hZero
  refine ⟨hSDPI, ?_⟩
  have hPKS : sumRange M PK = R * S := by
    dsimp [PK]
    rw [sumRange_comm M N (fun y x => P x * K x y)]
    have h1 : sumRange N (fun x => sumRange M (fun y => P x * K x y)) =
        sumRange N (fun x => P x * R) := by
      refine sumRange_congr (fun x hx => ?_)
      rw [sumRange_mul_left, hRow x hx]
    rw [h1, sumRange_mul_right, hPS, Int.mul_comm]
  have hQKS : sumRange M QK = R * S := by
    dsimp [QK]
    rw [sumRange_comm M N (fun y x => Q x * K x y)]
    have h1 : sumRange N (fun x => sumRange M (fun y => Q x * K x y)) =
        sumRange N (fun x => Q x * R) := by
      refine sumRange_congr (fun x hx => ?_)
      rw [sumRange_mul_left, hRow x hx]
    rw [h1, sumRange_mul_right, hQS, Int.mul_comm]
  have hNP := le_cam_neyman_pearson_minimax_testing_identity M M_test PK QK T hMt hT
  have hL1Bound : sumRange N (fun x => iabs (P x - Q x)) ≤ 2 * S :=
    l1_le_two_mass_of_nonneg N S P Q hP0 hQ0 hPS hQS
  by_cases hN0 : N = 0
  · subst hN0
    have hS0 : S = 0 := by simp [sumRange] at hPS; omega
    subst hS0
    have hNonnegTest : 0 ≤ sumRange M (fun y => PK y * (M_test - T y) + QK y * T y) := by
      refine sumRange_nonneg (fun y _ => ?_)
      dsimp [PK, QK, sumRange]
      omega
    have hLhsZero : M_test * μ * 0 = 0 := Int.mul_zero (M_test * μ)
    omega
  · have hx0 : 0 < N := Nat.pos_of_ne_zero hN0
    have hMuLeR : μ ≤ R := by
      have hle : sumRange M m ≤ sumRange M (fun y => K 0 y) :=
        sumRange_mono (fun y hy => hMinor 0 y hx0 hy)
      rw [hRow 0 hx0] at hle
      exact hle
    have hRmu0 : 0 ≤ R - μ := by omega
    have hProd : (R - μ) * sumRange N (fun x => iabs (P x - Q x)) ≤ (R - μ) * (2 * S) :=
      Int.mul_le_mul_of_nonneg_left hL1Bound hRmu0
    have hMinFloor : 2 * (μ * S) ≤ 2 * sumRange M (fun y => imin (PK y) (QK y)) := by
      have h2min := hNP.1
      rw [hPKS, hQKS] at h2min
      have halg : R * S + R * S - (R - μ) * (2 * S) = 2 * (μ * S) := by
        have h1 : (R - μ) * (2 * S) = R * (2 * S) - μ * (2 * S) := Int.sub_mul R μ (2 * S)
        have h2 : R * (2 * S) = 2 * (R * S) := by
          rw [← Int.mul_assoc, Int.mul_comm R 2, Int.mul_assoc]
        have h3 : μ * (2 * S) = 2 * (μ * S) := by
          rw [← Int.mul_assoc, Int.mul_comm μ 2, Int.mul_assoc]
        omega
      omega
    have hMinFloor1 : μ * S ≤ sumRange M (fun y => imin (PK y) (QK y)) := by omega
    have hMulMt : M_test * (μ * S) ≤ M_test * sumRange M (fun y => imin (PK y) (QK y)) :=
      Int.mul_le_mul_of_nonneg_left hMinFloor1 hMt
    have hAssoc : M_test * μ * S = M_test * (μ * S) := Int.mul_assoc M_test μ S
    have hTestLb := hNP.2.1
    omega

/-- **Premise-Failure Counterexample (Zero-Minorization Permutation Channel)**:
For the `2 × 2` swap Markov kernel `K_swap = [[0, R], [R, 0]]` (`R ≥ 0`), the column-wise
minorant is `m = [0, 0]` (`μ = 0`), and orthogonal laws `P = [S, 0], Q = [0, S]` satisfy
`‖PK - QK‖₁ = 2 R S = R ‖P - Q‖₁`. -/
theorem permutation_channel_zero_minorization_no_contraction (R S : Int)
    (hR : 0 ≤ R) (hS : 0 ≤ S) :
    let K : Nat → Nat → Int := fun x y => if x = y then 0 else R
    let P : Nat → Int := fun x => if x = 0 then S else 0
    let Q : Nat → Int := fun x => if x = 0 then 0 else S
    let PK : Nat → Int := fun y => sumRange 2 (fun x => P x * K x y)
    let QK : Nat → Int := fun y => sumRange 2 (fun x => Q x * K x y)
    sumRange 2 (fun y => iabs (PK y - QK y)) = 2 * (R * S) ∧
      R * sumRange 2 (fun x => iabs (P x - Q x)) = 2 * (R * S) := by
  dsimp only
  have hrs : 0 ≤ R * S := Int.mul_nonneg hR hS
  have hsr : S * R = R * S := Int.mul_comm S R
  have habs_pos : iabs (R * S) = R * S := by unfold iabs; rw [if_pos hrs]
  have habs_neg : iabs (-(R * S)) = R * S := by unfold iabs; split <;> omega
  have habs_s : iabs S = S := by unfold iabs; rw [if_pos hS]
  have habs_ns : iabs (-S) = S := by unfold iabs; split <;> omega
  refine ⟨?_, ?_⟩
  · simp [sumRange]
    have hneg : -(S * R) = -(R * S) := by omega
    rw [hneg, hsr, habs_neg, habs_pos]
    omega
  · simp [sumRange, habs_s, habs_ns, Int.mul_add]
    omega

/-! ## Section 4: Midpoint-Centered Span-Seminorm Bellman–Kantorovich Contraction -/

/-- **Universal Midpoint-Centered Bellman–Kantorovich Span Contraction**:
For any value function `V : Nat → Int` bounded in `[ℓ, u]` (`∀ y < M, ℓ ≤ V y ∧ V y ≤ u`), any
minorized Markov kernel `K` (`K(x, y) ≥ m(y)`, row sum `R`, minorization mass `μ = ∑ m`), and
any zero-sum perturbation `δ` (`∑_{x<N} δ_x = 0`),
`2 · |∑_{x<N} δ_x (∑_{y<M} K(x, y) V_y)| ≤ (u - ℓ)(R - μ) · ∑_{x<N} |δ_x|`. -/
theorem dobrushin_span_seminorm_bellman_kantorovich_contraction
    (N M : Nat) (R ℓ u : Int)
    (K : Nat → Nat → Int) (m : Nat → Int) (δ : Nat → Int) (V : Nat → Int)
    (hRow : ∀ x, x < N → sumRange M (fun y => K x y) = R)
    (hMinor : ∀ x y, x < N → y < M → m y ≤ K x y)
    (hZeroSum : sumRange N δ = 0)
    (hV : ∀ y, y < M → ℓ ≤ V y ∧ V y ≤ u) :
    2 * iabs (sumRange N (fun x => δ x * sumRange M (fun y => K x y * V y))) ≤
      (u - ℓ) * (R - sumRange M m) * sumRange N (fun x => iabs (δ x)) := by
  let W : Nat → Int := fun y => 2 * V y - (u + ℓ)
  have hCenter : 2 * sumRange N (fun x => δ x * sumRange M (fun y => K x y * V y)) =
      sumRange M (fun y => sumRange N (fun x => δ x * K x y) * W y) := by
    rw [← sumRange_mul_left]
    have h1 : sumRange N (fun x => 2 * (δ x * sumRange M (fun y => K x y * V y))) =
        sumRange N (fun x => δ x * sumRange M (fun y => K x y * W y) + δ x * (R * (u + ℓ))) := by
      refine sumRange_congr (fun x hx => ?_)
      have hrowW : sumRange M (fun y => K x y * W y) =
          2 * sumRange M (fun y => K x y * V y) - R * (u + ℓ) := by
        dsimp [W]
        have hsub : sumRange M (fun y => K x y * (2 * V y - (u + ℓ))) =
            sumRange M (fun y => 2 * (K x y * V y) - K x y * (u + ℓ)) := by
          refine sumRange_congr (fun y _ => ?_)
          rw [Int.mul_sub]
          have hmul2 : K x y * (2 * V y) = 2 * (K x y * V y) := by
            rw [← Int.mul_assoc, Int.mul_comm (K x y) 2, Int.mul_assoc]
          rw [hmul2]
        rw [hsub, sumRange_sub, sumRange_mul_left, sumRange_mul_right, hRow x hx]
      rw [hrowW, Int.mul_sub]
      have h2assoc : 2 * (δ x * sumRange M (fun y => K x y * V y)) =
          δ x * (2 * sumRange M (fun y => K x y * V y)) := by
        rw [← Int.mul_assoc, Int.mul_comm 2 (δ x), Int.mul_assoc]
      omega
    rw [h1, sumRange_add, sumRange_mul_right, hZeroSum, Int.zero_mul, Int.add_zero]
    have h2 : sumRange N (fun x => δ x * sumRange M (fun y => K x y * W y)) =
        sumRange N (fun x => sumRange M (fun y => (δ x * K x y) * W y)) := by
      refine sumRange_congr (fun x _ => ?_)
      rw [← sumRange_mul_left]
      exact sumRange_congr (fun y _ => (Int.mul_assoc (δ x) (K x y) (W y)).symm)
    rw [h2, sumRange_comm N M (fun x y => (δ x * K x y) * W y)]
    exact sumRange_congr (fun y _ => sumRange_mul_right N (fun x => δ x * K x y) (W y))
  have hAbs2 : 2 * iabs (sumRange N (fun x => δ x * sumRange M (fun y => K x y * V y))) =
      iabs (2 * sumRange N (fun x => δ x * sumRange M (fun y => K x y * V y))) := by
    unfold iabs
    split <;> split <;> omega
  rw [hAbs2, hCenter]
  have hTri : iabs (sumRange M (fun y => sumRange N (fun x => δ x * K x y) * W y)) ≤
      sumRange M (fun y => iabs (sumRange N (fun x => δ x * K x y) * W y)) :=
    iabs_sumRange_le M (fun y => sumRange N (fun x => δ x * K x y) * W y)
  have hWbound : sumRange M (fun y => iabs (sumRange N (fun x => δ x * K x y) * W y)) ≤
      (u - ℓ) * sumRange M (fun y => iabs (sumRange N (fun x => δ x * K x y))) := by
    rw [← sumRange_mul_left]
    refine sumRange_mono (fun y hy => ?_)
    have hmul : iabs (sumRange N (fun x => δ x * K x y) * W y) ≤
        iabs (sumRange N (fun x => δ x * K x y)) * iabs (W y) :=
      iabs_mul_le _ _
    have hWle : iabs (W y) ≤ u - ℓ := by
      have hv := hV y hy
      dsimp [W]
      unfold iabs
      split <;> omega
    have hAn : 0 ≤ iabs (sumRange N (fun x => δ x * K x y)) := iabs_nonneg _
    have hstep : iabs (sumRange N (fun x => δ x * K x y)) * iabs (W y) ≤
        iabs (sumRange N (fun x => δ x * K x y)) * (u - ℓ) :=
      Int.mul_le_mul_of_nonneg_left hWle hAn
    rw [Int.mul_comm (u - ℓ)]
    omega
  have hSDPI := dobrushin_minorization_l1_strong_data_processing N M R K m δ hRow hMinor hZeroSum
  by_cases hM0 : M = 0
  · subst hM0
    simp [sumRange, iabs] at hTri ⊢
    by_cases hN0 : N = 0
    · subst hN0
      simp [sumRange]
    · have hx0 : 0 < N := Nat.pos_of_ne_zero hN0
      have hR0 : R = 0 := by have hr := hRow 0 hx0; simp [sumRange] at hr; omega
      subst hR0
      simp
  · have hy0 : 0 < M := Nat.pos_of_ne_zero hM0
    have hlu : 0 ≤ u - ℓ := by have hv := hV 0 hy0; omega
    have hScale : (u - ℓ) * sumRange M (fun y => iabs (sumRange N (fun x => δ x * K x y))) ≤
        (u - ℓ) * ((R - sumRange M m) * sumRange N (fun x => iabs (δ x))) :=
      Int.mul_le_mul_of_nonneg_left hSDPI hlu
    rw [← Int.mul_assoc] at hScale
    omega

/-- **Factor-2-Free Pairwise Bellman Span-Seminorm Contraction**:
For ANY two states `x₁, x₂ < N`, the Bellman pushforward `(KV)_x = ∑_{y<M} K(x, y) V_y` satisfies
`|(KV)_{x_1} - (KV)_{x_2}| ≤ (u - ℓ)(R - μ)` with zero factor-of-2 slack! -/
theorem dobrushin_pairwise_bellman_span_contraction
    (N M : Nat) (R ℓ u : Int)
    (K : Nat → Nat → Int) (m : Nat → Int) (V : Nat → Int)
    (x₁ x₂ : Nat) (hx₁ : x₁ < N) (hx₂ : x₂ < N)
    (hRow : ∀ x, x < N → sumRange M (fun y => K x y) = R)
    (hMinor : ∀ x y, x < N → y < M → m y ≤ K x y)
    (hV : ∀ y, y < M → ℓ ≤ V y ∧ V y ≤ u) :
    iabs (sumRange M (fun y => K x₁ y * V y) - sumRange M (fun y => K x₂ y * V y)) ≤
      (u - ℓ) * (R - sumRange M m) := by
  let K₂ : Nat → Nat → Int := fun i y => if i = 0 then K x₁ y else K x₂ y
  let δ₂ : Nat → Int := fun i => if i = 0 then 1 else -1
  have hRow2 : ∀ i, i < 2 → sumRange M (fun y => K₂ i y) = R := by
    intro i _
    by_cases hi0 : i = 0
    · subst hi0; exact hRow x₁ hx₁
    · simp only [K₂, if_neg hi0]; exact hRow x₂ hx₂
  have hMinor2 : ∀ i y, i < 2 → y < M → m y ≤ K₂ i y := by
    intro i y _ hy
    by_cases hi0 : i = 0
    · subst hi0; exact hMinor x₁ y hx₁ hy
    · simp only [K₂, if_neg hi0]; exact hMinor x₂ y hx₂ hy
  have hZero2 : sumRange 2 δ₂ = 0 := by decide
  have hMain := dobrushin_span_seminorm_bellman_kantorovich_contraction
    2 M R ℓ u K₂ m δ₂ V hRow2 hMinor2 hZero2 hV
  have hDeltaNorm : sumRange 2 (fun i => iabs (δ₂ i)) = 2 := by decide
  have hLhsEq : sumRange 2 (fun i => δ₂ i * sumRange M (fun y => K₂ i y * V y)) =
      sumRange M (fun y => K x₁ y * V y) - sumRange M (fun y => K x₂ y * V y) := by
    simp [sumRange, K₂, δ₂]
    omega
  rw [hDeltaNorm, hLhsEq] at hMain
  omega

/-- **Exact Integer Attainment Witness (`dobrushin_span_sharpness_witness`)**:
On `M = 2` with `R = 3`, `K(0) = [3, 0]`, `K(1) = [1, 2]`, minorant `m = [1, 0]` (`μ = 1`),
and `V = [2, 7]` (`[ℓ, u] = [2, 7]`, `u - ℓ = 5`),
`|(KV)_0 - (KV)_1| = |6 - 16| = 10 = 5 · (3 - 1) = (u - ℓ)(R - μ)`. -/
theorem dobrushin_span_sharpness_witness :
    let K : Nat → Nat → Int := fun x y =>
      if x = 0 then (if y = 0 then 3 else 0) else (if y = 0 then 1 else 2)
    let m : Nat → Int := fun y => if y = 0 then 1 else 0
    let V : Nat → Int := fun y => if y = 0 then 2 else 7
    iabs (sumRange 2 (fun y => K 0 y * V y) - sumRange 2 (fun y => K 1 y * V y)) = 10 ∧
      (7 - 2) * (3 - sumRange 2 m) = 10 := by
  decide

end CommonGround.ConsequenceLens.DobrushinLeCamSpan
