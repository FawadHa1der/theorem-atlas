/-!
# Omnibus Multi-Calibration, Outcome Indistinguishability, Two-Stage Coreset Compression & Bregman L² Boosting Drop

Pure-core Lean 4.33.0 formalization (zero external dependencies, zero `sorry`) in
`02-universal-affine-query-compression`, uniting **Hebert-Johnson–Kim–Reingold–Rothblum
Multi-Calibration / Dwork–Roth–Vadhan Outcome Indistinguishability** directly with Common Ground's
**Folder `02` Connes–Carathéodory Universal Affine Query Compression** (`ObservableSpan.lean`,
`ApproximateAffineCoreset.lean`) and **Folder `03` Bregman / KL Pythagorean Projection**:

1. **Exact Omnibus Outcome-Indistinguishability Transfer (`omnibus_multicalibrated_affine_payoff_transfer`)**:
   If a predictor `p` is globally calibrated (`∑_i w_i (y_i - p_i) = 0`) and multi-calibrated across
   `K` subgroup-level observables `g_0, …, g_{K-1}` (`∑_i w_i g_r(i) (y_i - p_i) = 0`), then for
   **every** downstream decision rule or linear payoff `q(i) = c_0 + ∑_{r < K} a_r g_r(i)` in their
   affine span, the unknown true outcomes `y` and synthetic predictor `p` yield **identical**
   population payoffs:
   `∑_{i < N} w_i q(i) y_i = ∑_{i < N} w_i q(i) p_i`.

2. **Two-Stage Statistical Multi-Calibration + Geometric `(K+1)`-Coreset Certificate
   (`omnibus_surrogate_plus_coreset_error_decomposition` & `omnibus_surrogate_plus_coreset_natAbs_bound`)**:
   Composes statistical multi-calibration (`|∑_i w_i g_r(i)(y_i - p_i)| ≤ ε_r`) with Carathéodory
   sparse coreset compression (`|∑_i (w_i - w_core(i)) g_r(i) p_i| ≤ δ_r`), proving that evaluating
   any linear payoff `q_lin(i) = ∑_{r < K} a_r g_r(i)` on the **sparse synthetic coreset** `(w_core, p)`
   approximates the **full-population true-outcome expectation** `(w, y)` within
   `∑_{r < K} |a_r| · (ε_r + δ_r)`.

3. **Exact Integer-Scaled Bregman `L²` Calibration-Boosting Potential Drop
   (`multicalibration_bregman_l2_pythagorean_drop`)**:
   For any calibration violation `R = ∑_{i < N} w_i g(i) (y_i - p_i)` on subgroup `g` with energy
   `E = ∑_{i < N} w_i g(i)²`, the division-free residual update `p_scaled(i) = E · p_i + R · g(i)`
   satisfies the exact algebraic identity:
   `E² · ∑_i w_i (y_i - p_i)² - ∑_i w_i (E · y_i - (E · p_i + R · g(i)))² = E · R²`,
   certifying strictly positive potential drop `E · R² > 0` whenever `E > 0` and `R ≠ 0` (the exact
   `O(1 / α²)` termination mechanism of multi-calibration boosting!).

4. **Two Sharp Premise-Failure Counterexamples**:
   - `marginal_calibration_fails_xor_subgroup`: Global calibration (`∑ (2y_i - 2p_i) = 0` for
     `2y = (2, 0, 0, 2)`, `2p = (1, 1, 1, 1)`) still suffers `100%` vs. `50%` bias (`residual = 2 ≠ 0`)
     on the structured subgroup `g = (1, 0, 0, 1)`.
   - `multicalibration_fails_quadratic_variance_query`: Cell-wise exact calibration (`2y = (2, 0)` vs.
     `2p = (1, 1)`) preserves every linear-in-`y` payoff yet fails on nonlinear quadratic outcome
     moments (`∑ (2y_i)² = 4 ≠ 2 = ∑ (2p_i)²`).
-/

namespace CommonGround.ObservableSpan.MultiCalibrationCoreset

/-- Finite integer sum `∑_{i < n} f i`. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

/-- Finite natural-number sum `∑_{i < n} f i` for `natAbs` error certificates. -/
def sumNatRange : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumNatRange n f + f n

theorem sumRange_zero (n : Nat) :
    sumRange n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumRange, ih]

theorem sumRange_congr (n : Nat) (f h : Nat → Int)
    (heq : ∀ i : Nat, i < n → f i = h i) :
    sumRange n f = sumRange n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hPrev : sumRange n f = sumRange n h := ih (fun i hi => heq i (by omega))
    have hLast : f n = h n := heq n (by omega)
    simp only [sumRange, hPrev, hLast]

theorem sumRange_eq_zero_of_forall_zero (n : Nat) (f : Nat → Int)
    (hz : ∀ i : Nat, i < n → f i = 0) :
    sumRange n f = 0 := by
  rw [sumRange_congr n f (fun _ => 0) hz]
  exact sumRange_zero n

theorem sumRange_add (n : Nat) (f h : Nat → Int) :
    sumRange n (fun i => f i + h i) = sumRange n f + sumRange n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumRange, ih]
    omega

theorem sumRange_sub (n : Nat) (f h : Nat → Int) :
    sumRange n (fun i => f i - h i) = sumRange n f - sumRange n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumRange, ih]
    omega

theorem sumRange_mul_const_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => simp only [sumRange, ih, Int.mul_add]

theorem sumRange_mul_const_right (n : Nat) (f : Nat → Int) (c : Int) :
    sumRange n (fun i => f i * c) = (sumRange n f) * c := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => simp only [sumRange, ih, Int.add_mul]

theorem sumRange_comm (n m : Nat) (F : Nat → Nat → Int) :
    sumRange n (fun i => sumRange m (fun j => F i j)) =
      sumRange m (fun j => sumRange n (fun i => F i j)) := by
  induction n with
  | zero =>
    simp only [sumRange]
    exact (sumRange_zero m).symm
  | succ n ihn =>
    simp only [sumRange]
    rw [ihn, ← sumRange_add]

/-- Linear span of `K` subgroup/level-set features `g 0, …, g (K - 1)`. -/
def linearFeatureSpan (K : Nat) (a : Nat → Int) (g : Nat → Nat → Int) (i : Nat) : Int :=
  sumRange K (fun r => a r * g r i)

/-- Affine span `c0 + ∑_{r < K} a_r g_r(i)` of `K` subgroup/level-set features. -/
def affineFeatureSpan (K : Nat) (c0 : Int) (a : Nat → Int) (g : Nat → Nat → Int) (i : Nat) : Int :=
  c0 + linearFeatureSpan K a g i

theorem weighted_linearFeatureSpan_swap (N K : Nat) (w d : Nat → Int)
    (a : Nat → Int) (g : Nat → Nat → Int) :
    sumRange N (fun i => w i * linearFeatureSpan K a g i * d i) =
      sumRange K (fun r => a r * sumRange N (fun i => w i * g r i * d i)) := by
  have h1 :
      sumRange N (fun i => w i * linearFeatureSpan K a g i * d i) =
        sumRange N (fun i => sumRange K (fun r => a r * (w i * g r i * d i))) := by
    apply sumRange_congr
    intro i _hi
    unfold linearFeatureSpan
    rw [← sumRange_mul_const_left, ← sumRange_mul_const_right]
    apply sumRange_congr
    intro r _hr
    ac_rfl
  rw [h1, sumRange_comm N K]
  apply sumRange_congr
  intro r _hr
  exact sumRange_mul_const_left N (a r) (fun i => w i * g r i * d i)

/-- **Theorem 1 (Omnibus Multi-Calibration / Outcome-Indistinguishability Transfer)**:
If `p` is globally calibrated (`∑_{i < N} w_i (y_i - p_i) = 0`) and multi-calibrated across `K`
subgroup-level features `g_0, …, g_{K-1}` (`∀ r < K, ∑_{i < N} w_i g_r(i) (y_i - p_i) = 0`), then
for **every** affine downstream query/payoff `q(i) = c0 + ∑_{r < K} a_r g_r(i)`, the true outcome
expectation equals the synthetic predictor expectation identically. -/
theorem omnibus_multicalibrated_affine_payoff_transfer
    (N K : Nat) (w y p : Nat → Int) (c0 : Int) (a : Nat → Int) (g : Nat → Nat → Int)
    (hGlobal : sumRange N (fun i => w i * (y i - p i)) = 0)
    (hMultiCal : ∀ r : Nat, r < K → sumRange N (fun i => w i * g r i * (y i - p i)) = 0) :
    sumRange N (fun i => w i * affineFeatureSpan K c0 a g i * y i) =
      sumRange N (fun i => w i * affineFeatureSpan K c0 a g i * p i) := by
  have hDiff :
      sumRange N (fun i => w i * affineFeatureSpan K c0 a g i * y i) -
        sumRange N (fun i => w i * affineFeatureSpan K c0 a g i * p i) =
      c0 * sumRange N (fun i => w i * (y i - p i)) +
        sumRange K (fun r => a r * sumRange N (fun i => w i * g r i * (y i - p i))) := by
    rw [← sumRange_sub]
    have hPoint :
        sumRange N (fun i =>
          w i * affineFeatureSpan K c0 a g i * y i - w i * affineFeatureSpan K c0 a g i * p i) =
        sumRange N (fun i =>
          c0 * (w i * (y i - p i)) + w i * linearFeatureSpan K a g i * (y i - p i)) := by
      apply sumRange_congr
      intro i _hi
      unfold affineFeatureSpan
      have e1 :
          w i * (c0 + linearFeatureSpan K a g i) * y i -
            w i * (c0 + linearFeatureSpan K a g i) * p i =
          w i * (c0 + linearFeatureSpan K a g i) * (y i - p i) := by
        rw [Int.mul_sub]
      rw [e1, Int.mul_add, Int.add_mul]
      have e2 : w i * c0 * (y i - p i) = c0 * (w i * (y i - p i)) := by ac_rfl
      rw [e2]
    rw [hPoint, sumRange_add, sumRange_mul_const_left, weighted_linearFeatureSpan_swap]
  have hSumZero :
      sumRange K (fun r => a r * sumRange N (fun i => w i * g r i * (y i - p i))) = 0 := by
    apply sumRange_eq_zero_of_forall_zero
    intro r hr
    rw [hMultiCal r hr, Int.mul_zero]
  rw [hGlobal, hSumZero] at hDiff
  omega

/-- **Theorem 2a (Two-Stage Surrogate + Carathéodory Coreset Error Decomposition)**:
Decomposes the difference between the **full-population true-outcome payoff** `(w, y)` and the
**sparse Carathéodory coreset synthetic payoff** `(wCore, p)` into:
1. Statistical multi-calibration residuals `∑_i w_i g_r(i) (y_i - p_i)`, plus
2. Geometric coreset moment-matching residuals `∑_i (w_i - wCore_i) g_r(i) p_i`. -/
theorem omnibus_surrogate_plus_coreset_error_decomposition
    (N K : Nat) (w wCore y p : Nat → Int) (a : Nat → Int) (g : Nat → Nat → Int) :
    sumRange N (fun i => w i * linearFeatureSpan K a g i * y i) -
      sumRange N (fun i => wCore i * linearFeatureSpan K a g i * p i) =
    sumRange K (fun r => a r * sumRange N (fun i => w i * g r i * (y i - p i))) +
      sumRange K (fun r => a r * sumRange N (fun i => (w i - wCore i) * g r i * p i)) := by
  have hSplit :
      sumRange N (fun i => w i * linearFeatureSpan K a g i * y i) -
        sumRange N (fun i => wCore i * linearFeatureSpan K a g i * p i) =
      (sumRange N (fun i => w i * linearFeatureSpan K a g i * y i) -
        sumRange N (fun i => w i * linearFeatureSpan K a g i * p i)) +
      (sumRange N (fun i => w i * linearFeatureSpan K a g i * p i) -
        sumRange N (fun i => wCore i * linearFeatureSpan K a g i * p i)) := by
    omega
  rw [hSplit]
  have hStage1 :
      sumRange N (fun i => w i * linearFeatureSpan K a g i * y i) -
        sumRange N (fun i => w i * linearFeatureSpan K a g i * p i) =
      sumRange N (fun i => w i * linearFeatureSpan K a g i * (y i - p i)) := by
    rw [← sumRange_sub]
    apply sumRange_congr
    intro i _hi
    rw [Int.mul_sub]
  have hStage2 :
      sumRange N (fun i => w i * linearFeatureSpan K a g i * p i) -
        sumRange N (fun i => wCore i * linearFeatureSpan K a g i * p i) =
      sumRange N (fun i => (w i - wCore i) * linearFeatureSpan K a g i * p i) := by
    rw [← sumRange_sub]
    apply sumRange_congr
    intro i _hi
    rw [Int.sub_mul, Int.sub_mul]
  rw [hStage1, hStage2,
    weighted_linearFeatureSpan_swap N K w (fun i => y i - p i) a g,
    weighted_linearFeatureSpan_swap N K (fun i => w i - wCore i) p a g]

theorem natAbs_sumRange_le (K : Nat) (F : Nat → Int) (B : Nat → Nat)
    (hB : ∀ r : Nat, r < K → (F r).natAbs ≤ B r) :
    (sumRange K F).natAbs ≤ sumNatRange K B := by
  induction K with
  | zero =>
    simp [sumRange, sumNatRange]
  | succ K ih =>
    simp only [sumRange, sumNatRange]
    have hTri : (sumRange K F + F K).natAbs ≤ (sumRange K F).natAbs + (F K).natAbs :=
      Int.natAbs_add_le (sumRange K F) (F K)
    have hPrev : (sumRange K F).natAbs ≤ sumNatRange K B :=
      ih (fun r hr => hB r (by omega))
    have hLast : (F K).natAbs ≤ B K := hB K (by omega)
    omega

/-- **Theorem 2b (Two-Stage Multi-Calibration + Coreset Quantitative `natAbs` Bound)**:
If `p` is `eps r`-multi-calibrated against `y` on feature `g r` and `wCore` matches the `g r · p`
moments of `w` within `delta r`, then the sparse synthetic coreset approximates every linear
downstream payoff `linearFeatureSpan K a g` within `∑_{r < K} |a_r| · (eps_r + delta_r)`. -/
theorem omnibus_surrogate_plus_coreset_natAbs_bound
    (N K : Nat) (w wCore y p : Nat → Int) (a : Nat → Int) (g : Nat → Nat → Int)
    (eps delta : Nat → Nat)
    (hCal : ∀ r : Nat, r < K → (sumRange N (fun i => w i * g r i * (y i - p i))).natAbs ≤ eps r)
    (hCore : ∀ r : Nat, r < K → (sumRange N (fun i => (w i - wCore i) * g r i * p i)).natAbs ≤ delta r) :
    (sumRange N (fun i => w i * linearFeatureSpan K a g i * y i) -
      sumRange N (fun i => wCore i * linearFeatureSpan K a g i * p i)).natAbs ≤
    sumNatRange K (fun r => (a r).natAbs * (eps r + delta r)) := by
  rw [omnibus_surrogate_plus_coreset_error_decomposition, ← sumRange_add]
  apply natAbs_sumRange_le
  intro r hr
  have hFactor :
      a r * sumRange N (fun i => w i * g r i * (y i - p i)) +
        a r * sumRange N (fun i => (w i - wCore i) * g r i * p i) =
      a r * (sumRange N (fun i => w i * g r i * (y i - p i)) +
        sumRange N (fun i => (w i - wCore i) * g r i * p i)) := by
    rw [Int.mul_add]
  rw [hFactor, Int.natAbs_mul]
  have hTri :=
    Int.natAbs_add_le
      (sumRange N (fun i => w i * g r i * (y i - p i)))
      (sumRange N (fun i => (w i - wCore i) * g r i * p i))
  have hc := hCal r hr
  have hd := hCore r hr
  have hSumLe :
      (sumRange N (fun i => w i * g r i * (y i - p i)) +
        sumRange N (fun i => (w i - wCore i) * g r i * p i)).natAbs ≤ eps r + delta r := by
    omega
  exact Nat.mul_le_mul_left (a r).natAbs hSumLe

theorem sq_pos_of_ne_zero (z : Int) (hz : z ≠ 0) : 0 < z * z := by
  rcases Int.lt_trichotomy z 0 with hn | rfl | hp
  · exact Int.mul_pos_of_neg_of_neg hn hn
  · contradiction
  · exact Int.mul_pos hp hp

theorem sq_diff_ring (A B : Int) :
    (A - B) * (A - B) = A * A - 2 * (A * B) + B * B := by
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm B A]
  omega

theorem bregman_pointwise_ring (E R w d g : Int) :
    E * E * (w * (d * d)) - w * ((E * d - R * g) * (E * d - R * g)) =
      (2 * E * R) * (w * g * d) - (R * R) * (w * (g * g)) := by
  rw [sq_diff_ring (E * d) (R * g)]
  have m1 : (E * d) * (E * d) = (E * E) * (d * d) := by ac_rfl
  have m2 : 2 * ((E * d) * (R * g)) = (2 * E * R) * (g * d) := by ac_rfl
  have m3 : (R * g) * (R * g) = (R * R) * (g * g) := by ac_rfl
  rw [m1, m2, m3, Int.mul_add, Int.mul_sub]
  have w1 : E * E * (w * (d * d)) = w * ((E * E) * (d * d)) := by ac_rfl
  have w2 : w * ((2 * E * R) * (g * d)) = (2 * E * R) * (w * g * d) := by ac_rfl
  have w3 : w * ((R * R) * (g * g)) = (R * R) * (w * (g * g)) := by ac_rfl
  rw [w1, w2, w3]
  omega

theorem bregman_l2_step_identity
    (N : Nat) (w y p g : Nat → Int) (R E : Int)
    (hR : sumRange N (fun i => w i * g i * (y i - p i)) = R)
    (hE : sumRange N (fun i => w i * (g i * g i)) = E) :
    E * E * sumRange N (fun i => w i * ((y i - p i) * (y i - p i))) -
      sumRange N (fun i =>
        w i * ((E * y i - (E * p i + R * g i)) * (E * y i - (E * p i + R * g i)))) =
      E * (R * R) := by
  rw [← sumRange_mul_const_left, ← sumRange_sub]
  have hPoint :
      sumRange N (fun i =>
        E * E * (w i * ((y i - p i) * (y i - p i))) -
          w i * ((E * y i - (E * p i + R * g i)) * (E * y i - (E * p i + R * g i)))) =
      sumRange N (fun i =>
        (2 * E * R) * (w i * g i * (y i - p i)) - (R * R) * (w i * (g i * g i))) := by
    apply sumRange_congr
    intro i _hi
    have hRewrite : E * y i - (E * p i + R * g i) = E * (y i - p i) - R * g i := by
      rw [Int.mul_sub]
      omega
    rw [hRewrite]
    exact bregman_pointwise_ring E R (w i) (y i - p i) (g i)
  rw [hPoint, sumRange_sub, sumRange_mul_const_left, sumRange_mul_const_left, hR, hE]
  have hComm : R * R * E = E * (R * R) := by ac_rfl
  have hTwo : 2 * E * R * R = 2 * (E * (R * R)) := by ac_rfl
  rw [hComm, hTwo]
  omega

/-- **Theorem 3 (Division-Free Bregman `L²` Multi-Calibration Boosting Potential Drop)**:
Let `R = ∑_{i < N} w_i g(i) (y_i - p_i)` be the subgroup calibration residual and
`E = ∑_{i < N} w_i g(i)²` be the subgroup second-moment energy. Updating `p` via
`p_scaled(i) = E · p_i + R · g(i)` yields the **exact Pythagorean `L²` potential drop**:
`E² · ∑_i w_i (y_i - p_i)² - ∑_i w_i (E y_i - (E p_i + R g(i)))² = E · R²`,
which is **strictly positive (`> 0`)** whenever `0 < E` and `R ≠ 0`! -/
theorem multicalibration_bregman_l2_pythagorean_drop
    (N : Nat) (w y p g : Nat → Int) :
    let R := sumRange N (fun i => w i * g i * (y i - p i))
    let E := sumRange N (fun i => w i * (g i * g i))
    (E * E * sumRange N (fun i => w i * ((y i - p i) * (y i - p i))) -
      sumRange N (fun i =>
        w i * ((E * y i - (E * p i + R * g i)) * (E * y i - (E * p i + R * g i)))) =
      E * (R * R)) ∧
    (0 < E → R ≠ 0 → 0 < E * (R * R)) := by
  dsimp only
  refine ⟨bregman_l2_step_identity N w y p g _ _ rfl rfl, ?_⟩
  intro hE hR
  exact Int.mul_pos hE (sq_pos_of_ne_zero _ hR)

/-- **Premise-Failure Counterexample 1 (Marginal Calibration Fails on Structured Subgroups)**:
On `N = 4` uniform points (`w ≡ 1`), scaled true outcomes `twoY = (2, 0, 0, 2)` and constant
predictor `twoP = (1, 1, 1, 1)` are **perfectly globally calibrated** (`∑_{i < 4} (twoY_i - twoP_i) = 0`),
yet on subgroup `g = (1, 0, 0, 1)` have calibration residual `2 ≠ 0` (`100%` true outcome rate vs.
`50%` predicted rate!). -/
theorem marginal_calibration_fails_xor_subgroup :
    let twoY : Nat → Int := fun i => if i = 0 ∨ i = 3 then 2 else 0
    let twoP : Nat → Int := fun _ => 1
    let g : Nat → Int := fun i => if i = 0 ∨ i = 3 then 1 else 0
    (sumRange 4 (fun i => twoY i - twoP i) = 0) ∧
    (sumRange 4 (fun i => g i * (twoY i - twoP i)) = 2) ∧
    (sumRange 4 (fun i => g i * twoY i) ≠ sumRange 4 (fun i => g i * twoP i)) := by
  dsimp only
  simp [sumRange]

/-- **Premise-Failure Counterexample 2 (Multi-Calibration Fails on Nonlinear Quadratic Outcome Moments)**:
On a homogeneous 2-point cell (`N = 2`), `twoY = (2, 0)` and `twoP = (1, 1)` are **exact cell-calibrated**
(`∑_{i < 2} (twoY_i - twoP_i) = 0`), matching every cell-constant linear-in-`y` query, yet disagree on
the nonlinear squared-outcome moment `∑_{i < 2} (twoY_i)² = 4 ≠ 2 = ∑_{i < 2} (twoP_i)²`! -/
theorem multicalibration_fails_quadratic_variance_query :
    let twoY : Nat → Int := fun i => if i = 0 then 2 else 0
    let twoP : Nat → Int := fun _ => 1
    (sumRange 2 (fun i => twoY i - twoP i) = 0) ∧
    (sumRange 2 (fun i => twoY i * twoY i) = 4) ∧
    (sumRange 2 (fun i => twoP i * twoP i) = 2) ∧
    (sumRange 2 (fun i => twoY i * twoY i) ≠ sumRange 2 (fun i => twoP i * twoP i)) := by
  dsimp only
  simp [sumRange]

end CommonGround.ObservableSpan.MultiCalibrationCoreset
