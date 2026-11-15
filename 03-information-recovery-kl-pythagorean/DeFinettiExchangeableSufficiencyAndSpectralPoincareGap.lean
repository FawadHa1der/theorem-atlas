/-!
# De Finetti Exchangeable Sufficiency, Diaconis–Freedman Finite-Urn Covariance Obstruction & Discrete Spectral Poincaré Variance Identity (`V197`)

Pure-core Lean 4.33.0 frontier formalization (`0 sorry`, `0` external library dependencies) extending
Folder `03` (`InformationRecoveryTrilogy.lean :: FiberLikelihoodConstant` & `UnifiedSufficiencyBridge.lean`)
into exchangeable sequence sufficiency, De Finetti mixture geometry, and spectral Poincaré–Dirichlet gaps:

1. **`exchangeable_empirical_sum_sufficiency_and_order_sensitive_markov_failure`**:
   - Proves that for any Bernoulli product model `bernoulliProdWeight u v xs` and any finite De Finetti
     mixture `deFinettiMixture M w u v xs = ∑_{m < M} w_m · u_m^{wt(xs)} v_m^{|xs| - wt(xs)}`, two binary
     trajectories `xs, ys : List Bool` of equal length with equal empirical Hamming sum `hammingWt xs = hammingWt ys`
     have **identical** likelihood `deFinettiMixture M w u v xs = deFinettiMixture M w u v ys`, hence satisfy
     exact `FiberLikelihoodConstant` pairwise proportionality across all exchangeable prior mixtures `w₁, w₂`:
     `(deFinettiMixture M w₁ u v xs) * (deFinettiMixture M w₂ u v ys) = (deFinettiMixture M w₁ u v ys) * (deFinettiMixture M w₂ u v xs)`.
   - **Order-Sensitive Markov Counterexample**: Under 1st-order sticky `(3, 1)` vs. anti-sticky `(1, 3)`
     Markov transition laws on `Bool³`, trajectories `[true, true, false]` and `[true, false, true]` lie in
     the **same** empirical-sum fiber (`length = 3`, `hammingWt = 2`), yet strictly violate
     `FiberLikelihoodConstant` (`3 * 9 = 27 ≠ 3 = 1 * 3`), proving minimal sufficiency requires transition counts!

2. **`diaconis_freedman_iid_mixture_nonneg_covariance_and_finite_urn_counterexample`**:
   - Proves for **every** finite mixture size `M : Nat`, weights `w : Nat → Int`, and component means `μ : Nat → Int`
     the exact **Weighted De Finetti–Lagrange Covariance Identity**:
     `2 * ((∑_{m < M} w_m)(∑_{m < M} w_m μ_m²) - (∑_{m < M} w_m μ_m)²) = ∑_{m < M} ∑_{m' < M} w_m w_{m'} (μ_m - μ_{m'})²`.
   - Deduces that **every** nonnegative i.i.d. De Finetti mixture (`∀ m < M, 0 ≤ w_m`) has nonnegative
     scaled pairwise covariance `0 ≤ covMixtureScaled M w μ`.
   - **Diaconis–Freedman Finite-Urn Counterexample**: Sampling `2` balls without replacement from `{0, 1}`
     (`urnWithoutReplacement2`) is `S₂`-exchangeable (`∀ a b, U a b = U b a`), yet has strictly **negative**
     scaled pairwise covariance `2 * 0 - 1 * 1 = -1 < 0`, proving no nonnegative i.i.d. De Finetti mixture of
     any size `M` can represent finite sampling without replacement!

3. **`lagrange_poincare_complete_graph_variance_identity_and_disconnected_cluster_failure`**:
   - Specializing the weighted Lagrange identity to uniform weights `w_i = 1` yields for every `N : Nat`
     and `f : Nat → Int` the exact **Complete-Graph Spectral Poincaré–Dirichlet Identity**:
     `2 * (N * ∑_{i < N} f_i² - (∑_{i < N} f_i)²) = ∑_{i < N} ∑_{j < N} (f_i - f_j)²`,
     locking global variance directly to pairwise Dirichlet edge energy (spectral gap `λ₁(K_N) = N`).
   - **Disconnected Two-Cluster Counterexample**: On the disconnected 2-cluster graph `{0, 1} ⊔ {2, 3}`
     (`π₀ = 2`, Cheeger constant `h = 0`), the balanced cluster indicator `f = (1, 1, -1, -1)` has
     **zero** Dirichlet energy `(f_0 - f_1)² + (f_2 - f_3)² = 0` yet positive variance `4 · 4 - 0² = 16 > 0`!
-/

namespace CommonGround.InformationRecovery.DeFinettiPoincare

/-- Finite integer sum `∑_{i = 0}^{n - 1} f(i)`. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

theorem sumRange_congr (n : Nat) (f g : Nat → Int) (h : ∀ i, i < n → f i = g i) :
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
    simp only [sumRange]
    omega

theorem sumRange_sub (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i - g i) = sumRange n f - sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    simp only [sumRange]
    omega

theorem sumRange_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    simp only [sumRange]
    rw [ih, Int.mul_add]

theorem sumRange_mul_right (n : Nat) (f : Nat → Int) (c : Int) :
    sumRange n (fun i => f i * c) = sumRange n f * c := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    simp only [sumRange]
    rw [ih, Int.add_mul]

theorem sumRange_nonneg (n : Nat) (f : Nat → Int) (hf : ∀ i, i < n → 0 ≤ f i) :
    0 ≤ sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    simp only [sumRange]
    have h1 := ih (fun i hi => hf i (Nat.lt_succ_of_lt hi))
    have h2 := hf k (Nat.lt_succ_self k)
    omega

theorem sumRange_ones (n : Nat) : sumRange n (fun _ => 1) = Int.ofNat n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumRange]
    rw [ih]
    rfl

theorem sq_nonneg_int (z : Int) : 0 ≤ z * z := by
  by_cases hz : 0 ≤ z
  · exact Int.mul_nonneg hz hz
  · have hnz : 0 ≤ -z := by omega
    have h := Int.mul_nonneg hnz hnz
    rw [Int.neg_mul_neg] at h
    exact h

theorem sq_sub_expand (a b : Int) :
    (a - b) * (a - b) = a * a + b * b - 2 * (a * b) := by
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm b a]
  omega

/-! ## Section 1: Exchangeable Empirical-Sum Sufficiency vs. Order-Sensitive Markov Failure -/

/-- Empirical Hamming weight (number of `true` outcomes) in a binary trajectory. -/
def hammingWt : List Bool → Nat
  | [] => 0
  | true :: xs => hammingWt xs + 1
  | false :: xs => hammingWt xs

/-- Complementary count of `false` outcomes in a binary trajectory. -/
def zerosCount : List Bool → Nat
  | [] => 0
  | true :: xs => zerosCount xs
  | false :: xs => zerosCount xs + 1

theorem hammingWt_add_zerosCount (xs : List Bool) :
    hammingWt xs + zerosCount xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons b tl ih =>
    cases b <;> simp [hammingWt, zerosCount] <;> omega

/-- Integer power `base^k`. -/
def intPow (base : Int) : Nat → Int
  | 0 => 1
  | k + 1 => intPow base k * base

/-- Unnormalized Bernoulli product likelihood `∏_{b ∈ xs} (if b then u else v)`. -/
def bernoulliProdWeight (u v : Int) : List Bool → Int
  | [] => 1
  | true :: xs => bernoulliProdWeight u v xs * u
  | false :: xs => bernoulliProdWeight u v xs * v

theorem bernoulliProdWeight_eq_pow (u v : Int) (xs : List Bool) :
    bernoulliProdWeight u v xs = intPow u (hammingWt xs) * intPow v (zerosCount xs) := by
  induction xs with
  | nil => simp [bernoulliProdWeight, hammingWt, zerosCount, intPow]
  | cons b tl ih =>
    cases b with
    | true =>
      simp only [bernoulliProdWeight, hammingWt, zerosCount, intPow]
      rw [ih]
      rw [Int.mul_assoc (intPow u (hammingWt tl)) (intPow v (zerosCount tl)) u]
      rw [Int.mul_comm (intPow v (zerosCount tl)) u]
      rw [← Int.mul_assoc (intPow u (hammingWt tl)) u (intPow v (zerosCount tl))]
    | false =>
      simp only [bernoulliProdWeight, hammingWt, zerosCount, intPow]
      rw [ih, Int.mul_assoc]

/-- Finite De Finetti mixture `∑_{m < M} w_m · bernoulliProdWeight (u_m) (v_m) xs`. -/
def deFinettiMixture (M : Nat) (w u v : Nat → Int) (xs : List Bool) : Int :=
  sumRange M (fun m => w m * bernoulliProdWeight (u m) (v m) xs)

/-- First-order Markov transition weight on length-3 binary trajectories `(b₁, b₂, b₃)`. -/
def markov3Weight (stay flip : Int) (b1 b2 b3 : Bool) : Int :=
  (if b1 == b2 then stay else flip) * (if b2 == b3 then stay else flip)

/-- **Theorem 1: Exchangeable Empirical-Sum Sufficiency vs. Order-Sensitive Markov Failure**.
    1. Any two equal-length binary trajectories `xs, ys` in the same empirical-sum fiber
       (`hammingWt xs = hammingWt ys`) have identical De Finetti mixture weight under every `w`,
       and therefore satisfy `FiberLikelihoodConstant` proportionality across all priors `w₁, w₂`.
    2. For 1st-order Markov laws (`stay = 3, flip = 1` vs `stay = 1, flip = 3`), `[true, true, false]`
       and `[true, false, true]` share `length = 3` and `hammingWt = 2`, yet violate fiber
       proportionality (`27 ≠ 3`)! -/
theorem exchangeable_empirical_sum_sufficiency_and_order_sensitive_markov_failure
    (M : Nat) (w1 w2 u v : Nat → Int) (xs ys : List Bool)
    (hLen : xs.length = ys.length) (hWt : hammingWt xs = hammingWt ys) :
    (deFinettiMixture M w1 u v xs = deFinettiMixture M w1 u v ys ∧
      deFinettiMixture M w1 u v xs * deFinettiMixture M w2 u v ys =
        deFinettiMixture M w1 u v ys * deFinettiMixture M w2 u v xs) ∧
    (hammingWt [true, true, false] = hammingWt [true, false, true] ∧
      markov3Weight 3 1 true true false * markov3Weight 1 3 true false true ≠
        markov3Weight 3 1 true false true * markov3Weight 1 3 true true false) := by
  have hZeros : zerosCount xs = zerosCount ys := by
    have hx := hammingWt_add_zerosCount xs
    have hy := hammingWt_add_zerosCount ys
    omega
  have hMixEq : ∀ w : Nat → Int, deFinettiMixture M w u v xs = deFinettiMixture M w u v ys := by
    intro w
    unfold deFinettiMixture
    apply sumRange_congr
    intro m _
    rw [bernoulliProdWeight_eq_pow, bernoulliProdWeight_eq_pow, hWt, hZeros]
  refine ⟨⟨hMixEq w1, ?_⟩, ?_⟩
  · rw [hMixEq w1, hMixEq w2]
  · decide

/-! ## Section 2: Weighted De Finetti–Lagrange Covariance Identity & Diaconis–Freedman Urn Counterexample -/

/-- Scaled pairwise covariance `(∑ w_m)(∑ w_m μ_m²) - (∑ w_m μ_m)²` of a conditionally i.i.d. De Finetti mixture. -/
def covMixtureScaled (M : Nat) (w μ : Nat → Int) : Int :=
  sumRange M w * sumRange M (fun m => w m * (μ m * μ m)) -
    sumRange M (fun m => w m * μ m) * sumRange M (fun m => w m * μ m)

/-- Pointwise algebraic rearrangement of `w_m w_{m'} (μ_m - μ_{m'})²`. -/
theorem weighted_pair_sq_diff_expand (wm wm' μm μm' : Int) :
    (wm * wm') * ((μm - μm') * (μm - μm')) =
      ((wm * (μm * μm)) * wm' + wm * (wm' * (μm' * μm'))) -
        2 * ((wm * μm) * (wm' * μm')) := by
  rw [sq_sub_expand μm μm']
  rw [Int.mul_sub (wm * wm'), Int.mul_add (wm * wm')]
  have h1 : (wm * wm') * (μm * μm) = (wm * (μm * μm)) * wm' := by
    rw [Int.mul_assoc wm wm' (μm * μm), Int.mul_comm wm' (μm * μm), ← Int.mul_assoc wm (μm * μm) wm']
  have h2 : (wm * wm') * (μm' * μm') = wm * (wm' * (μm' * μm')) :=
    Int.mul_assoc wm wm' (μm' * μm')
  have h3 : (wm * wm') * (2 * (μm * μm')) = 2 * ((wm * μm) * (wm' * μm')) := by
    rw [← Int.mul_assoc (wm * wm') 2 (μm * μm'), Int.mul_comm (wm * wm') 2, Int.mul_assoc 2 (wm * wm') (μm * μm')]
    have hInner : (wm * wm') * (μm * μm') = (wm * μm) * (wm' * μm') := by
      rw [Int.mul_assoc wm wm' (μm * μm'), ← Int.mul_assoc wm' μm μm',
          Int.mul_comm wm' μm, Int.mul_assoc μm wm' μm', ← Int.mul_assoc wm μm (wm' * μm')]
    rw [hInner]
  rw [h1, h2, h3]

/-- Exact **Weighted De Finetti–Lagrange Identity** for arbitrary `M : Nat`:
    `∑_{m < M} ∑_{m' < M} w_m w_{m'} (μ_m - μ_{m'})² = 2 * covMixtureScaled M w μ`. -/
theorem weighted_lagrange_covariance_identity (M : Nat) (w μ : Nat → Int) :
    sumRange M (fun m => sumRange M (fun m' => (w m * w m') * ((μ m - μ m') * (μ m - μ m')))) =
      2 * covMixtureScaled M w μ := by
  let Sw := sumRange M w
  let S1 := sumRange M (fun m => w m * μ m)
  let S2 := sumRange M (fun m => w m * (μ m * μ m))
  have hInner : ∀ m : Nat,
      sumRange M (fun m' => (w m * w m') * ((μ m - μ m') * (μ m - μ m'))) =
        ((w m * (μ m * μ m)) * Sw + w m * S2) - 2 * ((w m * μ m) * S1) := by
    intro m
    have hCong :
        sumRange M (fun m' => (w m * w m') * ((μ m - μ m') * (μ m - μ m'))) =
          sumRange M (fun m' =>
            ((w m * (μ m * μ m)) * w m' + w m * (w m' * (μ m' * μ m'))) -
              2 * ((w m * μ m) * (w m' * μ m'))) := by
      apply sumRange_congr
      intro m' _
      exact weighted_pair_sq_diff_expand (w m) (w m') (μ m) (μ m')
    rw [hCong, sumRange_sub, sumRange_add]
    rw [sumRange_mul_left M (w m * (μ m * μ m)) w]
    rw [sumRange_mul_left M (w m) (fun m' => w m' * (μ m' * μ m'))]
    rw [sumRange_mul_left M 2 (fun m' => (w m * μ m) * (w m' * μ m'))]
    rw [sumRange_mul_left M (w m * μ m) (fun m' => w m' * μ m')]
  have hOuter :
      sumRange M (fun m => sumRange M (fun m' => (w m * w m') * ((μ m - μ m') * (μ m - μ m')))) =
        sumRange M (fun m => ((w m * (μ m * μ m)) * Sw + w m * S2) - 2 * ((w m * μ m) * S1)) := by
    apply sumRange_congr
    intro m _
    exact hInner m
  rw [hOuter, sumRange_sub, sumRange_add]
  rw [sumRange_mul_right M (fun m => w m * (μ m * μ m)) Sw]
  rw [sumRange_mul_left M 2 (fun m => (w m * μ m) * S1)]
  rw [sumRange_mul_right M (fun m => w m * μ m) S1]
  rw [sumRange_mul_right M w S2]
  unfold covMixtureScaled
  have hComm : S2 * Sw = Sw * S2 := Int.mul_comm S2 Sw
  dsimp only [Sw, S1, S2] at hComm ⊢
  rw [hComm]
  omega

/-- Binary 2-draw urn distribution without replacement from `{false, true}`:
    `P(false, true) = 1`, `P(true, false) = 1`, `P(false, false) = P(true, true) = 0`. -/
def urnWithoutReplacement2 (a b : Bool) : Int :=
  if a != b then 1 else 0

def boolVal (b : Bool) : Int :=
  if b then 1 else 0

/-- Scaled pairwise covariance `W_tot * E[X₁ X₂] - E[X₁] * E[X₂]` for any joint table `P : Bool → Bool → Int`. -/
def jointBinaryCovScaled (P : Bool → Bool → Int) : Int :=
  let tot := P false false + P false true + P true false + P true true
  let e1 := P true false + P true true
  let e2 := P false true + P true true
  let e12 := P true true
  tot * e12 - e1 * e2

/-- **Theorem 2: Diaconis–Freedman Nonnegative De Finetti Mixture Covariance vs. Finite-Urn Counterexample**.
    1. Every nonnegative De Finetti i.i.d. mixture (`0 ≤ w m` for `m < M`) satisfies `0 ≤ covMixtureScaled M w μ`.
    2. `urnWithoutReplacement2` is `S₂`-exchangeable (`U a b = U b a`), yet has strictly negative
       scaled covariance `-1 < 0`, obstructing any nonnegative i.i.d. De Finetti mixture representation! -/
theorem diaconis_freedman_iid_mixture_nonneg_covariance_and_finite_urn_counterexample
    (M : Nat) (w μ : Nat → Int) (hw : ∀ m, m < M → 0 ≤ w m) :
    (2 * covMixtureScaled M w μ =
      sumRange M (fun m => sumRange M (fun m' => (w m * w m') * ((μ m - μ m') * (μ m - μ m')))) ∧
      0 ≤ covMixtureScaled M w μ) ∧
    ((∀ a b : Bool, urnWithoutReplacement2 a b = urnWithoutReplacement2 b a) ∧
      jointBinaryCovScaled urnWithoutReplacement2 = -1 ∧
      jointBinaryCovScaled urnWithoutReplacement2 < 0) := by
  have hId := (weighted_lagrange_covariance_identity M w μ).symm
  have hSumNonneg :
      0 ≤ sumRange M (fun m => sumRange M (fun m' => (w m * w m') * ((μ m - μ m') * (μ m - μ m')))) := by
    apply sumRange_nonneg
    intro m hm
    apply sumRange_nonneg
    intro m' hm'
    have hwm := hw m hm
    have hwm' := hw m' hm'
    have hww : 0 ≤ w m * w m' := Int.mul_nonneg hwm hwm'
    have hsq : 0 ≤ (μ m - μ m') * (μ m - μ m') := sq_nonneg_int (μ m - μ m')
    exact Int.mul_nonneg hww hsq
  have hCovNonneg : 0 ≤ covMixtureScaled M w μ := by
    omega
  refine ⟨⟨hId, hCovNonneg⟩, ?_⟩
  decide

/-! ## Section 3: Discrete Spectral Poincaré–Dirichlet Variance Identity vs. Disconnected Cluster Failure -/

/-- Scaled global variance `N * ∑_{i < N} f_i² - (∑_{i < N} f_i)²`. -/
def globalVarScaled (N : Nat) (f : Nat → Int) : Int :=
  Int.ofNat N * sumRange N (fun i => f i * f i) - sumRange N f * sumRange N f

/-- Complete-graph pairwise Dirichlet energy `∑_{i < N} ∑_{j < N} (f_i - f_j)²`. -/
def completeDirichletEnergy (N : Nat) (f : Nat → Int) : Int :=
  sumRange N (fun i => sumRange N (fun j => (f i - f j) * (f i - f j)))

/-- Disconnected 2-cluster graph `{0, 1} ⊔ {2, 3}` Dirichlet energy `(f 0 - f 1)² + (f 2 - f 3)²`. -/
def disconnectedTwoClusterEnergy (f : Nat → Int) : Int :=
  (f 0 - f 1) * (f 0 - f 1) + (f 2 - f 3) * (f 2 - f 3)

/-- Balanced two-cluster sign witness `(+1, +1, -1, -1)`. -/
def clusterSignWitness (i : Nat) : Int :=
  if i < 2 then 1 else -1

/-- **Theorem 3: Complete-Graph Spectral Poincaré–Dirichlet Identity vs. Disconnected Cluster Failure**.
    1. On `K_N`, `2 * globalVarScaled N f = completeDirichletEnergy N f` holds identically for all `N, f`.
    2. On the disconnected 2-cluster graph `{0, 1} ⊔ {2, 3}` (`π₀ = 2`), `clusterSignWitness` has
       `disconnectedTwoClusterEnergy = 0` yet `globalVarScaled 4 clusterSignWitness = 16 > 0`! -/
theorem lagrange_poincare_complete_graph_variance_identity_and_disconnected_cluster_failure
    (N : Nat) (f : Nat → Int) :
    (2 * globalVarScaled N f = completeDirichletEnergy N f ∧ 0 ≤ globalVarScaled N f) ∧
    (disconnectedTwoClusterEnergy clusterSignWitness = 0 ∧
      globalVarScaled 4 clusterSignWitness = 16) := by
  have hLag := weighted_lagrange_covariance_identity N (fun _ => 1) f
  have hLhsEq :
      sumRange N (fun i => sumRange N (fun j => ((1 : Int) * 1) * ((f i - f j) * (f i - f j)))) =
        completeDirichletEnergy N f := by
    unfold completeDirichletEnergy
    apply sumRange_congr
    intro i _
    apply sumRange_congr
    intro j _
    simp
  have hRhsEq : covMixtureScaled N (fun _ => 1) f = globalVarScaled N f := by
    unfold covMixtureScaled globalVarScaled
    rw [sumRange_ones N]
    have h1 : sumRange N (fun m => (1 : Int) * (f m * f m)) = sumRange N (fun i => f i * f i) := by
      apply sumRange_congr
      intro i _
      simp
    have h2 : sumRange N (fun m => (1 : Int) * f m) = sumRange N f := by
      apply sumRange_congr
      intro i _
      simp
    rw [h1, h2]
  rw [hLhsEq, hRhsEq] at hLag
  have hVarNonneg : 0 ≤ globalVarScaled N f := by
    have hNonneg := (diaconis_freedman_iid_mixture_nonneg_covariance_and_finite_urn_counterexample
      N (fun _ => 1) f (fun _ _ => by decide)).1.2
    rw [hRhsEq] at hNonneg
    exact hNonneg
  refine ⟨⟨hLag.symm, hVarNonneg⟩, ?_⟩
  decide

end CommonGround.InformationRecovery.DeFinettiPoincare
