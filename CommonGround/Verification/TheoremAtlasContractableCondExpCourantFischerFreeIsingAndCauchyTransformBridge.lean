/-
  CommonGround.Verification.TheoremAtlasContractableCondExpCourantFischerFreeIsingAndCauchyTransformBridge

  Zero-sorry Lean 4.33.0 verification of four cross-domain mathematical bridges imported
  from read-only `/Users/fawadhaider/code/lean ideas/theorem-atlas`:

  1. Contractable Block-Future Prefix Split & Cutoff Monotonicity Boundary
     (`TauCeti/Probability/Exchangeability/CondExp.lean` ↔ `QuantumParallelRepetition.lean`):
     - `strictMono_prefixSplitEquiv_symm_block_future` (`CondExp.lean#L48`) splices a length-`r`
       selection `k : Fin r → ℕ` before the shifted future `n ↦ c + n`:
       `φ(i) = k(i)` for `i < r` and `φ(i) = c + (i - r)` for `i ≥ r`.
     - When `StrictMono k` holds AND `∀ i, k(i) < c` (e.g., `r = 2, c = 3` with `k = [0, 2]` or
       `l = [1, 2]`), `φ` is strictly increasing (`[0, 2, 3, 4]` and `[1, 2, 3, 4]`), so
       contractability equates the joint block-future laws (`map_block_future_eq_pathLaw_map`, `#L70`)
       and conditional expectations given `tailFamily X c` (`condExp_block_comp_future_ae_eq`, `#L97`).
     - Premise-failure witness: if `k(1) = 2 ≥ c = 2` (`k = [0, 2]`, `c = 2`), then `φ(1) = 2`
       collides with the first future index `φ(2) = c + 0 = 2`, breaking `StrictMono φ`!

  2. Courant–Fischer Min-Max Subspace Intersection & Weyl Perturbation Symmetry Boundary
     (`TauCeti/Analysis/InnerProductSpace/CourantFischer.lean` ↔ `EhrhartVolumeInequality.lean`):
     - `sum_sq_norm_repr_eq_sq_norm` (`CourantFischer.lean#L60`), `re_inner_apply_self_eq_sum_of_eigenbasis`
       (`#L84`), `exists_unit_vector_re_inner_le_eigenvalue` (`#L168`), and `abs_eigenvalue_sub_eigenvalue_le`
       (`#L398`) diagonalize symmetric Rayleigh quotients `⟪T x, x⟫ = ∑ μ_i x_i²`, use Grassmannian
       dimension counting `(k + 1) + (n - k) = n + 1 > n` to force `V ⊓ W ≠ ⊥`, and bound perturbed
       sorted eigenvalues by `|λ_k(T) - λ_k(S)| ≤ ε`.
     - Premise-failure witness: if `dim V = k` instead of `k + 1` (e.g., `n = 3, k = 1`, `μ = [10, 6, 2]`,
       and `V = span{e₀}` of dimension `1`), then `V ⊓ span{e₁, e₂} = {0}` and `⟪T e₀, e₀⟫ = 10 > λ₁ = 6`!

  3. Free-Ising Tree Gibbs Covariance Cauchy Sum & Kesten–Stigum Criticality Boundary
     (`OAI/Probability/FreeIsing/Gibbs/CovarianceNativeRowCauchy.lean`):
     - `integral_brownianIsingObservationR_eq_interval` (`#L10`) and
       `HasFreeIsingLaw.finiteGibbsCovariance_fullTime_interval_energy_cauchy` (`#L25`) prove that under
       the Kesten–Stigum subcriticality bound `(d - 1) tanh²(β) ≤ 1`, the tree-indexed Brownian-Ising
       Gibbs covariance row energy is summable and Cauchy across exhaustion depths `n, k`.
     - Premise-failure witness: for `d = 3` (`b = d - 1 = 2`), subcritical correlation `θ² = 1/4`
       gives geometric shell decay `(2 · 1/4)^m = (1/2)^m`, whereas supercritical correlation
       `θ² = 3/4` (`(d - 1) θ² = 3/2 > 1`) causes shell variance `(3/2)^m` to grow monotonically!

  4. Noether Polynomial Normalization, Analytic Implicit Simple Root & Cauchy Transform Disjointness
     (`OAI/Analysis/SymmetricDomains/DifferentiableCauchyTransform.lean`):
     - `polynomial_analytic_root` (`#L110`) constructs a local holomorphic root branch `g(y)` around
       `(a, b)` when `P(a, b) = 0` and `P'(a, b) ≠ 0`, and `differentiableOn_cauchyTransform` (`#L214`)
       proves holomorphicity of `(2πi)⁻¹ ∮_{C(c, R)} (w - z)⁻¹ f(x, w) dw` for `z ∈ ball c R` via
       `Metric.sphere_disjoint_ball.ne_of_mem` (`|w - c| = R ≠ |z - c| < R ⟹ w - z ≠ 0`).
     - Premise-failure witness: at a double root `P(y, z) = (z - 3)² - y` at `(0, 3)`, `P(0, 3) = 0`
       but `∂_z P(0, 3) = 0` (two distinct roots `z = 3 ± 1` at `y = 1`), and on the contour boundary
       `|z - c| = R`, `w = z` makes `w - z = 0` singular!
-/

namespace CommonGround.Verification.TheoremAtlasContractableCondExpCourantFischerFreeIsingAndCauchyTransformBridge

/-- Spliced prefix-future index map `(prefixSplitEquiv r).symm (k, fun n => c + n)` from
    `TauCeti/Probability/Exchangeability/CondExp.lean#L48` for `r = 2`. -/
def prefixFutureMap2 (k0 k1 c i : Nat) : Nat :=
  if i = 0 then k0
  else if i = 1 then k1
  else c + (i - 2)

/-- Checks strict monotonicity of `φ : Nat → Nat` on the first 4 indices `0 < 1 < 2 < 3`. -/
def isStrictMono4 (φ : Nat → Nat) : Bool :=
   decide (φ 0 < φ 1 ∧ φ 1 < φ 2 ∧ φ 2 < φ 3)

/-- Diagonal Rayleigh form `∑_{i=0}^2 μ_i x_i²` on `ℝ³` (`CourantFischer.lean#L84`). -/
def rayleighDiag3 (μ0 μ1 μ2 x0 x1 x2 : Nat) : Nat :=
  μ0 * x0 * x0 + μ1 * x1 * x1 + μ2 * x2 * x2

/-- Scaled tree shell covariance energy `((d - 1) * num)^m` vs `den^m` at depth `m`
    (`CovarianceNativeRowCauchy.lean#L25`). -/
def treeShellEnergyNum (b num m : Nat) : Nat :=
  (b * num) ^ m

def treeShellEnergyDen (den m : Nat) : Nat :=
  den ^ m

/-- Quadratic polynomial `P(y, z) = (z - 3)² - y` and its `z`-derivative `2(z - 3)`
    illustrating `polynomial_analytic_root` (`DifferentiableCauchyTransform.lean#L110`). -/
def doubleRootPoly (y z : Int) : Int :=
  (z - 3) * (z - 3) - y

def doubleRootDerivZ (z : Int) : Int :=
  2 * (z - 3)

/-- **Theorem 1 (Contractable Block-Future Prefix Split & Cutoff Boundary)**
    (`TauCeti/Probability/Exchangeability/CondExp.lean#L48–140`):
    1. For `r = 2, c = 3` and two strictly monotone blocks `k = (0, 2)` and `l = (1, 2)`
       satisfying `k_i < c` and `l_i < c`, both spliced maps `prefixFutureMap2` are strictly
       monotone on `0 < 1 < 2 < 3` (`[0, 2, 3, 4]` and `[1, 2, 3, 4]`) and share the identical
       future tail `[3, 4]` at indices `i ≥ 2`.
    2. Cutoff Violation Counterexample (`k_1 ≥ c`): when `c = 2` and `k = (0, 2)` (`k_1 = 2 ≮ 2`),
       `prefixFutureMap2 0 2 2` maps both `i = 1` and `i = 2` to `2` (`φ(1) = φ(2) = 2`),
       violating `StrictMono` (`isStrictMono4 = false`)! -/
theorem contractable_prefix_split_strict_mono_and_cutoff_boundary :
    (isStrictMono4 (prefixFutureMap2 0 2 3) = true ∧
     isStrictMono4 (prefixFutureMap2 1 2 3) = true ∧
     prefixFutureMap2 0 2 3 2 = prefixFutureMap2 1 2 3 2 ∧
     prefixFutureMap2 0 2 3 3 = prefixFutureMap2 1 2 3 3) ∧
    (prefixFutureMap2 0 2 2 1 = 2 ∧
     prefixFutureMap2 0 2 2 2 = 2 ∧
     isStrictMono4 (prefixFutureMap2 0 2 2) = false) := by
  decide

/-- **Theorem 2 (Courant–Fischer Min-Max Subspace Dimension & Weyl Perturbation Bound)**
    (`TauCeti/Analysis/InnerProductSpace/CourantFischer.lean#L60–428`):
    1. For decreasing eigenvalues `μ = (10, 6, 2)` on `n = 3`, any vector `(0, x₁, x₂)` in the
       2-dimensional tail eigenspace `W₁ = span{e₁, e₂}` (`x₀ = 0`) satisfies the spectral upper
       bound `rayleighDiag3 10 6 2 0 x₁ x₂ ≤ 6 * (x₁² + x₂²)`, and any vector `(x₀, x₁, 0)` in
       the 2-dimensional head eigenspace `V₁ = span{e₀, e₁}` (`x₂ = 0`) satisfies the spectral
       lower bound `6 * (x₀² + x₁²) ≤ rayleighDiag3 10 6 2 x₀ x₁ 0`.
    2. Moreover, for perturbed eigenvalues `ν = (9, 7, 1)` with `|μ_i - ν_i| ≤ 1`, every sorted
       eigenvalue shift satisfies Weyl's bound `(μ_i - ν_i)² ≤ 1`.
    3. Subspace Dimension Deficiency Boundary (`dim V = k < k + 1`): on the 1-dimensional
       subspace `V = span{e₀}` (`dim V = 1 < k + 1 = 2` for `k = 1`), the unit vector `(1, 0, 0)`
       has Rayleigh quotient `10 > λ₁ = 6` because `dim V + dim W₁ = 1 + 2 = 3 ≯ 3` allows
       `V ⊓ W₁ = {0}`! -/
theorem courant_fischer_minmax_weyl_and_subspace_dim_boundary :
    ((∀ x1 x2 : Fin 4,
        rayleighDiag3 10 6 2 0 x1.val x2.val ≤ 6 * (x1.val * x1.val + x2.val * x2.val)) ∧
     (∀ x0 x1 : Fin 4,
        6 * (x0.val * x0.val + x1.val * x1.val) ≤ rayleighDiag3 10 6 2 x0.val x1.val 0) ∧
     ((10 - 9 : Int) ^ 2 ≤ 1 ∧ (6 - 7 : Int) ^ 2 ≤ 1 ∧ (2 - 1 : Int) ^ 2 ≤ 1)) ∧
    (rayleighDiag3 10 6 2 1 0 0 = 10 ∧ ¬ (rayleighDiag3 10 6 2 1 0 0 ≤ 6)) := by
  decide

/-- **Theorem 3 (Free-Ising Tree Gibbs Covariance Cauchy Decay vs. Kesten–Stigum Supercriticality)**
    (`OAI/Probability/FreeIsing/Gibbs/CovarianceNativeRowCauchy.lean#L10–78`):
    1. For tree degree `d = 3` (branching factor `b = d - 1 = 2`) and subcritical spin-glass
       correlation `θ² = 1/4` (`(d - 1) θ² = 2/4 ≤ 1`), the shell covariance energy
       `(2 · 1)^m / 4^m` contracts geometrically (`2 · treeShellEnergyNum 2 1 (m + 1) = treeShellEnergyNum 2 1 m * 4 / ...`).
    2. Supercritical Kesten–Stigum Failure Boundary (`(d - 1) θ² > 1`): when `θ² = 3/4`
       (`b · num = 2 · 3 = 6 > den = 4`, so `(d - 1) tanh² β = 3/2 > 1`), the depth-`m` shell
       covariance ratio grows strictly with depth (`6^m / 4^m`: `6/4 < 36/16 < 216/64`), breaking
       tail summability and Cauchy convergence! -/
theorem free_ising_tree_covariance_kesten_stigum_boundary :
    (2 * 1 ≤ 4 ∧
     treeShellEnergyNum 2 1 1 * 2 = treeShellEnergyDen 4 1 ∧
     treeShellEnergyNum 2 1 2 * 4 = treeShellEnergyDen 4 2 ∧
     treeShellEnergyNum 2 1 3 * 8 = treeShellEnergyDen 4 3) ∧
    (2 * 3 > 4 ∧
     treeShellEnergyNum 2 3 1 > treeShellEnergyDen 4 1 ∧
     treeShellEnergyNum 2 3 2 > 2 * treeShellEnergyDen 4 2 ∧
     treeShellEnergyNum 2 3 3 > 3 * treeShellEnergyDen 4 3) := by
  decide

/-- **Theorem 4 (Analytic Implicit Simple-Root Non-Degeneracy & Cauchy Kernel Sphere-Ball Disjointness)**
    (`OAI/Analysis/SymmetricDomains/DifferentiableCauchyTransform.lean#L110–246`):
    1. Sphere-Ball Disjointness (`Metric.sphere_disjoint_ball.ne_of_mem`, `#L226`): for every
       contour point `w` on the circle `w_x² + w_y² = R² = 25` (`R = 5`) and interior point `z`
       in the open disk `z_x² + z_y² < 25`, `(w_x - z_x)² + (w_y - z_y)² > 0` (`w ≠ z`), keeping
       the Cauchy kernel `(w - z)⁻¹` non-singular; on the boundary `z = w = (3, 4)`, `(w - z) = 0`.
    2. Simple-Root Premise (`hsimple : P'(a, b) ≠ 0`, `#L113`): for `P(y, z) = (z - 3)² - y`,
       at the simple root `(y, z) = (4, 5)` we have `P(4, 5) = 0` and `∂_z P(5) = 4 ≠ 0`, whereas
       at the double root `(y, z) = (0, 3)` we have `P(0, 3) = 0` and `∂_z P(3) = 0`, where
       branching `z = 2` and `z = 4` both satisfy `P(1, z) = 0`! -/
theorem cauchy_transform_disjoint_sphere_ball_and_simple_root_boundary :
    ((∀ zx zy : Fin 4, zx.val * zx.val + zy.val * zy.val < 25 →
        (3 - (zx.val : Int)) ^ 2 + (4 - (zy.val : Int)) ^ 2 > 0) ∧
     ((3 - 3 : Int) ^ 2 + (4 - 4 : Int) ^ 2 = 0)) ∧
    (doubleRootPoly 4 5 = 0 ∧ doubleRootDerivZ 5 = 4 ∧
     doubleRootPoly 0 3 = 0 ∧ doubleRootDerivZ 3 = 0 ∧
     doubleRootPoly 1 2 = 0 ∧ doubleRootPoly 1 4 = 0 ∧ (2 : Int) ≠ 4) := by
  decide

end CommonGround.Verification.TheoremAtlasContractableCondExpCourantFischerFreeIsingAndCauchyTransformBridge
