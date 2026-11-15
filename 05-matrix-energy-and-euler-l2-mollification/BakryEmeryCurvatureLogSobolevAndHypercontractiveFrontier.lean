/-
Copyright (c) 2026 Common Ground Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Discrete Bakry–Émery Curvature, Efron–Stein Tensorization, 2D Bonami–Schmidt Hypercontractivity (`3ρ² ≤ 1`) & Khintchine Sub-Gaussianity

Foundational pure-core Lean 4.33.0 module (`0` imports, `0` `sorry`) unifying:
- **Folder `05` (`05-matrix-energy-and-euler-l2-mollification`)**: Dirichlet gradient energy,
  Ornstein–Uhlenbeck / heat spectral dissipation, and discrete Bakry–Émery $\Gamma_2$ curvature;
- **Folder `03` (`03-information-recovery-kl-pythagorean`)**: Efron–Stein jackknife variance
  tensorization and Walsh–Hadamard orthogonal ANOVA decomposition;
- **Folder `02` (`02-universal-affine-query-compression`)**: Tensorized 2D Bonami–Beckner
  `(2, 4)` hypercontractive noise attenuation $T_\rho$ and Khintchine Rademacher moment control;
- **Folder `07` (`07-game-sampler-and-quantum-parallel-bridge`)**: Exact **Schmidt / Entanglement
  Determinant** `det M_f = c₀ c₁₂ - c₁ c₂` governing 4-wave Walsh resonance damping!

## Main Machine-Checked Results

1. `efron_stein_bakry_emery_tensorization_vs_correlated_diagonal_failure`:
   - **Exact Walsh–Hadamard / Efron–Stein / Bakry–Émery Identity**: For *every* integer observable
     `f` on `{0, 1}²`, the surplus of summed coordinate Dirichlet energies
     `dirichletCoord1 + dirichletCoord2` over scaled variance `var16` equals the exact square of
     the discrete mixed Hessian / degree-2 Walsh harmonic:
     `(dirichletCoord1 a b c d + dirichletCoord2 a b c d) - var16 a b c d = (d - c - b + a)^2 ≥ 0`.
   - **Corollaries**: Universal tensorized Poincaré / Efron–Stein inequality
     `var16 ≤ dirichletCoord1 + dirichletCoord2` with equality iff `f` is additive, whereas XOR
     parity concentrates `100%` of variance in `mixedHessian` (`32 > 16`).
   - **Premise-Failure Counterexample (Correlated Diagonal Coupling)**: Under non-product diagonal
     law `{(0,0), (1,1)}`, `f(x₁, x₂) = x₁ + x₂` has conditional coordinate variances `0 + 0 = 0`
     while total variance is `1 > 0` (`1 > 0 + 0`).

2. `bonami_beckner_2d_schmidt_sos_and_sharp_one_third_phase_transition`:
   - **Exact 2D Bonami–Schmidt Positivstellensatz Certificate (Minkowski-Free SOS)**: For *every*
     2-bit Walsh polynomial `f(x, y) = c₀ + c₁ x + c₂ y + c₁₂ x y` on `{-1, +1}²` and rational
     Ornstein–Uhlenbeck attenuation `ρ = p / q`, `4 q⁸ ‖f‖₂⁴ - ∑_{x,y ∈ {±1}} (q² T_{p/q} f(x,y))⁴`
     equals an explicit 6-term positive polynomial in `(q² - 3 p²)` PLUS the **Schmidt entanglement
     determinant** `48 p⁴ q⁴ (c₀ c₁₂ - c₁ c₂)²`!
   - **Universal 2D `(2, 4)` Hypercontractivity & Entanglement Damping Surplus**: Whenever
     `3 * p^2 ≤ q^2` (`ρ² ≤ 1/3`), `∑ (q² T_{p/q} f)⁴ ≤ 4 q⁸ (c₀² + c₁² + c₂² + c₁₂²)²` holds for
     all `c₀, c₁, c₂, c₁₂ : Int`, with strict surplus `≥ 48 p⁴ q⁴ (c₀ c₁₂ - c₁ c₂)²` on entangled
     (non-product) Boolean functions such as the bent state `(1, 1, 1, -1)` (`det M_f = -2`).
   - **Sharp Phase-Boundary Counterexample (`ρ = 2/3 < 1`, `3 ρ² = 4/3 > 1`)**: At `p = 2, q = 3`
     and `(c₀, c₁, c₂, c₁₂) = (3, 1, 0, 0)`, `3 * 2^2 = 12 > 9 = 3^2` and the 4th moment strictly
     exceeds the squared `L²` bound (`34084 > 32400`, i.e., `8521 > 8100`).

3. `khintchine_fourth_moment_subgaussian_vs_spiky_kurtosis_explosion`:
   - **Exact 3-Coordinate Rademacher Khintchine `(2, 4)` Identity**: Over all `8` vertices of
     `{-1, +1}³`, `24 (a₁² + a₂² + a₃²)² - ∑_{ε ∈ {±1}³} (a₁ ε₁ + a₂ ε₂ + a₃ ε₃)⁴ = 16 (a₁⁴ + a₂⁴ + a₃⁴) ≥ 0`,
     proving universal sub-Gaussian fourth-moment control `E[S₃⁴] ≤ 3 (E[S₃²])²`.
   - **Premise-Failure Counterexample (Heavy-Tailed Rare Spike `Z_M`)**: Replacing bounded
     Rademacher signs by the zero-mean `2M`-atom rare-spike law (`±M` once each, `0` on `2M - 2`
     atoms) yields `E[Z_M²] = M` and `E[Z_M⁴] = M³`, violating `E[Z⁴] ≤ 3 (E[Z²])²` for all `M ≥ 4`
     (`64 > 48` at `M = 4`, with kurtosis `M → ∞`).
-/

namespace BakryEmeryCurvatureLogSobolevAndHypercontractiveFrontier

/-! ## Section 0: Pure-Core Integer Nonnegativity Helpers (`0` Imports) -/

theorem int_sq_nonneg (z : Int) : 0 ≤ z * z := by
  by_cases hz : 0 ≤ z
  · exact Int.mul_nonneg hz hz
  · have hneg : 0 ≤ -z := by omega
    have hnn : 0 ≤ (-z) * (-z) := Int.mul_nonneg hneg hneg
    have hsq : (-z) * (-z) = z * z := by rw [Int.neg_mul_neg]
    rw [← hsq]
    exact hnn

theorem int_pow2_nonneg (z : Int) : 0 ≤ z ^ 2 := by
  have h : z ^ 2 = z * z := by grind
  rw [h]
  exact int_sq_nonneg z

theorem int_pow4_nonneg (z : Int) : 0 ≤ z ^ 4 := by
  have h : z ^ 4 = (z ^ 2) * (z ^ 2) := by grind
  rw [h]
  exact Int.mul_nonneg (int_pow2_nonneg z) (int_pow2_nonneg z)

/-! ## Section 1: Discrete Bakry–Émery `Γ₂` & Efron–Stein Variance Tensorization -/

/-- Scaled total variance `16 * Var(f)` on `{0, 1}²` under uniform product measure `1/4`. -/
def var16 (f00 f01 f10 f11 : Int) : Int :=
  4 * (f00 ^ 2 + f01 ^ 2 + f10 ^ 2 + f11 ^ 2) - (f00 + f01 + f10 + f11) ^ 2

/-- Scaled first-coordinate conditional variance / Dirichlet energy `16 * E[Var₁(f)]`. -/
def dirichletCoord1 (f00 f01 f10 f11 : Int) : Int :=
  2 * ((f10 - f00) ^ 2 + (f11 - f01) ^ 2)

/-- Scaled second-coordinate conditional variance / Dirichlet energy `16 * E[Var₂(f)]`. -/
def dirichletCoord2 (f00 f01 f10 f11 : Int) : Int :=
  2 * ((f01 - f00) ^ 2 + (f11 - f10) ^ 2)

/-- Discrete mixed Hessian / degree-2 Walsh–Fourier harmonic `f(1,1) - f(1,0) - f(0,1) + f(0,0)`. -/
def mixedHessian (f00 f01 f10 f11 : Int) : Int :=
  f11 - f10 - f01 + f00

/-- Exact Walsh–Hadamard / Efron–Stein / Bakry–Émery `Γ₂` identity:
`(E₁ + E₂) - Var₁₆ = (f₁₁ - f₁₀ - f₀₁ + f₀₀)²`. -/
theorem efron_stein_walsh_gap_identity (a b c d : Int) :
    (dirichletCoord1 a b c d + dirichletCoord2 a b c d) - var16 a b c d =
      (mixedHessian a b c d) ^ 2 := by
  dsimp [dirichletCoord1, dirichletCoord2, var16, mixedHessian]
  grind

/-- Variance of `f(x₁, x₂) = x₁ + x₂` under correlated diagonal coupling `{(0,0), (1,1)}` (`1/2` each):
values are `0` and `2`, so `Var = ((0-1)² + (2-1)²)/2 = 1`, while each coordinate is deterministic
given the other (`E[Var₁] + E[Var₂] = 0`). -/
def diagonalCouplingTotalVar : Int := ((0 - 1) ^ 2 + (2 - 1) ^ 2) / 2
def diagonalCouplingCondVarSum : Int := 0 + 0

/-- **Theorem 1**: Universal Efron–Stein / Poincaré tensorization on `{0, 1}²`, additive tightness,
XOR degree-2 interaction surplus, and premise-failure counterexample under correlated coupling. -/
theorem efron_stein_bakry_emery_tensorization_vs_correlated_diagonal_failure :
    -- (1) Universal Efron-Stein / Poincare variance sub-additivity for ALL f : {0,1}^2 -> Int
    (∀ a b c d : Int, var16 a b c d ≤ dirichletCoord1 a b c d + dirichletCoord2 a b c d) ∧
    -- (2) Exact tightness on every additive observable f(x, y) = u0 + u1 x + u2 y
    (∀ u0 u1 u2 : Int,
      mixedHessian u0 (u0 + u2) (u0 + u1) (u0 + u1 + u2) = 0 ∧
      var16 u0 (u0 + u2) (u0 + u1) (u0 + u1 + u2) =
        dirichletCoord1 u0 (u0 + u2) (u0 + u1) (u0 + u1 + u2) +
          dirichletCoord2 u0 (u0 + u2) (u0 + u1) (u0 + u1 + u2)) ∧
    -- (3) XOR parity f = x ⊕ y (0, 1, 1, 0) doubles Dirichlet sum over variance (8 = 4 + (-2)^2)
    (var16 0 1 1 0 = 4 ∧ dirichletCoord1 0 1 1 0 + dirichletCoord2 0 1 1 0 = 8 ∧
      mixedHessian 0 1 1 0 = -2) ∧
    -- (4) Premise-failure counterexample: non-product diagonal coupling violates tensorization (1 > 0)
    (diagonalCouplingCondVarSum < diagonalCouplingTotalVar ∧
      diagonalCouplingTotalVar = 1 ∧ diagonalCouplingCondVarSum = 0) := by
  refine ⟨?_, ?_, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩
  · intro a b c d
    have hId := efron_stein_walsh_gap_identity a b c d
    have hSq := int_pow2_nonneg (mixedHessian a b c d)
    omega
  · intro u0 u1 u2
    constructor
    · dsimp [mixedHessian]; omega
    · have hId := efron_stein_walsh_gap_identity u0 (u0 + u2) (u0 + u1) (u0 + u1 + u2)
      have hMH : mixedHessian u0 (u0 + u2) (u0 + u1) (u0 + u1 + u2) = 0 := by
        dsimp [mixedHessian]; omega
      rw [hMH] at hId
      omega

/-! ## Section 2: 2D Tensorized Bonami–Schmidt `(2, 4)` Hypercontractivity (`3ρ² ≤ 1`) -/

/-- Sum of fourth powers of `q² (T_{p/q} f)` over all 4 vertices of `{-1, +1}²` for
`f(x, y) = c0 + c1 x + c2 y + c12 x y`. -/
def bonami2DFourthSum (c0 c1 c2 c12 p q : Int) : Int :=
  (q ^ 2 * c0 + p * q * (c1 + c2) + p ^ 2 * c12) ^ 4 +
  (q ^ 2 * c0 + p * q * (c1 - c2) - p ^ 2 * c12) ^ 4 +
  (q ^ 2 * c0 + p * q * (-c1 + c2) - p ^ 2 * c12) ^ 4 +
  (q ^ 2 * c0 + p * q * (-c1 - c2) + p ^ 2 * c12) ^ 4

/-- Scaled squared `L²` norm `4 * q⁸ * (E[f²])² = 4 * q⁸ * (c0² + c1² + c2² + c12²)²`. -/
def bonami2DL2SqBound (c0 c1 c2 c12 q : Int) : Int :=
  4 * (q ^ 8) * ((c0 ^ 2 + c1 ^ 2 + c2 ^ 2 + c12 ^ 2) ^ 2)

/-- Schmidt entanglement determinant `det [[c0, c1], [c2, c12]] = c0 * c12 - c1 * c2` of the
2-bit Walsh–Fourier spectrum (vanishes iff `f(x, y) = g(x) h(y)` is separable). -/
def walshSchmidtDet (c0 c1 c2 c12 : Int) : Int :=
  c0 * c12 - c1 * c2

/-- Exact 6-term Minkowski-free Positivstellensatz slack polynomial for 2D `(2, 4)` hypercontractivity. -/
def bonami2DSlackSOS (c0 c1 c2 c12 p q : Int) : Int :=
  4 * (
    (q ^ 8 - p ^ 4 * q ^ 4) * (c1 ^ 4 + c2 ^ 4) +
    (q ^ 8 - p ^ 8) * (c12 ^ 4) +
    2 * (q ^ 6) * (q ^ 2 - 3 * p ^ 2) * (c0 ^ 2) * (c1 ^ 2 + c2 ^ 2) +
    2 * (q ^ 4) * (q ^ 2 - 3 * p ^ 2) * (q ^ 2 + 3 * p ^ 2) * (c0 ^ 2 * c12 ^ 2 + c1 ^ 2 * c2 ^ 2) +
    2 * (q ^ 2) * (q ^ 6 - 3 * p ^ 6) * (c1 ^ 2 + c2 ^ 2) * (c12 ^ 2) +
    12 * (p ^ 4) * (q ^ 4) * ((walshSchmidtDet c0 c1 c2 c12) ^ 2)
  )

/-- Exact degree-12 algebraic identity: `4 q⁸ ‖f‖₂⁴ - ∑ (q² T_{p/q} f)⁴ = bonami2DSlackSOS`. -/
theorem bonami_2d_schmidt_sos_identity (c0 c1 c2 c12 p q : Int) :
    bonami2DL2SqBound c0 c1 c2 c12 q - bonami2DFourthSum c0 c1 c2 c12 p q =
      bonami2DSlackSOS c0 c1 c2 c12 p q := by
  dsimp [bonami2DL2SqBound, bonami2DFourthSum, bonami2DSlackSOS, walshSchmidtDet]
  grind

/-- Helper: `3 * P ≤ Q` and `0 ≤ P` imply `0 ≤ Q^3 - 3 * P^3`. -/
theorem cubic_three_gap_nonneg (P Q : Int) (hP : 0 ≤ P) (h3 : 3 * P ≤ Q) :
    0 ≤ Q ^ 3 - 3 * P ^ 3 := by
  have hId : Q ^ 3 - 3 * P ^ 3 = (Q - 3 * P) * (Q ^ 2 + 3 * P * Q + 9 * P ^ 2) + 24 * P ^ 3 := by
    grind
  have hQ : 0 ≤ Q := by omega
  have hDiff : 0 ≤ Q - 3 * P := by omega
  have hQuad : 0 ≤ Q ^ 2 + 3 * P * Q + 9 * P ^ 2 := by
    have h1 : 0 ≤ Q * Q := Int.mul_nonneg hQ hQ
    have h2 : 0 ≤ 3 * (P * Q) := Int.mul_nonneg (by decide) (Int.mul_nonneg hP hQ)
    have h3p : 0 ≤ 9 * (P * P) := Int.mul_nonneg (by decide) (Int.mul_nonneg hP hP)
    have hEq : Q ^ 2 + 3 * P * Q + 9 * P ^ 2 = Q * Q + 3 * (P * Q) + 9 * (P * P) := by grind
    omega
  have hCub : 0 ≤ 24 * P ^ 3 := by
    have hP2 : 0 ≤ P * P := Int.mul_nonneg hP hP
    have hP3 : 0 ≤ (P * P) * P := Int.mul_nonneg hP2 hP
    have hEq : 24 * P ^ 3 = 24 * ((P * P) * P) := by grind
    have h24 : 0 ≤ 24 * ((P * P) * P) := Int.mul_nonneg (by decide) hP3
    omega
  have hProd : 0 ≤ (Q - 3 * P) * (Q ^ 2 + 3 * P * Q + 9 * P ^ 2) := Int.mul_nonneg hDiff hQuad
  omega

/-- Helper: whenever `3 * p^2 ≤ q^2`, the entire 6-term `bonami2DSlackSOS` dominates the Schmidt
entanglement term `48 * p^4 * q^4 * (walshSchmidtDet c0 c1 c2 c12)^2 ≥ 0`. -/
theorem bonami_2d_slack_ge_schmidt (c0 c1 c2 c12 p q : Int) (hSub : 3 * p ^ 2 ≤ q ^ 2) :
    48 * (p ^ 4) * (q ^ 4) * ((walshSchmidtDet c0 c1 c2 c12) ^ 2) ≤
      bonami2DSlackSOS c0 c1 c2 c12 p q := by
  dsimp [bonami2DSlackSOS]
  have hP : 0 ≤ p ^ 2 := int_pow2_nonneg p
  have hQ : 0 ≤ q ^ 2 := int_pow2_nonneg q
  have hGap3 : 0 ≤ q ^ 2 - 3 * p ^ 2 := by omega
  have hGap1 : 0 ≤ q ^ 2 - p ^ 2 := by omega
  have hTerm1 : 0 ≤ (q ^ 8 - p ^ 4 * q ^ 4) * (c1 ^ 4 + c2 ^ 4) := by
    have hA : q ^ 8 - p ^ 4 * q ^ 4 = (q ^ 4) * ((q ^ 2 - p ^ 2) * (q ^ 2 + p ^ 2)) := by grind
    have hB : 0 ≤ (q ^ 4) * ((q ^ 2 - p ^ 2) * (q ^ 2 + p ^ 2)) :=
      Int.mul_nonneg (int_pow4_nonneg q) (Int.mul_nonneg hGap1 (by omega))
    have hC : 0 ≤ c1 ^ 4 + c2 ^ 4 := by
      have hc1 := int_pow4_nonneg c1; have hc2 := int_pow4_nonneg c2; omega
    rw [hA]
    exact Int.mul_nonneg hB hC
  have hTerm2 : 0 ≤ (q ^ 8 - p ^ 8) * (c12 ^ 4) := by
    have hA : q ^ 8 - p ^ 8 = ((q ^ 2 - p ^ 2) * (q ^ 2 + p ^ 2)) * (q ^ 4 + p ^ 4) := by grind
    have hQ4P4 : 0 ≤ q ^ 4 + p ^ 4 := by
      have hq4 := int_pow4_nonneg q; have hp4 := int_pow4_nonneg p; omega
    have hB : 0 ≤ ((q ^ 2 - p ^ 2) * (q ^ 2 + p ^ 2)) * (q ^ 4 + p ^ 4) :=
      Int.mul_nonneg (Int.mul_nonneg hGap1 (by omega)) hQ4P4
    rw [hA]
    exact Int.mul_nonneg hB (int_pow4_nonneg c12)
  have hTerm3 : 0 ≤ 2 * (q ^ 6) * (q ^ 2 - 3 * p ^ 2) * (c0 ^ 2) * (c1 ^ 2 + c2 ^ 2) := by
    have hq6 : 0 ≤ 2 * (q ^ 6) := by
      have hEq : q ^ 6 = (q ^ 4) * (q ^ 2) := by grind
      rw [hEq]
      exact Int.mul_nonneg (by decide) (Int.mul_nonneg (int_pow4_nonneg q) hQ)
    have hc12s : 0 ≤ c1 ^ 2 + c2 ^ 2 := by
      have hc1 := int_pow2_nonneg c1; have hc2 := int_pow2_nonneg c2; omega
    have hEq : 2 * (q ^ 6) * (q ^ 2 - 3 * p ^ 2) * (c0 ^ 2) * (c1 ^ 2 + c2 ^ 2) =
        ((2 * (q ^ 6)) * (q ^ 2 - 3 * p ^ 2)) * ((c0 ^ 2) * (c1 ^ 2 + c2 ^ 2)) := by grind
    rw [hEq]
    exact Int.mul_nonneg (Int.mul_nonneg hq6 hGap3) (Int.mul_nonneg (int_pow2_nonneg c0) hc12s)
  have hTerm4 : 0 ≤ 2 * (q ^ 4) * (q ^ 2 - 3 * p ^ 2) * (q ^ 2 + 3 * p ^ 2) * (c0 ^ 2 * c12 ^ 2 + c1 ^ 2 * c2 ^ 2) := by
    have hCoeff : 0 ≤ (2 * (q ^ 4)) * ((q ^ 2 - 3 * p ^ 2) * (q ^ 2 + 3 * p ^ 2)) :=
      Int.mul_nonneg (Int.mul_nonneg (by decide) (int_pow4_nonneg q)) (Int.mul_nonneg hGap3 (by omega))
    have hVars : 0 ≤ c0 ^ 2 * c12 ^ 2 + c1 ^ 2 * c2 ^ 2 := by
      have ha := Int.mul_nonneg (int_pow2_nonneg c0) (int_pow2_nonneg c12)
      have hb := Int.mul_nonneg (int_pow2_nonneg c1) (int_pow2_nonneg c2)
      omega
    have hEq : 2 * (q ^ 4) * (q ^ 2 - 3 * p ^ 2) * (q ^ 2 + 3 * p ^ 2) * (c0 ^ 2 * c12 ^ 2 + c1 ^ 2 * c2 ^ 2) =
        ((2 * (q ^ 4)) * ((q ^ 2 - 3 * p ^ 2) * (q ^ 2 + 3 * p ^ 2))) * (c0 ^ 2 * c12 ^ 2 + c1 ^ 2 * c2 ^ 2) := by grind
    rw [hEq]
    exact Int.mul_nonneg hCoeff hVars
  have hTerm5 : 0 ≤ 2 * (q ^ 2) * (q ^ 6 - 3 * p ^ 6) * (c1 ^ 2 + c2 ^ 2) * (c12 ^ 2) := by
    have hCubEq : q ^ 6 - 3 * p ^ 6 = (q ^ 2) ^ 3 - 3 * (p ^ 2) ^ 3 := by grind
    have hCub : 0 ≤ q ^ 6 - 3 * p ^ 6 := by
      rw [hCubEq]
      exact cubic_three_gap_nonneg (p ^ 2) (q ^ 2) hP hSub
    have hc12s : 0 ≤ c1 ^ 2 + c2 ^ 2 := by
      have hc1 := int_pow2_nonneg c1; have hc2 := int_pow2_nonneg c2; omega
    have hEq : 2 * (q ^ 2) * (q ^ 6 - 3 * p ^ 6) * (c1 ^ 2 + c2 ^ 2) * (c12 ^ 2) =
        ((2 * (q ^ 2)) * (q ^ 6 - 3 * p ^ 6)) * ((c1 ^ 2 + c2 ^ 2) * (c12 ^ 2)) := by grind
    rw [hEq]
    exact Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg (by decide) hQ) hCub) (Int.mul_nonneg hc12s (int_pow2_nonneg c12))
  have hSplit :
      4 * ((q ^ 8 - p ^ 4 * q ^ 4) * (c1 ^ 4 + c2 ^ 4) +
        (q ^ 8 - p ^ 8) * (c12 ^ 4) +
        2 * (q ^ 6) * (q ^ 2 - 3 * p ^ 2) * (c0 ^ 2) * (c1 ^ 2 + c2 ^ 2) +
        2 * (q ^ 4) * (q ^ 2 - 3 * p ^ 2) * (q ^ 2 + 3 * p ^ 2) * (c0 ^ 2 * c12 ^ 2 + c1 ^ 2 * c2 ^ 2) +
        2 * (q ^ 2) * (q ^ 6 - 3 * p ^ 6) * (c1 ^ 2 + c2 ^ 2) * (c12 ^ 2) +
        12 * (p ^ 4) * (q ^ 4) * ((walshSchmidtDet c0 c1 c2 c12) ^ 2)) -
      48 * (p ^ 4) * (q ^ 4) * ((walshSchmidtDet c0 c1 c2 c12) ^ 2) =
      4 * ((q ^ 8 - p ^ 4 * q ^ 4) * (c1 ^ 4 + c2 ^ 4) +
        (q ^ 8 - p ^ 8) * (c12 ^ 4) +
        2 * (q ^ 6) * (q ^ 2 - 3 * p ^ 2) * (c0 ^ 2) * (c1 ^ 2 + c2 ^ 2) +
        2 * (q ^ 4) * (q ^ 2 - 3 * p ^ 2) * (q ^ 2 + 3 * p ^ 2) * (c0 ^ 2 * c12 ^ 2 + c1 ^ 2 * c2 ^ 2) +
        2 * (q ^ 2) * (q ^ 6 - 3 * p ^ 6) * (c1 ^ 2 + c2 ^ 2) * (c12 ^ 2)) := by grind
  omega

/-- **Theorem 2**: Universal 2D Bonami–Schmidt `(2, 4)` hypercontractivity (`3 p² ≤ q²`), strict
Schmidt entanglement damping surplus on bent Boolean functions, and sharp phase-boundary failure
at `ρ = 2/3` (`3 * 2² = 12 > 9 = 3²`, `34084 > 32400`). -/
theorem bonami_beckner_2d_schmidt_sos_and_sharp_one_third_phase_transition :
    -- (1) Universal 2D (2, 4) hypercontractivity + Schmidt entanglement damping surplus for 3 p^2 <= q^2
    (∀ c0 c1 c2 c12 p q : Int, 3 * p ^ 2 ≤ q ^ 2 →
      bonami2DFourthSum c0 c1 c2 c12 p q +
        48 * (p ^ 4) * (q ^ 4) * ((walshSchmidtDet c0 c1 c2 c12) ^ 2) ≤
          bonami2DL2SqBound c0 c1 c2 c12 q ∧
      bonami2DFourthSum c0 c1 c2 c12 p q ≤ bonami2DL2SqBound c0 c1 c2 c12 q) ∧
    -- (2) Entangled bent Boolean function (1, 1, 1, -1) has det = -2 != 0 (strict extra damping at rho = 1/2)
    (walshSchmidtDet 1 1 1 (-1) = -2 ∧
      bonami2DL2SqBound 1 1 1 (-1) 2 - bonami2DFourthSum 1 1 1 (-1) 1 2 = 12732) ∧
    -- (3) Sharp phase-transition failure at rho = 2/3 < 1 (p = 2, q = 3 => 3 p^2 = 12 > 9 = q^2):
    --     (c0, c1, c2, c12) = (3, 1, 0, 0) violates (2, 4) hypercontractivity (2760804 > 2624400, i.e., 8521 > 8100)!
    (3 * (2 : Int) ^ 2 > (3 : Int) ^ 2 ∧
      bonami2DL2SqBound 3 1 0 0 3 = 2624400 ∧
      bonami2DFourthSum 3 1 0 0 2 3 = 2760804 ∧
      bonami2DL2SqBound 3 1 0 0 3 < bonami2DFourthSum 3 1 0 0 2 3) := by
  refine ⟨?_, ⟨by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩⟩
  intro c0 c1 c2 c12 p q hSub
  have hId := bonami_2d_schmidt_sos_identity c0 c1 c2 c12 p q
  have hGe := bonami_2d_slack_ge_schmidt c0 c1 c2 c12 p q hSub
  have hDetNN : 0 ≤ 48 * (p ^ 4) * (q ^ 4) * ((walshSchmidtDet c0 c1 c2 c12) ^ 2) := by
    have hEq : 48 * (p ^ 4) * (q ^ 4) * ((walshSchmidtDet c0 c1 c2 c12) ^ 2) =
        (48 * ((p ^ 4) * (q ^ 4))) * ((walshSchmidtDet c0 c1 c2 c12) ^ 2) := by grind
    rw [hEq]
    exact Int.mul_nonneg
      (Int.mul_nonneg (by decide) (Int.mul_nonneg (int_pow4_nonneg p) (int_pow4_nonneg q)))
      (int_pow2_nonneg (walshSchmidtDet c0 c1 c2 c12))
  omega

/-! ## Section 3: Khintchine `(2, 4)` Sub-Gaussianity vs. Heavy-Tailed Rare-Spike Kurtosis -/

/-- Sum of fourth powers of `a₁ ε₁ + a₂ ε₂ + a₃ ε₃` over all `8` Rademacher vertices `ε ∈ {-1, +1}³`. -/
def khintchine3DFourthSum (a1 a2 a3 : Int) : Int :=
  (a1 + a2 + a3) ^ 4 + (a1 + a2 - a3) ^ 4 + (a1 - a2 + a3) ^ 4 + (a1 - a2 - a3) ^ 4 +
  (-a1 + a2 + a3) ^ 4 + (-a1 + a2 - a3) ^ 4 + (-a1 - a2 + a3) ^ 4 + (-a1 - a2 - a3) ^ 4

/-- Scaled Gaussian fourth-moment envelope `8 * 3 * (a₁² + a₂² + a₃²)² = 24 * (a₁² + a₂² + a₃²)²`. -/
def khintchine3DSubGaussianBound (a1 a2 a3 : Int) : Int :=
  24 * ((a1 ^ 2 + a2 ^ 2 + a3 ^ 2) ^ 2)

/-- Exact Khintchine `(2, 4)` platykurtic slack identity:
`24 (a₁² + a₂² + a₃²)² - ∑_{ε ∈ {±1}³} (a₁ ε₁ + a₂ ε₂ + a₃ ε₃)⁴ = 16 (a₁⁴ + a₂⁴ + a₃⁴)`. -/
theorem khintchine_3d_platykurtic_identity (a1 a2 a3 : Int) :
    khintchine3DSubGaussianBound a1 a2 a3 - khintchine3DFourthSum a1 a2 a3 =
      16 * (a1 ^ 4 + a2 ^ 4 + a3 ^ 4) := by
  dsimp [khintchine3DSubGaussianBound, khintchine3DFourthSum]
  grind

/-- Symmetric `2M`-atom rare-spike variable `Z_M` (`+M` once, `-M` once, `0` on `2M - 2` atoms):
`E[Z_M²] = (M² + (-M)²) / (2M) = M`, while `E[Z_M⁴] = (M⁴ + (-M)⁴) / (2M) = M³`. -/
def rareSpikeSecondMoment (M : Int) : Int := M
def rareSpikeFourthMoment (M : Int) : Int := M ^ 3

/-- **Theorem 3**: Universal 3-coordinate Khintchine `B₄ = ⁴√3` sub-Gaussian moment bound
contrasted with heavy-tailed rare-spike kurtosis explosion (`M³ > 3 M²` for every `M ≥ 4`). -/
theorem khintchine_fourth_moment_subgaussian_vs_spiky_kurtosis_explosion :
    -- (1) Universal sub-Gaussian fourth-moment bound for ALL Rademacher linear forms S_3
    (∀ a1 a2 a3 : Int, khintchine3DFourthSum a1 a2 a3 ≤ khintchine3DSubGaussianBound a1 a2 a3) ∧
    -- (2) Isotropic 3-bit walk (1, 1, 1) has E[S^4] = 168/8 = 21 < 27 = 3 * 3^2 (216 - 168 = 48)
    (khintchine3DFourthSum 1 1 1 = 168 ∧ khintchine3DSubGaussianBound 1 1 1 = 216) ∧
    -- (3) Premise-failure counterexample: rare-spike law Z_M violates 3*(E[Z^2])^2 for ALL M >= 4
    (rareSpikeFourthMoment 4 = 64 ∧ 3 * (rareSpikeSecondMoment 4) ^ 2 = 48 ∧
      3 * (rareSpikeSecondMoment 4) ^ 2 < rareSpikeFourthMoment 4) ∧
    (∀ M : Int, 4 ≤ M → 3 * (rareSpikeSecondMoment M) ^ 2 < rareSpikeFourthMoment M) := by
  refine ⟨?_, ⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, ?_⟩
  · intro a1 a2 a3
    have hId := khintchine_3d_platykurtic_identity a1 a2 a3
    have h1 := int_pow4_nonneg a1
    have h2 := int_pow4_nonneg a2
    have h3 := int_pow4_nonneg a3
    omega
  · intro M hM
    dsimp [rareSpikeSecondMoment, rareSpikeFourthMoment]
    have hGap : M ^ 3 - 3 * M ^ 2 = (M - 3) * (M ^ 2) := by grind
    have hPosM2 : 0 < M ^ 2 := by
      have hMul : 16 ≤ M * M := Int.mul_le_mul hM hM (by decide) (by omega)
      have hEq : M ^ 2 = M * M := by grind
      omega
    have hGe : M ^ 2 ≤ (M - 3) * (M ^ 2) := by
      have h1 : 1 ≤ M - 3 := by omega
      have hMul := Int.mul_le_mul_of_nonneg_right h1 (by omega : 0 ≤ M ^ 2)
      have hOne : 1 * (M ^ 2) = M ^ 2 := by grind
      omega
    omega

end BakryEmeryCurvatureLogSobolevAndHypercontractiveFrontier
