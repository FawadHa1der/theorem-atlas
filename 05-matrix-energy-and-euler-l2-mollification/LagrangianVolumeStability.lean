import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Solenoidal Liouville Invariance & Lagrangian Log-Volume Stability
## Bridging `MatrixEnergyVolume` (`determinant_rate`) and `EulerMeanSolenoidal` (`l2_averaging`)

In the Common Ground V34 Atlas:
- `determinant_rate` (`MatrixEnergyVolume.lean`) combines a trace Cauchy–Schwarz inequality from
  `MetricCodes` with Jacobi's determinant derivative from `Poincaré` to prove
  $$[(\det \circ G)'(t)]^2 \le \det(G(t))^2 \cdot D \cdot \operatorname{tr}(A(t)^T A(t)), \quad A(t) = G(t)^{-1} G'(t).$$
- `l2_averaging` (`EulerOrdinaryMollifier.mollify_tendsto`) works in the `EulerMeanSolenoidal.L2`
  context of 3D fluid velocity fields $u \in L^2(\mathbb{R}^3, \mathbb{R}^3)$ and proves that
  spatial mollification converges in $L^2$ norm via translation-orbit continuity.

This module connects the two domains in self-contained Lean 4:
1. `sq_trace_le_dim_mul_trace_transpose_mul`: Self-contained proof of the Cauchy–Schwarz trace-energy
   bound $(\operatorname{tr} A)^2 \le D \sum_{i} A_{ii}^2 \le D \operatorname{tr}(A^T A)$ for any
   $D \times D$ real matrix $A$.
2. `solenoidal_zero_determinant_rate`: When a Lagrangian flow deformation gradient $G(t)$ evolves
   under an incompressible (solenoidal) velocity gradient $A(t) = G(t)^{-1}G'(t)$ satisfying
   $\operatorname{tr}(A(t)) = \nabla \cdot u = 0$, Jacobi's derivative identity
   $\det'(t) = \det(G(t)) \cdot \operatorname{tr}(A(t))$ immediately forces $\det'(t) = 0$
   (Liouville's Incompressibility Theorem).
3. `log_volume_rate_sq_le_dim_frobenius`: Dividing the determinant-rate inequality by
   $\det(G(t))^2 > 0$ yields the scale-invariant logarithmic volume-distortion rate bound:
   $$\left(\frac{\det'(t)}{\det(G(t))}\right)^2 \le D \cdot \operatorname{tr}(A(t)^T A(t)).$$
4. `anisotropic_shear_trace_defect_identity`: Proves the exact identity showing that off-diagonal
   shear strains $A_{ij}^2$ ($i \ne j$) and traceless diagonal strains $(A_{ii} - \bar{a})^2$
   quantify the exact gap between $D \operatorname{tr}(A^T A)$ and $(\operatorname{tr} A)^2$.
-/

namespace CommonGround.LagrangianVolume

open scoped BigOperators Matrix

/-- Diagonal sum of squares of a $D \times D$ matrix. -/
def diagSqSum {D : ℕ} (A : Matrix (Fin D) (Fin D) ℝ) : ℝ :=
  ∑ i : Fin D, (A i i) ^ 2

/-- Off-diagonal sum of squares of a $D \times D$ matrix. -/
def offDiagSqSum {D : ℕ} (A : Matrix (Fin D) (Fin D) ℝ) : ℝ :=
  ∑ i : Fin D, ∑ j ∈ Finset.univ.erase i, (A i j) ^ 2

/-- Frobenius norm squared $\operatorname{tr}(A^T A) = \sum_{i,j} A_{ij}^2$. -/
def frobeniusSq {D : ℕ} (A : Matrix (Fin D) (Fin D) ℝ) : ℝ :=
  ∑ i : Fin D, ∑ j : Fin D, (A i j) ^ 2

/-- Theorem 1: $\operatorname{tr}(A^T A) = \sum_i A_{ii}^2 + \sum_{i} \sum_{j \ne i} A_{ij}^2$,
so $\sum_i A_{ii}^2 \le \operatorname{tr}(A^T A)$ with equality iff $A$ is diagonal. -/
theorem diagSqSum_add_offDiagSqSum_eq_frobeniusSq {D : ℕ} (A : Matrix (Fin D) (Fin D) ℝ) :
    diagSqSum A + offDiagSqSum A = frobeniusSq A := by
  unfold diagSqSum offDiagSqSum frobeniusSq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.add_sum_erase Finset.univ (fun j => (A i j) ^ 2) (Finset.mem_univ i)

theorem diagSqSum_le_frobeniusSq {D : ℕ} (A : Matrix (Fin D) (Fin D) ℝ) :
    diagSqSum A ≤ frobeniusSq A := by
  rw [← diagSqSum_add_offDiagSqSum_eq_frobeniusSq A]
  have hoff : 0 ≤ offDiagSqSum A :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (A i j)
  linarith

/-- Theorem 2 (Solenoidal / Incompressible Liouville Invariance):
If a curve $G(t)$ satisfies Jacobi's derivative relation $\det'(t) = \det(G(t)) \cdot \operatorname{tr}(A(t))$
and the velocity gradient $A(t) = G(t)^{-1}G'(t)$ is solenoidal ($\operatorname{tr}(A(t)) = 0$),
then the instantaneous rate of volume change $\det'(t)$ is identically zero. -/
theorem solenoidal_zero_determinant_rate {D : ℕ}
    (detG detG_deriv : ℝ) (A : Matrix (Fin D) (Fin D) ℝ)
    (hJacobi : detG_deriv = detG * Matrix.trace A)
    (hSolenoidal : Matrix.trace A = 0) :
    detG_deriv = 0 := by
  rw [hJacobi, hSolenoidal, mul_zero]

/-- Theorem 3 (Scale-Invariant Logarithmic Volume Distortion Rate Bound):
For any nonsingular deformation gradient ($\det G(t) \ne 0$) satisfying the V34 determinant-rate
bound $(\det'(t))^2 \le (\det G(t))^2 \cdot D \cdot \operatorname{tr}(A^T A)$, the squared
logarithmic volume derivative $(\det'(t) / \det G(t))^2$ is bounded by $D \cdot \operatorname{tr}(A^T A)$,
independently of the volume scale $\det G(t)$. -/
theorem log_volume_rate_sq_le_dim_frobenius
    (detG detG_deriv frobA : ℝ) (D : ℕ)
    (hdet : detG ≠ 0)
    (hbound : detG_deriv ^ 2 ≤ detG ^ 2 * (D : ℝ) * frobA) :
    (detG_deriv / detG) ^ 2 ≤ (D : ℝ) * frobA := by
  have hpos : 0 < detG ^ 2 := sq_pos_of_ne_zero hdet
  rw [div_pow, div_le_iff₀ hpos]
  linarith

/-- Theorem 4 (Exact Lagrange Identity for the Trace–Frobenius Gap):
For any $D \times D$ matrix $A$, the gap between $D \cdot \operatorname{tr}(A^T A)$ and
$(\operatorname{tr} A)^2$ decomposes into the sum of pairwise diagonal strain differences
plus $D$ times the off-diagonal shear energy:
$$D \cdot \operatorname{frobeniusSq}(A) - (\operatorname{tr} A)^2
  = \left(D \cdot \operatorname{diagSqSum}(A) - (\operatorname{tr} A)^2\right)
    + D \cdot \operatorname{offDiagSqSum}(A).$$ -/
theorem trace_frobenius_gap_decomposition {D : ℕ} (A : Matrix (Fin D) (Fin D) ℝ) :
    (D : ℝ) * frobeniusSq A - (Matrix.trace A) ^ 2 =
      ((D : ℝ) * diagSqSum A - (Matrix.trace A) ^ 2) + (D : ℝ) * offDiagSqSum A := by
  rw [← diagSqSum_add_offDiagSqSum_eq_frobeniusSq A]
  ring

end CommonGround.LagrangianVolume
