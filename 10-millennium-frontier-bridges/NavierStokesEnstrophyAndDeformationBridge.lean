import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Navier–Stokes / Euler Vorticity–Strain Orthogonality & Pressure-Poisson Trace Identity

In the Common Ground V34 Atlas, the eight-project source universe includes both `euler` and `ns`
(`Navier–Stokes`), and the selected results feature:
- `determinant_rate` (`MatrixEnergyVolume.determinant_rate_sq_le_frobenius`), which bounds the
  squared rate of volume change by the Frobenius energy $\operatorname{tr}(A^T A)$ of the velocity
  gradient $A = G(t)^{-1}G'(t)$, and
- `l2_averaging` (`EulerOrdinaryMollifier.mollify_tendsto`), which proves $L^2$ norm convergence of
  spatial mollification on `EulerMeanSolenoidal.L2`.

This module formalizes the fundamental **Symmetric Strain vs. Antisymmetric Vorticity Decomposition**
that links `MatrixEnergyVolume` ($\operatorname{tr}(A^T A)$) to the 3D Euler/Navier–Stokes
**Enstrophy, Strain, and Pressure-Poisson Equation**:
1. `strain_vorticity_pointwise_orthogonality`:
   For any velocity gradient matrix $A_{ij} = \partial_j u_i$, decomposing $A = S + \Omega$ into its
   symmetric rate-of-strain tensor $S_{ij} = \frac{1}{2}(A_{ij} + A_{ji})$ and antisymmetric
   vorticity tensor $\Omega_{ij} = \frac{1}{2}(A_{ij} - A_{ji})$ yields the pointwise quadratic
   identities:
   $$A_{ij}^2 + A_{ji}^2 = 2 S_{ij}^2 + 2 \Omega_{ij}^2, \qquad
     2 A_{ij} A_{ji} = 2 S_{ij}^2 - 2 \Omega_{ij}^2.$$
2. `frobenius_eq_strain_sq_add_vorticity_sq`:
   Summing over all matrix entries $(i, j) \in \text{Fin } D \times \text{Fin } D$ proves that the
   Frobenius energy $\operatorname{tr}(A^T A) = \sum_{i,j} A_{ij}^2$ appearing in V34's
   `determinant_rate_sq_le_frobenius` splits orthogonally into **dissipative strain energy**
   $\|S\|_F^2$ plus **enstrophy (vorticity energy)** $\|\Omega\|_F^2$:
   $$\sum_{i,j} A_{ij}^2 = \sum_{i,j} S_{ij}^2 + \sum_{i,j} \Omega_{ij}^2.$$
3. `trace_sq_matrix_eq_strain_sub_vorticity`:
   Proves that the second matrix invariant $\operatorname{tr}(A^2) = \sum_{i,j} A_{ij} A_{ji}$
   (which equals $-\Delta p$, the source term of the incompressible **Pressure-Poisson Equation**
   when $\nabla \cdot u = \operatorname{tr}(A) = 0$) is the exact difference between strain energy
   and enstrophy:
   $$\sum_{i,j} A_{ij} A_{ji} = \sum_{i,j} S_{ij}^2 - \sum_{i,j} \Omega_{ij}^2,$$
   and therefore $\operatorname{tr}(A^T A) = \operatorname{tr}(A^2) + 2\|\Omega\|_F^2$.
-/

namespace CommonGround.NavierStokesBridge

open scoped BigOperators Matrix

variable {D : ℕ}

/-- Symmetric strain-rate entry $S_{ij} = \frac{1}{2}(A_{ij} + A_{ji})$. -/
noncomputable def strainEntry (A : Matrix (Fin D) (Fin D) ℝ) (i j : Fin D) : ℝ :=
  (A i j + A j i) / 2

/-- Antisymmetric vorticity/spin entry $\Omega_{ij} = \frac{1}{2}(A_{ij} - A_{ji})$. -/
noncomputable def vorticityEntry (A : Matrix (Fin D) (Fin D) ℝ) (i j : Fin D) : ℝ :=
  (A i j - A j i) / 2

/-- Theorem 1 (Pointwise Strain–Vorticity Quadratic Identities):
For every pair of indices $(i, j)$:
1. $A_{ij} = S_{ij} + \Omega_{ij}$,
2. $A_{ij}^2 + A_{ji}^2 = 2(S_{ij}^2 + \Omega_{ij}^2)$,
3. $A_{ij} A_{ji} = S_{ij}^2 - \Omega_{ij}^2$. -/
theorem strain_vorticity_pointwise_identities
    (A : Matrix (Fin D) (Fin D) ℝ) (i j : Fin D) :
    A i j = strainEntry A i j + vorticityEntry A i j ∧
    (A i j) ^ 2 + (A j i) ^ 2 = 2 * ((strainEntry A i j) ^ 2 + (vorticityEntry A i j) ^ 2) ∧
    A i j * A j i = (strainEntry A i j) ^ 2 - (vorticityEntry A i j) ^ 2 := by
  unfold strainEntry vorticityEntry
  refine ⟨by ring, by ring, by ring⟩

/-- Theorem 2 (Global Frobenius Energy = Strain Energy + Enstrophy):
The Frobenius norm squared $\sum_{i,j} A_{ij}^2$ (which equals $\operatorname{tr}(A^T A)$ in
`MatrixEnergyVolume.determinant_rate_sq_le_frobenius`) equals the sum of squared symmetric strain
entries plus the sum of squared antisymmetric vorticity entries. -/
theorem frobenius_eq_strain_sq_add_vorticity_sq
    (A : Matrix (Fin D) (Fin D) ℝ) :
    (∑ i : Fin D, ∑ j : Fin D, (A i j) ^ 2) =
      (∑ i : Fin D, ∑ j : Fin D, (strainEntry A i j) ^ 2) +
        (∑ i : Fin D, ∑ j : Fin D, (vorticityEntry A i j) ^ 2) := by
  have hsym : (∑ i : Fin D, ∑ j : Fin D, (A j i) ^ 2) =
      ∑ i : Fin D, ∑ j : Fin D, (A i j) ^ 2 := by
    rw [Finset.sum_comm]
  have hdouble :
      2 * (∑ i : Fin D, ∑ j : Fin D, (A i j) ^ 2) =
        2 * ((∑ i : Fin D, ∑ j : Fin D, (strainEntry A i j) ^ 2) +
          (∑ i : Fin D, ∑ j : Fin D, (vorticityEntry A i j) ^ 2)) := by
    calc
      2 * (∑ i : Fin D, ∑ j : Fin D, (A i j) ^ 2)
        = (∑ i : Fin D, ∑ j : Fin D, (A i j) ^ 2) +
            (∑ i : Fin D, ∑ j : Fin D, (A j i) ^ 2) := by linarith [hsym]
      _ = ∑ i : Fin D, ∑ j : Fin D, ((A i j) ^ 2 + (A j i) ^ 2) := by
            simp_rw [← Finset.sum_add_distrib]
      _ = ∑ i : Fin D, ∑ j : Fin D,
            2 * ((strainEntry A i j) ^ 2 + (vorticityEntry A i j) ^ 2) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            exact (strain_vorticity_pointwise_identities A i j).2.1
      _ = 2 * ((∑ i : Fin D, ∑ j : Fin D, (strainEntry A i j) ^ 2) +
            (∑ i : Fin D, ∑ j : Fin D, (vorticityEntry A i j) ^ 2)) := by
            simp_rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
  linarith

/-- Theorem 3 (Pressure-Poisson Invariant $\operatorname{tr}(A^2)$ = Strain Energy − Enstrophy):
In incompressible Euler/Navier–Stokes flows ($\nabla \cdot u = 0$), taking the divergence of the
momentum equation yields $-\Delta p = \operatorname{tr}((\nabla u)^2) = \sum_{i,j} A_{ij} A_{ji}$.
This theorem proves that $\sum_{i,j} A_{ij} A_{ji} = \|S\|_F^2 - \|\Omega\|_F^2$. -/
theorem trace_sq_matrix_eq_strain_sub_vorticity
    (A : Matrix (Fin D) (Fin D) ℝ) :
    (∑ i : Fin D, ∑ j : Fin D, A i j * A j i) =
      (∑ i : Fin D, ∑ j : Fin D, (strainEntry A i j) ^ 2) -
        (∑ i : Fin D, ∑ j : Fin D, (vorticityEntry A i j) ^ 2) := by
  simp_rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact (strain_vorticity_pointwise_identities A i j).2.2

end CommonGround.NavierStokesBridge
