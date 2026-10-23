import MetricCodesTraceTransport
import PoincareLib.Analysis.Matrix.Determinant
import Mathlib.Tactic.Ring

namespace CommonGround.MatrixEnergyVolume
open scoped BigOperators Matrix Matrix.Norms.Elementwise

theorem determinant_rate_sq_le_frobenius
    {D : ℕ} (G : ℝ → Matrix (Fin D) (Fin D) ℝ)
    (G' : Matrix (Fin D) (Fin D) ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t)
    (hunit : IsUnit (G t).det) :
    (deriv (fun s => (G s).det) t) ^ 2 ≤
      ((G t).det) ^ 2 * (D : ℝ) *
        Matrix.trace ((((G t)⁻¹ * G')ᵀ) * ((G t)⁻¹ * G'))
 := by
  rw [(Poincare.Matrix.hasDerivAt_det_eq_det_mul_trace_inv_mul G G' t hG hunit).deriv,
    mul_pow]
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left
      (CommonGround.MetricCodesSelectedTransport.sq_trace_le_dimension_mul_trace_sq
        ((G t)⁻¹ * G')) (sq_nonneg (G t).det))

end CommonGround.MatrixEnergyVolume
