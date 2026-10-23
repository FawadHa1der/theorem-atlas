# Discovery 05: Matrix Energy Volume Bounds, Euler $L^2$ Mollification & Lagrangian Volume Stability

## Overview & Verification Status
- **V34 Record Owners:** [`determinant_rate`](http://127.0.0.1:4200/preview/v34/?v=1&a=determinant_rate&s=det-rate) (`CommonGround.MatrixEnergyVolume.determinant_rate_sq_le_frobenius`) and [`l2_averaging`](http://127.0.0.1:4200/preview/v34/?v=1&a=l2_averaging&s=l2-mollify-tendsto) (`EulerOrdinaryMollifier.mollify_tendsto`)
- **V34 Proof Status:**
  - `determinant_rate`: Native Lean 4.33.1 verified (`Mathlib db584cd6`), combining `MetricCodesSelectedTransport.sq_trace_le_dimension_mul_trace_sq` and `Poincare.Matrix.hasDerivAt_det_eq_det_mul_trace_inv_mul`.
  - `l2_averaging`: Native Lean 4.34.0-rc2 constructor-graph capture (`422` type rows, `1,106` value rows across `46,227` visited declarations, SHA-256 `174ff9ecd1152e7cd92b6c788638f175e8100af1df51d0cf7c89fa306153f277`), zero `sorryAx`.
- **Source Files in This Folder:**
  1. [`MatrixEnergyVolume.lean`](./MatrixEnergyVolume.lean) — Verified V34 Lean 4 source proving `determinant_rate_sq_le_frobenius`.
  2. [`LagrangianVolumeStability.lean`](./LagrangianVolumeStability.lean) — **Novel Breakthrough Formalization** connecting the matrix determinant-rate inequality with incompressible/compressible Lagrangian fluid mechanics and solenoidal trace conditions.

## 1. The V34 Discoveries
1. **Coding-to-Poincaré Matrix Adapter (`determinant_rate`):** For a differentiable curve $G : \mathbb{R} \to \text{Matrix}(\text{Fin } D, \text{Fin } D, \mathbb{R})$ at a nonsingular matrix $G(t)$, writing $A = G(t)^{-1}G'(t)$, Jacobi's formula $(\det \circ G)'(t) = \det(G(t))\,\text{tr}(A)$ combines with the Cauchy–Schwarz trace inequality $(\text{tr } A)^2 \le D\,\text{tr}(A^T A)$ to yield:
   $$\big((\det \circ G)'(t)\big)^2 \le \det(G(t))^2 \cdot D \cdot \text{tr}(A^T A).$$
2. **Whole-Field $L^2$ Mollification (`l2_averaging`):** For any square-integrable vector field $u \in L^2(\mathbb{R}^3, \mathbb{R}^3; \text{volume})$ (the underlying type of `EulerMeanSolenoidal.L2`), shrinking normalized bump convolutions $\text{mollify } n\ u$ converge to $u$ in $L^2$ norm by composing `ContDiffBump.convolution_tendsto_right_of_continuous` with whole-field translation continuity `EulerMeanTimeTranslation.translation_continuous`.

## 2. New Breakthrough in `LagrangianVolumeStability.lean`
In continuum mechanics, a Lagrangian flow map $X(t, x)$ has deformation gradient $G(t) = \nabla_x X(t, x)$ satisfying $G'(t) = (\nabla u) G(t)$, so $\text{tr}(G(t)^{-1}G'(t)) = \text{tr}(\nabla u) = \nabla \cdot u$. In [`LagrangianVolumeStability.lean`](./LagrangianVolumeStability.lean), we formalize:
- **Solenoidal Liouville Invariance (`solenoidal_zero_determinant_rate`):** When the velocity gradient is solenoidal ($\text{tr } A = \nabla \cdot u = 0$), Jacobi's identity immediately gives $\det'(t) = 0$.
- **Scale-Invariant Logarithmic Volume Rate (`log_volume_rate_sq_le_dim_frobenius`):** Dividing by $\det(G(t))^2 > 0$ isolates the logarithmic volume distortion rate:
  $$\left(\frac{\det'(t)}{\det G(t)}\right)^2 \le D \cdot \text{tr}(A^T A).$$
- **Exact Shear–Dilatation Gap Decomposition (`trace_frobenius_gap_decomposition`):** Separates the Frobenius energy into diagonal dilatation variance and off-diagonal shear energy (`offDiagSqSum`), showing why pure shear flows increase Frobenius energy $\text{tr}(A^T A)$ without changing volume.
