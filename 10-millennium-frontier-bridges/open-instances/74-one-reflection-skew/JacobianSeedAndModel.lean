import Proposal.PhysicalCubicJets
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-!
# Exact Integral-Incidence Seed, 13×13 Inverse Jacobian over `𝔽_5`,
# Residue Divergence Cancellation, and 5×5 Physical-to-Weierstrass Determinant Law (`#74`)
-/
noncomputable section
set_option maxHeartbeats 8000000
namespace OneReflectionSkewJacobianSeed
open Polynomial

abbrev F5 := ZMod 5

def r_seed : Polynomial F5 := 2 * X^2 + 3 * X + 1
def x_seed : Polynomial F5 := 2 * X^4 + 2 * X^3 + X^2 + X + 3
def y_seed : Polynomial F5 := 4 * X^6 + 4 * X^5 + 3 * X^4 + X^2 + 4 * X + 2

def reducedEquation {R : Type*} [CommRing R] (r t x y : R) : R :=
  r^6 + 2 * r^5 * t + 3 * r^4 * t^2 + 4 * r^3 * t * x + 3 * r * t^5 + r * t^3 * x + t^6 + 3 * x^3 + 2 * y^2

lemma five_zero : (5 : Polynomial F5) = 0 := by
  simpa only [map_ofNat, map_zero] using congrArg (Polynomial.C : F5 →+* Polynomial F5)
    (by decide : (5 : F5) = 0)

theorem seed_incidence : reducedEquation r_seed X x_seed y_seed = 0 := by
  have he : reducedEquation r_seed X x_seed y_seed =
      5 * (24 * X^12 + 168 * X^11 + 684 * X^10 + 1736 * X^9 + 2954 * X^8 +
        3506 * X^7 + 3000 * X^6 + 1904 * X^5 + 919 * X^4 + 326 * X^3 +
        88 * X^2 + 29 * X + 18) := by
    dsimp [reducedEquation, r_seed, x_seed, y_seed]
    ring
  rw [he, five_zero, zero_mul]

def coefficientJacobian : Matrix (Fin 13) (Fin 13) F5 := ![
  ![0,0,0,0,0,0,3,0,0,0,0,0,0],
  ![1,0,1,0,0,0,1,3,0,0,0,0,0],
  ![1,1,3,1,0,0,4,1,3,0,0,0,0],
  ![0,1,4,3,1,0,0,4,1,3,0,0,0],
  ![3,0,4,4,3,1,2,0,4,1,3,0,0],
  ![1,3,3,4,4,3,1,2,0,4,1,3,0],
  ![0,1,3,3,4,4,1,1,2,0,4,1,3],
  ![2,0,1,3,3,4,0,1,1,2,0,4,1],
  ![2,2,4,1,3,3,0,0,1,1,2,0,4],
  ![0,2,1,4,1,3,0,0,0,1,1,2,0],
  ![1,0,0,1,4,1,0,0,0,0,1,1,2],
  ![2,1,0,0,1,4,0,0,0,0,0,1,1],
  ![0,2,0,0,0,1,0,0,0,0,0,0,1]
]

def inverseJacobian : Matrix (Fin 13) (Fin 13) F5 := ![
  ![0,4,3,1,0,1,3,1,3,3,3,1,1],
  ![2,4,2,3,4,2,2,3,3,0,2,3,2],
  ![0,0,0,1,2,4,2,1,1,1,4,1,0],
  ![4,0,0,1,3,1,1,3,2,2,0,0,1],
  ![0,4,0,0,1,3,1,1,3,2,2,0,0],
  ![0,0,4,3,1,3,4,4,4,1,4,0,0],
  ![2,0,0,0,0,0,0,0,0,0,0,0,0],
  ![1,4,4,1,1,0,0,1,2,2,1,1,3],
  ![0,1,4,2,2,3,1,3,4,0,4,4,1],
  ![4,0,1,0,4,1,0,2,4,0,4,0,4],
  ![2,4,0,1,0,4,1,0,2,4,0,4,0],
  ![2,2,4,2,0,3,3,3,2,4,2,2,4],
  ![1,2,2,1,1,3,2,0,0,4,2,4,2]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem inverse_product : coefficientJacobian * inverseJacobian = 1 := by decide

theorem mordell_residue_divergence_cancellation
    {K : Type*} [CommRing K] (X Y2 B6 psi d_psi d_B6 : K)
    (hcurve : Y2 = X ^ 3 + B6) :
    (d_psi * (2 * Y2) - psi * d_B6) + (2 * d_psi * (2 * Y2) - (2 * X * d_psi) * (3 * X ^ 2)) =
      6 * B6 * d_psi - psi * d_B6 := by
  linear_combination 6 * d_psi * hcurve

theorem mordell_wronskian_divergence_zero
    {K : Type*} [CommRing K] (X Y2 B6 E1_B6 E2_B6 E1_E2_B6 : K)
    (hcurve : Y2 = X ^ 3 + B6) :
    let psi1 := E2_B6
    let psi2 := -E1_B6
    let d1_psi1 := E1_E2_B6
    let d2_psi2 := -E1_E2_B6
    ((d1_psi1 * (2 * Y2) - psi1 * E1_B6) +
      (2 * d1_psi1 * (2 * Y2) - (2 * X * d1_psi1) * (3 * X ^ 2))) +
    ((d2_psi2 * (2 * Y2) - psi2 * E2_B6) +
      (2 * d2_psi2 * (2 * Y2) - (2 * X * d2_psi2) * (3 * X ^ 2))) = 0 := by
  dsimp
  linear_combination 0 * hcurve

theorem raw_determinant_74_cleared
    {K : Type*} [CommRing K]
    (X0 X1 Y1 U_x U_y Theta_x Theta_y J_x J_y J_c1 : K) :
    let dX0_U := 2 * X0 * U_x
    let dX1_U := 2 * X1 * U_y - Y1 * (U_y * (2 * X1))
    let dY1_U := X1 * (U_y * (2 * X1))
    let dX0_Th := 2 * X0 * Theta_x
    let dX1_Th := 2 * X1 * Theta_y
    let dX0_J := 2 * X0 * J_x
    let dX1_J := 2 * X1 * J_y - Y1 * J_c1
    let dY1_J := X1 * J_c1
    (dX0_U * (dX1_Th * dY1_J) - dX0_Th * (dX1_U * dY1_J - dY1_U * dX1_J) +
      dX0_J * (dX1_U * 0 - dY1_U * dX1_Th)) =
    4 * X0 * X1 ^ 2 *
      (J_c1 * (U_x * Theta_y - U_y * Theta_x) +
        2 * X1 * U_y * (Theta_x * J_y - Theta_y * J_x)) := by
  dsimp
  ring

end OneReflectionSkewJacobianSeed
end
