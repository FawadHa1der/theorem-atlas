import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Exact Integral-Incidence Seed, 13×13 Inverse Jacobian over `𝔽_5`,
# Residue Divergence Cancellation, and Binary-Block Contact-Cover Wronskian Law (`#71`)
-/
noncomputable section
set_option maxHeartbeats 8000000
namespace FourPlusTwoJacobianSeed
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

theorem binary_block_wronskian_certificate_directional
    {K : Type*} [CommRing K]
    (C0 r0 C0_x C0_y r0_x r0_y C1 r1 C1_u C1_v r1_u r1_v : K) :
    let J0 := C0_x * r0_y - C0_y * r0_x
    let J1 := C1_u * r1_v - C1_v * r1_u
    let P0_x := 3 * C0 ^ 2 * C0_x + 2 * r0 * r0_x
    let P0_y := 3 * C0 ^ 2 * C0_y + 2 * r0 * r0_y
    let P1_u := 3 * C1 ^ 2 * C1_u + 2 * r1 * r1_u
    let P1_v := 3 * C1 ^ 2 * C1_v + 2 * r1 * r1_v
    let N_x := J1 * r0 * (-C0_y)
    let N_y := J1 * r0 * C0_x
    let N_u := J0 * r1 * (-C1_v)
    let N_v := J0 * r1 * C1_u
    let D_contact := r0 ^ 2 + r1 ^ 2
    N_x * P0_x + N_y * P0_y + N_u * P1_u + N_v * P1_v =
      (2 * J0 * J1) * D_contact := by
  dsimp
  ring

end FourPlusTwoJacobianSeed
end
