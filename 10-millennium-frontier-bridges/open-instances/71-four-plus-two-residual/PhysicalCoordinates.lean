import Proposal.PhysicalField
import Proposal.ReverseEdgeCovariants
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Reverse-Edge `e = 0` Cubic Coordinates (`f = 2d`) in the Physical Function Field for `#71`

Under `B1 = (X0, X1)`, `B2 = (Y0, Y1)`, `B3 = (X2, Y2)` with `radial = X2^2`,
`x = X0^2 / X2^2`, `y = Y0^2 / X2^2`, `z = 1`, and passive ratios
`c0 = X1 / X0`, `c1 = Y1 / Y0`, `c2 = Y2 / X2`, the official sextic `sextic = 0`
in `FunctionField` satisfies `U_e0 coeffA coeffB coeffC coeffD coeffF x y 1 = 0`
with `coeffF = 2 * coeffD = (10/7) * c0 * c1`.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace FourPlusTwoCoordinates
open FourPlusTwoPhysical ReverseEdgeCovariants

def coordinate (i : Fin 6) : FunctionField := residueMap (MvPolynomial.X i)
local notation "p" => coordinate

lemma coordinate_ne_zero (i : Fin 6) : p i ≠ 0 := by
  intro hz
  have hd := (residueMap_kernel _).mp hz
  have hb := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hd (MvPolynomial.X_ne_zero i)
  rw [sextic_homogeneous.totalDegree sextic_irreducible.ne_zero,
    MvPolynomial.totalDegree_X] at hb
  norm_num at hb

lemma field_seventh : residueMap (MvPolynomial.C (1/7 : ℂ)) = (1/7 : FunctionField) := by
  change (residueMap.comp MvPolynomial.C) (1/7 : ℂ) = _
  rw [map_div₀, map_one, map_ofNat]

lemma equation_zero :
    p 0^6 + 5 * p 0^5 * p 1 * (1/7) + 5 * p 0^3 * p 1 * p 3 * p 4 * (1/7) +
      10 * p 0 * p 1^5 * (1/7) + 10 * p 0 * p 1 * p 3^3 * p 4 * (1/7) +
      p 1^6 + p 2^6 + 15 * p 2^4 * p 5^2 * (1/7) + 10 * p 2^2 * p 5^4 * (1/7) +
      p 3^6 + 5 * p 3^5 * p 4 * (1/7) + 15 * p 3 * p 4^5 * (1/7) + p 4^6 + p 5^6 = 0 := by
  have he := (residueMap_kernel sextic).mpr (dvd_refl sextic)
  simpa only [sextic, map_add, map_mul, map_pow, map_ofNat, field_seventh, coordinate] using he

def radial : FunctionField := p 2^2
def c0 : FunctionField := p 1 / p 0
def c1 : FunctionField := p 4 / p 3
def c2 : FunctionField := p 5 / p 2
def x : FunctionField := p 0^2 / radial
def y : FunctionField := p 3^2 / radial
def coeffA : FunctionField := 1 + 5 * c0 * (1/7) + 10 * c0^5 * (1/7) + c0^6
def coeffB : FunctionField := 1 + 5 * c1 * (1/7) + 15 * c1^5 * (1/7) + c1^6
def coeffC : FunctionField := 1 + 15 * c2^2 * (1/7) + 10 * c2^4 * (1/7) + c2^6
def coeffD : FunctionField := 5 * c0 * c1 * (1/7)
def coeffF : FunctionField := 10 * c0 * c1 * (1/7)

lemma radial_ne_zero : radial ≠ 0 := pow_ne_zero _ (coordinate_ne_zero 2)
lemma c0_ne_zero : c0 ≠ 0 := div_ne_zero (coordinate_ne_zero 1) (coordinate_ne_zero 0)
lemma c1_ne_zero : c1 ≠ 0 := div_ne_zero (coordinate_ne_zero 4) (coordinate_ne_zero 3)
lemma c2_ne_zero : c2 ≠ 0 := div_ne_zero (coordinate_ne_zero 5) (coordinate_ne_zero 2)

theorem coeffF_eq_two_coeffD : coeffF = 2 * coeffD := by
  unfold coeffF coeffD
  ring

theorem cubic_equation :
    U_e0 coeffA coeffB coeffC coeffD coeffF x y 1 = 0 := by
  have h0 := coordinate_ne_zero 0
  have h2 := coordinate_ne_zero 2
  have h3 := coordinate_ne_zero 3
  have he := equation_zero
  simp only [U_e0, fBin, coeffA, coeffB, coeffC, coeffD, coeffF, x, y, radial, c0, c1, c2]
  field_simp
  linear_combination he

end FourPlusTwoCoordinates
end
