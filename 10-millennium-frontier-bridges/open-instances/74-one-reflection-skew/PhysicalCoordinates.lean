import Proposal.PhysicalField
import Proposal.ReverseEdgeCovariants
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Reverse-Edge `e = 0` Cubic Coordinates in the Physical Function Field for `#74 one-reflection-skew`

Under `B1 = (X0, X2, Y0)`, `B2 = (X1, Y1)`, `B3 = (Y2)` with `radial = Y2^2`,
`x = X0^2 / Y2^2`, `y = X1^2 / Y2^2`, `z = 1`, and passive ratios
`c0 = Y0 / X0`, `c1 = Y1 / X1`, `c2 = X2 / X0`, the official sextic `sextic = 0`
in `FunctionField` satisfies `U_e0 coeffA coeffB coeffC coeffD coeffF x y 1 = 0`.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace OneReflectionSkewCoordinates
open OneReflectionSkewPhysical ReverseEdgeCovariants

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
    p 0^6 + p 0^3*p 1*p 3*p 4 +
      p 0*p 1*p 3^3*p 4 * (1/7) - p 0*p 1*p 3*p 4^3 * (1/7) +
      p 1^6 + p 1^3*p 2*p 3*p 4 + p 2^6 + p 3^6 + p 4^6 + p 5^6 = 0 := by
  have he := (residueMap_kernel sextic).mpr (dvd_refl sextic)
  simpa only [sextic, map_add, map_sub, map_mul, map_pow, field_seventh, coordinate] using he

def radial : FunctionField := p 5^2
def c0 : FunctionField := p 3 / p 0
def c1 : FunctionField := p 4 / p 1
def c2 : FunctionField := p 2 / p 0
def x : FunctionField := p 0^2 / radial
def y : FunctionField := p 1^2 / radial
def coeffA : FunctionField := 1 + c0^6 + c2^6
def coeffB : FunctionField := 1 + c1^6
def coeffC : FunctionField := 1
def coeffD : FunctionField := c0 * c1 * (1 + (1/7) * c0^2)
def coeffF : FunctionField := c0 * c1 * (c2 - (1/7) * c1^2)

lemma radial_ne_zero : radial ≠ 0 := pow_ne_zero _ (coordinate_ne_zero 5)
lemma c0_ne_zero : c0 ≠ 0 := div_ne_zero (coordinate_ne_zero 3) (coordinate_ne_zero 0)
lemma c1_ne_zero : c1 ≠ 0 := div_ne_zero (coordinate_ne_zero 4) (coordinate_ne_zero 1)
lemma c2_ne_zero : c2 ≠ 0 := div_ne_zero (coordinate_ne_zero 2) (coordinate_ne_zero 0)

theorem cubic_equation :
    U_e0 coeffA coeffB coeffC coeffD coeffF x y 1 = 0 := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h5 := coordinate_ne_zero 5
  have he := equation_zero
  simp only [U_e0, fBin, coeffA, coeffB, coeffC, coeffD, coeffF, x, y, radial, c0, c1, c2]
  field_simp
  linear_combination he

end OneReflectionSkewCoordinates
end
