import Proposal.PhysicalChart

/-!
# Block Paired-Normal Gradient Identities for `#71 four-plus-two-residual`

Proves that in the physical function field `FunctionField` of `#71 four-plus-two-residual`,
the paired Euler gradient `X0 * F0 + X1 * F1` on `B1 = (X0, X1)` equals `2 * radial^3 * x * cubicNormal`,
and the paired Euler gradient `Y0 * F3 + Y1 * F4` on `B2 = (Y0, Y1)` equals `2 * radial^3 * y * cubicNormalY`.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace FourPlusTwoNormalTransport
open FourPlusTwoPhysical FourPlusTwoCoordinates ReverseEdgeCovariants

local notation "p" => coordinate

lemma coordinate_X (i : Fin 6) : residueMap (MvPolynomial.X i) = p i := rfl

def gradient (i : Fin 6) : FunctionField := residueMap (MvPolynomial.pderiv i sextic)
def hessian (i j : Fin 6) : FunctionField :=
  residueMap (MvPolynomial.pderiv i (MvPolynomial.pderiv j sextic))

def pairedGradientX : FunctionField := p 0 * gradient 0 + p 1 * gradient 1
def pairedGradientY : FunctionField := p 3 * gradient 3 + p 4 * gradient 4
def cubicNormal : FunctionField := fxBin coeffA coeffB coeffD coeffF x y
def cubicNormalY : FunctionField := fyBin coeffA coeffB coeffD coeffF x y

theorem paired_gradient_identity_X : pairedGradientX = 2 * radial^3 * x * cubicNormal := by
  have h0 := coordinate_ne_zero 0
  have h2 := coordinate_ne_zero 2
  have h3 := coordinate_ne_zero 3
  simp only [pairedGradientX, gradient, sextic, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    map_add, map_mul, map_pow, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X, Pi.single_apply]
  norm_num [Fin.ext_iff, coordinate_X, map_ofNat, field_seventh]
  simp only [cubicNormal, fxBin, coeffA, coeffD, coeffF, radial, x, y, c0, c1]
  field_simp
  ring

theorem paired_gradient_identity_Y : pairedGradientY = 2 * radial^3 * y * cubicNormalY := by
  have h0 := coordinate_ne_zero 0
  have h2 := coordinate_ne_zero 2
  have h3 := coordinate_ne_zero 3
  simp only [pairedGradientY, gradient, sextic, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    map_add, map_mul, map_pow, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X, Pi.single_apply]
  norm_num [Fin.ext_iff, coordinate_X, map_ofNat, field_seventh]
  simp only [cubicNormalY, fyBin, coeffB, coeffD, coeffF, radial, x, y, c0, c1]
  field_simp
  ring

end FourPlusTwoNormalTransport
end
