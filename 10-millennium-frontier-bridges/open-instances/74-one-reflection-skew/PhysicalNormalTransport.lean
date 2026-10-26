import Proposal.PhysicalChart

/-!
# 3-Coordinate Paired-Normal Transport and Paired-Gradient Identities for `#74 one-reflection-skew`

Proves the 3-coordinate paired-normal gradient identity `X0*F0 + X2*F2 + Y0*F3 = 2*R^3*x*U_x`,
the 2-coordinate paired-normal gradient identity `X1*F1 + Y1*F4 = 2*R^3*y*U_y`, and the
cleared 3-coordinate paired-normal residue transport identity `paired_normal_change_3coord_cleared`.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace OneReflectionSkewNormalTransport
open OneReflectionSkewPhysical OneReflectionSkewCoordinates ReverseEdgeCovariants

local notation "p" => coordinate

lemma coordinate_X (i : Fin 6) : residueMap (MvPolynomial.X i) = p i := rfl

def gradient (i : Fin 6) : FunctionField := residueMap (MvPolynomial.pderiv i sextic)
def hessian (i j : Fin 6) : FunctionField :=
  residueMap (MvPolynomial.pderiv i (MvPolynomial.pderiv j sextic))

def pairedGradient3 : FunctionField := p 0 * gradient 0 + p 2 * gradient 2 + p 3 * gradient 3
def pairedGradient2 : FunctionField := p 1 * gradient 1 + p 4 * gradient 4
def cubicNormal : FunctionField := fxBin coeffA coeffB coeffD coeffF x y
def cubicNormalY : FunctionField := fyBin coeffA coeffB coeffD coeffF x y

theorem paired_gradient_identity_3 : pairedGradient3 = 2 * radial^3 * x * cubicNormal := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h5 := coordinate_ne_zero 5
  simp only [pairedGradient3, gradient, sextic, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    map_add, map_sub, map_mul, map_pow, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X, Pi.single_apply]
  norm_num [Fin.ext_iff, coordinate_X, map_ofNat, field_seventh]
  simp only [cubicNormal, fxBin, coeffA, coeffD, coeffF, radial, x, y, c0, c1, c2]
  field_simp
  ring

theorem paired_gradient_identity_2 : pairedGradient2 = 2 * radial^3 * y * cubicNormalY := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h5 := coordinate_ne_zero 5
  simp only [pairedGradient2, gradient, sextic, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    map_add, map_sub, map_mul, map_pow, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X, Pi.single_apply]
  norm_num [Fin.ext_iff, coordinate_X, map_ofNat, field_seventh]
  simp only [cubicNormalY, fyBin, coeffB, coeffD, coeffF, radial, x, y, c0, c1, c2]
  field_simp
  ring

theorem paired_normal_change_3coord_cleared
    {K : Type*} [CommRing K]
    (p0 r q f h g fpp fpr fpq frr frq fqq : K) :
    let G1 := p0 * f + r * h + q * g
    let H11 := p0 ^ 2 * fpp + r ^ 2 * frr + q ^ 2 * fqq +
               2 * p0 * r * fpr + 2 * p0 * q * fpq + 2 * r * q * frq
    let f_df_r := f * fpr - h * fpp
    let f_dh_r := f * frr - h * fpr
    let f_dg_r := f * frq - h * fpq
    let f_dG1_r := -h * f + p0 * f_df_r + f * h + r * f_dh_r + q * f_dg_r
    let f_df_q := f * fpq - g * fpp
    let f_dh_q := f * frq - g * fpr
    let f_dg_q := f * fqq - g * fpq
    let f_dG1_q := -g * f + p0 * f_df_q + r * f_dh_q + f * g + q * f_dg_q
    let num_div_r := G1 * f * (3 * p0 ^ 2 * h * q ^ 3 * r - p0 ^ 3 * q ^ 3 * f) +
                     p0 ^ 3 * q ^ 3 * r * (f * f_dG1_r + G1 * f_df_r)
    let num_div_q := G1 * f * (3 * p0 ^ 2 * g * q ^ 4 - 4 * p0 ^ 3 * q ^ 3 * f) +
                     p0 ^ 3 * q ^ 4 * (f * f_dG1_q + G1 * f_df_q)
    G1 ^ 2 * (3 * p0 ^ 2 * q ^ 3 * f - p0 ^ 3 * q ^ 3 * fpp) =
      f ^ 2 * p0 ^ 3 * q ^ 3 * (8 * G1 - H11) + (num_div_r + num_div_q) := by
  dsimp
  ring

end OneReflectionSkewNormalTransport
end
