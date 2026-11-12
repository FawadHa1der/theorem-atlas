import Proposal.PhysicalNormalTransport

/-!
# In-Field 3-Coordinate Paired-Normal Source Reduction for `#74 one-reflection-skew`

Proves in `FunctionField` of `#74 one-reflection-skew`:
1. `paired_hessian_identity_3 : pairedHessian3 - pairedGradient3 = 4 * radial^3 * x^2 * cubicSecondNormal`
2. `paired_normal_change_3coord`: For any two derivations `Dr, Dq` satisfying the normal-chart rules on `(p, r, q)`,
   the `X0`-normal source `3 * p^2 * q^3 / f - p^3 * q^3 * fpp / f^2` reduces to the paired-normal source
   `p^3 * q^3 * (8 * G1 - H11) / G1^2` plus the exact 2-component `residueDivergence` of `(-p^3 * q^3 * r / G1, -p^3 * q^4 / G1)`.
3. `physical_source_transport_74`: In `FunctionField`,
   `residueMap (MvPolynomial.pderiv 0 source) / gradient 0 - residueMap source * hessian 0 0 / (gradient 0)^2`
   equals `cubicNormalJet3 + residueDivergence tangent (gradient 0) correctionVector`.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
namespace OneReflectionSkewPairedNormal
open HoldoutConstruction OneReflectionSkewPhysical OneReflectionSkewCoordinates
open OneReflectionSkewChart OneReflectionSkewNormalTransport ReverseEdgeCovariants
open scoped BigOperators

instance physical_charZero : CharZero FunctionField :=
  charZero_of_injective_ringHom (f := residueMap.comp MvPolynomial.C)
    (residueMap.comp MvPolynomial.C).injective

section Algebra
variable {K : Type*} [Field K]

lemma paired_normal_change_3coord (Dr Dq : Derivation ℤ K K)
    (p0 r q f h g fpp fpr fpq frr frq fqq : K)
    (hf : f ≠ 0) (hh : p0 * f + r * h + q * g ≠ 0)
    (Dr_p : Dr p0 = -h / f) (Dr_r : Dr r = 1) (Dr_q : Dr q = 0)
    (Dr_f : Dr f = fpr - h / f * fpp) (Dr_h : Dr h = frr - h / f * fpr) (Dr_g : Dr g = frq - h / f * fpq)
    (Dq_p : Dq p0 = -g / f) (Dq_r : Dq r = 0) (Dq_q : Dq q = 1)
    (Dq_f : Dq f = fpq - g / f * fpp) (Dq_h : Dq h = frq - g / f * fpr) (Dq_g : Dq g = fqq - g / f * fpq) :
    3 * p0^2 * q^3 / f - p0^3 * q^3 * fpp / f^2 =
      p0^3 * q^3 * (8 * (p0 * f + r * h + q * g) -
        (p0^2 * fpp + r^2 * frr + q^2 * fqq + 2 * p0 * r * fpr + 2 * p0 * q * fpq + 2 * r * q * frq)) /
        (p0 * f + r * h + q * g)^2 +
      (Dr (-p0^3 * q^3 * r / (p0 * f + r * h + q * g)) -
        (-p0^3 * q^3 * r / (p0 * f + r * h + q * g)) * Dr f / f) +
      (Dq (-p0^3 * q^4 / (p0 * f + r * h + q * g)) -
        (-p0^3 * q^4 / (p0 * f + r * h + q * g)) * Dq f / f) := by
  simp only [Derivation.leibniz_div, Derivation.leibniz, Derivation.leibniz_pow,
    map_neg, map_add, smul_eq_mul, nsmul_eq_mul,
    Dr_p, Dr_r, Dr_q, Dr_f, Dr_h, Dr_g,
    Dq_p, Dq_r, Dq_q, Dq_f, Dq_h, Dq_g]
  generalize hG : p0 * f + r * h + q * g = G at *
  field_simp [hf, hh]
  rw [← hG]
  ring

end Algebra

local notation "p" => coordinate

def pairedHessian3 : FunctionField :=
  p 0^2 * hessian 0 0 + p 2^2 * hessian 2 2 + p 3^2 * hessian 3 3 +
    2 * p 0 * p 2 * hessian 0 2 + 2 * p 0 * p 3 * hessian 0 3 + 2 * p 2 * p 3 * hessian 2 3

def cubicSecondNormal : FunctionField := 6 * coeffA * x + 2 * coeffD * y
def cubicNormalJet3 : FunctionField :=
  c0^3 * x * (7 * x * cubicNormal - 2 * x^2 * cubicSecondNormal) / (2 * cubicNormal^2)

def corr1 : FunctionField := -(p 0)^3 * (p 3)^3 * (p 2) / pairedGradient3
def corr2 : FunctionField := -(p 0)^3 * (p 3)^4 / pairedGradient3

def correctionVector : Fin 5 → FunctionField :=
  Pi.single 1 corr1 + Pi.single 2 corr2

theorem paired_hessian_identity_3 :
    pairedHessian3 - pairedGradient3 = 4 * radial^3 * x^2 * cubicSecondNormal := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h5 := coordinate_ne_zero 5
  simp only [pairedHessian3, pairedGradient3, hessian, gradient, sextic,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, map_add, map_sub, map_mul, map_pow,
    MvPolynomial.pderiv_C, MvPolynomial.pderiv_X, Pi.single_apply, Derivation.map_natCast]
  norm_num [Fin.ext_iff, coordinate_X, map_ofNat, field_seventh]
  simp only [cubicSecondNormal, coeffA, coeffD, radial, x, y, c0, c1, c2]
  field_simp
  ring

lemma cubic_normal_ne_zero : cubicNormal ≠ 0 := OneReflectionSkewChart.physical_normal_ne_zero

lemma paired_gradient_3_ne_zero : pairedGradient3 ≠ 0 := by
  rw [paired_gradient_identity_3]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero _ radial_ne_zero)) (div_ne_zero (pow_ne_zero _ (coordinate_ne_zero 0))
      radial_ne_zero)) cubic_normal_ne_zero

lemma tangent1_p0 : tangent 1 (p 0) = -gradient 2 / gradient 0 := by
  rw [coordinate, tangent_apply]
  norm_num [gradient, MvPolynomial.pderiv_X, Pi.single_apply,
    show (1 : Fin 5).succ = (2 : Fin 6) from rfl, Fin.ext_iff, neg_div]
lemma tangent1_p2 : tangent 1 (p 2) = 1 := by
  rw [coordinate, tangent_apply]
  norm_num [MvPolynomial.pderiv_X, Pi.single_apply,
    show (1 : Fin 5).succ = (2 : Fin 6) from rfl, Fin.ext_iff]
lemma tangent1_p3 : tangent 1 (p 3) = 0 := by
  rw [coordinate, tangent_apply]
  norm_num [MvPolynomial.pderiv_X, Pi.single_apply,
    show (1 : Fin 5).succ = (2 : Fin 6) from rfl, Fin.ext_iff]

lemma tangent2_p0 : tangent 2 (p 0) = -gradient 3 / gradient 0 := by
  rw [coordinate, tangent_apply]
  norm_num [gradient, MvPolynomial.pderiv_X, Pi.single_apply,
    show (2 : Fin 5).succ = (3 : Fin 6) from rfl, Fin.ext_iff, neg_div]
lemma tangent2_p2 : tangent 2 (p 2) = 0 := by
  rw [coordinate, tangent_apply]
  norm_num [MvPolynomial.pderiv_X, Pi.single_apply,
    show (2 : Fin 5).succ = (3 : Fin 6) from rfl, Fin.ext_iff]
lemma tangent2_p3 : tangent 2 (p 3) = 1 := by
  rw [coordinate, tangent_apply]
  norm_num [MvPolynomial.pderiv_X, Pi.single_apply,
    show (2 : Fin 5).succ = (3 : Fin 6) from rfl, Fin.ext_iff]

lemma tangent1_gradient (j : Fin 6) :
    tangent 1 (gradient j) = hessian 2 j - gradient 2 / gradient 0 * hessian 0 j :=
  tangent_apply 1 _
lemma tangent2_gradient (j : Fin 6) :
    tangent 2 (gradient j) = hessian 3 j - gradient 3 / gradient 0 * hessian 0 j :=
  tangent_apply 2 _

lemma hessian_commute (i j : Fin 6) : hessian i j = hessian j i := by
  unfold hessian
  rw [HoldoutConstruction.pderiv_commute]

lemma correction_divergence :
    residueDivergence tangent (gradient 0) correctionVector =
      (tangent 1 corr1 - corr1 * tangent 1 (gradient 0) / gradient 0) +
      (tangent 2 corr2 - corr2 * tangent 2 (gradient 0) / gradient 0) := by
  rw [correctionVector, residueDivergence_add]
  congr 1
  · simp [residueDivergence, fieldDivergence, Pi.single_apply, Finset.sum_ite_eq', apply_ite]
  · simp [residueDivergence, fieldDivergence, Pi.single_apply, Finset.sum_ite_eq', apply_ite]

lemma source_value : residueMap source = (p 0)^3 * (p 3)^3 := by
  simp only [source, map_mul, map_pow, coordinate]
lemma source_derivative : residueMap (MvPolynomial.pderiv 0 source) = 3 * (p 0)^2 * (p 3)^3 := by
  norm_num [source, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_X, Pi.single_apply, coordinate_X, map_ofNat, Fin.ext_iff]
  ring

theorem physical_source_transport_74 :
    residueMap (MvPolynomial.pderiv 0 source) / gradient 0 -
      residueMap source * hessian 0 0 / (gradient 0)^2 =
      cubicNormalJet3 + residueDivergence tangent (gradient 0) correctionVector := by
  have hn : gradient 0 ≠ 0 := normal_ne_zero
  have hp := paired_normal_change_3coord (tangent 1) (tangent 2)
    (p 0) (p 2) (p 3) (gradient 0) (gradient 2) (gradient 3)
    (hessian 0 0) (hessian 0 2) (hessian 0 3) (hessian 2 2) (hessian 2 3) (hessian 3 3)
    hn paired_gradient_3_ne_zero
    tangent1_p0 tangent1_p2 tangent1_p3
    (by rw [tangent1_gradient, hessian_commute 2 0])
    (tangent1_gradient 2) (tangent1_gradient 3)
    tangent2_p0 tangent2_p2 tangent2_p3
    (by rw [tangent2_gradient, hessian_commute 3 0])
    (by rw [tangent2_gradient, hessian_commute 3 2])
    (tangent2_gradient 3)
  rw [source_value, source_derivative, correction_divergence]
  change _ = _ + ((tangent 1 (-(p 0)^3 * (p 3)^3 * (p 2) / pairedGradient3) -
      (-(p 0)^3 * (p 3)^3 * (p 2) / pairedGradient3) * tangent 1 (gradient 0) / gradient 0) +
    (tangent 2 (-(p 0)^3 * (p 3)^4 / pairedGradient3) -
      (-(p 0)^3 * (p 3)^4 / pairedGradient3) * tangent 2 (gradient 0) / gradient 0))
  change _ = (p 0)^3 * (p 3)^3 * (8 * pairedGradient3 - pairedHessian3) / pairedGradient3^2 +
    (tangent 1 (-(p 0)^3 * (p 3)^3 * (p 2) / pairedGradient3) -
      (-(p 0)^3 * (p 3)^3 * (p 2) / pairedGradient3) * tangent 1 (gradient 0) / gradient 0) +
    (tangent 2 (-(p 0)^3 * (p 3)^4 / pairedGradient3) -
      (-(p 0)^3 * (p 3)^4 / pairedGradient3) * tangent 2 (gradient 0) / gradient 0) at hp
  rw [← add_assoc]
  rw [hp]
  congr 1
  congr 1
  have hs := paired_hessian_identity_3
  rw [paired_gradient_identity_3] at hs ⊢
  have hg := cubic_normal_ne_zero
  have h0 := coordinate_ne_zero 0
  have h5 := coordinate_ne_zero 5
  have hr := radial_ne_zero
  have hx : x ≠ 0 := div_ne_zero (pow_ne_zero _ h0) hr
  have he : (p 0)^3 * (p 3)^3 = c0^3 * radial^3 * x^3 := by
    simp only [c0, x, radial]
    field_simp
  rw [he]
  unfold cubicNormalJet3
  rw [sub_eq_iff_eq_add.mp hs]
  field_simp
  ring

end OneReflectionSkewPairedNormal
end
