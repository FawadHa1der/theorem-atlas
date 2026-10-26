import HodgeComputer.Constructions.HoldoutCover.HomogeneousCertificate
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import HodgeComputer.Constructions.HoldoutCover.ResidueClearing
import HodgeComputer.Constructions.HoldoutCover.ResiduePiolaPullback
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The Physical Function Field, Tangent Derivations, and Clearing Theorem for `#71 four-plus-two-residual`

Establishes irreducibility of the official `#71 four-plus-two-residual` polynomial `F_71` over `ℂ`
via the Eisenstein specialization `holdoutSpecialization Complex.I`, constructs the coordinate ring
and function field, proves nonvanishing of the `X0`-normal derivative, and supplies both
`certificate_of_normalized` and `certificate_of_residue_solution`.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace FourPlusTwoPhysical
open HoldoutConstruction Polynomial
open scoped BigOperators

abbrev Ambient := MvPolynomial (Fin 6) ℂ
abbrev Coeff := MvPolynomial (Fin 5) ℂ
local notation "v" => (MvPolynomial.X : Fin 6 → Ambient)
local notation "w" => (MvPolynomial.X : Fin 5 → Coeff)

def sextic : Ambient :=
  v 0^6 + MvPolynomial.C (5 : ℂ) * v 0^5 * v 1 * MvPolynomial.C (1/7 : ℂ) +
    MvPolynomial.C (5 : ℂ) * v 0^3 * v 1 * v 3 * v 4 * MvPolynomial.C (1/7 : ℂ) +
    MvPolynomial.C (10 : ℂ) * v 0 * v 1^5 * MvPolynomial.C (1/7 : ℂ) +
    MvPolynomial.C (10 : ℂ) * v 0 * v 1 * v 3^3 * v 4 * MvPolynomial.C (1/7 : ℂ) +
    v 1^6 + v 2^6 + MvPolynomial.C (15 : ℂ) * v 2^4 * v 5^2 * MvPolynomial.C (1/7 : ℂ) +
    MvPolynomial.C (10 : ℂ) * v 2^2 * v 5^4 * MvPolynomial.C (1/7 : ℂ) +
    v 3^6 + MvPolynomial.C (5 : ℂ) * v 3^5 * v 4 * MvPolynomial.C (1/7 : ℂ) +
    MvPolynomial.C (15 : ℂ) * v 3 * v 4^5 * MvPolynomial.C (1/7 : ℂ) + v 4^6 + v 5^6

def source : Ambient := v 0^3 * v 3^3

def equation : Polynomial Coeff :=
  X^6 + (C (MvPolynomial.C (5 : ℂ) * w 0 * MvPolynomial.C (1/7 : ℂ)) * X^5 +
    C (MvPolynomial.C (5 : ℂ) * w 0 * w 2 * w 3 * MvPolynomial.C (1/7 : ℂ)) * X^3 +
    C (MvPolynomial.C (10 : ℂ) * w 0^5 * MvPolynomial.C (1/7 : ℂ) +
       MvPolynomial.C (10 : ℂ) * w 0 * w 2^3 * w 3 * MvPolynomial.C (1/7 : ℂ)) * X^1 +
    C (w 0^6 + w 1^6 + MvPolynomial.C (15 : ℂ) * w 1^4 * w 4^2 * MvPolynomial.C (1/7 : ℂ) +
       MvPolynomial.C (10 : ℂ) * w 1^2 * w 4^4 * MvPolynomial.C (1/7 : ℂ) +
       w 2^6 + MvPolynomial.C (5 : ℂ) * w 2^5 * w 3 * MvPolynomial.C (1/7 : ℂ) +
       MvPolynomial.C (15 : ℂ) * w 2 * w 3^5 * MvPolynomial.C (1/7 : ℂ) + w 3^6 + w 4^6))

lemma equation_monic : equation.Monic := by
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt
    · apply lt_of_le_of_lt (degree_add_le _ _)
      apply max_lt
      · exact lt_of_le_of_lt (degree_C_mul_X_pow_le 5 _) (by decide)
      · exact lt_of_le_of_lt (degree_C_mul_X_pow_le 3 _) (by decide)
    · exact lt_of_le_of_lt (degree_C_mul_X_pow_le 1 _) (by decide)
  · exact lt_of_le_of_lt degree_C_le (by decide)

lemma equation_specialization :
    equation.map (holdoutSpecialization Complex.I) = X^6 + C ((X + 1)^6 - 1) := by
  have hi : (Complex.I : ℂ)^6 = -1 := by
    rw [show (6:ℕ) = 2*3 by decide, pow_mul, Complex.I_sq]
    norm_num
  simp [equation, holdoutSpecialization, ← map_pow, hi, sub_eq_add_neg]

lemma equation_irreducible : Irreducible equation := by
  apply equation_monic.irreducible_of_irreducible_map (holdoutSpecialization Complex.I)
  rw [equation_specialization]
  exact irreducible_power_add_constant ((X + 1)^6 - 1 : Polynomial ℂ)
    (by simp [coeff_X_add_one_pow]) (by norm_num [coeff_X_add_one_pow, coeff_one])
    6 (by decide)

lemma sextic_univariate : MvPolynomial.finSuccEquiv ℂ 5 sextic = equation := by
  have he : (Fin.cases (X : Polynomial Coeff) (fun j => C (MvPolynomial.X j))) =
      ![X, C (w 0), C (w 1), C (w 2), C (w 3), C (w 4)] := by
    funext i
    fin_cases i <;> rfl
  simp [sextic, equation, MvPolynomial.finSuccEquiv_apply, he]
  ring

lemma sextic_irreducible : Irreducible sextic := by
  apply (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℂ 5)).mp
  rw [sextic_univariate]
  exact equation_irreducible

abbrev CoordinateRing := AdjoinRoot equation
instance coordinate_domain : IsDomain CoordinateRing :=
  AdjoinRoot.isDomain_of_prime equation_irreducible.prime
abbrev FunctionField := FractionRing CoordinateRing
def projection : Ambient →+* CoordinateRing :=
  (AdjoinRoot.mk equation).comp (MvPolynomial.finSuccEquiv ℂ 5).toRingHom
lemma projection_surjective : Function.Surjective projection :=
  (AdjoinRoot.mk_surjective (g := equation)).comp (MvPolynomial.finSuccEquiv ℂ 5).surjective
lemma projection_kernel (p : Ambient) : projection p = 0 ↔ sextic ∣ p := by
  change AdjoinRoot.mk equation (MvPolynomial.finSuccEquiv ℂ 5 p) = 0 ↔ _
  rw [AdjoinRoot.mk_eq_zero, ← sextic_univariate]
  exact map_dvd_iff (MvPolynomial.finSuccEquiv ℂ 5)
def residueMap : Ambient →+* FunctionField :=
  (algebraMap CoordinateRing FunctionField).comp projection
lemma residueMap_kernel (p : Ambient) : residueMap p = 0 ↔ sextic ∣ p := by
  constructor
  · intro h
    apply (projection_kernel p).mp
    apply IsFractionRing.injective CoordinateRing FunctionField
    simpa only [residueMap, RingHom.comp_apply, map_zero] using h
  · intro h
    change algebraMap CoordinateRing FunctionField (projection p) = 0
    rw [(projection_kernel p).mpr h, map_zero]

def axis : Ambient →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom C (fun i => if i = 0 then X else 0)
lemma axis_sextic : axis sextic = X^6 := by
  norm_num [axis, sextic,
    show (1:Fin 6) ≠ 0 by decide, show (2:Fin 6) ≠ 0 by decide, show (3:Fin 6) ≠ 0 by decide,
    show (4:Fin 6) ≠ 0 by decide, show (5:Fin 6) ≠ 0 by decide]
lemma axis_normal : axis (MvPolynomial.pderiv 0 sextic) = 6 * X^5 := by
  norm_num [axis, sextic, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    Polynomial.C_ofNat, Pi.single_apply, Matrix.cons_val,
    show (1:Fin 6) ≠ 0 by decide, show (2:Fin 6) ≠ 0 by decide, show (3:Fin 6) ≠ 0 by decide,
    show (4:Fin 6) ≠ 0 by decide, show (5:Fin 6) ≠ 0 by decide]
lemma normal_legal : ¬ sextic ∣ MvPolynomial.pderiv 0 sextic := by
  intro h
  have hm := map_dvd axis h
  rw [axis_sextic, axis_normal] at hm
  have hc := (Polynomial.X_pow_dvd_iff.mp hm) 5 (by decide)
  norm_num at hc
lemma normal_ne_zero : residueMap (integerPartial 0 sextic) ≠ 0 := by
  intro h
  exact normal_legal ((residueMap_kernel _).mp h)

local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra _
def tangent (i : Fin 5) : Derivation ℤ FunctionField FunctionField :=
  residueTangent (K := FunctionField) projection projection_surjective
    (integerPartial 0) (integerPartial i.succ) sextic projection_kernel normal_ne_zero
lemma tangent_apply (i : Fin 5) (p : Ambient) :
    tangent i (residueMap p) = residueMap (MvPolynomial.pderiv i.succ p) -
      residueMap (MvPolynomial.pderiv i.succ sextic) / residueMap (MvPolynomial.pderiv 0 sextic) *
        residueMap (MvPolynomial.pderiv 0 p) :=
  residueTangent_apply (K := FunctionField) projection projection_surjective
    (integerPartial 0) (integerPartial i.succ) sextic projection_kernel normal_ne_zero p

lemma sextic_homogeneous : sextic.IsHomogeneous 6 := by
  have hp (i : Fin 6) : (v i^6).IsHomogeneous 6 := MvPolynomial.isHomogeneous_X_pow i 6
  have h51 (a : ℂ) (i j : Fin 6) : (MvPolynomial.C a * v i^5 * v j * MvPolynomial.C (1/7 : ℂ)).IsHomogeneous 6 := by
    have h0 : (MvPolynomial.C a : Ambient).IsHomogeneous 0 := MvPolynomial.isHomogeneous_C (Fin 6) a
    have h5 : (MvPolynomial.C a * v i^5).IsHomogeneous 5 := by
      simpa only [zero_add] using h0.mul (MvPolynomial.isHomogeneous_X_pow i 5)
    have h6 : (MvPolynomial.C a * v i^5 * v j).IsHomogeneous 6 :=
      h5.mul (MvPolynomial.isHomogeneous_X ℂ j)
    simpa only [add_zero] using h6.mul (MvPolynomial.isHomogeneous_C (Fin 6) (1/7 : ℂ))
  have h15 (a : ℂ) (i j : Fin 6) : (MvPolynomial.C a * v i * v j^5 * MvPolynomial.C (1/7 : ℂ)).IsHomogeneous 6 := by
    have h0 : (MvPolynomial.C a : Ambient).IsHomogeneous 0 := MvPolynomial.isHomogeneous_C (Fin 6) a
    have h1 : (MvPolynomial.C a * v i).IsHomogeneous 1 := by
      simpa only [zero_add] using h0.mul (MvPolynomial.isHomogeneous_X ℂ i)
    have h6 : (MvPolynomial.C a * v i * v j^5).IsHomogeneous 6 :=
      h1.mul (MvPolynomial.isHomogeneous_X_pow j 5)
    simpa only [add_zero] using h6.mul (MvPolynomial.isHomogeneous_C (Fin 6) (1/7 : ℂ))
  have h3111 (a : ℂ) (i j k l : Fin 6) : (MvPolynomial.C a * v i^3 * v j * v k * v l * MvPolynomial.C (1/7 : ℂ)).IsHomogeneous 6 := by
    have h0 : (MvPolynomial.C a : Ambient).IsHomogeneous 0 := MvPolynomial.isHomogeneous_C (Fin 6) a
    have h3 : (MvPolynomial.C a * v i^3).IsHomogeneous 3 := by
      simpa only [zero_add] using h0.mul (MvPolynomial.isHomogeneous_X_pow i 3)
    have h4 : (MvPolynomial.C a * v i^3 * v j).IsHomogeneous 4 := h3.mul (MvPolynomial.isHomogeneous_X ℂ j)
    have h5 : (MvPolynomial.C a * v i^3 * v j * v k).IsHomogeneous 5 := h4.mul (MvPolynomial.isHomogeneous_X ℂ k)
    have h6 : (MvPolynomial.C a * v i^3 * v j * v k * v l).IsHomogeneous 6 := h5.mul (MvPolynomial.isHomogeneous_X ℂ l)
    simpa only [add_zero] using h6.mul (MvPolynomial.isHomogeneous_C (Fin 6) (1/7 : ℂ))
  have h1131 (a : ℂ) (i j k l : Fin 6) : (MvPolynomial.C a * v i * v j * v k^3 * v l * MvPolynomial.C (1/7 : ℂ)).IsHomogeneous 6 := by
    have h0 : (MvPolynomial.C a : Ambient).IsHomogeneous 0 := MvPolynomial.isHomogeneous_C (Fin 6) a
    have h1 : (MvPolynomial.C a * v i).IsHomogeneous 1 := by
      simpa only [zero_add] using h0.mul (MvPolynomial.isHomogeneous_X ℂ i)
    have h2 : (MvPolynomial.C a * v i * v j).IsHomogeneous 2 := h1.mul (MvPolynomial.isHomogeneous_X ℂ j)
    have h5 : (MvPolynomial.C a * v i * v j * v k^3).IsHomogeneous 5 := h2.mul (MvPolynomial.isHomogeneous_X_pow k 3)
    have h6 : (MvPolynomial.C a * v i * v j * v k^3 * v l).IsHomogeneous 6 := h5.mul (MvPolynomial.isHomogeneous_X ℂ l)
    simpa only [add_zero] using h6.mul (MvPolynomial.isHomogeneous_C (Fin 6) (1/7 : ℂ))
  have h42 (a : ℂ) (i j : Fin 6) : (MvPolynomial.C a * v i^4 * v j^2 * MvPolynomial.C (1/7 : ℂ)).IsHomogeneous 6 := by
    have h0 : (MvPolynomial.C a : Ambient).IsHomogeneous 0 := MvPolynomial.isHomogeneous_C (Fin 6) a
    have h4 : (MvPolynomial.C a * v i^4).IsHomogeneous 4 := by
      simpa only [zero_add] using h0.mul (MvPolynomial.isHomogeneous_X_pow i 4)
    have h6 : (MvPolynomial.C a * v i^4 * v j^2).IsHomogeneous 6 := h4.mul (MvPolynomial.isHomogeneous_X_pow j 2)
    simpa only [add_zero] using h6.mul (MvPolynomial.isHomogeneous_C (Fin 6) (1/7 : ℂ))
  have h24 (a : ℂ) (i j : Fin 6) : (MvPolynomial.C a * v i^2 * v j^4 * MvPolynomial.C (1/7 : ℂ)).IsHomogeneous 6 := by
    have h0 : (MvPolynomial.C a : Ambient).IsHomogeneous 0 := MvPolynomial.isHomogeneous_C (Fin 6) a
    have h2 : (MvPolynomial.C a * v i^2).IsHomogeneous 2 := by
      simpa only [zero_add] using h0.mul (MvPolynomial.isHomogeneous_X_pow i 2)
    have h6 : (MvPolynomial.C a * v i^2 * v j^4).IsHomogeneous 6 := h2.mul (MvPolynomial.isHomogeneous_X_pow j 4)
    simpa only [add_zero] using h6.mul (MvPolynomial.isHomogeneous_C (Fin 6) (1/7 : ℂ))
  exact (((((((((((((hp 0).add (h51 5 0 1)).add (h3111 5 0 1 3 4)).add (h15 10 0 1)).add
    (h1131 10 0 1 3 4)).add (hp 1)).add (hp 2)).add (h42 15 2 5)).add (h24 10 2 5)).add
    (hp 3)).add (h51 5 3 4)).add (h15 15 3 4)).add (hp 4)).add (hp 5)

lemma source_homogeneous : source.IsHomogeneous 6 :=
  (MvPolynomial.isHomogeneous_X_pow (0 : Fin 6) 3).mul
    (MvPolynomial.isHomogeneous_X_pow (3 : Fin 6) 3)

theorem certificate_of_normalized
    (D : Ambient) (N : Fin 6 → Ambient) (Q : Ambient)
    (legal : IsRelPrime sextic D)
    (normal : HodgeTestbed.directional sextic N = source * D)
    (divergence : HodgeTestbed.divergenceNumerator D N = sextic * Q) :
    HodgeComputer.HasCertificate sextic source 1 :=
  hasCertificate_of_normalized sextic source D N Q sextic_homogeneous source_homogeneous
    sextic_irreducible.prime legal normal divergence 0 normal_legal

theorem certificate_of_residue_solution
    (vec : Fin 5 → FunctionField)
    (hw : residueDivergence tangent (residueMap (MvPolynomial.pderiv 0 sextic)) vec =
      -(residueMap (MvPolynomial.pderiv 0 source) / residueMap (MvPolynomial.pderiv 0 sextic) -
        residueMap source * residueMap (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 sextic)) /
          (residueMap (MvPolynomial.pderiv 0 sextic))^2)) :
    HodgeComputer.HasCertificate sextic source 1 := by
  have hd : residueDivergence tangent (residueMap (MvPolynomial.pderiv 0 sextic)) vec =
      ∑ i, (tangent i (vec i) - vec i * tangent i (residueMap (MvPolynomial.pderiv 0 sextic)) /
        residueMap (MvPolynomial.pderiv 0 sextic)) := by
    simp only [residueDivergence, fieldDivergence, Finset.sum_sub_distrib, Finset.sum_div]
  obtain ⟨D, N₀, N, Q, hD, hlegal, hnormal, hdiv, _⟩ :=
    residue_solution_clearing residueMap (integerPartial 0)
      (fun i : Fin 5 => integerPartial i.succ) tangent sextic source vec
      sextic_irreducible residueMap_kernel normal_ne_zero
      (fun i => integerPartial_commute i.succ 0 sextic) tangent_apply
      (residue_common_representatives projection projection_surjective vec) (by
        rw [hd] at hw
        simp only [integerPartial_apply]
        rw [hw]
        have hn : residueMap (MvPolynomial.pderiv 0 sextic) ≠ 0 := normal_ne_zero
        field_simp
        ring)
  apply certificate_of_normalized D (Fin.cases N₀ N) Q hlegal
  · simpa only [HodgeTestbed.directional, Fin.sum_univ_succ, Fin.cases_zero,
      Fin.cases_succ, integerPartial_apply, mul_comm] using hnormal
  · simpa only [HodgeTestbed.divergenceNumerator, HodgeTestbed.divergence,
      HodgeTestbed.directional, residueDivNum, Fin.sum_univ_succ, Fin.cases_zero,
      Fin.cases_succ, integerPartial_apply, mul_comm] using hdiv

end FourPlusTwoPhysical
end
