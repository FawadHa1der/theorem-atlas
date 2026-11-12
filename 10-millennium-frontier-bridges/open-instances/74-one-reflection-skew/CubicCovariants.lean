import Proposal.PhysicalPairedNormal
import Proposal.PhysicalCubicJets
import HodgeComputer.Constructions.ResidueTransport.CoordinateIndependence
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Relative Cubic Derivation, Divergence-Free Volume Direction, Invariant Differential,
# and 5×5 Physical-to-Weierstrass Jacobian Matrix for `#74 one-reflection-skew`
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace OneReflectionSkewCubicCovariants
open HoldoutConstruction OneReflectionSkewPhysical OneReflectionSkewCoordinates
open OneReflectionSkewChart OneReflectionSkewNormalTransport OneReflectionSkewPairedNormal
open OneReflectionSkewCubicJets ReverseEdgeCovariants
open scoped BigOperators

section Determinant
variable {K : Type*} [Field K]

def rawMatrix (p f : Fin 6 → K) (z : Fin 5 → K) (u : K) : Matrix (Fin 5) (Fin 5) K :=
  !![p 3 * f 1 / (p 0^2 * f 0),
     p 3 * f 2 / (p 0^2 * f 0),
     1 / p 0 + p 3 * f 3 / (p 0^2 * f 0),
     p 3 * f 4 / (p 0^2 * f 0),
     p 3 * f 5 / (p 0^2 * f 0);
     -p 4 / p 1^2, 0, 0, 1 / p 1, 0;
     p 2 * f 1 / (p 0^2 * f 0),
     1 / p 0 + p 2 * f 2 / (p 0^2 * f 0),
     p 2 * f 3 / (p 0^2 * f 0),
     p 2 * f 4 / (p 0^2 * f 0),
     p 2 * f 5 / (p 0^2 * f 0);
     0, 0, 0, 0, 2 * p 5;
     p 5^4 * z 0, p 5^4 * z 1, p 5^4 * z 2, p 5^4 * z 3, p 5^4 * z 4 + 4 * p 5^3 * u]

theorem raw_determinant (p f : Fin 6 → K) (z : Fin 5 → K) (u : K)
    (h0 : p 0 ≠ 0) (h1 : p 1 ≠ 0) (hf : f 0 ≠ 0) :
    (rawMatrix p f z u).det =
      2 * p 5^5 / (p 0^3 * p 1^2 * f 0) *
        ((p 0 * f 0 + p 2 * f 2 + p 3 * f 3) * p 1 * z 0 -
          (p 1 * f 1 + p 4 * f 4) * p 2 * z 1 -
          (p 1 * f 1 + p 4 * f 4) * p 3 * z 2 +
          (p 0 * f 0 + p 2 * f 2 + p 3 * f 3) * p 4 * z 3) := by
  rw [Matrix.det_succ_row _ (3 : Fin 5)]
  have hrow (j : Fin 5) : rawMatrix p f z u 3 j = if j = 4 then 2 * p 5 else 0 := by
    fin_cases j <;> rfl
  simp_rw [hrow]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have hminor (A : Matrix (Fin 4) (Fin 4) K) :
      A.det = A 0 0 * (A 1 1 * A 2 2 * A 3 3 - A 1 1 * A 2 3 * A 3 2 - A 1 2 * A 2 1 * A 3 3 +
        A 1 2 * A 2 3 * A 3 1 + A 1 3 * A 2 1 * A 3 2 - A 1 3 * A 2 2 * A 3 1) -
      A 0 1 * (A 1 0 * A 2 2 * A 3 3 - A 1 0 * A 2 3 * A 3 2 - A 1 2 * A 2 0 * A 3 3 +
        A 1 2 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 2 - A 1 3 * A 2 2 * A 3 0) +
      A 0 2 * (A 1 0 * A 2 1 * A 3 3 - A 1 0 * A 2 3 * A 3 1 - A 1 1 * A 2 0 * A 3 3 +
        A 1 1 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 1 - A 1 3 * A 2 1 * A 3 0) -
      A 0 3 * (A 1 0 * A 2 1 * A 3 2 - A 1 0 * A 2 2 * A 3 1 - A 1 1 * A 2 0 * A 3 2 +
        A 1 1 * A 2 2 * A 3 0 + A 1 2 * A 2 0 * A 3 1 - A 1 2 * A 2 1 * A 3 0) := by
    rw [Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    norm_num only [Fin.val_zero, Fin.val_succ, Fin.val_one]
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      show (Fin.succAbove (0 : Fin 4) (0 : Fin 3)) = (1 : Fin 4) by decide,
      show (Fin.succAbove (0 : Fin 4) (1 : Fin 3)) = (2 : Fin 4) by decide,
      show (Fin.succAbove (0 : Fin 4) (2 : Fin 3)) = (3 : Fin 4) by decide,
      show (Fin.succAbove (1 : Fin 4) (0 : Fin 3)) = (0 : Fin 4) by decide,
      show (Fin.succAbove (1 : Fin 4) (1 : Fin 3)) = (2 : Fin 4) by decide,
      show (Fin.succAbove (1 : Fin 4) (2 : Fin 3)) = (3 : Fin 4) by decide,
      show (Fin.succAbove (2 : Fin 4) (0 : Fin 3)) = (0 : Fin 4) by decide,
      show (Fin.succAbove (2 : Fin 4) (1 : Fin 3)) = (1 : Fin 4) by decide,
      show (Fin.succAbove (2 : Fin 4) (2 : Fin 3)) = (3 : Fin 4) by decide,
      show (Fin.succAbove (3 : Fin 4) (0 : Fin 3)) = (0 : Fin 4) by decide,
      show (Fin.succAbove (3 : Fin 4) (1 : Fin 3)) = (1 : Fin 4) by decide,
      show (Fin.succAbove (3 : Fin 4) (2 : Fin 3)) = (2 : Fin 4) by decide,
      show (Fin.succ (0 : Fin 3)) = (1 : Fin 4) by decide,
      show (Fin.succ (1 : Fin 3)) = (2 : Fin 4) by decide,
      show (Fin.succ (2 : Fin 3)) = (3 : Fin 4) by decide]
    ring
  rw [hminor]
  have hc : (-1 : K)^((3 : Fin 5).val + (4 : Fin 5).val) = -1 := by norm_num
  rw [hc, neg_one_mul]
  change -(2 * p 5) * ((rawMatrix p f z u 0 0) * ((rawMatrix p f z u 1 1) * (rawMatrix p f z u 2 2) * (rawMatrix p f z u 4 3) - (rawMatrix p f z u 1 1) * (rawMatrix p f z u 2 3) * (rawMatrix p f z u 4 2) - (rawMatrix p f z u 1 2) * (rawMatrix p f z u 2 1) * (rawMatrix p f z u 4 3) + (rawMatrix p f z u 1 2) * (rawMatrix p f z u 2 3) * (rawMatrix p f z u 4 1) + (rawMatrix p f z u 1 3) * (rawMatrix p f z u 2 1) * (rawMatrix p f z u 4 2) - (rawMatrix p f z u 1 3) * (rawMatrix p f z u 2 2) * (rawMatrix p f z u 4 1)) - (rawMatrix p f z u 0 1) * ((rawMatrix p f z u 1 0) * (rawMatrix p f z u 2 2) * (rawMatrix p f z u 4 3) - (rawMatrix p f z u 1 0) * (rawMatrix p f z u 2 3) * (rawMatrix p f z u 4 2) - (rawMatrix p f z u 1 2) * (rawMatrix p f z u 2 0) * (rawMatrix p f z u 4 3) + (rawMatrix p f z u 1 2) * (rawMatrix p f z u 2 3) * (rawMatrix p f z u 4 0) + (rawMatrix p f z u 1 3) * (rawMatrix p f z u 2 0) * (rawMatrix p f z u 4 2) - (rawMatrix p f z u 1 3) * (rawMatrix p f z u 2 2) * (rawMatrix p f z u 4 0)) + (rawMatrix p f z u 0 2) * ((rawMatrix p f z u 1 0) * (rawMatrix p f z u 2 1) * (rawMatrix p f z u 4 3) - (rawMatrix p f z u 1 0) * (rawMatrix p f z u 2 3) * (rawMatrix p f z u 4 1) - (rawMatrix p f z u 1 1) * (rawMatrix p f z u 2 0) * (rawMatrix p f z u 4 3) + (rawMatrix p f z u 1 1) * (rawMatrix p f z u 2 3) * (rawMatrix p f z u 4 0) + (rawMatrix p f z u 1 3) * (rawMatrix p f z u 2 0) * (rawMatrix p f z u 4 1) - (rawMatrix p f z u 1 3) * (rawMatrix p f z u 2 1) * (rawMatrix p f z u 4 0)) - (rawMatrix p f z u 0 3) * ((rawMatrix p f z u 1 0) * (rawMatrix p f z u 2 1) * (rawMatrix p f z u 4 2) - (rawMatrix p f z u 1 0) * (rawMatrix p f z u 2 2) * (rawMatrix p f z u 4 1) - (rawMatrix p f z u 1 1) * (rawMatrix p f z u 2 0) * (rawMatrix p f z u 4 2) + (rawMatrix p f z u 1 1) * (rawMatrix p f z u 2 2) * (rawMatrix p f z u 4 0) + (rawMatrix p f z u 1 2) * (rawMatrix p f z u 2 0) * (rawMatrix p f z u 4 1) - (rawMatrix p f z u 1 2) * (rawMatrix p f z u 2 1) * (rawMatrix p f z u 4 0))) = _
  norm_num only [rawMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ', Matrix.cons_val_zero', Function.comp_apply]
  field_simp
  ring

end Determinant

local instance cachedPhysicalField : Field FunctionField := inferInstance
local instance cachedPhysicalCharZero : CharZero FunctionField := inferInstance
local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra _
local notation "p" => coordinate

@[simp] lemma derivation_numeral {K : Type*} [CommRing K]
    (D : Derivation ℤ K K) (n : ℕ) [n.AtLeastTwo] :
    D (ofNat(n) : K) = 0 := D.map_natCast n

def velocity : Fin 6 → FunctionField :=
  ![-p 0 * pairedGradient2 / (2 * y * pairedGradient3),
    p 1 / (2 * y),
    -p 2 * pairedGradient2 / (2 * y * pairedGradient3),
    -p 3 * pairedGradient2 / (2 * y * pairedGradient3),
    p 4 / (2 * y),
    0]

def derivative : Derivation ℤ FunctionField FunctionField :=
  velocity 1 • tangent 0 + velocity 2 • tangent 1 +
    velocity 3 • tangent 2 + velocity 4 • tangent 3

lemma y_ne_zero : y ≠ 0 :=
  div_ne_zero (pow_ne_zero _ (coordinate_ne_zero 1)) radial_ne_zero

lemma tangent_coordinate (i : Fin 5) (j : Fin 6) :
    tangent i (p j) = (if j = i.succ then 1 else 0) -
      gradient i.succ / gradient 0 * (if j = 0 then 1 else 0) := by
  rw [coordinate, tangent_apply]
  simp only [MvPolynomial.pderiv_X, Pi.single_apply, apply_ite, map_one, map_zero, gradient]
  split_ifs <;> rfl

lemma derivative_coordinate (j : Fin 6) : derivative (p j) = velocity j := by
  have hy := y_ne_zero
  have hh := paired_gradient_3_ne_zero
  have hf : gradient 0 ≠ 0 := normal_ne_zero
  fin_cases j <;>
    simp only [derivative, Derivation.add_apply, Derivation.smul_apply, smul_eq_mul,
      tangent_coordinate, velocity, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.reduceSucc, Matrix.cons_val_one, Matrix.cons_val] <;>
    norm_num [Fin.ext_iff] <;>
    field_simp <;> simp only [pairedGradient3, pairedGradient2] <;> ring

lemma derivative_constant (c : ℂ) : derivative (residueMap (MvPolynomial.C c)) = 0 := by
  simp only [derivative, Derivation.add_apply, Derivation.smul_apply, smul_eq_mul,
    tangent_apply, MvPolynomial.pderiv_C, map_zero, mul_zero, sub_zero, add_zero]

lemma passive_parameters :
    derivative radial = 0 ∧ derivative c0 = 0 ∧ derivative c1 = 0 ∧ derivative c2 = 0 ∧
      derivative y = 1 ∧ derivative x = -x * pairedGradient2 / (y * pairedGradient3) := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h5 := coordinate_ne_zero 5
  have hy := y_ne_zero
  have hh := paired_gradient_3_ne_zero
  have hr := radial_ne_zero
  simp only [radial, c0, c1, c2, x, y, Derivation.leibniz_div,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, derivative_coordinate,
    velocity, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  repeat' apply And.intro
  all_goals norm_num <;> field_simp <;> ring
  all_goals simp

lemma coefficient_constants :
    derivative coeffA = 0 ∧ derivative coeffB = 0 ∧ derivative coeffC = 0 ∧
      derivative coeffD = 0 ∧ derivative coeffF = 0 := by
  obtain ⟨hR, hc0, hc1, hc2, hy, hx⟩ := passive_parameters
  have h1 : derivative (1 : FunctionField) = 0 := derivative.map_one_eq_zero
  have h7 : derivative (1 / 7 : FunctionField) = 0 := by
    rw [← field_seventh]
    exact derivative_constant (1 / 7 : ℂ)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [coeffA, coeffB, coeffC, coeffD, coeffF, map_add, map_sub,
      Derivation.leibniz_pow, Derivation.leibniz, smul_eq_mul, nsmul_eq_mul,
      h1, hc0, hc1, hc2, h7, mul_zero, zero_mul, add_zero, sub_zero]

lemma derivative_x : derivative x = -cubicNormalY / cubicNormal := by
  rw [passive_parameters.2.2.2.2.2, paired_gradient_identity_2, paired_gradient_identity_3]
  have hx : x ≠ 0 := div_ne_zero (pow_ne_zero _ (coordinate_ne_zero 0)) radial_ne_zero
  have hy := y_ne_zero
  have hr := radial_ne_zero
  have hg := cubic_normal_ne_zero
  field_simp

lemma derivative_hBin : derivative (hBin coeffA coeffB coeffD coeffF x y) =
    kBin coeffA coeffB coeffD coeffF x y / cubicNormal := by
  obtain ⟨ha, hb, hc, hd, hf⟩ := coefficient_constants
  have hy := passive_parameters.2.2.2.2.1
  have hx := derivative_x
  have hg : fxBin coeffA coeffB coeffD coeffF x y ≠ 0 := cubic_normal_ne_zero
  simp only [hBin, map_add, map_sub, Derivation.leibniz_pow, Derivation.leibniz,
    smul_eq_mul, nsmul_eq_mul, derivation_numeral, ha, hb, hd, hf, hx, hy]
  unfold kBin hxBin hyBin cubicNormal cubicNormalY
  field_simp [hg]
  unfold fxBin fyBin
  ring

lemma derivative_fBin : derivative (fBin coeffA coeffB coeffD coeffF x y) = 0 := by
  obtain ⟨ha, hb, hc, hd, hf⟩ := coefficient_constants
  have hy := passive_parameters.2.2.2.2.1
  have hx := derivative_x
  have hg : fxBin coeffA coeffB coeffD coeffF x y ≠ 0 := cubic_normal_ne_zero
  simp only [fBin, map_add, Derivation.leibniz_pow, Derivation.leibniz,
    smul_eq_mul, nsmul_eq_mul, derivation_numeral, ha, hb, hd, hf, hx, hy]
  unfold cubicNormal cubicNormalY
  field_simp [hg]
  unfold fxBin fyBin
  ring

lemma derivative_H_phys : derivative H_phys =
    Dop_H_e0 coeffA coeffB coeffC coeffD coeffF x y 1 / cubicNormal := by
  obtain ⟨ha, hb, hc, hd, hf⟩ := coefficient_constants
  have h1 : derivative (1 : FunctionField) = 0 := derivative.map_one_eq_zero
  have hh := derivative_hBin
  unfold H_phys H_e0 Dop_H_e0
  simp only [Derivation.leibniz, smul_eq_mul, derivation_numeral, h1, hc, hh]
  ring

lemma derivative_Theta_phys : derivative Theta_phys =
    Dop_Theta_e0 coeffA coeffB coeffC coeffD coeffF x y 1 / cubicNormal := by
  obtain ⟨ha, hb, hc, hd, hf⟩ := coefficient_constants
  have h1 : derivative (1 : FunctionField) = 0 := derivative.map_one_eq_zero
  have hh := derivative_hBin
  have hfb := derivative_fBin
  have hd0 : derivative (discBin coeffA coeffB coeffD coeffF) = 0 := by
    simp [discBin, disc0Bin, map_add, map_sub, Derivation.leibniz_pow, Derivation.leibniz,
      smul_eq_mul, ha, hb, hd, hf]
  unfold Theta_phys Theta_e0 Dop_Theta_e0
  simp only [map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow,
    smul_eq_mul, nsmul_eq_mul, derivation_numeral, h1, hc, hd0, hh, hfb]
  ring

lemma H_phys_ne_zero : H_phys ≠ 0 := OneReflectionSkewChart.physical_hessian_ne_zero
lemma J_phys_ne_zero : J_phys ≠ 0 := OneReflectionSkewChart.physical_jacobian_ne_zero

lemma eta_nonzero : eta ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr J_phys_ne_zero)
    (mul_ne_zero (by norm_num) (pow_ne_zero _ H_phys_ne_zero))

theorem invariant_differential : derivative xi / (2 * eta) = 3 / cubicNormal := by
  have hi := cleared_differential_e0 coeffA coeffB coeffC coeffD coeffF x y 1
  rw [cubic_equation, mul_zero] at hi
  change H_phys * Dop_Theta_e0 coeffA coeffB coeffC coeffD coeffF x y 1 -
    2 * Theta_phys * Dop_H_e0 coeffA coeffB coeffC coeffD coeffF x y 1 +
    3 * 1 * J_phys = 0 at hi
  have hH := H_phys_ne_zero
  have hJ := J_phys_ne_zero
  have hg := cubic_normal_ne_zero
  unfold xi eta
  rw [Derivation.leibniz_div, Derivation.leibniz_pow, derivative_H_phys, derivative_Theta_phys]
  simp only [smul_eq_mul, nsmul_eq_mul]
  norm_num
  field_simp
  linear_combination -hi

theorem xi_derivative_ne_zero : derivative xi ≠ 0 := by
  intro hz
  have h := invariant_differential
  rw [hz, zero_div] at h
  exact (div_ne_zero (by norm_num : (3 : FunctionField) ≠ 0) cubic_normal_ne_zero) h.symm

lemma tangent_gradient_all (i : Fin 5) (j : Fin 6) :
    tangent i (gradient j) = hessian i.succ j - gradient i.succ / gradient 0 * hessian 0 j :=
  tangent_apply i _

def weight : FunctionField := (p 3)^3 / (4 * (p 0)^6 * (p 1)^2 * (p 5)^2)
def volumeVector : Fin 5 → FunctionField :=
  ![weight * pairedGradient3 * p 1,
    -weight * pairedGradient2 * p 2,
    -weight * pairedGradient2 * p 3,
    weight * pairedGradient3 * p 4,
    0]

theorem volume_divergence : residueDivergence tangent (gradient 0) volumeVector = 0 := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h5 := coordinate_ne_zero 5
  have hn : gradient 0 ≠ 0 := normal_ne_zero
  simp only [residueDivergence, fieldDivergence, volumeVector,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.reduceSucc,
    Finset.univ_eq_empty, Finset.sum_empty, map_zero, zero_mul, zero_div, add_zero,
    weight, pairedGradient3, pairedGradient2, Derivation.leibniz_div,
    Derivation.leibniz_pow, Derivation.leibniz, map_add, map_neg,
    smul_eq_mul, nsmul_eq_mul, derivation_numeral, tangent_coordinate, tangent_gradient_all]
  norm_num [Fin.ext_iff]
  simp only [hessian_commute 1 0, hessian_commute 2 0, hessian_commute 3 0, hessian_commute 4 0,
    hessian_commute 2 1, hessian_commute 3 1, hessian_commute 4 1,
    hessian_commute 3 2, hessian_commute 4 2, hessian_commute 4 3]
  field_simp
  ring

theorem volume_vector_identity (i : Fin 5) :
    volumeVector i = (c0^3 * cubicNormal / p 0) * velocity i.succ := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h5 := coordinate_ne_zero 5
  have hr := radial_ne_zero
  have hx : x ≠ 0 := div_ne_zero (pow_ne_zero _ h0) hr
  have hy := y_ne_zero
  have hh := paired_gradient_3_ne_zero
  have hg : cubicNormal = pairedGradient3 / (2 * radial^3 * x) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hr)) hx)).2
    linear_combination -paired_gradient_identity_3
  rw [hg]
  fin_cases i <;>
    norm_num [volumeVector, velocity, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, weight, c0, radial, x, y] <;>
    field_simp <;> ring

lemma volume_direction (z : FunctionField) :
    (∑ i, volumeVector i * tangent i z) = (c0^3 * cubicNormal / p 0) * derivative z := by
  simp only [volume_vector_identity, Fin.sum_univ_succ, velocity,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.reduceSucc,
    Finset.univ_eq_empty, Finset.sum_empty, zero_mul, mul_zero, add_zero,
    derivative, Derivation.add_apply, Derivation.smul_apply, smul_eq_mul]
  norm_num [velocity, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons]
  ring

def targetX : FunctionField := radial^2 * xi
def targetY : FunctionField := radial^3 * eta
def passive : Fin 5 → FunctionField := ![c0, c1, c2, radial, targetX]
def matrix : Matrix (Fin 5) (Fin 5) FunctionField := fun j i => tangent i (passive j)

theorem matrix_formula : matrix = rawMatrix coordinate gradient (fun i => tangent i xi) xi := by
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h5 := coordinate_ne_zero 5
  have hn : gradient 0 ≠ 0 := normal_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [matrix, passive, targetX, rawMatrix, radial, c0, c1, c2,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.reduceSucc, Matrix.cons_val_one, Matrix.cons_val,
      Derivation.leibniz_div, Derivation.leibniz_pow, Derivation.leibniz,
      smul_eq_mul, nsmul_eq_mul, derivation_numeral, tangent_coordinate] <;>
    norm_num [Fin.ext_iff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, Derivation.leibniz, Derivation.leibniz_pow,
      Derivation.leibniz_div, Derivation.leibniz_inv,
      smul_eq_mul, nsmul_eq_mul, tangent_coordinate] <;> try field_simp <;> ring
  all_goals first | rfl | simp

theorem determinant_volume : c0^3 * gradient 0 * matrix.det =
    8 * p 5^7 * (∑ i, volumeVector i * tangent i xi) := by
  rw [matrix_formula, raw_determinant coordinate gradient (fun i => tangent i xi) xi
    (coordinate_ne_zero 0) (coordinate_ne_zero 1) normal_ne_zero]
  have h0 := coordinate_ne_zero 0
  have h1 := coordinate_ne_zero 1
  have h5 := coordinate_ne_zero 5
  have hn : gradient 0 ≠ 0 := normal_ne_zero
  simp only [volumeVector, weight, pairedGradient3, pairedGradient2, radial, c0, x,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.reduceSucc,
    Finset.univ_eq_empty, Finset.sum_empty, zero_mul, add_zero]
  field_simp
  ring

theorem determinant_relative : gradient 0 * matrix.det =
    8 * p 5^7 * cubicNormal / p 0 * derivative xi := by
  apply mul_left_cancel₀ (pow_ne_zero 3 c0_ne_zero)
  have h := determinant_volume
  rw [volume_direction] at h
  linear_combination h

theorem matrix_det_nonzero : matrix.det ≠ 0 := by
  have he := determinant_relative
  have h0 := coordinate_ne_zero 0
  have h5 := coordinate_ne_zero 5
  have hright : 8 * p 5^7 * cubicNormal / p 0 * derivative xi ≠ 0 :=
    mul_ne_zero (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero _ h5)) cubic_normal_ne_zero) h0) xi_derivative_ne_zero
  intro hz
  rw [hz, mul_zero] at he
  exact hright he.symm

def inverse : Matrix (Fin 5) (Fin 5) FunctionField := matrix⁻¹

lemma matrix_inverse : matrix * inverse = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr matrix_det_nonzero)
lemma inverse_matrix : inverse * matrix = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr matrix_det_nonzero)

def coordinateDerivation (j : Fin 5) : Derivation ℤ FunctionField FunctionField :=
  ∑ k, inverse k j • tangent k
lemma coordinateDerivation_apply (j : Fin 5) (z : FunctionField) :
    coordinateDerivation j z = ∑ k, inverse k j * tangent k z := by
  simp only [coordinateDerivation, Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,
    Derivation.add_apply, Derivation.smul_apply, smul_eq_mul, Derivation.coe_zero, Pi.zero_apply, add_zero]
lemma coordinateDerivation_passive (j i : Fin 5) :
    coordinateDerivation j (passive i) = if i = j then 1 else 0 := by
  rw [coordinateDerivation_apply]
  have h := congrArg (fun A : Matrix (Fin 5) (Fin 5) FunctionField => A i j) matrix_inverse
  simpa only [Matrix.mul_apply, Matrix.one_apply, matrix, mul_comm] using h
lemma coordinateDerivation_constant (j : Fin 5) (c : ℂ) :
    coordinateDerivation j (residueMap (MvPolynomial.C c)) = 0 := by
  simp only [coordinateDerivation_apply, tangent_apply, MvPolynomial.pderiv_C, map_zero,
    mul_zero, sub_zero, Finset.sum_const_zero]
theorem coefficient_evaluation_injective :
    Function.Injective (MvPolynomial.eval₂Hom (residueMap.comp MvPolynomial.C) passive) := by
  apply ResidueCoordinateIndependence.injective_of_coordinate_derivations
    (residueMap.comp MvPolynomial.C) passive coordinateDerivation
  · exact coordinateDerivation_constant
  · exact coordinateDerivation_passive

lemma tangents_commute (i j : Fin 5) : Function.Commute (tangent i) (tangent j) :=
  residueTangent_commute (K := FunctionField) projection projection_surjective
    (integerPartial 0) (integerPartial i.succ) (integerPartial j.succ) sextic
    projection_kernel normal_ne_zero (integerPartial_commute i.succ 0)
    (integerPartial_commute j.succ 0) (integerPartial_commute i.succ j.succ)
lemma matrix_mixed (i j k : Fin 5) : tangent k (matrix j i) = tangent i (matrix j k) :=
  tangents_commute k i (passive j)

end OneReflectionSkewCubicCovariants
end
