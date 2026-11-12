import Proposal.PhysicalCoordinates
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Open Chart Localization and Nonvanishing Point Check for `#74 one-reflection-skew`

Evaluates the reverse-edge cubic chart at the Gaussian-rational point
`(X0, X1, X2, Y0, Y1, Y2) = (2, 1 - i, 0, 1 + i, 0, 2i)` on `F_74 = 0`, where
`denominator = X0 * X1 * Y0 * Y2 ≠ 0`, and proves that `cubicNormal`, `H_phys`, and
`J_phys` are nonzero in `FunctionField`.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace OneReflectionSkewChart
open OneReflectionSkewPhysical OneReflectionSkewCoordinates ReverseEdgeCovariants

local notation "ii" => Complex.I
local notation "X" => (MvPolynomial.X : Fin 6 → Ambient)

def point (i : Fin 6) : ℂ :=
  if i = 0 then 2 else
  if i = 1 then 1 - ii else
  if i = 2 then 0 else
  if i = 3 then 1 + ii else
  if i = 4 then 0 else 2 * ii

def value : Ambient →+* ℂ := MvPolynomial.eval₂Hom (RingHom.id ℂ) point

lemma on_sextic : value sextic = 0 := by
  simp [value, sextic, point]
  apply Complex.ext <;> norm_num [pow_succ, Complex.mul_re, Complex.mul_im]

def denominator : Ambient := X 0 * X 1 * X 3 * X 5
abbrev Chart := Localization.Away denominator
def ofPolynomial : Ambient →+* Chart := algebraMap Ambient Chart
def coord (i : Fin 6) : Chart := ofPolynomial (X i)
def invDenominator : Chart := IsLocalization.Away.invSelf denominator

def inv0 : Chart := coord 1 * coord 3 * coord 5 * invDenominator
def inv1 : Chart := coord 0 * coord 3 * coord 5 * invDenominator
def inv3 : Chart := coord 0 * coord 1 * coord 5 * invDenominator
def inv5 : Chart := coord 0 * coord 1 * coord 3 * invDenominator

lemma inv_spec :
    coord 0 * inv0 = 1 ∧ coord 1 * inv1 = 1 ∧ coord 3 * inv3 = 1 ∧ coord 5 * inv5 = 1 := by
  have h := IsLocalization.Away.mul_invSelf (S := Chart) denominator
  change ofPolynomial denominator * invDenominator = 1 at h
  simp only [denominator, map_mul] at h
  change coord 0 * coord 1 * coord 3 * coord 5 * invDenominator = 1 at h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [inv0, inv1, inv3, inv5] <;> linear_combination h

lemma denominator_residue_ne_zero : residueMap denominator ≠ 0 := by
  simpa only [denominator, map_mul, coordinate] using
    mul_ne_zero (mul_ne_zero (mul_ne_zero (coordinate_ne_zero 0)
      (coordinate_ne_zero 1)) (coordinate_ne_zero 3)) (coordinate_ne_zero 5)

lemma point_0 : point 0 = 2 := rfl
lemma point_1 : point 1 = 1 - ii := rfl
lemma point_2 : point 2 = 0 := rfl
lemma point_3 : point 3 = 1 + ii := rfl
lemma point_4 : point 4 = 0 := rfl
lemma point_5 : point 5 = 2 * ii := rfl

lemma denominator_point_ne_zero : value denominator ≠ 0 := by
  simp only [denominator, map_mul, value, MvPolynomial.eval₂Hom_X',
    point_0, point_1, point_3, point_5]
  intro h
  have him := congrArg Complex.im h
  norm_num [Complex.mul_re, Complex.mul_im] at him

def toField : Chart →+* FunctionField := IsLocalization.Away.lift denominator
  (isUnit_iff_ne_zero.mpr denominator_residue_ne_zero)
def toPoint : Chart →+* ℂ := IsLocalization.Away.lift denominator
  (isUnit_iff_ne_zero.mpr denominator_point_ne_zero)

lemma field_polynomial (p : Ambient) : toField (ofPolynomial p) = residueMap p :=
  IsLocalization.Away.lift_eq _ _ _
lemma point_polynomial (p : Ambient) : toPoint (ofPolynomial p) = value p :=
  IsLocalization.Away.lift_eq _ _ _

lemma nonzero_of_point (z : Chart) (hz : toPoint z ≠ 0) : toField z ≠ 0 := by
  intro hf
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj denominator z
  have hr := congrArg toField hp
  simp only [map_mul, map_pow, show algebraMap Ambient Chart = ofPolynomial from rfl,
    field_polynomial, hf, zero_mul] at hr
  obtain ⟨q, hq⟩ := (residueMap_kernel p).mp hr.symm
  have he : value p = 0 := by
    rw [hq, map_mul, on_sextic, zero_mul]
  have ht := congrArg toPoint hp
  simp only [map_mul, map_pow, show algebraMap Ambient Chart = ofPolynomial from rfl,
    point_polynomial, he] at ht
  exact hz ((mul_eq_zero.mp ht).resolve_right (pow_ne_zero _ denominator_point_ne_zero))

lemma field_coordinate (i : Fin 6) : toField (coord i) = coordinate i := field_polynomial _
lemma point_coordinate (i : Fin 6) : toPoint (coord i) = point i := by
  rw [coord, point_polynomial]
  simp [value]

lemma field_inv0 : toField inv0 = (coordinate 0)⁻¹ := by
  have h := congrArg toField inv_spec.1
  rw [map_mul, map_one, field_coordinate] at h
  exact eq_inv_of_mul_eq_one_right h
lemma field_inv1 : toField inv1 = (coordinate 1)⁻¹ := by
  have h := congrArg toField inv_spec.2.1
  rw [map_mul, map_one, field_coordinate] at h
  exact eq_inv_of_mul_eq_one_right h
lemma field_inv3 : toField inv3 = (coordinate 3)⁻¹ := by
  have h := congrArg toField inv_spec.2.2.1
  rw [map_mul, map_one, field_coordinate] at h
  exact eq_inv_of_mul_eq_one_right h
lemma field_inv5 : toField inv5 = (coordinate 5)⁻¹ := by
  have h := congrArg toField inv_spec.2.2.2
  rw [map_mul, map_one, field_coordinate] at h
  exact eq_inv_of_mul_eq_one_right h

lemma point_inv0 : toPoint inv0 = (point 0)⁻¹ := by
  have h := congrArg toPoint inv_spec.1
  rw [map_mul, map_one, point_coordinate] at h
  exact eq_inv_of_mul_eq_one_right h
lemma point_inv1 : toPoint inv1 = (point 1)⁻¹ := by
  have h := congrArg toPoint inv_spec.2.1
  rw [map_mul, map_one, point_coordinate] at h
  exact eq_inv_of_mul_eq_one_right h
lemma point_inv3 : toPoint inv3 = (point 3)⁻¹ := by
  have h := congrArg toPoint inv_spec.2.2.1
  rw [map_mul, map_one, point_coordinate] at h
  exact eq_inv_of_mul_eq_one_right h
lemma point_inv5 : toPoint inv5 = (point 5)⁻¹ := by
  have h := congrArg toPoint inv_spec.2.2.2
  rw [map_mul, map_one, point_coordinate] at h
  exact eq_inv_of_mul_eq_one_right h

def seventh : Chart := ofPolynomial (MvPolynomial.C (1/7 : ℂ))
def c0_chart : Chart := coord 3 * inv0
def c1_chart : Chart := coord 4 * inv1
def c2_chart : Chart := coord 2 * inv0
def x_chart : Chart := coord 0^2 * inv5^2
def y_chart : Chart := coord 1^2 * inv5^2
def a_chart : Chart := 1 + c0_chart^6 + c2_chart^6
def b_chart : Chart := 1 + c1_chart^6
def c_chart : Chart := 1
def d_chart : Chart := c0_chart * c1_chart * (1 + c0_chart^2 * seventh)
def f_chart : Chart := c0_chart * c1_chart * (c2_chart - c1_chart^2 * seventh)
def normal_chart : Chart := fxBin a_chart b_chart d_chart f_chart x_chart y_chart
def hessian_chart : Chart := H_e0 a_chart b_chart c_chart d_chart f_chart x_chart y_chart 1
def jacobian_chart : Chart := J_e0 a_chart b_chart c_chart d_chart f_chart x_chart y_chart 1

lemma point_seventh : toPoint seventh = (1/7 : ℂ) := by
  rw [seventh, point_polynomial]
  simp [value]
lemma field_seventh_chart : toField seventh = (1/7 : FunctionField) := by
  rw [seventh, field_polynomial]
  exact field_seventh

lemma coord_0 : (0 : Fin 6) = 0 := rfl
lemma coord_1 : (1 : Fin 6) = 1 := rfl
lemma coord_2 : (2 : Fin 6) = 2 := rfl
lemma coord_3 : (3 : Fin 6) = 3 := rfl
lemma coord_4 : (4 : Fin 6) = 4 := rfl
lemma coord_5 : (5 : Fin 6) = 5 := rfl

lemma point_values :
    toPoint a_chart = 1 - ii / 8 ∧ toPoint b_chart = 1 ∧ toPoint c_chart = 1 ∧
    toPoint d_chart = 0 ∧ toPoint f_chart = 0 ∧
    toPoint x_chart = -1 ∧ toPoint y_chart = ii / 2 := by
  simp only [a_chart, b_chart, c_chart, d_chart, f_chart, c0_chart, c1_chart, c2_chart,
    x_chart, y_chart, map_add, map_sub, map_mul, map_pow, map_one,
    point_seventh, point_coordinate, point_inv0, point_inv1, point_inv5,
    point_0, point_1, point_2, point_3, point_4, point_5]
  repeat' apply And.intro
  all_goals first | trivial | (apply Complex.ext <;>
    norm_num [pow_succ, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.normSq])

lemma normal_at_point : toPoint normal_chart ≠ 0 := by
  obtain ⟨ha, hb, hc, hd, hf, hx, hy⟩ := point_values
  simp only [normal_chart, fxBin, map_add, map_mul, map_pow, map_ofNat, ha, hd, hf, hx, hy]
  intro h
  have hre := congrArg Complex.re h
  norm_num [Complex.mul_re, Complex.mul_im] at hre

lemma hessian_at_point : toPoint hessian_chart ≠ 0 := by
  obtain ⟨ha, hb, hc, hd, hf, hx, hy⟩ := point_values
  simp only [hessian_chart, H_e0, hBin, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat,
    ha, hb, hc, hd, hf, hx, hy]
  intro h
  have him := congrArg Complex.im h
  norm_num [Complex.mul_re, Complex.mul_im] at him

lemma jacobian_at_point : toPoint jacobian_chart ≠ 0 := by
  obtain ⟨ha, hb, hc, hd, hf, hx, hy⟩ := point_values
  simp only [jacobian_chart, J_e0, kBin, hxBin, hyBin, fxBin, fyBin, hBin, fBin, discBin, disc0Bin,
    map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, ha, hb, hc, hd, hf, hx, hy]
  intro h
  have hre := congrArg Complex.re h
  norm_num [pow_succ, Complex.mul_re, Complex.mul_im] at hre

lemma field_values :
    toField a_chart = coeffA ∧ toField b_chart = coeffB ∧ toField c_chart = coeffC ∧
    toField d_chart = coeffD ∧ toField f_chart = coeffF ∧
    toField x_chart = x ∧ toField y_chart = y := by
  simp only [a_chart, b_chart, c_chart, d_chart, f_chart, c0_chart, c1_chart, c2_chart,
    x_chart, y_chart, map_add, map_sub, map_mul, map_pow, map_one,
    field_seventh_chart, field_coordinate, field_inv0, field_inv1, field_inv5,
    coeffA, coeffB, coeffC, coeffD, coeffF, x, y, radial, c0, c1, c2,
    div_eq_mul_inv, inv_pow]
  repeat' apply And.intro
  all_goals first | trivial | ring

lemma physical_normal_ne_zero :
    fxBin coeffA coeffB coeffD coeffF x y ≠ 0 := by
  have h := nonzero_of_point normal_chart normal_at_point
  obtain ⟨ha, hb, hc, hd, hf, hx, hy⟩ := field_values
  simpa only [normal_chart, fxBin, map_add, map_mul, map_pow, map_ofNat, ha, hd, hf, hx, hy] using h

lemma physical_hessian_ne_zero :
    H_e0 coeffA coeffB coeffC coeffD coeffF x y 1 ≠ 0 := by
  have h := nonzero_of_point hessian_chart hessian_at_point
  obtain ⟨ha, hb, hc, hd, hf, hx, hy⟩ := field_values
  simpa only [hessian_chart, H_e0, hBin, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat,
    ha, hb, hc, hd, hf, hx, hy] using h

lemma physical_jacobian_ne_zero :
    J_e0 coeffA coeffB coeffC coeffD coeffF x y 1 ≠ 0 := by
  have h := nonzero_of_point jacobian_chart jacobian_at_point
  obtain ⟨ha, hb, hc, hd, hf, hx, hy⟩ := field_values
  simpa only [jacobian_chart, J_e0, kBin, hxBin, hyBin, fxBin, fyBin, hBin, fBin, discBin, disc0Bin,
    map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, ha, hb, hc, hd, hf, hx, hy] using h

end OneReflectionSkewChart
end
