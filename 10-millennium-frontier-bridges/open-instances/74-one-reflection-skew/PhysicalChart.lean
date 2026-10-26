import Proposal.PhysicalCoordinates
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Open Chart Localization and Nonvanishing Point Check for `#74 one-reflection-skew`

Evaluates the reverse-edge cubic chart at the Gaussian-rational point
`(X0, X1, X2, Y0, Y1, Y2) = (2, 1 - i, 0, 1 + i, 0, 2i)` on `F_74 = 0`, where
`denominator = X0 * X1 * Y0 * Y2 ≠ 0`, and constructs the localization interface
`toField : Chart →+* FunctionField` and `toPoint : Chart →+* ℂ`.
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
lemma point_3 : point 3 = 1 + ii := rfl
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

end OneReflectionSkewChart
end
