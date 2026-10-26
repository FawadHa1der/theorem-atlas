import Proposal.PhysicalCoordinates
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Open Chart Localization for `#71 four-plus-two-residual`

Inverts `denominator = X0 * X2 * Y0` (`B1`, `B3`, `B2` block leaders), providing
the chart localization interface `toField : Chart →+* FunctionField`.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace FourPlusTwoChart
open FourPlusTwoPhysical FourPlusTwoCoordinates ReverseEdgeCovariants

local notation "X" => (MvPolynomial.X : Fin 6 → Ambient)

def denominator : Ambient := X 0 * X 2 * X 3
abbrev Chart := Localization.Away denominator
def ofPolynomial : Ambient →+* Chart := algebraMap Ambient Chart
def coord (i : Fin 6) : Chart := ofPolynomial (X i)
def invDenominator : Chart := IsLocalization.Away.invSelf denominator

def inv0 : Chart := coord 2 * coord 3 * invDenominator
def inv2 : Chart := coord 0 * coord 3 * invDenominator
def inv3 : Chart := coord 0 * coord 2 * invDenominator

lemma inv_spec :
    coord 0 * inv0 = 1 ∧ coord 2 * inv2 = 1 ∧ coord 3 * inv3 = 1 := by
  have h := IsLocalization.Away.mul_invSelf (S := Chart) denominator
  change ofPolynomial denominator * invDenominator = 1 at h
  simp only [denominator, map_mul] at h
  change coord 0 * coord 2 * coord 3 * invDenominator = 1 at h
  refine ⟨?_, ?_, ?_⟩ <;> simp only [inv0, inv2, inv3] <;> linear_combination h

lemma denominator_residue_ne_zero : residueMap denominator ≠ 0 := by
  simpa only [denominator, map_mul, coordinate] using
    mul_ne_zero (mul_ne_zero (coordinate_ne_zero 0)
      (coordinate_ne_zero 2)) (coordinate_ne_zero 3)

def toField : Chart →+* FunctionField := IsLocalization.Away.lift denominator
  (isUnit_iff_ne_zero.mpr denominator_residue_ne_zero)

lemma field_polynomial (p : Ambient) : toField (ofPolynomial p) = residueMap p :=
  IsLocalization.Away.lift_eq _ _ _

end FourPlusTwoChart
end
