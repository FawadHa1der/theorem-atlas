/-
Formal Target & Structural Reduction Module for Open Instance #81: `eight-plane-configuration`
Title: Eight planes · contact arrangement
Upstream Repository: https://github.com/hodge-computer/sextics/tree/main/data/eight-plane-configuration
Paper: Benjamin E. Diamond, arXiv:2603.29157
-/

namespace HodgeOpenInstance.Case81

def instanceId : String := "eight-plane-configuration"
def instanceTitle : String := "Eight planes · contact arrangement"
def poleOrder : Nat := 1
def targetPolynomial : String := "X0**3*Y0**3"
def sexticTermCount : Nat := 236
def verifiedReductionSummary : String := "{\"eight_plane_contact_residual\": 0}"

theorem pole_order_positive : poleOrder > 0 := by decide

/-- Along each of the 8 isotropic planes `Y_i = ± √(-1) X_i` (`X_i² + Y_i² = 0`),
both `X_i⁶ + Y_i⁶ = (X_i² + Y_i²)(X_i⁴ - X_i² Y_i² + Y_i⁴)` and `(X_i² + Y_i²) C_i` vanish identically. -/
theorem eight_plane_isotropic_factor (x2 y2 : Int) (h : x2 + y2 = 0) :
    (x2 + y2) * (x2^2 - x2 * y2 + y2^2) = 0 := by
   rw [h, Int.zero_mul]

end HodgeOpenInstance.Case81
