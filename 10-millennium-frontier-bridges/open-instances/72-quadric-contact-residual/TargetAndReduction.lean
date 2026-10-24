/-
Formal Target & Structural Reduction Module for Open Instance #72: `quadric-contact-residual`
Title: Quadric contact · residual sector
Upstream Repository: https://github.com/hodge-computer/sextics/tree/main/data/quadric-contact-residual
Paper: Benjamin E. Diamond, arXiv:2603.29157
-/

namespace HodgeOpenInstance.Case72

def instanceId : String := "quadric-contact-residual"
def instanceTitle : String := "Quadric contact · residual sector"
def poleOrder : Nat := 1
def targetPolynomial : String := "X0**3*Y0**3"
def sexticTermCount : Nat := 16
def verifiedReductionSummary : String := "{\"same_F_as_solved\": \"55-quadric-contact-broken\", \"solved_target\": \"X0*X1^2*Y0*Y1^2\", \"open_target\": \"X0^3*Y0^3\"}"

theorem pole_order_positive : poleOrder > 0 := by decide

/-- In `quadric-contact-residual`, the quadratic contact map `S = 2(X₀²+Y₀²), T = 4 X₀ Y₀`
has Jacobian `16(X₀² - Y₀²)`, which is odd under `X₀ ↔ Y₀`, whereas `A₇₂ = X₀³ Y₀³` is even. -/
theorem quadric_contact_exchange_parity (x0 y0 : Int) :
    (y0^2 - x0^2) = -(x0^2 - y0^2) ∧ (y0 * x0)^3 = (x0 * y0)^3 := by
  omega

end HodgeOpenInstance.Case72
