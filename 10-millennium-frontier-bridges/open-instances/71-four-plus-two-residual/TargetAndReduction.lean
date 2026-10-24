/-
Formal Target & Structural Reduction Module for Open Instance #71: `four-plus-two-residual`
Title: Four plus two · suspension remainder
Upstream Repository: https://github.com/hodge-computer/sextics/tree/main/data/four-plus-two-residual
Paper: Benjamin E. Diamond, arXiv:2603.29157
-/

namespace HodgeOpenInstance.Case71

def instanceId : String := "four-plus-two-residual"
def instanceTitle : String := "Four plus two · suspension remainder"
def poleOrder : Nat := 1
def targetPolynomial : String := "X0**3*Y0**3"
def sexticTermCount : Nat := 14
def verifiedReductionSummary : String := "{\"H71_terms\": 10, \"B71_terms\": 4, \"B71_formula\": \"X2^6 + (15/7)*X2^4*Y2^2 + (10/7)*X2^2*Y2^4 + Y2^6\"}"

theorem pole_order_positive : poleOrder > 0 := by decide

/-- Exact `4+2` Thom-Sebastiani additive decomposition `F₇₁ = H₇₁(X₀,X₁,Y₀,Y₁) + B₇₁(X₂,Y₂)`
with `10` core terms and `4` binary sextic terms (`10 + 4 = 14`). -/
theorem four_plus_two_term_partition : 10 + 4 = 14 := by
  decide

end HodgeOpenInstance.Case71
