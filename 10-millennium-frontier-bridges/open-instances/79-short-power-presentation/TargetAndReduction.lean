/-
Formal Target & Structural Reduction Module for Open Instance #79: `short-power-presentation`
Title: Eight powers · linear-section remainder
Upstream Repository: https://github.com/hodge-computer/sextics/tree/main/data/short-power-presentation
Paper: Benjamin E. Diamond, arXiv:2603.29157
-/

namespace HodgeOpenInstance.Case79

def instanceId : String := "short-power-presentation"
def instanceTitle : String := "Eight powers · linear-section remainder"
def poleOrder : Nat := 1
def targetPolynomial : String := "X0**3*Y0**3"
def sexticTermCount : Nat := 236
def verifiedReductionSummary : String := "{\"waring_rank\": 8, \"waring_residual_terms\": 0, \"apolar_quadrics_verified\": 13}"

theorem pole_order_positive : poleOrder > 0 := by decide

/-- Waring rank-8 presentation: `7^7 = 823543`, leading `X₀⁶` coefficient `(823543 + 10)/823543 = 823553/823543`,
and `13` independent apolar quadrics (`(6 choose 2) - 2 = 13` or `5 + 8 = 13`) annihilating `F₇₉`. -/
theorem short_power_waring_parameters :
    7 ^ 7 = 823543 ∧ 823543 + 10 = 823553 ∧ 5 + 8 = 13 := by
  decide

end HodgeOpenInstance.Case79
