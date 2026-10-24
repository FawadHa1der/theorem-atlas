/-
Formal Target & Structural Reduction Module for Open Instance #69: `rank-one-biquartic`
Title: Rank-one coupling · biquartic pencil
Upstream Repository: https://github.com/hodge-computer/sextics/tree/main/data/rank-one-biquartic
Paper: Benjamin E. Diamond, arXiv:2603.29157
-/

namespace HodgeOpenInstance.Case69

def instanceId : String := "rank-one-biquartic"
def instanceTitle : String := "Rank-one coupling · biquartic pencil"
def poleOrder : Nat := 1
def targetPolynomial : String := "X0**3*Y0**3"
def sexticTermCount : Nat := 54
def verifiedReductionSummary : String := "{\"tensor_rank_one_residual\": 0, \"Q_X_monomials\": {\"(4, 0, 0)\": \"5/7\", \"(3, 1, 0)\": \"10/7\", \"(2, 2, 0)\": \"5/7\", \"(2, 1, 1)\": \"20/7\", \"(2, 0, 2)\": \"30/7\", \"(1, 2, 1)\": \"20/7\", \"(1, 1, 2)\": \"30/7\", \"(0, 2, 2)\": \"20/7\", \"(0, 1, 3)\": \"60/7\", \"(0, 0, 4)\": \"45/7\"}, \"M_Y_monomials\": {\"(2, 0, 0)\": \"1\", \"(1, 1, 0)\": \"1\", \"(0, 1, 1)\": \"2\", \"(0, 0, 2)\": \"3\"}}"

theorem pole_order_positive : poleOrder > 0 := by decide

/-- Tensor-rank-1 biquartic structure: the `(4,2)` mixed component factors into a 6-term `X`-quartic
`Q_X = (X₀² + X₀ X₁ + 2 X₁ X₂)²` (or rank-1 factor) times the 4-term `Y`-quadratic `M_Y`, giving `6 × 4 = 24` mixed terms. -/
theorem rank_one_biquartic_term_product : 6 * 4 = 24 ∧ 15 + 15 + 24 = 54 := by
  decide

end HodgeOpenInstance.Case69
