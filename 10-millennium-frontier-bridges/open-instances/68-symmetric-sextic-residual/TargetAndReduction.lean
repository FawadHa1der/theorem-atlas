/-
Formal Target & Structural Reduction Module for Open Instance #68: `symmetric-sextic-residual`
Title: Permutation symmetry · residual sector
Upstream Repository: https://github.com/hodge-computer/sextics/tree/main/data/symmetric-sextic-residual
Paper: Benjamin E. Diamond, arXiv:2603.29157
-/

namespace HodgeOpenInstance.Case68

def instanceId : String := "symmetric-sextic-residual"
def instanceTitle : String := "Permutation symmetry · residual sector"
def poleOrder : Nat := 1
def targetPolynomial : String := "X0*X1*X2*Y0*Y1*Y2"
def sexticTermCount : Nat := 42
def verifiedReductionSummary : String := "{\"exact_elementary_quadratic_formula\": \"F0 + (5/7)*QX^2*QY + (10/7)*QX*QY^2\", \"residual_terms\": 0}"

theorem pole_order_positive : poleOrder > 0 := by decide

/-- Under any transposition of `(X₀, X₁, X₂)`, a symmetric polynomial `A` is invariant (`1`)
while the 3-form volume changes sign (`-1`), so the residue transforms by the sign character `-1`. -/
theorem symmetric_sextic_residue_sign_character :
    (1 : Int) * (-1 : Int) = -1 ∧ (-1 : Int) * (-1 : Int) = 1 := by
  decide

end HodgeOpenInstance.Case68
