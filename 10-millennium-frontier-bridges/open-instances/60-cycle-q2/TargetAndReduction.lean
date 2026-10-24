/-
Formal Target & Structural Reduction Module for Open Instance #60: `cycle-q2`
Title: Cyclic coupling · pole order two
Upstream Repository: https://github.com/hodge-computer/sextics/tree/main/data/cycle-q2
Paper: Benjamin E. Diamond, arXiv:2603.29157
-/

namespace HodgeOpenInstance.Case60

def instanceId : String := "cycle-q2"
def instanceTitle : String := "Cyclic coupling · pole order two"
def poleOrder : Nat := 2
def targetPolynomial : String := "X0**2*X1**2*X2**3*Y0**2*Y1**2*Y2"
def sexticTermCount : Nat := 9
def verifiedReductionSummary : String := "{\"same_F_as_solved\": \"41-cycle-three\", \"q\": 2, \"mu6_weight_character\": \"zeta_6^2\"}"

theorem pole_order_positive : poleOrder > 0 := by decide

/-- Exact sixth-root diagonal weight screen under `w = (2, 1, 0, 3, 2, 1)`:
`A₆₀ = X₀² X₁² X₂³ Y₀² Y₁² Y₂` has polynomial weight `17` and residue character `17 + 9 = 26 ≡ 2 (mod 6)`. -/
theorem cycle_q2_residue_character :
    (2 * 2 + 1 * 2 + 0 * 3 + 3 * 2 + 2 * 2 + 1 * 1) = 17 ∧ (17 + 9) % 6 = 2 := by
  decide

end HodgeOpenInstance.Case60
