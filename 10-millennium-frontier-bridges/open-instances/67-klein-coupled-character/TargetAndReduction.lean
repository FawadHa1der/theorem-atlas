/-
Formal Target & Structural Reduction Module for Open Instance #67: `klein-coupled-character`
Title: Coupled Klein · nontrivial character
Upstream Repository: https://github.com/hodge-computer/sextics/tree/main/data/klein-coupled-character
Paper: Benjamin E. Diamond, arXiv:2603.29157
-/

namespace HodgeOpenInstance.Case67

def instanceId : String := "klein-coupled-character"
def instanceTitle : String := "Coupled Klein · nontrivial character"
def poleOrder : Nat := 1
def targetPolynomial : String := "X0**3*Y0**3"
def sexticTermCount : Nat := 9
def verifiedReductionSummary : String := "{\"F_weights_mod7\": 0, \"target_A_weight_mod7\": 3, \"invariant_cubic_X_monomial\": \"X0*X1*X2\", \"character_shift_ratio\": \"X0^2 / (X1*X2) [weight 3 mod 7]\"}"

theorem pole_order_positive : poleOrder > 0 := by decide

/-- Exact order-7 weight invariance under `w = (1, 2, 4, 0, 0, 0)`: all 9 monomials of `F₆₇`
have weight `0 mod 7`, `X₀ X₁ X₂ Y₀³` has weight `0 mod 7`, and `A₆₇ = X₀³ Y₀³` has weight `3 mod 7`. -/
def w7 (e0 e1 e2 : Nat) : Nat := (1 * e0 + 2 * e1 + 4 * e2) % 7

theorem klein_coupled_character_shift :
    w7 5 1 0 = 0 ∧ w7 3 0 1 = 0 ∧ w7 1 3 0 = 0 ∧ w7 1 0 5 = 0 ∧
    w7 0 5 1 = 0 ∧ w7 0 1 3 = 0 ∧ w7 1 1 1 = 0 ∧ w7 3 0 0 = 3 := by
  decide

end HodgeOpenInstance.Case67
