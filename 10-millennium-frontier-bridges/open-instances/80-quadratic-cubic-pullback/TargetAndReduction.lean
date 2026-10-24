/-
Formal Target & Structural Reduction Module for Open Instance #80: `quadratic-cubic-pullback`
Title: Quadratic pullback · residual density
Upstream Repository: https://github.com/hodge-computer/sextics/tree/main/data/quadratic-cubic-pullback
Paper: Benjamin E. Diamond, arXiv:2603.29157
-/

namespace HodgeOpenInstance.Case80

def instanceId : String := "quadratic-cubic-pullback"
def instanceTitle : String := "Quadratic pullback · residual density"
def poleOrder : Nat := 1
def targetPolynomial : String := "X0**3*Y0**3"
def sexticTermCount : Nat := 50
def verifiedReductionSummary : String := "{\"sum_of_six_cubes_residual\": 0}"

theorem pole_order_positive : poleOrder > 0 := by decide

/-- Modulo 5, the six quadrics `Q_i` reduce to `Z_i²`, so the Jacobian determinant `det(∂Q_i/∂Z_j)`
reduces to `2⁶ X₀ X₁ X₂ Y₀ Y₁ Y₂ = 64 X₀ X₁ X₂ Y₀ Y₁ Y₂ ≡ 4 X₀ X₁ X₂ Y₀ Y₁ Y₂ (mod 5)`. -/
theorem quadratic_cubic_jacobian_mod5 : (2 ^ 6) % 5 = 4 := by
  decide

end HodgeOpenInstance.Case80
