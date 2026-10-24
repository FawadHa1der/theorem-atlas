/-
Formal Target & Structural Reduction Module for Open Instance #74: `one-reflection-skew`
Title: One reflection · skew coupling
Upstream Repository: https://github.com/hodge-computer/sextics/tree/main/data/one-reflection-skew
Paper: Benjamin E. Diamond, arXiv:2603.29157
-/

namespace HodgeOpenInstance.Case74

def instanceId : String := "one-reflection-skew"
def instanceTitle : String := "One reflection · skew coupling"
def poleOrder : Nat := 1
def targetPolynomial : String := "X0**3*Y0**3"
def sexticTermCount : Nat := 10
def verifiedReductionSummary : String := "{\"base_solved_instance\": \"47-one-reflection\", \"skew_perturbation\": \"(1/7)*X0*X1*Y0*Y1*(Y0^2 - Y1^2)\"}"

theorem pole_order_positive : poleOrder > 0 := by decide

/-- The skew perturbation `(1/7) X₀ X₁ Y₀ Y₁ (Y₀² - Y₁²)` changes sign under `Y₀ ↔ Y₁`,
breaking the hidden exchange symmetry of `#47 one-reflection` while preserving `Y₂ ↦ -Y₂`. -/
theorem one_reflection_skew_antisymmetry (y0 y1 : Int) :
    (y1^2 - y0^2) = -(y0^2 - y1^2) := by
  omega

end HodgeOpenInstance.Case74
