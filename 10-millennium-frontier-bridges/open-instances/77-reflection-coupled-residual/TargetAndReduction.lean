/-
Formal Target & Structural Reduction Module for Open Instance #77: `reflection-coupled-residual`
Title: Reflection · complementary character
Upstream Repository: https://github.com/hodge-computer/sextics/tree/main/data/reflection-coupled-residual
Paper: Benjamin E. Diamond, arXiv:2603.29157
-/

namespace HodgeOpenInstance.Case77

def instanceId : String := "reflection-coupled-residual"
def instanceTitle : String := "Reflection · complementary character"
def poleOrder : Nat := 1
def targetPolynomial : String := "X0**3*Y0**3"
def sexticTermCount : Nat := 13
def verifiedReductionSummary : String := "{\"same_F_as_solved\": \"73-reflection-coupled-fano\", \"solved_target\": \"X0^3*Y2^3\", \"open_target\": \"X0^3*Y0^3\"}"

theorem pole_order_positive : poleOrder > 0 := by decide

/-- Under `Y₂ ↦ -Y₂`, the quotient map `u = Y₂²` has Jacobian density `2 Y₂` (odd in `Y₂`),
serving `X₀³ Y₂³` (exponent `3 ≡ 1 mod 2`) but missing `X₀³ Y₀³` (exponent `0 ≡ 0 mod 2`). -/
theorem reflection_coupled_parity_mismatch : 3 % 2 = 1 ∧ 0 % 2 = 0 := by
  decide

end HodgeOpenInstance.Case77
