/-
Formal Target & Structural Reduction Module for Open Instance #78: `cyclic-triple-residual`
Title: Cyclic triple cover · complementary character
Upstream Repository: https://github.com/hodge-computer/sextics/tree/main/data/cyclic-triple-residual
Paper: Benjamin E. Diamond, arXiv:2603.29157
-/

namespace HodgeOpenInstance.Case78

def instanceId : String := "cyclic-triple-residual"
def instanceTitle : String := "Cyclic triple cover · complementary character"
def poleOrder : Nat := 1
def targetPolynomial : String := "X0**3*Y0**3"
def sexticTermCount : Nat := 12
def verifiedReductionSummary : String := "{\"same_F_as_solved\": \"75-cyclic-triple-fano\", \"solved_target\": \"X0*X2^2*Y0^3\", \"open_target\": \"X0^3*Y0^3\"}"

theorem pole_order_positive : poleOrder > 0 := by decide

/-- Under `Z = X₂³`, every pulled-back polynomial source `X₂² B(X₀,X₁,X₂³,Y₀,Y₁,Y₂)` has
`X₂`-exponent `3k + 2 ≡ 2 (mod 3)`, whereas `A₇₈ = X₀³ Y₀³` has `X₂`-exponent `0`. -/
theorem cyclic_triple_exponent_mismatch (k : Nat) : (3 * k + 2) % 3 = 2 ∧ 0 % 3 = 0 := by
  omega

end HodgeOpenInstance.Case78
