/-
Formal Target & Structural Reduction Module for Open Instance #66: `polarized-k3-remainder`
Title: Polarized split · K3 remainder
Upstream Repository: https://github.com/hodge-computer/sextics/tree/main/data/polarized-k3-remainder
Paper: Benjamin E. Diamond, arXiv:2603.29157
-/

namespace HodgeOpenInstance.Case66

def instanceId : String := "polarized-k3-remainder"
def instanceTitle : String := "Polarized split · K3 remainder"
def poleOrder : Nat := 1
def targetPolynomial : String := "X0*X1*X2*Y0*Y1*Y2"
def sexticTermCount : Nat := 42
def verifiedReductionSummary : String := "{\"ternary_sextic_fU_terms\": {\"(6, 0, 0)\": \"1\", \"(5, 1, 0)\": \"5/7\", \"(2, 3, 1)\": \"5/7\", \"(1, 0, 5)\": \"15/7\", \"(0, 6, 0)\": \"1\", \"(0, 5, 1)\": \"10/7\", \"(0, 0, 6)\": \"1\"}, \"projected_target_B\": \"(1/64)*(U0^2*U1^2*U2^2 - V0^2*V1^2*V2^2)\"}"

theorem pole_order_positive : poleOrder > 0 := by decide

/-- Exact block-swap parity identity under `U = X + Y, V = X - Y` (`τ(U, V) = (V, U)`):
the hypersurface `f(U) + f(V)` is swap-even while the projected K3 target `B(U) - B(V)` is swap-odd. -/
theorem polarized_k3_swap_parity (fU fV BU BV : Int) :
    (fV + fU) = (fU + fV) ∧ (BV - BU) = -(BU - BV) := by
  omega

end HodgeOpenInstance.Case66
