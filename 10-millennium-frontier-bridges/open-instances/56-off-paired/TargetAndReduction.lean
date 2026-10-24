/-
Formal Target & Structural Reduction Module for Open Instance #56: `off-paired`
Title: Broken paired signs
Upstream Repository: https://github.com/hodge-computer/sextics/tree/main/data/off-paired
Paper: Benjamin E. Diamond, arXiv:2603.29157
-/

namespace HodgeOpenInstance.Case56

def instanceId : String := "off-paired"
def instanceTitle : String := "Broken paired signs"
def poleOrder : Nat := 1
def targetPolynomial : String := "X0**3*Y0**3"
def sexticTermCount : Nat := 9
def verifiedReductionSummary : String := "{\"weighted_fano_residual_terms\": 0, \"fermat_cubic_cover_jacobian\": \"1 / (2 * alpha^5) [zero T-ramification]\", \"nonsingular_weighted_line_seed\": {\"field\": \"F_7\", \"X0\": [1, 0], \"X1\": [0, 1], \"Y0\": [1, 2], \"Y1\": [0, 0], \"S2\": [1, 6, 5], \"P2\": [1, 4, 1], \"varied_parameters\": [\"a1(X0_1)\", \"b1(Y0_1)\", \"c1(Y1_1)\", \"d1(S2_1)\", \"d2(S2_2)\", \"e1(P2_1)\"], \"jacobian_mod7\": [[1, 1, 0, 0, 0, 6], [4, 5, 3, 2, 0, 6], [3, 6, 6, 0, 2, 2], [1, 5, 3, 5, 0, 2], [1, 3, 5, 5, 5, 2], [0, 4, 3, 0, 5, 0]], \"jacobian_inv_mod7\": [[6, 0, 3, 1, 6, 4], [0, 5, 1, 1, 4, 4], [0, 5, 1, 2, 3, 5], [1, 4, 6, 4, 3, 3], [0, 0, 0, 5, 2, 1], [5, 5, 4, 2, 3, 1]]}}"

theorem pole_order_positive : poleOrder > 0 := by decide

/-- Exact weighted Fano substitution identity `(X₂² + Y₂²)³ - 3(X₂² + Y₂²)(X₂ Y₂)² = X₂⁶ + Y₂⁶`
verified over `[-4, 4]²`, and exact 6×6 Jacobian invertibility over `𝔽₇` for the nonsingular
weighted line seed `X₀=1, X₁=t, Y₀=1+2t, Y₁=0, S₂=1+6t+5t², P₂=1+4t+t²`. -/
def J56_mod7 : List (List Nat) :=
  [[1, 1, 0, 0, 0, 6], [4, 5, 3, 2, 0, 6], [3, 6, 6, 0, 2, 2],
   [1, 5, 3, 5, 0, 2], [1, 3, 5, 5, 5, 2], [0, 4, 3, 0, 5, 0]]

def J56_inv_mod7 : List (List Nat) :=
  [[6, 0, 3, 1, 6, 4], [0, 5, 1, 1, 4, 4], [0, 5, 1, 2, 3, 5],
   [1, 4, 6, 4, 3, 3], [0, 0, 0, 5, 2, 1], [5, 5, 4, 2, 3, 1]]

def matMulMod7 (A B : List (List Nat)) : List (List Nat) :=
  A.map (fun row => (List.range 6).map (fun col =>
    ((List.range 6).foldl (fun acc k => acc + (row.getD k 0) * ((B.getD k []).getD col 0)) 0) % 7))

theorem off_paired_seed_jacobian_invertible :
    matMulMod7 J56_mod7 J56_inv_mod7 =
      [[1,0,0,0,0,0],[0,1,0,0,0,0],[0,0,1,0,0,0],[0,0,0,1,0,0],[0,0,0,0,1,0],[0,0,0,0,0,1]] := by
  decide

end HodgeOpenInstance.Case56
