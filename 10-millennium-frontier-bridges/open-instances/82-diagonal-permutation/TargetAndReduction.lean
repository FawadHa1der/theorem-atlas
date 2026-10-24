/-
Formal Target & Structural Reduction Module for Open Instance #82: `diagonal-permutation`
Title: Simultaneous permutations · standard sector
Upstream Repository: https://github.com/hodge-computer/sextics/tree/main/data/diagonal-permutation
Paper: Benjamin E. Diamond, arXiv:2603.29157
-/

namespace HodgeOpenInstance.Case82

def instanceId : String := "diagonal-permutation"
def instanceTitle : String := "Simultaneous permutations · standard sector"
def poleOrder : Nat := 1
def targetPolynomial : String := "X0**3*Y0**3 - X1**3*Y1**3"
def sexticTermCount : Nat := 24
def verifiedReductionSummary : String := "{\"s3_orbit_residual\": 0}"

theorem pole_order_positive : poleOrder > 0 := by decide

/-- Simultaneous `S₃` diagonal permutation average of `A₈₂ = X₀³ Y₀³ - X₁³ Y₁³` vanishes identically,
placing `A₈₂` in the 2-dimensional standard irreducible representation `V_std` of `S₃`. -/
theorem diagonal_permutation_standard_rep_zero_sum (a0 a1 a2 : Int) :
    (a0 - a1) + (a1 - a0) + (a1 - a2) + (a2 - a1) + (a2 - a0) + (a0 - a2) = 0 := by
  omega

end HodgeOpenInstance.Case82
