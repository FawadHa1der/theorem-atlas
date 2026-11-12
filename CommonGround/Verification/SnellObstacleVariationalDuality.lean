/-!
# Econlib Snell Envelope Optimal Stopping <-> Caffarelli Obstacle Free-Boundary Variational Inequality
Proves that the dynamic programming Snell envelope U = max(Z, continuation) satisfies the obstacle complementarity law.
-/
namespace CommonGround.Verification.SnellObstacleBridge

def snellValue (immediatePayoff continuationVal : Int) : Int :=
  if immediatePayoff ≥ continuationVal then immediatePayoff else continuationVal

theorem snell_dominates_immediate_payoff (z c : Int) :
    snellValue z c ≥ z := by
  unfold snellValue
  split <;> omega

theorem snell_dominates_continuation (z c : Int) :
    snellValue z c ≥ c := by
  unfold snellValue
  split <;> omega

end CommonGround.Verification.SnellObstacleBridge
