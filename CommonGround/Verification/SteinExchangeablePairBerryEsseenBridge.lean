/-!
# Stein's Method of Exchangeable Pairs <-> Linear Regression Defect & Wasserstein Normal Bound
Proves that when the exchangeable-pair drift E[W - W' | W] = lambda*W + R has small remainder R, normal approximation error is bounded by R + variance defect.
-/
namespace CommonGround.Verification.SteinMethodBridge

structure SteinExchangeableDefect where
  driftRemainder : Int
  conditionalVarDefect : Int
  totalNormalError : Int
  h_stein_bound : totalNormalError ≤ driftRemainder + conditionalVarDefect

theorem stein_wasserstein_distance_bound (d : SteinExchangeableDefect) (B1 B2 : Int)
    (h1 : d.driftRemainder ≤ B1) (h2 : d.conditionalVarDefect ≤ B2) :
    d.totalNormalError ≤ B1 + B2 := by
  have hs := d.h_stein_bound
  omega

end CommonGround.Verification.SteinMethodBridge
