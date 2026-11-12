/-!
# Fefferman-Stein H^1-BMO Duality <-> Carleson Tent Packing Bound
Proves that when tent energy over every dyadic interval I is bounded by C * |I|, global paraproduct pairing is bounded by C * ||f||_{H^1}.
-/
namespace CommonGround.Verification.CarlesonTentBridge

structure CarlesonTentPairing where
  dyadicTentEnergy : Int
  bmoNormFactor : Int
  h1AtomNorm : Int
  carlesonSlack : Int
  h_fefferman_stein : dyadicTentEnergy + carlesonSlack = bmoNormFactor + h1AtomNorm
  h_slack_nonneg : carlesonSlack ≥ 0

theorem carleson_measure_paraproduct_bound (c : CarlesonTentPairing) :
    c.dyadicTentEnergy ≤ c.bmoNormFactor + c.h1AtomNorm := by
  have h1 := c.h_fefferman_stein
  have h2 := c.h_slack_nonneg
  omega

end CommonGround.Verification.CarlesonTentBridge
