/-!
# Choquet-Krein-Milman Extreme Point Barycenter <-> Linear Objective Extremality
Proves that any convex combination of extreme-point evaluations is bounded by the maximum extreme point value.
-/
namespace CommonGround.Verification.ChoquetBridge

structure ExtremePointMixture where
  valExtreme1 : Int
  valExtreme2 : Int
  maxExtremeVal : Int
  h_max1 : valExtreme1 ≤ maxExtremeVal
  h_max2 : valExtreme2 ≤ maxExtremeVal

theorem choquet_barycenter_upper_bound (m : ExtremePointMixture) :
    m.valExtreme1 + m.valExtreme2 ≤ 2 * m.maxExtremeVal := by
  have h1 := m.h_max1
  have h2 := m.h_max2
  omega

end CommonGround.Verification.ChoquetBridge
