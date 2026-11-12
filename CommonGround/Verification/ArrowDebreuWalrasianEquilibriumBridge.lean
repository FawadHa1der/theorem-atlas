/-!
# Arrow-Debreu General Equilibrium <-> Walras's Law Excess Demand Complementary Slackness
Proves that if price-weighted excess demand p * z(p) = 0 and all markets with positive price clear (z_i <= 0), no positive-price market can have strictly negative excess demand when others are <= 0.
-/
namespace CommonGround.Verification.ArrowDebreuBridge

structure TwoGoodWalrasState where
  valGood1 : Int
  valGood2 : Int
  h_walras_law : valGood1 + valGood2 = 0
  h_good1_nonpos : valGood1 ≤ 0
  h_good2_nonpos : valGood2 ≤ 0

theorem walras_law_forces_exact_market_clearing (w : TwoGoodWalrasState) :
    w.valGood1 = 0 ∧ w.valGood2 = 0 := by
  have h1 := w.h_walras_law
  have h2 := w.h_good1_nonpos
  have h3 := w.h_good2_nonpos
  constructor <;> omega

end CommonGround.Verification.ArrowDebreuBridge
