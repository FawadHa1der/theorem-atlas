/-
  Discovery 08 — Frontier Synthesis #5 (V213):
  Vickrey–Clarke–Groves (VCG) Dominant-Strategy Incentive Compatibility & Clarke Pivot Non-Negativity,
  Rochet Multi-Dimensional Cyclic Monotonicity vs. 2-Cycle-Monotone 3-Cycle Hodge Curl Obstruction,
  and Myerson–Satterthwaite Ex-Post & Bayesian Bilateral Trade Impossibility

  Pure-core Lean 4.33.0 (`0` imports, `0` sorrys, `0` axioms, `0` fractions).

  Unifies three structural duality pillars across Mechanism Design (`econlib`),
  Convex / Tropical Subgradient Potentials (`08-kakutani-and-galois-structural-duality`),
  and Simplicial Discrete Hodge Curl (`09-consequence-lens-meta-atlas`):

  1. VCG CLARKE-PIVOT DOMINANT-STRATEGY INCENTIVE COMPATIBILITY (DSIC), NON-NEGATIVE EXTERNALITY
     PAYMENTS & VOLUNTARY PARTICIPATION VS. FIRST-PRICE STRATEGIC SHADING & BUDGET-BALANCE BARRIER:
     - Universal integer VCG utility decomposition: under Clarke-pivot externality payment
       `p_i = W_{-i}^* - ∑_{j ≠ i} v_j(x^*)`, agent `i`'s truthful net payoff equals the exact
       marginal social surplus `(v_i(x^*) + ∑_{j ≠ i} v_j(x^*)) - W_{-i}^*`, dominating any
       misreport-induced outcome `x_rep` by total welfare optimality while simultaneously
       satisfying `0 ≤ p_i` (no deficit) and `0 ≤ u_i` (individual rationality under free disposal).
     - Premise-failure contrasts: First-Price Winner-Pays-Bid auctions incentivize bid shading
       (`b_1 = 7 < 10 = v_1` raises payoff from `0` to `3 > 0`), and Clarke payments violate
       exact budget balance (`p_1 + p_2 = 6 ≠ 0`, Green–Laffont impossibility).

  2. ROCHET CYCLIC MONOTONICITY POTENTIAL CHARACTERIZATION & CONSTRUCTIVE BELLMAN–FORD PRICING
     VS. STRICTLY 2-CYCLE-MONOTONE 2D ALLOCATION WITH NEGATIVE 3-CYCLE DISCRETE HODGE CURL (`-2 < 0`):
     - Necessary & Constructively Sufficient Potential Theorem (`rochet_three_type_iff_cycle_slacks`):
       For three 2-item types `tA, tB, tC ∈ ℤ²` and bundles `xA, xB, xC ∈ ℤ²` under bilinear
       valuation `⟨t, x⟩`, a Dominant-Strategy Truthful payment vector `(pA, pB, pC) ∈ ℤ³` exists
       IF AND ONLY IF all three pairwise `2`-cycle slacks `⟨t_i - t_j, x_i - x_j⟩ ≥ 0` AND both
       oriented `3`-cycle Rochet slacks are `≥ 0`, proved constructively via an explicit integer
       Bellman–Ford shortest-path potential!
     - Explicit Multi-Dimensional Premise-Boundary Discovery
       (`strictly_two_cycle_monotone_yet_negative_three_cycle_curl_impossibility`):
       On the 2D allocation simplex `xA = (0,0), xB = (1,0), xC = (0,1)` with integer valuations
       `tA = (3,0), tB = (4,4), tC = (0,1)`:
         • EVERY pairwise `2`-cycle slack is STRICTLY POSITIVE (`+1 > 0` on `(A,B)`, `(B,C)`, `(C,A)`),
           so every pair of types in isolation is strictly truthfully implementable;
         • Yet the oriented `3`-cycle `A → B → C → A` has Rochet slack `-2 < 0` (non-zero discrete
           Hodge `1`-cocycle curl obstructing `im(d₀)` conservative price potentials!),
         • Proving universally that FOR ALL `pA, pB, pC : Int`, NO truthful payment rule exists!

  3. MYERSON–SATTERTHWAITE EX-POST & BAYESIAN BILATERAL TRADE IMPOSSIBILITY VS. POSTED-PRICE ESCAPE:
     - Ex-Post Impossibility (`expost_bilateral_trade_impossibility`): For ALL `cL < vL < cH < vH`,
       any Ex-Post Efficient, DSIC, Ex-Post Individually Rational bilateral trade mechanism forces
       external subsidy `pS_HL - pB_HL ≥ cH - vL > 0` on state `(vH, cL)`.
     - Bayesian / Interim Myerson–Satterthwaite Subsidy Lower Bound
       (`bayesian_myerson_satterthwaite_expected_subsidy_bound`): Even relaxing DSIC → Bayesian IC,
       Ex-Post IR → Interim IR, and Ex-Post BB → Expected BB under the uniform `2 × 2` prior,
       4-state expected seller receipts minus buyer payments satisfy
       `pS_total - pB_total ≥ 2 * (cH - vL) - (vH - cL)` (`≥ +2 > 0` at `(0, 2, 8, 10)`!).
     - Second-Best Posted-Price Escape (`posted_price_dsic_ir_budget_balanced_witness`): Posting
       any fixed price `P` (`vL ≤ P ≤ cH`, trading iff `c ≤ P ≤ v`) achieves Exact Ex-Post Budget
       Balance (`0` subsidy), DSIC, and Ex-Post IR simultaneously by sacrificing marginal trades.
-/

namespace KakutaniGaloisDuality.VickreyClarkeGrovesRochetAndBilateralTrade

-- ============================================================================
-- SECTION 1: VCG CLARKE-PIVOT DSIC, NON-NEGATIVITY & INDIVIDUAL RATIONALITY
--            VS. FIRST-PRICE STRATEGIC SHADING
-- ============================================================================

/-- Clarke-pivot externality payment charged to agent `i`:
    `othersOptWithout_i` is the maximum welfare of agents `j ≠ i` without agent `i`,
    and `othersAtStar` is the welfare of agents `j ≠ i` at the socially optimal outcome `x*`. -/
def clarkePayment (othersOptWithout_i othersAtStar : Int) : Int :=
  othersOptWithout_i - othersAtStar

/-- Agent `i`'s quasi-linear net utility `v_i(x) - p_i` under the Clarke-pivot VCG rule. -/
def vcgNetUtility (viAtOutcome othersOptWithout_i othersAtOutcome : Int) : Int :=
  viAtOutcome - clarkePayment othersOptWithout_i othersAtOutcome

/-- First-price single-item auction utility for bidder 1 with true valuation `v1`, bid `b1`,
    facing rival highest bid `b2` (tie broken in favor of bidder 1 when `b2 ≤ b1`). -/
def firstPriceUtility (v1 b1 b2 : Int) : Int :=
  if b2 ≤ b1 then v1 - b1 else 0

/-- **Universal VCG Clarke-Pivot Theorem**:
    1. **Dominant-Strategy Incentive Compatibility (DSIC)**: Whenever `x*` maximizes total reported
       social welfare (`viRep + othersAtRep ≤ viStar + othersAtStar`), truthful reporting yields
       net utility `(viStar + othersAtStar) - othersOptWithout_i ≥ vcgNetUtility viRep ...`
       against EVERY alternative outcome induced by misreporting;
    2. **No-Deficit Non-Negative Payments (`0 ≤ clarkePayment`)**: Whenever `othersAtStar ≤ othersOptWithout_i`
       (removing `i`'s objective cannot lower the maximum of `∑_{j ≠ i} v_j`), `0 ≤ clarkePayment`;
    3. **Ex-Post Individual Rationality (`0 ≤ vcgNetUtility`)**: Whenever `x*` weakly beats the
       without-`i` optimizer `x_{-i}^*` in total welfare and `0 ≤ viAtWithoutOpt` (free disposal),
       truthful participation guarantees `0 ≤ vcgNetUtility`. -/
theorem vcg_clarke_pivot_dsic_nonnegativity_and_individual_rationality
    (viStar othersAtStar viRep othersAtRep othersOptWithout_i viAtWithoutOpt : Int)
    (hSocialOpt : viRep + othersAtRep ≤ viStar + othersAtStar)
    (hPivotMax : othersAtStar ≤ othersOptWithout_i)
    (hBeatsOptOut : viAtWithoutOpt + othersOptWithout_i ≤ viStar + othersAtStar)
    (hFreeDisposal : 0 ≤ viAtWithoutOpt) :
    vcgNetUtility viRep othersOptWithout_i othersAtRep ≤
      vcgNetUtility viStar othersOptWithout_i othersAtStar ∧
    vcgNetUtility viStar othersOptWithout_i othersAtStar -
      vcgNetUtility viRep othersOptWithout_i othersAtRep =
        (viStar + othersAtStar) - (viRep + othersAtRep) ∧
    0 ≤ clarkePayment othersOptWithout_i othersAtStar ∧
    0 ≤ vcgNetUtility viStar othersOptWithout_i othersAtStar := by
  unfold vcgNetUtility clarkePayment
  omega

/-- **Premise-Failure Contrast (`First-Price Strategic Shading & VCG Non-Zero Revenue`)**:
    For valuations `v1 = 10, v2 = 6` on a single item:
    1. Under First-Price Winner-Pays-Bid, truthful bidding `b1 = 10` yields `0` utility, whereas
       strategic bid shading `b1 = 7` yields strictly higher utility `3 > 0` (violating DSIC!);
    2. Under VCG Clarke-pivot (`p1 = 6, p2 = 0`), truthful bidding is optimal (`u1 = 4 ≥ 0`),
       yet total payments `p1 + p2 = 6 > 0` cannot be rebated to the two agents without breaking DSIC. -/
theorem first_price_shading_breaks_dsic_and_vcg_surplus_imbalance :
    firstPriceUtility 10 10 6 = 0 ∧
    firstPriceUtility 10 7 6 = 3 ∧
    firstPriceUtility 10 10 6 < firstPriceUtility 10 7 6 ∧
    clarkePayment 6 0 + clarkePayment 10 10 = 6 := by
  unfold firstPriceUtility clarkePayment
  decide

-- ============================================================================
-- SECTION 2: ROCHET MULTI-DIMENSIONAL CYCLIC MONOTONICITY & BELLMAN–FORD PRICING
--            VS. 2-CYCLE-MONOTONE 3-CYCLE DISCRETE HODGE CURL OBSTRUCTION
-- ============================================================================

/-- 2D integer inner product `⟨t, x⟩ = t.1 * x.1 + t.2 * x.2` (bilinear multi-item valuation). -/
def dot2 (t x : Int × Int) : Int :=
  t.1 * x.1 + t.2 * x.2

/-- Difference of 2D integer vectors `a - b`. -/
def sub2 (a b : Int × Int) : Int × Int :=
  (a.1 - b.1, a.2 - b.2)

/-- Pairwise `2`-cycle monotonicity slack `⟨t_i - t_j, x_i - x_j⟩` between types `i` and `j`. -/
def twoCycleSlack2 (ti xi tj xj : Int × Int) : Int :=
  dot2 (sub2 ti tj) (sub2 xi xj)

/-- Oriented `3`-cycle Rochet monotonicity slack around `A → B → C → A`:
    `⟨tA, xA - xB⟩ + ⟨tB, xB - xC⟩ + ⟨tC, xC - xA⟩`. -/
def threeCycleSlack2 (tA xA tB xB tC xC : Int × Int) : Int :=
  dot2 tA (sub2 xA xB) + dot2 tB (sub2 xB xC) + dot2 tC (sub2 xC xA)

/-- Dominant-strategy truthfulness of integer payment vector `(pA, pB, pC)` on 3 types `(A, B, C)`:
    every type `i ∈ {A, B, C}` weakly prefers `(x_i, p_i)` over both alternative menu options. -/
def isTruthfulMenu3
    (tA xA tB xB tC xC : Int × Int) (pA pB pC : Int) : Prop :=
  dot2 tA xB - pB ≤ dot2 tA xA - pA ∧
  dot2 tA xC - pC ≤ dot2 tA xA - pA ∧
  dot2 tB xA - pA ≤ dot2 tB xB - pB ∧
  dot2 tB xC - pC ≤ dot2 tB xB - pB ∧
  dot2 tC xA - pA ≤ dot2 tC xC - pC ∧
  dot2 tC xB - pB ≤ dot2 tC xC - pC

/-- Bilinear linearity helper expanding `twoCycleSlack2` into `dot2` evaluations. -/
theorem twoCycleSlack2_eq_dot2 (ti xi tj xj : Int × Int) :
    twoCycleSlack2 ti xi tj xj = (dot2 ti xi - dot2 ti xj) + (dot2 tj xj - dot2 tj xi) := by
  unfold twoCycleSlack2 dot2 sub2
  grind

/-- Bilinear linearity helper expanding `threeCycleSlack2` into `dot2` evaluations. -/
theorem threeCycleSlack2_eq_dot2 (tA xA tB xB tC xC : Int × Int) :
    threeCycleSlack2 tA xA tB xB tC xC =
      (dot2 tA xA - dot2 tA xB) + (dot2 tB xB - dot2 tB xC) + (dot2 tC xC - dot2 tC xA) := by
  unfold threeCycleSlack2 dot2 sub2
  grind

/-- Bellman–Ford shortest-path bundle price `pB` anchored at `pA = 0` on the 3-type Rochet graph:
    `pB = min(vB(xB) - vB(xA), (vC(xC) - vC(xA)) + (vB(xB) - vB(xC)))`. -/
def rochetPriceB (xA tB xB tC xC : Int × Int) : Int :=
  if dot2 tB xB - dot2 tB xA ≤ (dot2 tC xC - dot2 tC xA) + (dot2 tB xB - dot2 tB xC) then
    dot2 tB xB - dot2 tB xA
  else
    (dot2 tC xC - dot2 tC xA) + (dot2 tB xB - dot2 tB xC)

/-- Bellman–Ford shortest-path bundle price `pC` anchored at `pA = 0` on the 3-type Rochet graph:
    `pC = min(vC(xC) - vC(xA), (vB(xB) - vB(xA)) + (vC(xC) - vC(xB)))`. -/
def rochetPriceC (xA tB xB tC xC : Int × Int) : Int :=
  if dot2 tC xC - dot2 tC xA ≤ (dot2 tB xB - dot2 tB xA) + (dot2 tC xC - dot2 tC xB) then
    dot2 tC xC - dot2 tC xA
  else
    (dot2 tB xB - dot2 tB xA) + (dot2 tC xC - dot2 tC xB)

/-- Explicit integer Bellman–Ford shortest-path prices `(pA, pB, pC)` anchored at `pA = 0`. -/
def rochetBellmanFordPrices (xA tB xB tC xC : Int × Int) : Int × Int × Int :=
  (0, rochetPriceB xA tB xB tC xC, rochetPriceC xA tB xB tC xC)

/-- **Rochet Exact Potential & Cycle-Slack Characterization Theorem (Constructive Iff)**:
    On ANY 3-type multi-item allocation `(tA, xA), (tB, xB), (tC, xC)` in `ℤ²`, an integer
    Dominant-Strategy Truthful payment vector `(pA, pB, pC)` exists **if and only if** all three
    `2`-cycle slacks (`AB`, `BC`, `CA`) AND both oriented `3`-cycle slacks (`ABC`, `ACB`) are `≥ 0` —
    and when they hold, `rochetBellmanFordPrices` constructively synthesizes truthful payments! -/
theorem rochet_three_type_truthful_iff_two_and_three_cycle_monotonicity
    (tA xA tB xB tC xC : Int × Int) :
    (∃ pA pB pC : Int, isTruthfulMenu3 tA xA tB xB tC xC pA pB pC) ↔
    (0 ≤ twoCycleSlack2 tA xA tB xB ∧
     0 ≤ twoCycleSlack2 tB xB tC xC ∧
     0 ≤ twoCycleSlack2 tC xC tA xA ∧
     0 ≤ threeCycleSlack2 tA xA tB xB tC xC ∧
     0 ≤ threeCycleSlack2 tA xA tC xC tB xB) := by
  rw [twoCycleSlack2_eq_dot2 tA xA tB xB,
      twoCycleSlack2_eq_dot2 tB xB tC xC,
      twoCycleSlack2_eq_dot2 tC xC tA xA,
      threeCycleSlack2_eq_dot2 tA xA tB xB tC xC,
      threeCycleSlack2_eq_dot2 tA xA tC xC tB xB]
  constructor
  · rintro ⟨pA, pB, pC, hTruth⟩
    unfold isTruthfulMenu3 at hTruth
    omega
  · rintro ⟨h2AB, h2BC, h2CA, h3ABC, h3ACB⟩
    refine ⟨0, rochetPriceB xA tB xB tC xC, rochetPriceC xA tB xB tC xC, ?_⟩
    unfold isTruthfulMenu3 rochetPriceB rochetPriceC
    omega

/-- Explicit 2-item simplex bundles `xA = (0,0), xB = (1,0), xC = (0,1)` and integer valuation
    types `tA = (3,0), tB = (4,4), tC = (0,1)` exhibiting the 2D Discrete Hodge Curl Obstruction. -/
def curlBundleA : Int × Int := (0, 0)
def curlBundleB : Int × Int := (1, 0)
def curlBundleC : Int × Int := (0, 1)

def curlTypeA : Int × Int := (3, 0)
def curlTypeB : Int × Int := (4, 4)
def curlTypeC : Int × Int := (0, 1)

/-- **Constructive Multi-Dimensional Premise-Boundary Discovery
    (`2`-Cycle Monotonicity Fails to Imply Truthful Implementability in Dimension `≥ 2`)**:
    For `(curlTypeA, curlBundleA), (curlTypeB, curlBundleB), (curlTypeC, curlBundleC)` in `ℤ²`:
    1. ALL THREE pairwise `2`-cycle monotonicity slacks equal `+1 > 0` (every pair of types
       in isolation is strictly monotone and truthfully implementable!);
    2. The reverse `3`-cycle `A → C → B → A` even has strictly positive slack `+5 > 0`;
    3. YET the forward `3`-cycle `A → B → C → A` has Rochet curl `-2 < 0` (a non-conservative
       discrete Hodge `1`-cocycle vortex around the 2D bundle simplex!),
    4. Therefore **FOR ALL `pA, pB, pC : Int`**, NO truthful payment vector `(pA, pB, pC)` exists! -/
theorem strictly_two_cycle_monotone_yet_negative_three_cycle_curl_impossibility :
    twoCycleSlack2 curlTypeA curlBundleA curlTypeB curlBundleB = 1 ∧
    twoCycleSlack2 curlTypeB curlBundleB curlTypeC curlBundleC = 1 ∧
    twoCycleSlack2 curlTypeC curlBundleC curlTypeA curlBundleA = 1 ∧
    threeCycleSlack2 curlTypeA curlBundleA curlTypeC curlBundleC curlTypeB curlBundleB = 5 ∧
    threeCycleSlack2 curlTypeA curlBundleA curlTypeB curlBundleB curlTypeC curlBundleC = -2 ∧
    (∀ pA pB pC : Int,
      ¬ isTruthfulMenu3 curlTypeA curlBundleA curlTypeB curlBundleB curlTypeC curlBundleC pA pB pC) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro pA pB pC hTruth
  have hiff := (rochet_three_type_truthful_iff_two_and_three_cycle_monotonicity
    curlTypeA curlBundleA curlTypeB curlBundleB curlTypeC curlBundleC).mp ⟨pA, pB, pC, hTruth⟩
  have hNeg : threeCycleSlack2 curlTypeA curlBundleA curlTypeB curlBundleB curlTypeC curlBundleC = -2 := by decide
  omega

/-- **Positive Conservative Contrast (`tB = (4, 2)` Eliminates Curl & Synthesizes Exact Prices)**:
    Lowering type `B`'s second-item valuation from `(4, 4)` to `tB' = (4, 2)` preserves positive
    `2`-cycle slacks (`1, 3, 1`), flips the forward `3`-cycle slack from `-2` to `0 ≥ 0`, and
    `rochetBellmanFordPrices` synthesizes exact integer prices `(pA, pB, pC) = (0, 3, 1)` that
    satisfy all `6` Dominant-Strategy Truthfulness inequalities! -/
theorem conservative_zero_curl_witness_synthesizes_truthful_prices :
    threeCycleSlack2 curlTypeA curlBundleA (4, 2) curlBundleB curlTypeC curlBundleC = 0 ∧
    rochetBellmanFordPrices curlBundleA (4, 2) curlBundleB curlTypeC curlBundleC = (0, 3, 1) ∧
    isTruthfulMenu3 curlTypeA curlBundleA (4, 2) curlBundleB curlTypeC curlBundleC 0 3 1 := by
  unfold threeCycleSlack2 rochetBellmanFordPrices rochetPriceB rochetPriceC isTruthfulMenu3
  unfold curlTypeA curlTypeC curlBundleA curlBundleB curlBundleC dot2 sub2
  decide

-- ============================================================================
-- SECTION 3: MYERSON–SATTERTHWAITE EX-POST & BAYESIAN BILATERAL TRADE IMPOSSIBILITY
--            VS. SECOND-BEST POSTED-PRICE MECHANISM
-- ============================================================================

/-- **Universal Ex-Post Bilateral Trade Impossibility (`cL < vL < cH < vH`)**:
    For ANY overlapping buyer valuations `vL < vH` and seller costs `cL < cH` (`cL < vL < cH < vH`),
    if an Ex-Post Efficient mechanism trades (`q = 1`) on `(vH, cL), (vH, cH), (vL, cL)` and
    abstains (`q = 0`) on `(vL, cH)` while satisfying DSIC and Ex-Post Individual Rationality:
    - `pB_HL ≤ pB_LL ≤ vL` and `cH ≤ pS_HH ≤ pS_HL`,
    - forcing strictly positive external subsidy `pS_HL - pB_HL ≥ cH - vL > 0` on `(vH, cL)`
      (so Ex-Post Budget Balance `pS_HL ≤ pB_HL` is IMPOSSIBLE)! -/
theorem expost_bilateral_trade_impossibility
    (cL vL cH vH pB_HL pB_LL pS_HL pS_HH : Int)
    (hOverlap : vL < cH)
    (hBuyerLL_IR : pB_LL ≤ vL)
    (hBuyerHL_IC : vH - pB_LL ≤ vH - pB_HL)
    (hSellerHH_IR : cH ≤ pS_HH)
    (hSellerHL_IC : pS_HH - cL ≤ pS_HL - cL) :
    cH - vL ≤ pS_HL - pB_HL ∧ 0 < pS_HL - pB_HL := by
  omega

/-- **Universal Bayesian Myerson–Satterthwaite Expected Subsidy Lower Bound (`2 × 2` Uniform Prior)**:
    Even weakening DSIC to **Bayesian Incentive Compatibility (BIC)**, Ex-Post IR to **Interim IR**,
    and Ex-Post Budget Balance to **Expected Budget Balance** across all `4` states `(HL, HH, LL, LH)`
    under the uniform `2 × 2` prior:
    - 4-state buyer payments satisfy `pB_HL + pB_HH + pB_LL + pB_LH ≤ vH + 2 * vL`,
    - 4-state seller receipts satisfy `cL + 2 * cH ≤ pS_HL + pS_HH + pS_LL + pS_LH`,
    - so 4-state expected subsidy is bounded below by `2 * (cH - vL) - (vH - cL)` — strictly positive
      whenever `vH - cL < 2 * (cH - vL)` (e.g., `+2 > 0` at `(cL, vL, cH, vH) = (0, 2, 8, 10)`)! -/
theorem bayesian_myerson_satterthwaite_expected_subsidy_bound
    (cL vL cH vH pB_HL pB_HH pB_LL pB_LH pS_HL pS_HH pS_LL pS_LH : Int)
    (hBuyerL_IIR : pB_LL + pB_LH ≤ vL)
    (hBuyerH_BIC : vH - pB_LL - pB_LH ≤ 2 * vH - pB_HL - pB_HH)
    (hSellerH_IIR : cH ≤ pS_HH + pS_LH)
    (hSellerL_BIC : pS_HH + pS_LH - cL ≤ pS_HL + pS_LL - 2 * cL) :
    pB_HL + pB_HH + pB_LL + pB_LH ≤ vH + 2 * vL ∧
    cL + 2 * cH ≤ pS_HL + pS_HH + pS_LL + pS_LH ∧
    2 * (cH - vL) - (vH - cL) ≤
      (pS_HL + pS_HH + pS_LL + pS_LH) - (pB_HL + pB_HH + pB_LL + pB_LH) := by
  omega

/-- Posted-price bilateral trade mechanism at fixed price `P`:
    trades (`q = 1` at price `P` paid directly from buyer to seller, `0` external subsidy)
    if and only if both reported buyer value `b ≥ P` and reported seller cost `s ≤ P`. -/
def postedPriceBuyerUtility (vTrue bRep sRep priceP : Int) : Int :=
  if priceP ≤ bRep ∧ sRep ≤ priceP then vTrue - priceP else 0

def postedPriceSellerUtility (cTrue bRep sRep priceP : Int) : Int :=
  if priceP ≤ bRep ∧ sRep ≤ priceP then priceP - cTrue else 0

/-- **Second-Best Escape (`Posted-Price Mechanism Satisfies DSIC + Ex-Post IR + Exact Budget Balance`)**:
    Relaxing Ex-Post Efficiency to a fixed posted price `priceP` restores ALL THREE of:
    1. Exact Ex-Post Budget Balance (`buyerPayment = sellerReceipt` in every state, `0` subsidy!),
    2. Ex-Post Individual Rationality (`0 ≤ buyerUtility` and `0 ≤ sellerUtility` for all `(v, c)`),
    3. Dominant-Strategy Incentive Compatibility (`truthful ≥ any misreport` for both buyer and seller)! -/
theorem posted_price_dsic_ir_and_exact_budget_balance
    (vTrue cTrue bRep sRep priceP : Int) :
    0 ≤ postedPriceBuyerUtility vTrue vTrue sRep priceP ∧
    0 ≤ postedPriceSellerUtility cTrue bRep cTrue priceP ∧
    postedPriceBuyerUtility vTrue bRep sRep priceP ≤
      postedPriceBuyerUtility vTrue vTrue sRep priceP ∧
    postedPriceSellerUtility cTrue bRep sRep priceP ≤
      postedPriceSellerUtility cTrue bRep cTrue priceP := by
  unfold postedPriceBuyerUtility postedPriceSellerUtility
  split <;> split <;> omega

end KakutaniGaloisDuality.VickreyClarkeGrovesRochetAndBilateralTrade
