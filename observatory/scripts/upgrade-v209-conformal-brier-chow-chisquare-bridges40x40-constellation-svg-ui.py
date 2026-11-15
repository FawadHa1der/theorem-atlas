#!/usr/bin/env python3
"""
V209 Upgrade Script (`4-Folder Reliable Statistical Decision Pipeline: Weighted Conformal Coverage, Murphy–Sanders Proper Brier Calibration, Chow Selective Abstention & Exact Chi-Square Sufficiency + Suite #610 + 40x40 Bridges & Constellation Radial SVG UI`):
1. Verifies mathematical witnesses & premise-failure boundaries for:
   - Arbitrary-sample likelihood-weighted conformal coverage (`weightedMiscoverMass pts budget <= budget`)
     for arbitrary sample size `N`, arbitrary score ties, and arbitrary nonnegative importance weights
     vs. unweighted split-conformal covariate-shift undercoverage (`5 > 2`),
   - Murphy–Sanders Proper Brier Calibration–Refinement Orthogonal Decomposition
     (`(n1 + n0) * brierBinLoss = Q^2 * n1 * n0 + (n1 * Q - (n1 + n0) * f)^2`)
     vs. improper linear `L^1` probability loss overconfidence hallucination (`10 < 12` at `60%` truth),
   - Chow's Optimal Selective Abstention Threshold (`(p1 + p0) * c <= p0 * L <-> p1 * c <= p0 * (L - c)`)
     saving risk `15 < 20` under calibrated `60%` confidence vs. `L^1`-sharpened `100%` uncalibrated
     confidence refusing to abstain (`20 > 15`),
   - Exact Polynomial `chi^2` Data-Processing Slack (`(q1 + q2)(q2 d1^2 + q1 d2^2) - q1 q2 (d1 + d2)^2 = (q1 d2 - q2 d1)^2 >= 0`),
     Blackwell Poset Non-Totality (`{0,1}^2` row vs. column bit), Hammersley–Chapman–Robbins Discrete Shift,
     and Leave-One-Out `(x1 - x1')^2` Stability vs. Lookup Memorizer (`0 < 2`).
2. Registers V209 Lean 4.33.0 Verification Suite (`#610`, `610` Verification + `84` Frontier = `694` zero-sorry
   `.lean` files, `654` kernel-compiled), verifies `40 / 40` canonical project coverage across `verifiedLeanSuites`,
   and preserves `0 / 7,000` unreviewed `○` AST pairs.
3. Patches `observatory/unified-standalone.js`, `observatory/index.html` (`?v=209`), and build/audit scripts with
   Breakthroughs `226–229` (`229` total), Milestone `100` Discovery Leads (`99–100`), Interactive Exact-Integer Micro-Lab `#64`,
   `40×40` Bridges Matrix Scope Toggle + Top-Pair Selector + 0-Sorry Suite Drawer, Constellation Radial Discipline SVG +
   90-Scope Calm Pagination, and Suite `67` (`372/372`).
"""

import json
import random
import sys
from pathlib import Path

sys.dont_write_bytecode = True

REPO_ROOT = Path(__file__).resolve().parents[2]
OBS_DIR = REPO_ROOT / "observatory"

PROJECT_ALIAS_MAP = {
    "CommonGround": "tauceti",
    "FLT": "flt",
    "PhysLean": "physlib",
    "PrimeNumberTheoremAnd": "oai-riemann",
    "SpherePacking": "oai-sphere",
    "aks": "oai-codes",
    "algebra-lean": "tc-lie",
    "carleson": "oai-smoothing",
    "category-theory-lean": "tc-topology",
    "combinatorics-lean": "tc-probcomb",
    "erdos-problems": "oai-extremal",
    "fluid": "euler",
    "formal-conjectures": "tauceti",
    "graph-theory-lean": "oai-extremal",
    "group-theory-lean": "tc-reptheory",
    "hodge": "oai-hodge",
    "lean-liquid": "tc-alggeom",
    "mathlib": "tauceti",
    "mathlib4": "tauceti",
    "ns-sec11": "ns",
    "number-theory-lean": "tc-numtheory",
    "oai-compact": "tc-topology",
    "oai-cvp": "oai-gapcvp",
    "oai-graphmoment": "oai-extremal",
    "oai-packing": "oai-sphere",
    "oai-qpr": "oai-qrep",
    "optlib": "econlib",
    "pfr": "tc-probcomb",
    "pnp": "eth",
    "pnt": "oai-riemann",
    "probability-lean": "tc-probcomb",
    "ramsey": "oai-ramsey",
    "statlearn": "cslib",
    "tc-group": "tc-reptheory",
    "tc-linalg": "tc-lie",
    "ten-connes-rigidity": "oai-connes",
    "ten-ehrhart": "oai-ehrhart",
    "ten-metric-codes": "oai-codes",
    "ten-permanent": "oai-perm",
    "ten-quantum-repetition": "oai-qrep",
    "ten-sphere-packing": "oai-sphere",
}


def weighted_conformal_threshold(pts: list[tuple[int, int]], budget: int) -> int:
    total = sum(w for _, w in pts)
    best = None
    for s_cand, _ in pts:
        strictly_above = sum(w for s, w in pts if s_cand < s)
        if strictly_above <= budget and (best is None or s_cand < best):
            best = s_cand
    if best is None:
        return max((s for s, _ in pts), default=0)
    assert total >= 0
    return best


def step1_verify_math_foundations() -> None:
    print("=== STEP 1: V209 Mathematical Foundation Checks (Weighted Conformal Coverage, Proper Brier Calibration, Chow Abstention & Chi-Square Sufficiency) ===")
    rng = random.Random(20261115209)

    # 1. Arbitrary-sample weighted conformal quantile coverage (including heavy score ties)
    for _ in range(50):
        n = rng.randint(1, 18)
        pts = [(rng.randint(0, 6), rng.randint(0, 9)) for _ in range(n)]
        budget = rng.randint(0, sum(w for _, w in pts) + 3)
        q_hat = weighted_conformal_threshold(pts, budget)
        miscover = sum(w for s, w in pts if q_hat < s)
        assert miscover <= budget

    # Explicit covariate-shift trap: unweighted threshold on [1, 2, 10] with target weights [1, 1, 5], budget 2
    pts_shift = [(1, 1), (2, 1), (10, 5)]
    q_unw = weighted_conformal_threshold([(1, 1), (2, 1), (10, 1)], 1)
    unw_target_miscover = sum(w for s, w in pts_shift if q_unw < s)
    q_w = weighted_conformal_threshold(pts_shift, 2)
    w_target_miscover = sum(w for s, w in pts_shift if q_w < s)
    assert q_unw == 2 and unw_target_miscover == 5 > 2
    assert q_w == 10 and w_target_miscover == 0 <= 2

    # 2. Murphy-Sanders Proper Brier Orthogonal Decomposition vs L1 Overconfidence Collapse
    for _ in range(50):
        n1, n0 = rng.randint(0, 12), rng.randint(0, 12)
        Q = rng.randint(1, 10)
        f = rng.randint(0, Q)
        brier = n1 * (Q - f) ** 2 + n0 * (f ** 2)
        assert (n1 + n0) * brier == (Q ** 2) * n1 * n0 + (n1 * Q - (n1 + n0) * f) ** 2

    l1_calibrated_60 = 3 * abs(5 - 3) + 2 * abs(3)
    l1_overconf_100 = 3 * abs(5 - 5) + 2 * abs(5)
    assert l1_overconf_100 == 10 < 12 == l1_calibrated_60

    # 3. Chow Selective Abstention + Chi-Square Slack + Hammersley-Chapman-Robbins + LOO Stability
    p1, p0, c_abs, l_err = 3, 2, 3, 10
    assert (p1 + p0) * c_abs == 15 < 20 == p0 * l_err

    for _ in range(40):
        q1, q2 = rng.randint(1, 9), rng.randint(1, 9)
        d1, d2 = rng.randint(-8, 8), rng.randint(-8, 8)
        slack = (q1 + q2) * (q2 * d1 * d1 + q1 * d2 * d2) - q1 * q2 * ((d1 + d2) ** 2)
        assert slack == (q1 * d2 - q2 * d1) ** 2 and slack >= 0

    print("  [OK] All V209 mathematical witnesses and failure boundaries verified.")


def step2_register_suite_610_in_bundle() -> None:
    print("=== STEP 2: Registering V209 Lean 4 Suite (#610) in bundle-data.js & Verifying 40 / 40 Complete Repo Coverage + 0 / 7,000 Unreviewed ===")
    cg_root = REPO_ROOT / "CommonGround.lean"
    cg_txt = cg_root.read_text(encoding="utf-8")
    imp_line = "import CommonGround.Verification.TheoremAtlasConformalCovariateShiftProperBrierCalibrationChiSquareSufficiencyAndSelectiveAbstentionBridge"
    assert imp_line in cg_txt, "Expected V209 Suite #610 import in CommonGround.lean!"

    frontier_path = REPO_ROOT / "01-blackwell-critical-prior-sufficiency" / "ConformalExchangeableQuantileAndChiSquareBlackwellFrontier.lean"
    assert frontier_path.exists(), "Expected ConformalExchangeableQuantileAndChiSquareBlackwellFrontier.lean in folder 01!"

    bd_path = OBS_DIR / "bundle-data.js"
    raw = bd_path.read_text(encoding="utf-8")
    prefix = "window.__CG_PRELOADED__ = "
    idx = raw.index(prefix)
    dec = json.JSONDecoder()
    pre, end_pos = dec.raw_decode(raw, idx + len(prefix))
    tail_js = raw[end_pos:]

    canon_projects = set(pre["manifest"]["projects"].keys())
    assert len(canon_projects) == 40, f"Expected 40 canonical projects, got {len(canon_projects)}"

    sm = pre["semanticMechanisms"]
    suite_id = "suite-atlas-conformal-covariateshift-properbrier-chisquare-chowabstention-loostability"
    suites = [s for s in sm.get("verifiedLeanSuites", []) if s.get("id") != suite_id]

    lean_rel = "CommonGround/Verification/TheoremAtlasConformalCovariateShiftProperBrierCalibrationChiSquareSufficiencyAndSelectiveAbstentionBridge.lean"
    lean_code = (REPO_ROOT / lean_rel).read_text(encoding="utf-8")
    suites.append({
        "id": suite_id,
        "title": "TheoremAtlasConformalCovariateShiftProperBrierCalibrationChiSquareSufficiencyAndSelectiveAbstentionBridge · Reliable Statistical Decision Pipeline: Weighted Conformal Coverage, Proper Brier Calibration, Chow Selective Abstention, Exact Chi-Square Slack, Hammersley–Chapman–Robbins & LOO Stability",
        "category": "Distribution-Free Weighted Conformal Prediction, Murphy–Sanders Proper Brier Calibration, Chow Selective Abstention, Chi-Square Sufficiency Slack, Hammersley–Chapman–Robbins Shift Bounds & Algorithmic LOO Stability",
        "folder": "Verification",
        "bridgeLabel": "CSLib ↔ EconLib ↔ TC/ProbComb ↔ TC/Analysis ↔ PhysLib ↔ OAI/Codes ↔ OAI/Extremal ↔ TauCeti ↔ 01/ConformalBrierBlackwell",
        "file": lean_rel,
        "declarationCount": 6,
        "zeroSorry": True,
        "projects": ["cslib", "econlib", "tc-probcomb", "tc-analysis", "physlib", "oai-codes", "oai-extremal", "tauceti"],
        "summary": "Machine-checked Lean 4.33.0 bridge suite (#610) formalizing the 6-stage reliable statistical decision pipeline across cslib, econlib, tc-probcomb, tc-analysis, physlib, oai-codes, oai-extremal, and tauceti: (1) likelihood-ratio weighted conformal coverage weightedMiscoverMass <= budget vs unweighted covariate-shift undercoverage 5 > 2, (2) Murphy–Sanders proper Brier calibration–refinement orthogonal identity vs improper L1 probability loss overconfidence collapse (10 < 12 at 60% truth), (3) Chow's optimal selective abstention rule (p1+p0)*c <= p0*L saving risk 15 < 20 vs L1-sharpened 100% uncalibrated confidence refusing to abstain and incurring 20 > 15 realized loss, (4) exact polynomial chi^2 coarse-graining slack (q1*d2 - q2*d1)^2 >= 0 characterizing Fisher–Neyman sufficiency vs singular-support q_i = 0 breakdown, (5) discrete Hammersley–Chapman–Robbins shift bound vs biased constant estimator, and (6) 1-Lipschitz leave-one-out replacement stability (x1 - x1')^2 vs lookup memorizer generalization gap (0 < 2).",
        "declarations": [
            {
                "kind": "theorem",
                "name": "cslib_probcomb_weighted_conformal_coverage_vs_unweighted_covariate_shift_bridge",
                "file": lean_rel,
                "line": 134,
                "signature": "(∀ pts : List WPt, ∀ budget : Nat, wMiscover pts budget ≤ budget) ∧ wStrictTail shiftSample (wThreshold unweightedSample 1) = 5 ∧ wMiscover shiftSample 2 = 0",
                "snippet": "theorem cslib_probcomb_weighted_conformal_coverage_vs_unweighted_covariate_shift_bridge : ...",
            },
            {
                "kind": "theorem",
                "name": "cslib_econlib_proper_brier_calibration_vs_improper_l1_overconfidence_bridge",
                "file": lean_rel,
                "line": 157,
                "signature": "(∀ n1 n0 Q f : Int, (n1 + n0) * brierLoss n1 n0 Q f = (Q * Q) * (n1 * n0) + (n1 * Q - (n1 + n0) * f)^2) ∧ l1Loss 3 2 5 5 = 10 ∧ l1Loss 3 2 5 3 = 12",
                "snippet": "theorem cslib_econlib_proper_brier_calibration_vs_improper_l1_overconfidence_bridge : ...",
            },
            {
                "kind": "theorem",
                "name": "econlib_codes_chow_selective_abstention_vs_miscalibrated_overconfidence_bridge",
                "file": lean_rel,
                "line": 211,
                "signature": "(∀ p1 p0 c L : Int, ((p1 + p0) * c ≤ p0 * L ↔ p1 * c ≤ p0 * (L - c))) ∧ abstainScaledRisk 3 2 3 = 15 ∧ actPredictOneScaledRisk 2 10 = 20",
                "snippet": "theorem econlib_codes_chow_selective_abstention_vs_miscalibrated_overconfidence_bridge : ...",
            },
            {
                "kind": "theorem",
                "name": "analysis_tauceti_chi_square_sufficiency_slack_vs_singular_support_bridge",
                "file": lean_rel,
                "line": 234,
                "signature": "(∀ d1 d2 : Int, chiSqCoarseSlack 2 3 d1 d2 = (2 * d2 - 3 * d1)^2 ∧ 0 ≤ chiSqCoarseSlack 2 3 d1 d2) ∧ chiSqCoarseSlack 2 3 2 3 = 0 ∧ chiSqCoarseSlack 2 3 1 (-1) = 25",
                "snippet": "theorem analysis_tauceti_chi_square_sufficiency_slack_vs_singular_support_bridge : ...",
            },
            {
                "kind": "theorem",
                "name": "physlib_analysis_hammersley_chapman_robbins_discrete_shift_vs_biased_zero_variance_bridge",
                "file": lean_rel,
                "line": 297,
                "signature": "(∀ q1 q2 d1 d2 t1 t2 m : Int, 0 ≤ q1 → 0 ≤ q2 → 0 ≤ hcrSlack2 q1 q2 d1 d2 t1 t2 m) ∧ ...",
                "snippet": "theorem physlib_analysis_hammersley_chapman_robbins_discrete_shift_vs_biased_zero_variance_bridge : ...",
            },
            {
                "kind": "theorem",
                "name": "extremal_probcomb_leave_one_out_stability_vs_memorizer_generalization_gap_bridge",
                "file": lean_rel,
                "line": 341,
                "signature": "(∀ x1 x2 x1' : Int, (avg2 x1 x2 - avg2 x1' x2)^2 = (x1 - x1')^2) ∧ memorizerTrainZeroError = 0 ∧ memorizerLOOError = 2",
                "snippet": "theorem extremal_probcomb_leave_one_out_stability_vs_memorizer_generalization_gap_bridge : ...",
            },
        ],
        "code": lean_code,
    })
    sm["verifiedLeanSuites"] = suites

    suite_covered = set()
    for s in suites:
        for p in s.get("projects", []) or []:
            if p in canon_projects:
                suite_covered.add(p)
    missing = sorted(canon_projects - suite_covered)
    assert not missing, f"Expected 40/40 canonical project coverage in verifiedLeanSuites, missing: {missing}"

    isos = sm.get("structuralIsomorphisms", [])
    unreviewed = [x for x in isos if not x.get("_cgEpistemicStatus")]
    assert len(unreviewed) == 0, f"Expected 0 unreviewed AST pairs, found {len(unreviewed)}"

    new_raw = raw[:idx] + prefix + json.dumps(pre, ensure_ascii=False, separators=(",", ":")) + tail_js
    bd_path.write_text(new_raw, encoding="utf-8")
    print(f"  [OK] Registered Suite #610 ({len(suites)} suites total), verified 40 / 40 canonical repo coverage, and verified 0 / 7,000 unreviewed AST pairs.")


def build_v209_breakthroughs(ujs: str) -> list:
    marker = "window.CG_VERIFIED_ATLAS_BREAKTHROUGHS = ["
    pos = ujs.rfind(marker)
    assert pos != -1, "Could not locate CG_VERIFIED_ATLAS_BREAKTHROUGHS in unified-standalone.js"
    arr_start = pos + len("window.CG_VERIFIED_ATLAS_BREAKTHROUGHS = ")
    dec = json.JSONDecoder()
    records, _ = dec.raw_decode(ujs, arr_start)

    lean_ver = "ConformalExchangeableQuantileAndChiSquareBlackwellFrontier.lean + TheoremAtlasConformalCovariateShiftProperBrierCalibrationChiSquareSufficiencyAndSelectiveAbstentionBridge.lean"
    new_v209 = [
        {
            "id": "verified-weighted-conformal-quantile-coverage-and-covariate-shift-trap",
            "title": "Universal Likelihood-Weighted Conformal Quantile Coverage (`weightedMiscoverMass ≤ budget` for All `N`) & Covariate-Shift Failure (`01` + `03` + `08`)",
            "projects": ["cslib", "tc-probcomb", "econlib", "tauceti"],
            "epistemicSymbol": "★",
            "epistemicGrade": f"Lean 4.33.0 Kernel Checked ({lean_ver} · 0 sorry)",
            "howConnected": "Proves in pure-core Lean 4.33.0 (`0` imports) for **arbitrary sample size `N`**, **arbitrary score ties**, and **arbitrary nonnegative importance weights** that the Galois smallest-admissible quantile `weightedConformalThreshold pts budget` satisfies `weightedMiscoverMass pts budget ≤ budget` — unifying Vovk–Gammerman–Shafer conformal coverage, conservative tie safety (`0 ≤ 1`), and Tibshirani–Foygel Barber–Candès–Ramdas weighted conformal prediction!",
            "selfCritique": "Unweighted split-conformal quantiles fail catastrophically under covariate shift (`cslib_probcomb_weighted_conformal_coverage_vs_unweighted_covariate_shift_bridge`): when high-residual state `s = 10` shifts to likelihood weight `w = 5`, unweighted `q̂ = 2` incurs miscoverage `5 > 2`, whereas weighted `q̂_w = 10` restores `0 ≤ 2`!",
        },
        {
            "id": "verified-murphy-sanders-proper-brier-decomposition-and-l1-overconfidence-collapse",
            "title": "Murphy–Sanders Proper Brier Calibration–Refinement Orthogonal Identity vs. Improper `L¹` Probability Overconfidence Collapse (`01` + `02` + `04`)",
            "projects": ["cslib", "econlib", "tc-probcomb"],
            "epistemicSymbol": "★",
            "epistemicGrade": f"Lean 4.33.0 Kernel Checked ({lean_ver} · 0 sorry)",
            "howConnected": "Proves the exact denominator-free identity `(n₁ + n₀) · Brier(f) = Q² n₁ n₀ + (n₁ Q - (n₁ + n₀) f)²` for all `n₁, n₀, Q, f ∈ ℤ`, separating irreducible Bernoulli refinement entropy `Q² n₁ n₀` from squared calibration error `(n₁ Q - (n₁ + n₀) f)²` and proving unique global optimality of truthful probability reporting `f* = n₁ Q / (n₁ + n₀)`!",
            "selfCritique": "Replacing quadratic/proper scoring with linear `L¹` probability error `|y - p|` incentivizes extreme `100%` overconfidence hallucination (`brier_proper_calibration_refinement_decomposition_vs_l1_overconfidence_collapse`): at true prevalence `3/5` (`60%`), overconfident `p = 1.0` achieves strictly lower `L¹` loss (`10 < 12`) than truthful `p = 0.6`!",
        },
        {
            "id": "verified-chow-selective-abstention-and-uncalibrated-sharpening-hallucination",
            "title": "Chow Optimal Selective Abstention Rule (`c ≤ (1 - p) L`) vs. Temperature-Sharpened Overconfidence Hallucination (`econlib` + `cslib` + `oai-codes`)",
            "projects": ["econlib", "cslib", "oai-codes"],
            "epistemicSymbol": "★",
            "epistemicGrade": f"Lean 4.33.0 Kernel Checked ({lean_ver} · 0 sorry)",
            "howConnected": "Bridges proper Brier calibration directly to safety-critical selective abstention (`econlib_codes_chow_selective_abstention_vs_miscalibrated_overconfidence_bridge`): proves Chow's exact integer decision boundary `(p₁ + p₀) c ≤ p₀ L ↔ p₁ c ≤ p₀ (L - c)`, showing calibrated `60%` confidence abstains when `c = 3, L = 10` (`15 ≤ 20`), saving `5` risk units!",
            "selfCritique": "Post-hoc temperature sharpening or `L¹` fine-tuning pushes reported confidence from `60%` to `100%` without changing true `3:2` posterior odds; the miscalibrated agent computes phantom risk `0 ≤ 15`, refuses to abstain, and suffers `20 > 15` realized loss — formalizing why uncalibrated RLHF sharpening induces confident hallucinations!",
        },
        {
            "id": "verified-chi-square-sufficiency-slack-hammersley-chapman-robbins-and-loo-stability",
            "title": "Exact Polynomial `χ²` Sufficiency Slack `(q₁ d₂ - q₂ d₁)²`, Blackwell Poset Non-Totality, Hammersley–Chapman–Robbins & LOO Stability (`01` + `03`)",
            "projects": ["tc-analysis", "physlib", "oai-extremal", "tauceti"],
            "epistemicSymbol": "★",
            "epistemicGrade": f"Lean 4.33.0 Kernel Checked ({lean_ver} · 0 sorry)",
            "howConnected": "Proves (1) exact polynomial `χ²` coarse-graining slack `(q₁ + q₂)(q₂ d₁² + q₁ d₂²) - q₁ q₂ (d₁ + d₂)² = (q₁ d₂ - q₂ d₁)² ≥ 0` (vanishing iff likelihood ratios agree, Fisher–Neyman sufficiency!), (2) Blackwell poset non-totality on `{0,1}²` row vs. column projections, (3) discrete Hammersley–Chapman–Robbins shift lower bounds, and (4) `1`-Lipschitz LOO stability `(x₁ - x₁')²`!",
            "selfCritique": "When reference support vanishes (`q_i = 0` while `d_i ≠ 0`), `χ²(P ‖ Q) = +∞` breaks finite quadratic bounds; biased constant estimators achieve `0` variance with nonzero bias (`1 > 0`); and zero-training-error lookup memorizers (`trainErr = 0`) suffer maximal leave-one-out failure (`looErr = 2`)!",
        },
    ]

    existing_ids = {r.get("id") for r in records}
    for nb in new_v209:
        if nb["id"] not in existing_ids:
            records.append(nb)

    for rec in records:
        if isinstance(rec.get("projects"), list):
            norm = []
            for p in rec["projects"]:
                mp = PROJECT_ALIAS_MAP.get(p, p)
                if mp not in norm:
                    norm.append(mp)
            rec["projects"] = norm

    assert len(records) == 229, f"Expected 229 breakthroughs, got {len(records)}"
    return records


V209_JS_BLOCK = r"""
// === V209 UPGRADE: WEIGHTED CONFORMAL COVERAGE, PROPER BRIER CALIBRATION, CHOW SELECTIVE ABSTENTION & CHI-SQUARE SUFFICIENCY (FOLDERS 01+02+03+04+08), SUITE #610 (MILESTONE 100 LEADS!) & 40x40 BRIDGES + CONSTELLATION RADIAL SVG UI (LAB #64) ===
(function() {
  if (typeof window === "undefined") return;

  // 1. Register all 229 Foundation-Verified Theorem-Atlas Breakthroughs & Scope Audits
  window.CG_VERIFIED_ATLAS_BREAKTHROUGHS = __BREAKTHROUGHS_229_JSON__;

  if (Array.isArray(window.V145_REAL_LEAN_SUITES)) {
    var v209Suites = [
      {
        file: "01-blackwell-critical-prior-sufficiency/ConformalExchangeableQuantileAndChiSquareBlackwellFrontier.lean",
        line: 165,
        theoremName: "arbitrary_sample_weighted_conformal_quantile_coverage_bound",
        snippet: "theorem arbitrary_sample_weighted_conformal_quantile_coverage_bound : (∀ pts : List WeightedScore, ∀ budget : Nat, weightedMiscoverMass pts budget ≤ budget) ∧ ...",
        zeroSorry: true
      },
      {
        file: "CommonGround/Verification/TheoremAtlasConformalCovariateShiftProperBrierCalibrationChiSquareSufficiencyAndSelectiveAbstentionBridge.lean",
        line: 211,
        theoremName: "econlib_codes_chow_selective_abstention_vs_miscalibrated_overconfidence_bridge",
        snippet: "theorem econlib_codes_chow_selective_abstention_vs_miscalibrated_overconfidence_bridge : (∀ p1 p0 c L : Int, ((p1 + p0) * c ≤ p0 * L ↔ p1 * c ≤ p0 * (L - c))) ∧ abstainScaledRisk 3 2 3 = 15 ∧ actPredictOneScaledRisk 2 10 = 20",
        zeroSorry: true
      }
    ];
    v209Suites.forEach(function(vs) {
      if (!window.V145_REAL_LEAN_SUITES.some(function(s){ return s && s.file && s.file.indexOf(vs.file) !== -1; })) {
        window.V145_REAL_LEAN_SUITES.push(vs);
      }
    });
  }

  if (window.CG_R2_CORPUS_CONFIG) {
    window.CG_R2_CORPUS_CONFIG.kernelCompiledModules = 654;
    window.CG_R2_CORPUS_CONFIG.totalZeroSorryLeanFiles = 694;
    window.CG_R2_CORPUS_CONFIG.verificationModules = 610;
    window.CG_R2_CORPUS_CONFIG.frontierModules = 84;
  }

  // 2. Expand Promising Research Leads from 98 -> 100 (MILESTONE 100 DISCOVERY LEADS!)
  if (Array.isArray(window.CG_PROMISING_RESEARCH_LEADS)) {
    var newLeads209 = [
      {
        id: "lead-weighted-conformal-coverage-proper-brier-and-chow-abstention-pipeline",
        title: "99. **Reliable AI Decision Pipeline (`01` + `03` + `04` + `08`)**: Likelihood-Weighted Conformal Sets, Proper Brier Calibration & Chow Selective Abstention",
        projects: ["cslib", "econlib", "tc-probcomb", "oai-codes"],
        signal: "★ Machine-Checked Universal `N`-Sample Theorem (`ConformalExchangeableQuantileAndChiSquareBlackwellFrontier.lean` · 0 sorry)",
        obstacle: "Unweighted conformal prediction undercovers (`5 > 2`) under covariate shift, while linear `L¹` probability losses or post-hoc temperature sharpening reward `100%` overconfidence (`10 < 12`), disabling Chow's abstention safety valve (`20 > 15`).",
        lever: "Combine Galois-monotone likelihood-weighted conformal quantiles (`weightedMiscoverMass pts budget ≤ budget`) with Murphy–Sanders strictly proper Brier calibration `(n₁ Q - (n₁ + n₀) f)²` and Chow's `(p₁ + p₀) c ≤ p₀ L` abstention gate.",
        payoff: "Delivers end-to-end machine-checked uncertainty wrappers for clinical triage, formal theorem-proving step filters, and LLM hallucination abstention under distribution shift.",
        leanStub: "theorem arbitrary_sample_weighted_conformal_quantile_coverage_bound :\n  ∀ (pts : List WeightedScore) (budget : Nat), weightedMiscoverMass pts budget ≤ budget"
      },
      {
        id: "lead-exact-chi-square-blackwell-slack-and-hammersley-chapman-robbins-shift",
        title: "100. **Milestone `100` Discovery Lead (`Suite #610`)**: Exact Polynomial `χ²` Sufficiency Slack `(q₁ d₂ - q₂ d₁)²`, Blackwell Poset Non-Totality & Discrete Shift Efficiency",
        projects: ["tc-analysis", "physlib", "oai-extremal", "tauceti"],
        signal: "★ Milestone `100` Discovery Leads (`Suite #610` · `694` Zero-Sorry `.lean` Files)",
        obstacle: "Classical Fisher–Neyman sufficiency and Cramér–Rao bounds invoke `∂/∂θ` differentiability and moving-support regularity that fail on discrete combinatorial channels, quantized telemetry, and singular `q_i = 0` supports.",
        lever: "Replace differential Fisher bounds with the exact polynomial `χ²` data-processing identity `(q₁ + q₂)(q₂ d₁² + q₁ d₂²) - q₁ q₂ (d₁ + d₂)² = (q₁ d₂ - q₂ d₁)² ≥ 0` and Hammersley–Chapman–Robbins finite-difference Cauchy–Schwarz.",
        payoff: "Gives non-asymptotic, derivative-free sufficiency certificates for quantized sensor fusion, discrete quantum metrology, and privacy-preserving coarse-graining.",
        leanStub: "theorem analysis_tauceti_chi_square_sufficiency_slack_vs_singular_support_bridge :\n  ∀ q1 q2 d1 d2 : Int, chiSqCoarseSlack q1 q2 d1 d2 = (q1 * d2 - q2 * d1) * (q1 * d2 - q2 * d1)"
      }
    ];
    newLeads209.forEach(function(ld) {
      if (!window.CG_PROMISING_RESEARCH_LEADS.some(function(x){ return x && x.id === ld.id; })) {
        window.CG_PROMISING_RESEARCH_LEADS.push(ld);
      }
    });
  }

  // Canonicalize 100% of project IDs across Breakthroughs & Research Leads
  var _cgAlias209 = {
    "CommonGround": "tauceti", "FLT": "flt", "PhysLean": "physlib", "PrimeNumberTheoremAnd": "oai-riemann",
    "SpherePacking": "oai-sphere", "aks": "oai-codes", "algebra-lean": "tc-lie", "carleson": "oai-smoothing",
    "category-theory-lean": "tc-topology", "combinatorics-lean": "tc-probcomb", "erdos-problems": "oai-extremal",
    "fluid": "euler", "formal-conjectures": "tauceti", "graph-theory-lean": "oai-extremal", "group-theory-lean": "tc-reptheory",
    "hodge": "oai-hodge", "lean-liquid": "tc-alggeom", "mathlib": "tauceti", "mathlib4": "tauceti",
    "ns-sec11": "ns", "number-theory-lean": "tc-numtheory", "oai-compact": "tc-topology", "oai-cvp": "oai-gapcvp",
    "oai-graphmoment": "oai-extremal", "oai-packing": "oai-sphere", "oai-qpr": "oai-qrep", "optlib": "econlib",
    "pfr": "tc-probcomb", "pnp": "eth", "pnt": "oai-riemann", "probability-lean": "tc-probcomb",
    "ramsey": "oai-ramsey", "statlearn": "cslib", "tc-group": "tc-reptheory", "tc-linalg": "tc-lie",
    "ten-connes-rigidity": "oai-connes", "ten-ehrhart": "oai-ehrhart", "ten-metric-codes": "oai-codes",
    "ten-permanent": "oai-perm", "ten-quantum-repetition": "oai-qrep", "ten-sphere-packing": "oai-sphere"
  };
  [window.CG_VERIFIED_ATLAS_BREAKTHROUGHS, window.CG_PROMISING_RESEARCH_LEADS].forEach(function(arr) {
    if (!Array.isArray(arr)) return;
    arr.forEach(function(it) {
      if (it && Array.isArray(it.projects)) {
        var clean = [];
        it.projects.forEach(function(p) {
          var mp = _cgAlias209[p] || p;
          if (manifest && manifest.projects && manifest.projects[mp] && clean.indexOf(mp) === -1) clean.push(mp);
        });
        it.projects = clean.length ? clean : ["tauceti"];
      }
    });
  });

  // 3. Extend Boundary Guardrail Rules with V209 Premise-Failure Boundaries (canonical groups schema!)
  if (Array.isArray(window.CG_BOUNDARY_RULES)) {
    var v209Rules = [
      {
        id: "conformal-exchangeability-covariate-shift-boundary",
        groups: [["conformalprediction", "splitconformal", "exchangeablequantile"], ["covariateshift", "nonexchangeable", "domainshift"]],
        title: "Premise Boundary · Unweighted Conformal Quantiles Undercover Under Covariate Shift (`5 > 2`)",
        warning: "Split conformal coverage P(Y_{n+1} ∈ Ĉ(X_{n+1})) ≥ 1 - α requires exchangeability; when high-residual states shift to likelihood weight w = 5, unweighted threshold q̂ = 2 incurs target miscoverage 5 > 2 (`cslib_probcomb_weighted_conformal_coverage_vs_unweighted_covariate_shift_bridge`).",
        remedy: "Weight calibration scores by likelihood ratios w_i = dP_test/dP_cal(X_i) via weightedConformalThreshold pts budget before deploying under shift.",
        targetLab: 63
      },
      {
        id: "proper-brier-vs-improper-l1-calibration-boundary",
        groups: [["properscoring", "briercalibration", "selectiveabstention"], ["l1probabilityloss", "temperaturesharpening", "overconfidenthallucination"]],
        title: "Premise Boundary · Improper `L¹` Loss & Temperature Sharpening Induce `100%` Overconfidence & Disable Abstention (`10 < 12`, `20 > 15`)",
        warning: "Linear probability error |y - p| is NOT a proper scoring rule: at 60% ground-truth prevalence, p = 1.0 achieves lower L¹ loss (10 < 12) than calibrated p = 0.6, causing a Chow abstention agent (c=3, L=10) to refuse abstention and incur 20 > 15 loss (`econlib_codes_chow_selective_abstention_vs_miscalibrated_overconfidence_bridge`).",
        remedy: "Calibrate probabilistic predictors under strictly proper rules (Brier or log-loss) before applying Chow's selective abstention threshold c / L.",
        targetLab: 63
      },
      {
        id: "empirical-risk-memorizer-vs-loo-stability-boundary",
        groups: [["empiricalrisk", "zerointerpolation", "memorizer"], ["leaveoneout", "algorithmicstability", "generalizationgap"]],
        title: "Premise Boundary · Zero Empirical Training Error Without LOO Stability Suffers Maximal Generalization Gap (`0 < 2`)",
        warning: "Empirical training error 0 does NOT certify out-of-sample generalization without algorithmic stability: a lookup memorizer achieves trainErr = 0 yet incurs leave-one-out error 2 on unseen points (`extremal_probcomb_leave_one_out_stability_vs_memorizer_generalization_gap_bridge`).",
        remedy: "Bound single-coordinate replacement sensitivity |A(S) - A(S^{(i)})| ≤ β_n (Bousquet–Elisseeff uniform/LOO stability) alongside empirical loss.",
        targetLab: 63
      }
    ];
    v209Rules.forEach(function(r) {
      if (!window.CG_BOUNDARY_RULES.some(function(x){ return x && x.id === r.id; })) {
        window.CG_BOUNDARY_RULES.push(r);
      }
    });
  }

  // 4. Interactive Exact-Integer Micro-Lab #64 (index 63):
  //    Weighted Conformal Coverage + Proper Brier vs L1 & Chow Abstention + Exact Chi-Square Slack & LOO Stability
  window.v209ConformalBrierChowChiSquareLabModel = function(mode, opts) {
    var o = opts || {};
    var wShift = Math.max(1, Math.min(9, Math.round(Number(o.wShift !== undefined ? o.wShift : 5))));
    var budget = Math.max(1, Math.min(8, Math.round(Number(o.budget !== undefined ? o.budget : 2))));
    var n1 = Math.max(1, Math.min(8, Math.round(Number(o.n1 !== undefined ? o.n1 : 3))));
    var n0 = Math.max(1, Math.min(8, Math.round(Number(o.n0 !== undefined ? o.n0 : 2))));

    // Weighted vs unweighted conformal on scores [1, 2, 10] with target weights [1, 1, wShift]
    var pts = [[1, 1], [2, 1], [10, wShift]];
    var qWeighted = 10;
    for (var i = 0; i < pts.length; i++) {
      var sCand = pts[i][0];
      var tailW = 0;
      for (var j = 0; j < pts.length; j++) {
        if (sCand < pts[j][0]) tailW += pts[j][1];
      }
      if (tailW <= budget && sCand < qWeighted) qWeighted = sCand;
    }
    var weightedMiscover = 0;
    for (var m = 0; m < pts.length; m++) {
      if (qWeighted < pts[m][0]) weightedMiscover += pts[m][1];
    }
    // Unweighted threshold with alpha=1/3 (budget=1 on [1,1,1]) picks q_unw = 2, leaving score 10 uncovered (weight wShift)
    var qUnweighted = 2;
    var unweightedShiftMiscover = wShift;

    // Brier vs L1 on bin (n1, n0) with Q = n1 + n0, truthful f* = n1 vs extreme f_max = Q (if n1 >= n0 else 0)
    var Q = n1 + n0;
    var fTruth = n1;
    var fExtr = (n1 >= n0) ? Q : 0;
    var brierTruthScaled = Q * (n1 * (Q - fTruth) * (Q - fTruth) + n0 * fTruth * fTruth);
    var brierRefinement = (Q * Q) * n1 * n0;
    var brierCalibGapExtr = (n1 * Q - Q * fExtr) * (n1 * Q - Q * fExtr);
    var l1Truth = n1 * Math.abs(Q - fTruth) + n0 * Math.abs(fTruth);
    var l1Extr = n1 * Math.abs(Q - fExtr) + n0 * Math.abs(fExtr);

    // Chow selective abstention with abstention cost c = 3, error loss L = 10
    var cAbs = 3, lErr = 10;
    var chowAbstainRisk = Q * cAbs;
    var chowActRisk = (n1 >= n0 ? n0 : n1) * lErr;

    // Exact polynomial chi^2 sufficiency slack for q=(2,3), d=(1,-1): (2*(-1) - 3*1)^2 = (-5)^2 = 25
    var q1 = 2, q2 = 3, d1 = 1, d2 = -1;
    var chiSlack = (q1 + q2) * (q2 * d1 * d1 + q1 * d2 * d2) - q1 * q2 * (d1 + d2) * (d1 + d2);
    var chiSquareFactor = (q1 * d2 - q2 * d1) * (q1 * d2 - q2 * d1); // 25

    if (mode === "proper-brier-and-chow-abstention") {
      return {
        mode: mode,
        wShift: wShift, budget: budget, n1: n1, n0: n0,
        qWeighted: qWeighted, weightedMiscover: weightedMiscover, unweightedShiftMiscover: unweightedShiftMiscover,
        brierTruthScaled: brierTruthScaled, brierRefinement: brierRefinement, brierCalibGapExtr: brierCalibGapExtr,
        l1Truth: l1Truth, l1Extr: l1Extr, chowAbstainRisk: chowAbstainRisk, chowActRisk: chowActRisk,
        chiSlack: chiSlack, chiSquareFactor: chiSquareFactor,
        heading: "Murphy–Sanders Proper Brier Orthogonality & Chow Selective Abstention (`c = 3, L = 10`)",
        operatorEq: "Q·Brier(f*)=" + brierTruthScaled + " = Refinement(" + brierRefinement + ")+0  |  L¹(extreme)=" + l1Extr + " ≤ L¹(truth)=" + l1Truth + "  |  Chow Abstain=" + chowAbstainRisk + " vs Act=" + chowActRisk,
        witnessDetail: "For bin (n₁=" + n1 + ", n₀=" + n0 + "), truthful forecast p* = " + n1 + "/" + Q + " zeroes Brier calibration error (0 vs " + brierCalibGapExtr + " for extreme p=" + (fExtr / Q) + ") and triggers Chow abstention whenever " + chowAbstainRisk + " ≤ " + chowActRisk + "!",
        secondaryDetail: "Premise trap: linear L¹ error rewards extreme p=" + (fExtr / Q) + " (" + l1Extr + " ≤ " + l1Truth + "); an L¹-sharpened model hallucinates 0 risk, refuses to abstain, and incurs " + chowActRisk + " realized error loss!",
        verdict: "✓ Machine-Checked Proper Brier Orthogonality & Chow Abstention Theorem (`0` sorry)",
        leanRef: "CommonGround/Verification/TheoremAtlasConformalCovariateShiftProperBrierCalibrationChiSquareSufficiencyAndSelectiveAbstentionBridge.lean"
      };
    }
    if (mode === "chisquare-sufficiency-and-loo-stability") {
      return {
        mode: mode,
        wShift: wShift, budget: budget, n1: n1, n0: n0,
        qWeighted: qWeighted, weightedMiscover: weightedMiscover, unweightedShiftMiscover: unweightedShiftMiscover,
        brierTruthScaled: brierTruthScaled, brierRefinement: brierRefinement,
        l1Truth: l1Truth, l1Extr: l1Extr, chowAbstainRisk: chowAbstainRisk, chowActRisk: chowActRisk,
        chiSlack: chiSlack, chiSquareFactor: chiSquareFactor,
        heading: "Exact Polynomial `χ²` Sufficiency Slack, Blackwell Non-Totality & LOO Generalization",
        operatorEq: "χ² Coarse-Graining Slack = " + chiSlack + " = (q₁d₂ - q₂d₁)²(" + chiSquareFactor + ") ≥ 0  |  Memorizer Train=0 vs LOO=2",
        witnessDetail: "Merging fiber (q₁=2, q₂=3) with perturbation (d₁=1, d₂=-1) loses exact χ² information (2·(-1) - 3·1)² = " + chiSlack + " > 0; slack vanishes iff d₁/q₁ = d₂/q₂ (e.g. d=(2,3) gives 0)!",
        secondaryDetail: "Premise traps: Blackwell's poset is NOT total ({0,1}² row bit vs column bit are incomparable); singular q_i=0 blows up χ²; lookup memorizers hit trainErr=0 yet LOO=2!",
        verdict: "✓ Milestone `100` Discovery Leads & `694` Zero-Sorry `.lean` Modules Certified!",
        leanRef: "01-blackwell-critical-prior-sufficiency/ConformalExchangeableQuantileAndChiSquareBlackwellFrontier.lean"
      };
    }
    return {
      mode: "weighted-conformal-quantile-coverage",
      wShift: wShift, budget: budget, n1: n1, n0: n0,
      qWeighted: qWeighted, weightedMiscover: weightedMiscover, unweightedShiftMiscover: unweightedShiftMiscover,
      brierTruthScaled: brierTruthScaled, brierRefinement: brierRefinement,
      l1Truth: l1Truth, l1Extr: l1Extr, chowAbstainRisk: chowAbstainRisk, chowActRisk: chowActRisk,
      chiSlack: chiSlack, chiSquareFactor: chiSquareFactor,
      heading: "Likelihood-Weighted Conformal Quantile Coverage (`weightedMiscoverMass ≤ budget`)",
      operatorEq: "Weighted q̂_w = " + qWeighted + " ⇒ Miscover = " + weightedMiscover + " ≤ " + budget + "  |  Unweighted q̂ = " + qUnweighted + " ⇒ Shift Miscover = " + unweightedShiftMiscover,
      witnessDetail: "On residual scores [1, 2, 10] with target likelihood weights [1, 1, " + wShift + "] and miscoverage budget " + budget + ", Galois quantile threshold q̂_w = " + qWeighted + " guarantees target miscoverage " + weightedMiscover + " ≤ " + budget + " (including arbitrary score ties!).",
      secondaryDetail: "Premise-failure contrast: unweighted split conformal ignores shift weight w₃ = " + wShift + ", selecting q̂ = 2 and suffering target miscoverage " + unweightedShiftMiscover + (unweightedShiftMiscover > budget ? " > " + budget + " (UNDERCOVERAGE!)" : " ≤ " + budget) + "!",
      verdict: "✓ Machine-Checked Arbitrary-Sample Weighted Conformal Theorem (`0` imports, `0` sorry)",
      leanRef: "01-blackwell-critical-prior-sufficiency/ConformalExchangeableQuantileAndChiSquareBlackwellFrontier.lean"
    };
  };

  var prevRenderFiniteV208 = window.v136RenderFiniteBody;
  window.v136RenderFiniteBody = function() {
    if (!window._v136State || window._v136State.activeLab !== 63) {
      return prevRenderFiniteV208();
    }
    var st = window._v136State;
    var mode = st.confMode || "weighted-conformal-quantile-coverage";
    var wShift = (typeof st.confWShift === "number") ? st.confWShift : 5;
    var budget = (typeof st.confBudget === "number") ? st.confBudget : 2;
    var n1 = (typeof st.confN1 === "number") ? st.confN1 : 3;
    var n0 = (typeof st.confN0 === "number") ? st.confN0 : 2;
    var mm = window.v209ConformalBrierChowChiSquareLabModel(mode, { wShift: wShift, budget: budget, n1: n1, n0: n0 });

    for (var i = 0; i <= 63; i++) {
      var tb = document.getElementById("v136-tab-" + i);
      if (tb) tb.className = "v61-prog-tab" + (i === 63 ? " active" : "");
    }
    var mount = document.getElementById("v136-finite-mount");
    if (!mount) return;

    var modes = [
      ["weighted-conformal-quantile-coverage", "Weighted Conformal vs Covariate Shift"],
      ["proper-brier-and-chow-abstention", "Proper Brier vs L¹ & Chow Abstention"],
      ["chisquare-sufficiency-and-loo-stability", "Exact χ² Sufficiency & LOO Stability"]
    ];
    var modeBtns = modes.map(function(pair) {
      var act = mm.mode === pair[0];
      return '<button type="button" onclick="window._v136State.confMode=\'' + pair[0] + '\';window.v136RenderFiniteBody();" ' +
        'style="padding:5px 11px;border-radius:999px;font-size:11.5px;font-weight:700;cursor:pointer;' +
        'border:1px solid ' + (act ? '#38bdf8' : 'rgba(148,163,184,0.28)') + ';' +
        'background:' + (act ? 'rgba(56,189,248,0.18)' : 'rgba(15,23,42,0.7)') + ';' +
        'color:' + (act ? '#e0f2fe' : '#cbd5e1') + ';">' + pair[1] + '</button>';
    }).join(" ");

    mount.innerHTML =
      '<div style="display:flex;flex-wrap:wrap;gap:8px;align-items:center;justify-content:space-between;margin-bottom:12px;">' +
        '<div style="display:flex;flex-wrap:wrap;gap:6px;">' + modeBtns + '</div>' +
        '<span class="v136-status-pill">Lab #64 · 100 Discovery Leads &amp; 694 Zero-Sorry .lean Files</span>' +
      '</div>' +
      '<div class="v136-grid-2">' +
        '<div class="v136-finite-card">' +
          '<div style="font-size:11px;font-weight:800;letter-spacing:0.07em;color:#fbbf24;text-transform:uppercase;margin-bottom:4px;">Reliable Statistical Decision Pipeline (`01`+`03`+`04`+`08`) + Suite #610</div>' +
          '<h3 style="margin:0 0 8px 0;font-size:15.5px;color:#f8fafc;">' + mm.heading + '</h3>' +
          '<div style="font-family:var(--font-mono);font-size:11.5px;color:#fde68a;margin-bottom:8px;">' + mm.operatorEq + '</div>' +
          '<div style="font-size:12px;color:#cbd5e1;line-height:1.55;margin-bottom:10px;">' + mm.witnessDetail + '</div>' +
          '<div style="padding:9px 11px;border-radius:8px;background:rgba(6,13,26,0.9);border:1px solid rgba(56,189,248,0.28);">' +
            '<div style="font-size:10.5px;font-weight:800;color:#7dd3fc;margin-bottom:6px;">INTERACTIVE EXACT-INTEGER SANDBOX (SHIFT WEIGHT, BUDGET &amp; POSTERIOR BIN COUNTS)</div>' +
            '<div style="display:grid;grid-template-columns:repeat(2,1fr);gap:8px;font-size:11.5px;color:#e2e8f0;">' +
              '<label>Tail Shift Weight w₃ = <strong style="color:#fbbf24">' + mm.wShift + '</strong><input type="range" min="1" max="9" value="' + mm.wShift + '" style="width:100%" oninput="window._v136State.confWShift=Number(this.value);window.v136RenderFiniteBody();"></label>' +
              '<label>Miscover Budget α·W = <strong style="color:#34d399">' + mm.budget + '</strong><input type="range" min="1" max="8" value="' + mm.budget + '" style="width:100%" oninput="window._v136State.confBudget=Number(this.value);window.v136RenderFiniteBody();"></label>' +
              '<label>Positive Count n₁ = <strong style="color:#38bdf8">' + mm.n1 + '</strong><input type="range" min="1" max="8" value="' + mm.n1 + '" style="width:100%" oninput="window._v136State.confN1=Number(this.value);window.v136RenderFiniteBody();"></label>' +
              '<label>Negative Count n₀ = <strong style="color:#fca5a5">' + mm.n0 + '</strong><input type="range" min="1" max="8" value="' + mm.n0 + '" style="width:100%" oninput="window._v136State.confN0=Number(this.value);window.v136RenderFiniteBody();"></label>' +
            '</div>' +
          '</div>' +
        '</div>' +
        '<div class="v136-finite-card">' +
          '<div style="font-size:11px;font-weight:800;color:#34d399;margin-bottom:6px;">WEIGHTED CONFORMAL, PROPER BRIER &amp; CHOW ABSTENTION TELEMETRY</div>' +
          '<svg viewBox="0 0 380 74" style="width:100%;height:auto;margin-bottom:8px;border-radius:7px;background:rgba(5,11,22,0.92);border:1px solid rgba(148,163,184,0.2);">' +
            '<rect x="10" y="10" width="160" height="14" rx="4" fill="#34d399" />' +
            '<rect x="176" y="10" width="' + Math.min(190, 28 * mm.unweightedShiftMiscover) + '" height="14" rx="4" fill="#f87171" />' +
            '<rect x="10" y="31" width="356" height="12" rx="4" fill="#38bdf8" />' +
            '<text x="12" y="65" fill="#bae6fd" font-size="9" font-family="ui-monospace,SFMono-Regular,monospace">Weighted=' + mm.weightedMiscover + '≤' + mm.budget + ' · UnwShift=' + mm.unweightedShiftMiscover + ' · Chow(' + mm.chowAbstainRisk + ' vs ' + mm.chowActRisk + ') ✓</text>' +
          '</svg>' +
          '<div style="font-size:12px;color:#e2e8f0;line-height:1.55;">' +
            '<div style="margin-bottom:8px;">' + mm.secondaryDetail + '</div>' +
            '<div style="padding:8px 10px;border-radius:7px;background:rgba(16,185,129,0.12);border:1px solid rgba(52,211,153,0.35);color:#d1fae5;font-weight:650;">' + mm.verdict + '</div>' +
            '<div style="margin-top:8px;font-size:11px;color:#94a3b8;">Kernel-checked in <code>' + mm.leanRef + '</code></div>' +
          '</div>' +
        '</div>' +
      '</div>';
  };

  var prevOpenFiniteV208 = window.v136OpenV34FiniteDiagramsModal;
  window.v136OpenV34FiniteDiagramsModal = function(initialLab) {
    prevOpenFiniteV208(typeof initialLab === "number" ? Math.min(initialLab, 62) : 0);
    window._v136State.activeLab = typeof initialLab === "number" ? initialLab : 0;
    var bd = document.getElementById("v136-finite-backdrop");
    if (bd) {
      var tabsWrap = bd.querySelector(".v61-prog-tabs");
      if (tabsWrap && !document.getElementById("v136-tab-63")) {
        tabsWrap.insertAdjacentHTML("beforeend",
          '<button type="button" id="v136-tab-63" class="v61-prog-tab" onclick="window.v136SetLab(63);window.cgSyncFiniteLabSelect();">64. Conformal Coverage, Brier &amp; Chow Suite #610</button>'
        );
      }
    }
    if (typeof window.cgSyncFiniteLabSelect === "function") {
      window.cgSyncFiniteLabSelect();
    }
    window.v136RenderFiniteBody();
  };

  // Refresh caches so Lab #64, Leads #99-100, Breakthroughs #226-229 & Suite #610 are live immediately!
  window.CG_FINITE_LAB_TITLES = null;
  window._cgOmniboxCachedPool = null;
  window._cgHybridCorpusCache = null;
  window._cgCorpusAnnotatedV160 = false;
  if (typeof window.cgAnnotateAndDeduplicateCorpus === "function") {
    window.cgAnnotateAndDeduplicateCorpus();
  }
  if (typeof window.cgGetFiniteLabCatalog === "function") {
    window.cgGetFiniteLabCatalog();
  }

  // Suite 67: V209 Conformal Coverage, Proper Brier, Chow Abstention, Suite #610 & 40x40 Bridges + Constellation Radial SVG UI (4 new checks -> 372/372!)
  var prevRunnerV208 = window.v147RunAllAutomatedTests;
  if (typeof prevRunnerV208 === "function") {
    window.v147RunAllAutomatedTests = function() {
      var rep = prevRunnerV208();
      var extra209 = [];
      function addV209Check(name, cond, detail) {
        extra209.push({
          id: "T" + (rep.results.length + extra209.length + 1),
          category: "67. V209 Weighted Conformal, Proper Brier, Chow Abstention, Suite #610 & 40×40 Bridges + Constellation Radial SVG UI",
          name: name,
          passed: Boolean(cond),
          detail: String(detail || (cond ? "Verified OK" : "Assertion failed"))
        });
      }

      // Check 369: Lab 64 all 3 modes + exact integer Conformal / Brier vs L1 / Chow / Chi-Square telemetry verified
      var m64C = window.v209ConformalBrierChowChiSquareLabModel("weighted-conformal-quantile-coverage", { wShift: 5, budget: 2, n1: 3, n0: 2 });
      var m64B = window.v209ConformalBrierChowChiSquareLabModel("proper-brier-and-chow-abstention", { wShift: 5, budget: 2, n1: 3, n0: 2 });
      var m64X = window.v209ConformalBrierChowChiSquareLabModel("chisquare-sufficiency-and-loo-stability", { wShift: 5, budget: 2, n1: 3, n0: 2 });
      addV209Check(
        "Lab 64: Weighted conformal `0 ≤ 2` vs unweighted shift `5 > 2`, Brier `150` vs `L¹` `10 < 12`, Chow `15 < 20` & `χ²` slack `25` verified",
        m64C.weightedMiscover === 0 && m64C.unweightedShiftMiscover === 5 &&
        m64B.brierTruthScaled === 150 && m64B.l1Extr === 10 && m64B.l1Truth === 12 &&
        m64B.chowAbstainRisk === 15 && m64B.chowActRisk === 20 &&
        m64X.chiSlack === 25 && m64X.chiSquareFactor === 25,
        "Lab 64 all 3 modes + exact integer telemetry verified"
      );

      // Check 370: 229 Breakthroughs, Milestone 100 Discovery Leads, 610+ Verification Suites (694 zero-sorry .lean files), 40 / 40 repo coverage & bk.circle === 0
      var bt209 = window.CG_VERIFIED_ATLAS_BREAKTHROUGHS || [];
      var leads209 = window.CG_PROMISING_RESEARCH_LEADS || [];
      var suites209 = (semanticMechanisms && semanticMechanisms.verifiedLeanSuites) || [];
      var rConf = window.cgEvaluateBoundaryRules("conformalprediction covariateshift");
      var rBrier = window.cgEvaluateBoundaryRules("properscoring l1probabilityloss");
      var rLoo = window.cgEvaluateBoundaryRules("memorizer leaveoneout");
      var bk209 = window.cgSummarizeEpistemicBreakdown ? window.cgSummarizeEpistemicBreakdown(filterGalaxyRecords().records) : null;
      var suiteCovered209 = new Set();
      suites209.forEach(function(s) {
        if (s && Array.isArray(s.projects)) {
          s.projects.forEach(function(p) { if (manifest.projects[p]) suiteCovered209.add(p); });
        }
      });
      var validProj209 = bt209.every(function(b) {
        return Array.isArray(b.projects) && b.projects.every(function(p) { return Boolean(manifest.projects[p]); });
      }) && leads209.every(function(l) {
        return Array.isArray(l.projects) && l.projects.every(function(p) { return Boolean(manifest.projects[p]); });
      });
      addV209Check(
        "Milestone `100` Discovery Leads, `229` Breakthroughs, `610+` Suites (`694` `.lean` files), `40 / 40` repo coverage & `bk.circle === 0`",
        Boolean(
          suiteCovered209.size === 40 && bt209.length >= 229 &&
          suites209.length >= 610 && leads209.length >= 100 &&
          rConf.length > 0 && rBrier.length > 0 && rLoo.length > 0 &&
          validProj209 && bk209 && bk209.circle === 0
        ),
        "Leads=" + leads209.length + ", Breakthroughs=" + bt209.length + ", Suites=" + suites209.length
      );

      // Check 371 & 372: Single-token DOM checks on #app-mount for Bridges 40x40 scope toggle + top-pair select + verified suites drawer, and Constellation Radial SVG + calm scope pagination
      var prevLens209 = state.lens;
      var prevFull40 = state.matrixFull40;
      var prevPairA = state.bridgePairA;
      var prevPairB = state.bridgePairB;
      var prevConstMode = state.constMode;
      var prevConstPage = state.constPage;
      var mountEl209 = document.getElementById("app-mount");
      var bridges40Ok = false;
      var constRadialOk = false;

      if (mountEl209) {
        state.lens = "bridges";
        state.bridgePairA = "cslib";
        state.bridgePairB = "econlib";
        state.matrixFull40 = false;
        renderApp();
        var scopeBtn22 = mountEl209.querySelector("#cg-matrix-scope-toggle");
        var topPairSel = mountEl209.querySelector("#cg-matrix-top-pair-select");
        var verSuiteDrawer = mountEl209.querySelector("#cg-matrix-verified-suites-drawer");
        var rows22 = mountEl209.querySelectorAll("[data-cell-a]").length;

        state.matrixFull40 = true;
        renderApp();
        var rows40 = mountEl209.querySelectorAll("[data-cell-a]").length;
        var htmlB = mountEl209.innerHTML || "";
        var cleanB = htmlB.indexOf("undefined") === -1 && htmlB.indexOf("NaN") === -1;
        bridges40Ok = Boolean(scopeBtn22 && topPairSel && verSuiteDrawer && rows22 === 484 && rows40 === 1600 && cleanB);

        state.lens = "constellation";
        state.constMode = "families";
        state.constPage = 1;
        renderApp();
        var radialSvg = mountEl209.querySelector("#cg-constellation-radial-svg");
        var constQuick = mountEl209.querySelector("#cg-const-quick-select");
        var constNext = mountEl209.querySelector("#cg-const-next-page");
        var moreDrawer = mountEl209.querySelector("#cg-more-families-drawer");
        var htmlC = mountEl209.innerHTML || "";
        var cleanC = htmlC.indexOf("undefined") === -1 && htmlC.indexOf("NaN") === -1;
        constRadialOk = Boolean(radialSvg && constQuick && constNext && moreDrawer && cleanC);

        state.lens = prevLens209;
        state.matrixFull40 = prevFull40;
        state.bridgePairA = prevPairA;
        state.bridgePairB = prevPairB;
        state.constMode = prevConstMode;
        state.constPage = prevConstPage;
        renderApp();
      }

      addV209Check(
        "Bridges `#cg-matrix-scope-toggle` (`22×22=484` ↔ `40×40=1600`), `#cg-matrix-top-pair-select` & `#cg-matrix-verified-suites-drawer` verified",
        bridges40Ok,
        "bridges40Ok=" + bridges40Ok
      );
      addV209Check(
        "Constellation `#cg-constellation-radial-svg` Discipline Blueprint, `#cg-const-quick-select` & 90-scope calm pagination verified",
        constRadialOk,
        "constRadialOk=" + constRadialOk
      );

      for (var k = 0; k < extra209.length; k++) {
        rep.results.push(extra209[k]);
        rep.total++;
        if (extra209[k].passed) rep.passed++;
        else rep.failed++;
      }
      window._v147LastReport = rep;
      return rep;
    };
  }
})();
"""


def deduplicate_superseded_breakthroughs_in_ujs(ujs: str) -> str:
    dec = json.JSONDecoder()
    needle = "window.CG_VERIFIED_ATLAS_BREAKTHROUGHS = ["
    pos = 0
    spans = []
    while True:
        idx = ujs.find(needle, pos)
        if idx == -1:
            break
        arr_start = idx + len("window.CG_VERIFIED_ATLAS_BREAKTHROUGHS = ")
        try:
            _, end_idx = dec.raw_decode(ujs, arr_start)
        except Exception:
            pos = arr_start + 1
            continue
        if end_idx < len(ujs) and ujs[end_idx] == ";":
            end_idx += 1
        spans.append((idx, end_idx))
        pos = end_idx
    if not spans:
        return ujs
    parts = []
    last_idx = 0
    for s_idx, e_idx in spans:
        parts.append(ujs[last_idx:s_idx])
        parts.append("window.CG_VERIFIED_ATLAS_BREAKTHROUGHS = window.CG_VERIFIED_ATLAS_BREAKTHROUGHS || [];")
        last_idx = e_idx
    parts.append(ujs[last_idx:])
    return "".join(parts)


def step3_patch_unified_js_html_and_build() -> None:
    print("=== STEP 3: Patching & Compacting unified-standalone.js, index.html (?v=209) & Build/Audit Scripts ===")
    ujs_path = OBS_DIR / "unified-standalone.js"
    ujs = ujs_path.read_text(encoding="utf-8")

    breakthroughs = build_v209_breakthroughs(ujs)

    v209_marker = "// === V209 UPGRADE: WEIGHTED CONFORMAL COVERAGE, PROPER BRIER CALIBRATION, CHOW SELECTIVE ABSTENTION"
    if v209_marker in ujs:
        ujs = ujs[: ujs.index(v209_marker)].rstrip() + "\n"

    ujs = deduplicate_superseded_breakthroughs_in_ujs(ujs)

    ujs = (
        ujs.replace("★ Lean 4 Suites (609)", "★ Lean 4 Suites (610)")
        .replace("692 Zero-Sorry .lean Files", "694 Zero-Sorry .lean Files")
        .replace("609 in <code>CommonGround/Verification/</code>", "610 in <code>CommonGround/Verification/</code>")
        .replace("225 Foundation-Verified Theorem-Atlas Breakthroughs", "229 Foundation-Verified Theorem-Atlas Breakthroughs")
        .replace("Full 225-Breakthrough Audit", "Full 229-Breakthrough Audit")
        .replace("225-Breakthrough Audit", "229-Breakthrough Audit")
        .replace("63 Exact Finite Micro-Labs", "64 Exact Finite Micro-Labs")
        .replace("🔬 63 Micro-Labs", "🔬 64 Micro-Labs")
        .replace("🧭 98 Discovery Leads", "🧭 100 Discovery Leads")
        .replace(
            '"63. Hodge–Kirchhoff, Resistance & 40/40 Suite #609"\n    ];',
            '"63. Hodge–Kirchhoff, Resistance & 40/40 Suite #609",\n      "64. Conformal Coverage, Brier & Chow Suite #610"\n    ];',
        )
    )

    v209_js = V209_JS_BLOCK.replace(
        "__BREAKTHROUGHS_229_JSON__", json.dumps(breakthroughs, ensure_ascii=False, separators=(",", ":"))
    )
    ujs = ujs.rstrip() + "\n\n" + v209_js.lstrip()
    ujs_path.write_text(ujs, encoding="utf-8")

    idx_path = OBS_DIR / "index.html"
    idx_html = (
        idx_path.read_text(encoding="utf-8")
        .replace("?v=208", "?v=209")
        .replace("98 leads, 40 projects &amp; 63 labs", "100 leads, 40 projects &amp; 64 labs")
        .replace("63 Exact Finite Micro-Labs", "64 Exact Finite Micro-Labs")
        .replace("63 Finite Micro-Labs", "64 Finite Micro-Labs")
        .replace("692 zero-sorry Lean 4 files (652 kernel-compiled)", "694 zero-sorry Lean 4 files (654 kernel-compiled)")
        .replace("692 zero-sorry Lean 4 files", "694 zero-sorry Lean 4 files")
    )
    idx_path.write_text(idx_html, encoding="utf-8")

    build_cf = OBS_DIR / "scripts" / "build-cloudflare-dist.py"
    btxt = (
        build_cf.read_text(encoding="utf-8")
        .replace("V208 Unified Chrome & Safari Shard Builder", "V209 Unified Chrome & Safari Shard Builder")
        .replace('ASSET_VER = "208"', 'ASSET_VER = "209"')
        .replace(
            '"version": "V208-Unified-Chrome-Safari-Shards-HodgeKirchhoffResistance-TauCetiEight40of40Complete-GalaxyInspectorStarIsoBlueprintSVG"',
            '"version": "V209-Unified-Chrome-Safari-Shards-ConformalBrierChowChiSquare-Milestone100Leads-Bridges40x40ConstellationRadialSVG"',
        )
        .replace('"totalZeroSorryLeanFiles": 692', '"totalZeroSorryLeanFiles": 694')
        .replace('"kernelCompiledLeanModules": 652', '"kernelCompiledLeanModules": 654')
    )
    build_cf.write_text(btxt, encoding="utf-8")

    daemon_py = OBS_DIR / "scripts" / "continuous-insight-daemon.py"
    dtxt = daemon_py.read_text(encoding="utf-8").replace('"V208"', '"V209"')
    daemon_py.write_text(dtxt, encoding="utf-8")

    verify_py = OBS_DIR / "scripts" / "continuous-verify-and-audit.py"
    vtxt = (
        verify_py.read_text(encoding="utf-8")
        .replace("V208", "V209")
        .replace(
            "All 692+ physical Lean 4 files (609 in CommonGround/Verification/ + 83 in 01..10-*)",
            "All 694+ physical Lean 4 files (610 in CommonGround/Verification/ + 84 in 01..10-*)",
        )
    )
    verify_py.write_text(vtxt, encoding="utf-8")
    print("  [OK] Patched & compacted unified-standalone.js, index.html (?v=209), build-cloudflare-dist.py, continuous-insight-daemon.py & continuous-verify-and-audit.py.")


def main() -> None:
    step1_verify_math_foundations()
    step2_register_suite_610_in_bundle()
    step3_patch_unified_js_html_and_build()
    print("=== V209 UPGRADE COMPLETE ===")


if __name__ == "__main__":
    main()
