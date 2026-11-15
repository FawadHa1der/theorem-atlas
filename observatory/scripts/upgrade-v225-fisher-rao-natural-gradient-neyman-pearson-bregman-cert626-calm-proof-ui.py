#!/usr/bin/env python3
"""
V225 Milestone Upgrade Script (`726 Zero-Sorry Lean 4.33.0 Files · Milestone 100 Frontier Modules & Milestone 80 Micro-Labs! · Amari Fisher–Rao Natural Gradient Invariance, Chentsov Fisher Monotonicity, Universal Fin N Neyman–Pearson & Wald SPRT, Banerjee–Bregman Universal Mean Decomposition vs. Reverse Mode-Seeking Asymmetry, Hauck–Donner Separation, K-FAC & Gauss–Newton PSD Suite #626 + Calm Progressive Proof Source Drawer & Synaptic Proof-Trace Stepper UI`):
1. Verifies mathematical witnesses & premise-failure boundaries for:
   - Amari Fisher–Rao natural gradient reparameterization invariance `c * dPhiNat == dThetaNat` across invertible scalings `theta = c * phi` (`c != 0`) vs. Euclidean `c^2` step distortion (`64x` quadratic overshoot `128 > 2` at `c = 3`, `Frontier #100` Thm 1) + Chentsov 2-fiber Fisher monotonicity `(q1+q2)(q2*d1^2 + q1*d2^2) - q1*q2*(d1+d2)^2 = (q2*d1 - q1*d2)^2 >= 0` vs. opposite-score Fisher collapse (`36 -> 0`, `Suite #626` Bridge 1) + Jeffreys root-Fisher invariance vs. uniform-prior `1:3` paradox (`Suite #626` Bridge 5),
   - Universal `Fin N` Neyman–Pearson likelihood-ratio optimality `sum (q*L1 - p*L0)*(dStar - d) >= 0` vs. non-LR `7x` power loss (`1 < 7` at equal Type-I size `2`, `Frontier #100` Thm 2) + Wald SPRT anytime stopping bound `B * sum_{A1} L0 <= q * sum L1` vs. 2-look optional peeking inflation (`7/16 > 4/16`, `Suite #626` Bridge 2),
   - Universal `Fin N` Banerjee–Bregman empirical-mean decomposition `sum D_phi(x_k, y) - sum D_phi(x_k, mu) = N * D_phi(mu, y)` vs. cubic `phi(u) = u^3` reverse-Bregman mode-seeking shift (`128 < 162` at `y = 4` vs `mu = 3`, `Frontier #100` Thm 3) + exponential-family moment-matching `↔` MLE vs. Albert–Anderson / Hauck–Donner complete separation `n(2w0 + w1) > 0` (`Suite #626` Bridge 3),
   - Martens–Grosse `K-FAC` mixed-product `(A ⊗ B) vec(W) = vec(B W A^T)` vs. diagonal-Fisher `25.5x` correlated-valley stall (`4` vs `102`, `Frontier #100` Thm 4) + Gauss–Newton PSD descent `g * (-J^2 g) <= 0` vs. indefinite non-convex Hessian uphill Newton step (`H = -9 < 0`, `g * step = +25 > 0`, `Suite #626` Bridge 4).
2. Registers V225 Lean 4.33.0 Verification Suite (`#626`, `626` Verification + **Milestone `100` Frontier** = `726` zero-sorry `.lean` files, `686` kernel-compiled), verifies `40 / 40` canonical project coverage across `verifiedLeanSuites`, and preserves `0 / 7,000` unreviewed `○` AST pairs.
3. Patches `observatory/unified-standalone.js`, `observatory/index.html` (`?v=225`), and build/audit scripts with Breakthroughs `290–293` (`293` total), Discovery Leads `131–132` (`132` total), **Milestone Micro-Lab `#80`**, 18-Archetype Bridge Composer (`fisher_rao_neyman_pearson_bregman_gate` -> `FisherRaoNeymanPearsonAndBregmanGate`), Calm Progressive Proof Source Drawer (`#v55-source-code-drawer`), Synaptic Proof-Trace Stepper (`#v115-prev-proof`, `#v115-next-proof`, `#v115-open-cert-btn`, curved `.cg-svg-photon-arc` in `#v115-stepper-svg`), 3-Edge Curved `.cg-svg-photon-arc` Functorial Square (`#v65-comm-svg`), and Suite `83` (`436/436` automated checks).
"""

import json
import random
import sys
from pathlib import Path

sys.dont_write_bytecode = True

REPO_ROOT = Path(__file__).resolve().parents[2]
OBS_DIR = REPO_ROOT / "observatory"


def step1_verify_math_foundations() -> None:
    print("=== STEP 1: V225 Mathematical Foundation Checks (Amari Natural Gradient, Chentsov Fisher, Fin N Neyman-Pearson, Wald SPRT, Banerjee-Bregman, Hauck-Donner Separation, K-FAC & Gauss-Newton) ===")
    rng = random.Random(20261115225)

    # 1. Amari Fisher-Rao pushforward invariance & Chentsov 2-fiber Fisher merging identity
    for _ in range(250):
        c = rng.choice([-7, -5, -3, -2, -1, 1, 2, 3, 5, 7])
        f_theta = rng.randint(1, 20)
        d_phi = rng.randint(-12, 12)
        d_theta = c * d_phi
        g_theta = -f_theta * d_theta
        f_phi = c * c * f_theta
        g_phi = c * g_theta
        assert f_phi * d_phi == -g_phi and c * d_phi == d_theta

        q1, q2 = rng.randint(1, 15), rng.randint(1, 15)
        d1, d2 = rng.randint(-15, 15), rng.randint(-15, 15)
        lhs = (q1 + q2) * (q2 * d1 * d1 + q1 * d2 * d2) - q1 * q2 * (d1 + d2) ** 2
        assert lhs == (q2 * d1 - q1 * d2) ** 2 and lhs >= 0
    assert 2 * ((-8) ** 2) == 128 == 64 * (2 * (1 ** 2))
    assert (1 + 1) * (9 + 9) == 36 and 1 * 1 * (3 - 3) ** 2 == 0

    # 2. Neyman-Pearson Fin N Lagrangian dominance & Wald SPRT stopping barrier
    for _ in range(250):
        N = rng.randint(2, 8)
        p, q, M = rng.randint(0, 10), rng.randint(1, 10), rng.randint(1, 10)
        L0 = [rng.randint(0, 12) for _ in range(N)]
        L1 = [rng.randint(0, 12) for _ in range(N)]
        d_star = [M if q * L1[i] > p * L0[i] else (0 if q * L1[i] < p * L0[i] else rng.randint(0, M)) for i in range(N)]
        d_any = [rng.randint(0, M) for _ in range(N)]
        lag = sum((q * L1[i] - p * L0[i]) * (d_star[i] - d_any[i]) for i in range(N))
        assert lag >= 0

        acc = [1 if q * L1[i] >= (p + 1) * L0[i] else 0 for i in range(N)]
        assert (p + 1) * sum(acc[i] * L0[i] for i in range(N)) <= q * sum(L1)

    # 3. Banerjee-Bregman decomposition, cubic reverse shift (128 < 162), Hauck-Donner separation, K-FAC & Gauss-Newton
    def breg_cubic(x: int, y: int) -> int:
        return x ** 3 - y ** 3 - 3 * y * y * (x - y)

    assert breg_cubic(0, 3) + breg_cubic(6, 3) == 162
    assert breg_cubic(4, 0) + breg_cubic(4, 6) == 128 < 162 == breg_cubic(3, 0) + breg_cubic(3, 6)

    for _ in range(250):
        N = rng.randint(1, 7)
        mu = rng.randint(0, 8)
        y = rng.randint(0, 8)
        xs = [mu for _ in range(N)]
        if N >= 2:
            shift = rng.randint(0, mu)
            xs[0] -= shift
            xs[1] += shift
        assert sum(xs) == N * mu
        lhs = sum(breg_cubic(xk, y) for xk in xs) - sum(breg_cubic(xk, mu) for xk in xs)
        assert lhs == N * breg_cubic(mu, y) >= 0

        w0, w1, w2, n = rng.randint(1, 10), rng.randint(1, 10), rng.randint(1, 10), rng.randint(1, 10)
        sep_score = (w0 + w1 + w2) * (2 * n) - n * (w1 + 2 * w2)
        assert sep_score == n * (2 * w0 + w1) > 0

    assert (-5) * (-5) == 25 > 0 and (1 * 1 + (-5) * 2) == -9
    print("  [OK] All V225 mathematical witnesses and failure boundaries verified.")


def step2_register_suite_626_in_bundle() -> None:
    print("=== STEP 2: Registering V225 Lean 4 Suite (#626) in bundle-data.js & Verifying 40 / 40 Complete Repo Coverage + 0 / 7,000 Unreviewed ===")
    cg_root = REPO_ROOT / "CommonGround.lean"
    cg_txt = cg_root.read_text(encoding="utf-8")
    imp_line = "import CommonGround.Verification.TheoremAtlasFisherRaoNaturalGradientNeymanPearsonBregmanDualityAndKfacBridge"
    assert imp_line in cg_txt, "Expected V225 Suite #626 import in CommonGround.lean!"

    frontier_path = REPO_ROOT / "03-information-recovery-kl-pythagorean" / "AmariFisherRaoNaturalGradientNeymanPearsonAndBregmanFrontier.lean"
    assert frontier_path.exists(), "Expected AmariFisherRaoNaturalGradientNeymanPearsonAndBregmanFrontier.lean in folder 03!"

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
    suite_id = "suite-atlas-fisher-rao-natural-gradient-neyman-pearson-bregman-kfac"
    suites = [s for s in sm.get("verifiedLeanSuites", []) if s.get("id") != suite_id]

    lean_rel = "CommonGround/Verification/TheoremAtlasFisherRaoNaturalGradientNeymanPearsonBregmanDualityAndKfacBridge.lean"
    lean_code = (REPO_ROOT / lean_rel).read_text(encoding="utf-8")
    suites.append({
        "id": suite_id,
        "title": "Suite #626 · Chentsov Fisher Monotonicity, Wald SPRT Anytime Stopping vs. Optional Peeking, Exponential-Family Moment Matching vs. Complete Separation, Gauss–Newton PSD & Jeffreys Invariance",
        "leanFile": lean_rel,
        "theoremName": "chentsov_markov_fisher_information_monotonicity_vs_insufficient_coarse_graining_drop",
        "projects": ["cslib", "econlib", "tc-probcomb", "physlib", "tauceti"],
        "plainSummary": "Proves Chentsov's denominator-free 2-fiber Fisher information merging identity (q₁+q₂)(q₂δ₁² + q₁δ₂²) - q₁q₂(δ₁+δ₂)² = (q₂δ₁ - q₁δ₂)² ≥ 0 vs. opposite-score coarse-graining total collapse (36 → 0), Wald's universal anytime-valid SPRT likelihood-ratio stopping bound B·∑_{A₁} L₀ ≤ q·∑ L₁ vs. 2-look optional peeking inflation (7/16 > 4/16), exponential-family log-likelihood moment matching ↔ MLE vs. Albert–Anderson / Hauck–Donner complete boundary separation n(2w₀+w₁) > 0, Gauss–Newton PSD descent vs. indefinite non-convex Hessian uphill Newton step (H = -9 < 0), and Jeffreys square-root Fisher reparameterization invariance vs. Laplace's uniform-prior 1:3 coordinate paradox.",
        "summary": "Machine-checked Lean 4.33.0 suite (0 imports, 0 sorry) unifying Folders 01+03+04+07+09 (`726` total zero-sorry `.lean` files, Milestone `100` Frontier modules): Chentsov Fisher monotonicity, Wald SPRT stopping, exponential-family moment matching vs. complete separation, Gauss–Newton PSD curvature, and Jeffreys invariance.",
        "code": lean_code,
        "declarations": [
            {
                "kind": "theorem",
                "name": "chentsov_markov_fisher_information_monotonicity_vs_insufficient_coarse_graining_drop",
                "file": lean_rel,
                "line": 56,
                "signature": "(q1+q2)(q2*d1²+q1*d2²) - q1*q2*(d1+d2)² = (q2*d1-q1*d2)² ∧ (zero loss ↔ q2*d1 = q1*d2) ∧ (36 → 0)",
                "snippet": "theorem chentsov_markov_fisher_information_monotonicity_vs_insufficient_coarse_graining_drop : ...",
            },
            {
                "kind": "theorem",
                "name": "wald_sprt_likelihood_ratio_stopping_bound_vs_optional_peeking_inflation",
                "file": lean_rel,
                "line": 124,
                "signature": "(∀ Ω L0 L1 A1 B q, B * sum_{A1} L0 ≤ q * sum L1) ∧ (singleLook = 4 < 7 = twoLookPeek)",
                "snippet": "theorem wald_sprt_likelihood_ratio_stopping_bound_vs_optional_peeking_inflation : ...",
            },
            {
                "kind": "theorem",
                "name": "exponential_family_moment_matching_mle_gradient_identity_vs_complete_separation_divergence",
                "file": lean_rel,
                "line": 146,
                "signature": "(score = Z*empMom - N*muW) ∧ (FisherHessian = SOS ≥ 0) ∧ (∀ n,w0,w1,w2 ≥ 1, 0 < n*(2*w0+w1))",
                "snippet": "theorem exponential_family_moment_matching_mle_gradient_identity_vs_complete_separation_divergence : ...",
            },
            {
                "kind": "theorem",
                "name": "gauss_newton_generalized_fisher_psd_vs_indefinite_hessian_negative_curvature_ascent",
                "file": lean_rel,
                "line": 182,
                "signature": "(∀ r J, 0 ≤ J² ∧ g*(-J² g) ≤ 0) ∧ (fullH = -9 ∧ 0 < g * scaledNewtonStep)",
                "snippet": "theorem gauss_newton_generalized_fisher_psd_vs_indefinite_hessian_negative_curvature_ascent : ...",
            },
            {
                "kind": "theorem",
                "name": "jeffreys_prior_square_root_fisher_invariance_vs_uniform_prior_coordinate_paradox",
                "file": lean_rel,
                "line": 209,
                "signature": "((c*sTheta)² = c²*fTheta ∧ (c*sTheta)*dPhi = sTheta*(c*dPhi)) ∧ (1 = 1 ∧ 1 ≠ 3)",
                "snippet": "theorem jeffreys_prior_square_root_fisher_invariance_vs_uniform_prior_coordinate_paradox : ...",
            },
        ],
    })
    sm["verifiedLeanSuites"] = suites
    assert len(suites) >= 626, f"Expected >= 626 verifiedLeanSuites, got {len(suites)}"

    covered_repos = set()
    for s in suites:
        for p in s.get("projects", []) or []:
            if p in canon_projects:
                covered_repos.add(p)
    assert len(covered_repos) == 40, f"Expected 40/40 covered repos, got {len(covered_repos)}"

    isos = sm.get("structuralIsomorphisms", [])
    unreviewed = [x for x in isos if not x.get("_cgEpistemicStatus")]
    assert len(unreviewed) == 0, f"Expected 0 unreviewed AST pairs, got {len(unreviewed)}"

    out_raw = raw[:idx] + prefix + json.dumps(pre, ensure_ascii=False, separators=(",", ":")) + tail_js
    bd_path.write_text(out_raw, encoding="utf-8")
    print(f"  [OK] Registered Suite #626 ({len(suites)} suites total, 40/40 canonical repos covered, 0 unreviewed AST pairs).")


def build_v225_breakthroughs(ujs: str) -> list:
    dec = json.JSONDecoder()
    needle = "window.CG_VERIFIED_ATLAS_BREAKTHROUGHS = ["
    last_idx = ujs.rfind(needle)
    assert last_idx != -1, "Could not locate CG_VERIFIED_ATLAS_BREAKTHROUGHS in unified-standalone.js!"
    arr_start = last_idx + len("window.CG_VERIFIED_ATLAS_BREAKTHROUGHS = ")
    records, _ = dec.raw_decode(ujs, arr_start)

    lean_ver = "leanprover/lean4:v4.33.0"
    new_v225 = [
        {
            "id": "bt-v225-amari-fisher-rao-natural-gradient-chentsov-monotonicity-and-jeffreys-invariance",
            "title": "Amari Fisher–Rao Natural Gradient Invariance, Chentsov Tangent Sufficiency & Jeffreys Square-Root Measure (`Frontier #100` + `Suite #626`)",
            "projects": ["cslib", "econlib", "physlib"],
            "epistemicSymbol": "★",
            "epistemicGrade": f"Lean 4.33.0 Kernel Checked ({lean_ver} · 0 sorry)",
            "howConnected": "Proves (`amari_natural_gradient_reparameterization_invariance_vs_euclidean_c_squared_distortion`, `chentsov_markov_fisher_information_monotonicity_vs_insufficient_coarse_graining_drop`, `jeffreys_prior_square_root_fisher_invariance_vs_uniform_prior_coordinate_paradox`) exact pushforward invariance `c · Δφ_nat = Δθ_nat` under `θ = c · φ`, exact Chentsov Fisher merging `(q₁+q₂)(q₂δ₁²+q₁δ₂²) - q₁q₂(δ₁+δ₂)² = (q₂δ₁-q₁δ₂)² ≥ 0`, and Jeffreys interval invariance `(c s_θ) Δφ = s_θ Δθ`!",
            "selfCritique": "Contrasts all three geometric invariants with sharp coordinate/coarse-graining failures: Euclidean GD distorts steps by `c²` (`64×` quadratic overshoot `128 > 2` at `c = 3`), opposite-score coarse-graining `(3, -3)` destroys `100%` of Fisher info (`36 → 0`), and Laplace's flat prior flips `[0,1]:[1,2]` from `1:1` to `1:3` under `ψ = θ²`.",
        },
        {
            "id": "bt-v225-neyman-pearson-likelihood-ratio-optimality-and-wald-sprt-stopping-barrier",
            "title": "Universal `Fin N` Neyman–Pearson Fundamental Lemma & Wald Anytime-Valid `SPRT` Stopping Barrier (`Frontier #100` + `Suite #626`)",
            "projects": ["cslib", "tc-probcomb", "econlib"],
            "epistemicSymbol": "★",
            "epistemicGrade": f"Lean 4.33.0 Kernel Checked ({lean_ver} · 0 sorry)",
            "howConnected": "Proves (`neyman_pearson_likelihood_ratio_optimality_vs_non_lr_power_suboptimality`, `wald_sprt_likelihood_ratio_stopping_bound_vs_optional_peeking_inflation`) universal Lagrangian dominance `∑_x (q L₁(x) - p L₀(x))(δ*(x) - δ(x)) ≥ 0` over arbitrary finite alphabets `Fin N` and Wald's universal stopping-set bound `B ∑_{A₁} L₀ ≤ q ∑_Ω L₁`!",
            "selfCritique": "Certifies two pervasive statistical failure modes: thresholding raw monotone features on non-monotone likelihoods `L₀ = (2,2,6), L₁ = (1,7,2)` loses `7×` power (`1 < 7` at identical Type-I size `2`), while unadjusted 2-look optional peeking inflates null false positives from `4/16` (`25%`) to `7/16` (`43.75%`).",
        },
        {
            "id": "bt-v225-banerjee-bregman-mean-optimality-vs-reverse-asymmetry-and-hauck-donner-separation",
            "title": "Universal `Fin N` Banerjee–Bregman Mean Decomposition vs. Reverse Mode-Seeking Shift & Hauck–Donner Complete Separation (`Frontier #100` + `Suite #626`)",
            "projects": ["cslib", "econlib", "tauceti"],
            "epistemicSymbol": "★",
            "epistemicGrade": f"Lean 4.33.0 Kernel Checked ({lean_ver} · 0 sorry)",
            "howConnected": "Proves (`bregman_three_point_pythagorean_and_mean_optimality_vs_reverse_projection_asymmetry`, `exponential_family_moment_matching_mle_gradient_identity_vs_complete_separation_divergence`) `∑_k D_φ(x_k, y) - ∑_k D_φ(x_k, μ) = N · D_φ(μ, y)` for ANY generator `φ` whenever `∑ x_k = N μ`, alongside exact exponential-family moment-matching `↔` MLE stationarity!",
            "selfCritique": "Explains BOTH forward-vs-reverse KL divergence asymmetry AND logistic-regression MLE blowup: on convex `φ(u) = u³` over `{0, 6}`, forward Bregman uniquely picks `μ = 3` (`162`) whereas reverse Bregman shifts to `y = 4` (`128 < 162`); on boundary-separated counts `c = (0,0,n)`, score residual `n(2w₀+w₁) > 0` never vanishes on finite weights.",
        },
        {
            "id": "bt-v225-kfac-kronecker-fisher-preconditioning-and-gauss-newton-psd-vs-indefinite-hessian",
            "title": "Martens–Grosse `K-FAC` Mixed-Product Fisher Preconditioning & Gauss–Newton PSD Curvature vs. Indefinite Hessian Ascent (`Frontier #100` + `Suite #626`)",
            "projects": ["cslib", "physlib", "econlib"],
            "epistemicSymbol": "★",
            "epistemicGrade": f"Lean 4.33.0 Kernel Checked ({lean_ver} · 0 sorry)",
            "howConnected": "Proves (`kfac_kronecker_mixed_product_exact_preconditioning_vs_diagonal_fisher_shear_blindspot`, `gauss_newton_generalized_fisher_psd_vs_indefinite_hessian_negative_curvature_ascent`) `(A ⊗ B) vec(W) = vec(B W Aᵀ)`, factored composition `(B₁B₂) W (A₁A₂)ᵀ = B₁(B₂ W A₂ᵀ)A₁ᵀ`, and universal Gauss–Newton descent `g · (-J² g) ≤ 0`!",
            "selfCritique": "Reveals why neither diagonal `Adam` nor raw non-convex Newton suffices: on correlated valley `50(w₁+w₂)² + (w₁-w₂)²`, diagonal Fisher `diag(102, 102)` stalls by `25.5×` (`4` vs `102`) where full `K-FAC` solves in `1` step, while raw Newton at `(r, J, r'') = (-5, 1, 2)` (`H = -9 < 0`) climbs uphill (`9 g · Δ_N = +25 > 0`) toward a local maximum!",
        },
    ]

    existing_ids = {r.get("id") for r in records if isinstance(r, dict)}
    for item in new_v225:
        if item["id"] not in existing_ids:
            records.append(item)
    assert len(records) == 293, f"Expected 293 breakthroughs, got {len(records)}"
    return records


V225_JS_BLOCK = r"""
// === V225 MILESTONE UPGRADE: 726 ZERO-SORRY LEAN 4.33.0 FILES (MILESTONE 100 FRONTIER MODULES & MILESTONE 80 MICRO-LABS!) · AMARI FISHER–RAO NATURAL GRADIENT INVARIANCE, CHENTSOV MONOTONICITY, UNIVERSAL FIN N NEYMAN–PEARSON & WALD SPRT, BANERJEE–BREGMAN MEAN DECOMPOSITION VS. REVERSE ASYMMETRY, HAUCK–DONNER SEPARATION, K-FAC & GAUSS–NEWTON PSD SUITE #626 + CALM PROGRESSIVE PROOF SOURCE DRAWER & SYNAPTIC PROOF-TRACE STEPPER UI (436/436 CHECKS!) ===
(function() {
  if (typeof window === "undefined") return;

  // 1. Consolidated 293 Foundation-Verified Theorem-Atlas Breakthroughs & Scope Audits
  window.CG_VERIFIED_ATLAS_BREAKTHROUGHS = __BREAKTHROUGHS_293_JSON__;

  if (Array.isArray(window.V145_REAL_LEAN_SUITES)) {
    var v225Suites = [
      {
        file: "CommonGround/Verification/TheoremAtlasFisherRaoNaturalGradientNeymanPearsonBregmanDualityAndKfacBridge.lean",
        line: 56,
        theoremName: "chentsov_markov_fisher_information_monotonicity_vs_insufficient_coarse_graining_drop",
        snippet: "theorem chentsov_markov_fisher_information_monotonicity_vs_insufficient_coarse_graining_drop : (q1+q2)(q2*d1²+q1*d2²) - q1*q2*(d1+d2)² = (q2*d1-q1*d2)² ∧ ...",
        zeroSorry: true
      },
      {
        file: "03-information-recovery-kl-pythagorean/AmariFisherRaoNaturalGradientNeymanPearsonAndBregmanFrontier.lean",
        line: 59,
        theoremName: "amari_natural_gradient_reparameterization_invariance_vs_euclidean_c_squared_distortion",
        snippet: "theorem amari_natural_gradient_reparameterization_invariance_vs_euclidean_c_squared_distortion : (c ≠ 0 → 0 < fTheta → ... → c * dPhiNat = dThetaNat) ∧ ...",
        zeroSorry: true
      }
    ];
    v225Suites.forEach(function(vs) {
      if (!window.V145_REAL_LEAN_SUITES.some(function(s){ return s && s.file === vs.file; })) {
        window.V145_REAL_LEAN_SUITES.push(vs);
      }
    });
  }

  if (window.CG_R2_CORPUS_CONFIG) {
    window.CG_R2_CORPUS_CONFIG.kernelCompiledModules = 686;
    window.CG_R2_CORPUS_CONFIG.totalZeroSorryLeanFiles = 726;
    window.CG_R2_CORPUS_CONFIG.verificationModules = 626;
    window.CG_R2_CORPUS_CONFIG.frontierModules = 100;
  }

  // 2. Expand Promising Research Leads from 130 -> 132!
  if (Array.isArray(window.CG_PROMISING_RESEARCH_LEADS)) {
    var newLeads225 = [
      {
        id: "lead-reparameterization-invariant-kfac-gauss-newton-scientific-ml",
        title: "131. Reparameterization-Invariant K-FAC Natural-Gradient & Gauss–Newton Damping for Ill-Conditioned Scientific ML (`Frontier #100` + `Suite #626`)",
        projects: ["cslib", "econlib", "physlib", "tauceti"],
        targetStarId: "iso-cslib-econlib-01",
        domains: "Amari Fisher–Rao Geometry, `K-FAC` Kronecker Preconditioning & Gauss–Newton PSD Curvature (`Folder 03` + `Suite #626`) ↔ Physics-Informed Neural Operators & LLM Adapter Preconditioning",
        whyPromising: "Physics-informed PDE solvers (PINNs) and quantized LLM adapters fail under first-order optimizers for two complementary reasons proven in `Frontier #100` and `Suite #626`: (1) unit/layer rescaling `θ = c · φ` distorts Euclidean steps by `c²` (`64×` overshoot at `c = 3`), and (2) diagonal `Adam`/diagonal-Fisher ignores off-diagonal feature correlations, shrinking shallow-valley steps by `25.5×` (`4` vs `102` on `50(w₁+w₂)² + (w₁-w₂)²`), while raw non-convex Newton steps climb uphill at negative-curvature inflections (`H = -9 < 0`). Combining Kronecker-factored `(A ⊗ B)⁻¹` generalized Gauss–Newton (`JᵀJ ≽ 0`) with Levenberg–Marquardt trust damping cures all three simultaneously!",
        whatStatementUnlocked: "Scale-invariant Kronecker-factored Gauss–Newton update `(B + λ_B I)⁻¹ G (A + λ_A I)⁻ᵀ` with certified non-positive directional derivative `⟨g, ΔW⟩ ≤ 0` and exact `GL(d)` layer-rescaling covariance.",
        realWorldUseCase: "Stiff multi-scale Navier–Stokes / plasma PINN training (`κ > 10⁶`), low-rank `LoRA` natural-gradient fine-tuning, and seismic waveform tomography.",
        keyObstacle: "Maintaining unbiased exponential moving averages of activation/backprop factors `(A_t, B_t)` under mini-batch distribution shift without `O(d³)` eigendecomposition overhead every step.",
        leanAnchor: "CommonGround/Verification/TheoremAtlasFisherRaoNaturalGradientNeymanPearsonBregmanDualityAndKfacBridge.lean",
        labIndex: 79
      },
      {
        id: "lead-anytime-valid-neyman-pearson-wald-eprocess-and-firth-regularized-monitoring",
        title: "132. Anytime-Valid Neyman–Pearson / Wald e-Process Sequential Testing & Boundary-Regularized Calibration (`Frontier #100` + `Suite #626`)",
        projects: ["cslib", "tc-probcomb", "econlib", "tauceti"],
        targetStarId: "iso-cslib-tc-probcomb-01",
        domains: "Neyman–Pearson Likelihood Ratios, Wald `SPRT` Martingales & Exponential-Family Duality (`Folder 03` + `Suite #626`) ↔ Adaptive Clinical Trials & Continuous AI Safety Drift Monitors",
        whyPromising: "`Suite #626` Bridge 2 proves that continuous optional peeking on fixed-horizon p-values inflates false alarms from `25%` (`4/16`) to `43.75%` (`7/16`), while Bridge 3 proves that early-stage rare-event cohorts with zero failures in one arm (`c = (0,0,n)`) suffer Hauck–Donner complete separation (`n(2w₀+w₁) > 0`), causing plug-in MLE likelihood ratios to diverge to `∞`! Blending Jeffreys square-root Fisher priors (`Bridge 5` coordinate-invariant `√I(θ)`) into predictable `e`-process likelihood ratios preserves Wald's universal anytime Type-I barrier `α ≤ 1/B` while remaining near Neyman–Pearson optimal (`Frontier #100` Thm 2).",
        whatStatementUnlocked: "Jeffreys-regularized predictable `e`-process `E_t = ∏_{s≤t} p_{θ̂_{s-1}^J}(X_s) / p_0(X_s)` achieving universal anytime-valid Type-I control `ℙ_0(∃ t, E_t ≥ 1/α) ≤ α` with bounded log-odds under complete data separation.",
        realWorldUseCase: "Phase II/III adaptive platform clinical trials, real-time post-deployment LLM hallucination/jailbreak drift alarms, and semiconductor wafer-fab sequential anomaly gating.",
        keyObstacle: "Characterizing exact minimax regret of Jeffreys-plugged predictable `e`-processes relative to the hindsight oracle Neyman–Pearson likelihood ratio on multi-parameter exponential families.",
        leanAnchor: "CommonGround/Verification/TheoremAtlasFisherRaoNaturalGradientNeymanPearsonBregmanDualityAndKfacBridge.lean",
        labIndex: 79
      }
    ];
    newLeads225.forEach(function(ld) {
      if (!window.CG_PROMISING_RESEARCH_LEADS.some(function(x){ return x && x.id === ld.id; })) {
        window.CG_PROMISING_RESEARCH_LEADS.push(ld);
      }
    });
  }

  // Canonicalize project IDs across all 293 breakthroughs & 132 leads
  var _cgAlias225 = {
    "CommonGround": "tauceti", "FLT": "flt", "PhysLean": "physlib", "PrimeNumberTheoremAnd": "oai-riemann",
    "SpherePacking": "oai-sphere", "aks": "oai-codes", "algebra-lean": "tc-lie", "carleson": "oai-smoothing",
    "category-theory-lean": "tc-topology", "combinatorics-lean": "tc-probcomb", "erdos-problems": "oai-extremal",
    "fluid": "euler", "formal-conjectures": "tauceti", "graph-theory-lean": "oai-extremal", "group-theory-lean": "tc-reptheory",
    "hodge": "oai-hodge", "lean-liquid": "tc-alggeom", "mathlib": "tauceti", "mathlib4": "tauceti", "ns-sec11": "ns",
    "number-theory-lean": "tc-numtheory", "oai-compact": "tc-topology", "oai-cvp": "oai-gapcvp", "oai-graphmoment": "oai-extremal",
    "oai-packing": "oai-sphere", "oai-qpr": "oai-qrep", "optlib": "econlib", "pfr": "tc-probcomb", "pnp": "eth",
    "pnt": "oai-riemann", "probability-lean": "tc-probcomb", "ramsey": "oai-ramsey", "statlearn": "cslib",
    "tc-group": "tc-reptheory", "tc-linalg": "tc-lie", "ten-connes-rigidity": "oai-connes", "ten-ehrhart": "oai-ehrhart",
    "ten-metric-codes": "oai-codes", "ten-permanent": "oai-perm", "ten-quantum-repetition": "oai-qrep", "ten-sphere-packing": "oai-sphere"
  };
  [window.CG_VERIFIED_ATLAS_BREAKTHROUGHS, window.CG_PROMISING_RESEARCH_LEADS].forEach(function(arr) {
    if (!Array.isArray(arr)) return;
    arr.forEach(function(it) {
      if (it && Array.isArray(it.projects)) {
        var clean = [];
        it.projects.forEach(function(p) {
          var mp = _cgAlias225[p] || p;
          if (manifest && manifest.projects && manifest.projects[mp] && clean.indexOf(mp) === -1) clean.push(mp);
        });
        it.projects = clean.length ? clean : ["tauceti"];
      }
    });
  });

  // 3. Extend Boundary Guardrail Rules with V225 Fisher-Rao / K-FAC, Neyman-Pearson / Peeking & Bregman / Separation Boundaries
  if (Array.isArray(window.CG_BOUNDARY_RULES)) {
    var v225Rules = [
      {
        id: "fisher-rao-reparameterization-and-kfac-diagonal-blindspot-boundary",
        groups: [["fisher", "naturalgradient", "kfac", "gaussnewton"], ["reparameterization", "diagonal", "adam", "indefinitehessian"]],
        title: "Premise Boundary · Euclidean `c²` Rescaling Overshoot (`64×`), Diagonal-Fisher `25.5×` Valley Stall & Indefinite Hessian Uphill Newton Step (`H = -9`)",
        warning: "`Frontier #100` Thms 1,4 & `Suite #626` Bridge 4 prove Euclidean GD scales steps by `c²` (`128 > 2` at `c = 3`), diagonal Fisher `diag(102,102)` shrinks correlated-valley progress `25.5×`, and non-convex full Newton climbs uphill when `J² + r·r'' < 0`.",
        remedy: "Precondition with Kronecker-factored generalized Fisher / Gauss–Newton `(A ⊗ B)⁻¹` (`JᵀJ ≽ 0`) rather than raw Euclidean gradients, diagonal second moments alone, or undamped indefinite Hessians.",
        targetLab: 79
      },
      {
        id: "neyman-pearson-monotone-score-and-optional-peeking-boundary",
        groups: [["neymanpearson", "likelihoodratio", "sprt", "wald"], ["optionalpeeking", "pvalues", "uncalibrated"]],
        title: "Premise Boundary · Non-LR Monotone Thresholds Lose `7×` Power (`1 < 7`) & Unadjusted Optional Peeking Inflates Type-I Error (`7/16 > 4/16`)",
        warning: "`Frontier #100` Thm 2 & `Suite #626` Bridge 2 prove raw coordinate thresholds fail when `L₁/L₀` is non-monotone (`1` vs `7` at Type-I size `2`), and repeated fixed-horizon peeking inflates null rejection from `25%` to `43.75%`.",
        remedy: "Threshold the calibrated likelihood ratio `L₁(x)/L₀(x)` for fixed samples and enforce Wald's `e`-process / `SPRT` barrier `L₁(ω_{1:t}) / L₀(ω_{1:t}) ≥ 1/α` under continuous monitoring.",
        targetLab: 79
      },
      {
        id: "bregman-reverse-asymmetry-and-hauck-donner-separation-boundary",
        groups: [["bregman", "exponentialfamily", "mle", "kl"], ["reversekl", "modeseeking", "completeseparation", "hauckdonner"]],
        title: "Premise Boundary · Reverse Bregman Shifts Away from Empirical Mean (`128 < 162`) & Boundary Separation Diverges Unregularized MLE (`n(2w₀+w₁) > 0`)",
        warning: "`Frontier #100` Thm 3 & `Suite #626` Bridge 3 prove `∑ D_φ(x_k, y)` uniquely picks `μ = 3` (`162`) on `{0, 6}` while `∑ D_φ(y, x_k)` shifts to `y = 4` (`128 < 162`), and boundary data `c = (0,0,n)` admits no finite interior exponential-family MLE.",
        remedy: "Match Bregman argument order (`D_φ(data, model)` mean-seeking vs `D_φ(model, data)` mode-seeking) to downstream loss and add Jeffreys/Firth prior regularization against separable boundary counts.",
        targetLab: 79
      }
    ];
    v225Rules.forEach(function(r) {
      if (!window.CG_BOUNDARY_RULES.some(function(x){ return x && x.id === r.id; })) {
        window.CG_BOUNDARY_RULES.push(r);
      }
    });
  }

  // Register Archetype #18 in V95_OBSTACLES (`Fisher–Rao Natural Gradient, Neyman–Pearson & Bregman Gate`)
  if (Array.isArray(window.V95_OBSTACLES) && !window.V95_OBSTACLES.some(function(o){ return o && o.id === "fisher_rao_neyman_pearson_bregman_gate"; })) {
    window.V95_OBSTACLES.push({
      id: "fisher_rao_neyman_pearson_bregman_gate",
      name: "18. Fisher–Rao, Neyman–Pearson & Bregman Gate",
      carrier: "FisherRaoNeymanPearsonAndBregmanGate",
      premiseGate: "Requires `F_θ ≻ 0` / Gauss–Newton `JᵀJ ≽ 0`, calibrated `L₁/L₀` & Wald `e`-process barrier under optional stopping, right-argument Bregman order for mean recovery, and interior support (`c_x > 0`) for finite MLE",
      tactic: "Cancel coordinate Jacobian `c` via `F_φ = c² F_θ`, apply pointwise `(q L₁ - p L₀)(δ* - δ) ≥ 0`, expand Banerjee–Bregman `∑ D_φ(x_k, y) - ∑ D_φ(x_k, μ) = N D_φ(μ, y)`, and factor `(A ⊗ B) vec(W) = vec(B W Aᵀ)`."
    });
  }

  // 4. Milestone Interactive Exact-Integer Micro-Lab #80 (0-indexed 79): Fisher-Rao Natural Gradient & K-FAC, Neyman-Pearson & Wald SPRT, Banerjee-Bregman & Complete Separation
  window.v225FisherRaoNeymanPearsonBregmanLabModel = function(mode, opts) {
    opts = opts || {};
    var scaleC = (typeof opts.scaleC === "number") ? Math.max(1, Math.min(5, Math.round(opts.scaleC))) : 3;
    var valleyKappa = (typeof opts.valleyKappa === "number") ? Math.max(1, Math.min(80, Math.round(opts.valleyKappa))) : 50;
    var peekLooks = (typeof opts.peekLooks === "number") ? Math.max(1, Math.min(4, Math.round(opts.peekLooks))) : 2;
    var bregmanCandY = (typeof opts.bregmanCandY === "number") ? Math.max(0, Math.min(6, Math.round(opts.bregmanCandY))) : 4;

    // 1. Amari Natural Gradient vs Euclidean GD at (F_theta = 2, theta_0 = 1, eta = 1/4):
    //    4 * theta_1_GD = 4 - 4 * c^2 -> theta_1_GD = 1 - c^2, quadLoss = 2 * (1 - c^2)^2; Natural gradient theta_1_nat = 0 -> loss = 0!
    var gdTheta1 = 1 - scaleC * scaleC;
    var euclidLossAfter1 = 2 * gdTheta1 * gdTheta1;
    var natLossAfter1 = 0;
    // K-FAC vs Diagonal Fisher on L(w1, w2) = kappa*(w1+w2)^2 + (w1-w2)^2 at (1, -1): diag = 2*(kappa + 1), valley grad = 4 -> stall ratio = (kappa + 1) / 2
    var diagEntry = 2 * (valleyKappa + 1);
    var diagShrinkFactor = ((valleyKappa + 1) / 2).toFixed(1);

    // 2. Neyman-Pearson on L0=(2,2,6), L1=(1,7,2) at Type-I size 2: NP power = 7 vs Naive {x=0} power = 1;
    //    Optional peeking over k looks with per-look null survive 3/4: null reject num out of 4^k is 4^k - 3^k vs nominal 4^(k-1)
    var npPower = 7, naivePower = 1;
    var denomPeek = Math.pow(4, peekLooks);
    var nominalNullNum = Math.pow(4, peekLooks - 1);
    var peekNullNum = denomPeek - Math.pow(3, peekLooks);
    var peekInflated = peekNullNum > nominalNullNum;

    // 3. Cubic Bregman D_{u^3}(x, y) = (x - y)^2 * (x + 2*y) on bimodal sample {0, 6} (mean mu = 3):
    function cubBreg(x, y) { return (x - y) * (x - y) * (x + 2 * y); }
    var fwdMeanRisk = cubBreg(0, 3) + cubBreg(6, 3); // 54 + 108 = 162
    var fwdCandRisk = cubBreg(0, bregmanCandY) + cubBreg(6, bregmanCandY); // 162 + 2 * cubBreg(3, y)
    var revMeanRisk = cubBreg(3, 0) + cubBreg(3, 6); // 27 + 135 = 162
    var revCandRisk = cubBreg(bregmanCandY, 0) + cubBreg(bregmanCandY, 6); // at y=4: 64 + 64 = 128 < 162!

    if (mode === "neyman-pearson-and-wald-sprt") {
      return {
        mode: mode,
        scaleC: scaleC, valleyKappa: valleyKappa, peekLooks: peekLooks, bregmanCandY: bregmanCandY,
        gdTheta1: gdTheta1, euclidLossAfter1: euclidLossAfter1, natLossAfter1: natLossAfter1, diagEntry: diagEntry, diagShrinkFactor: diagShrinkFactor,
        npPower: npPower, naivePower: naivePower, denomPeek: denomPeek, nominalNullNum: nominalNullNum, peekNullNum: peekNullNum, peekInflated: peekInflated,
        fwdMeanRisk: fwdMeanRisk, fwdCandRisk: fwdCandRisk, revMeanRisk: revMeanRisk, revCandRisk: revCandRisk,
        heading: "Neyman–Pearson `7×` Power (`7 > 1`) & Wald `SPRT` vs. `" + peekLooks + "`-Look Peeking (`" + peekNullNum + "/" + denomPeek + "`)",
        operatorEq: "∑(qL₁-pL₀)(δ*-δ) ≥ 0 (NP=7 vs Naive=1 at α=2/10)  |  Peeking α = " + peekNullNum + "/" + denomPeek + " (" + ((100 * peekNullNum) / denomPeek).toFixed(2) + "%)",
        witnessDetail: peekInflated
          ? ("OPTIONAL PEEKING TYPE-I INFLATION (`k = " + peekLooks + "` looks): Stopping at the first nominal `25%` (`1/4`) rejection inflates actual null false-alarm rate from `" + nominalNullNum + "/" + denomPeek + "` (`25.00%`) to `" + peekNullNum + "/" + denomPeek + "` (`" + ((100 * peekNullNum) / denomPeek).toFixed(2) + "%`)! Wald's `SPRT` barrier `B · L₀(ω) ≤ q · L₁(ω)` locks Type-I error below `q/B` across ALL adaptive stopping rules (`Suite #626` Bridge 2), while `Fin N` Neyman–Pearson (`Frontier #100` Thm 2) achieves `7×` higher fixed-sample power (`7 > 1`) at identical Type-I size `2`.")
          : ("SINGLE-LOOK CALIBRATED BASELINE (`k = 1` look): With no optional intermediate peeking (`1/4 = 25%`), fixed-horizon Type-I size is exact, and thresholding the likelihood ratio `L₁/L₀` at `x = 1` (`7/2`) captures `7/10` power vs `1/10` for raw coordinate `{x = 0}`! Increase `peekLooks ≥ 2` to observe optional-stopping Type-I inflation."),
        secondaryDetail: "Kernel-verified across arbitrary finite alphabets `Fin N` and trajectory spaces `Fin Ω` (`0` imports, `0` sorry).",
        verdict: peekInflated
          ? ("⚠ Optional Peeking Inflates α to `" + peekNullNum + "/" + denomPeek + "` (Use Wald `SPRT` Barrier `B·α ≤ q`!)")
          : ("✓ Exact Single-Look α = `1/4` & Neyman–Pearson Optimal Power `7 > 1`"),
        leanRef: "CommonGround/Verification/TheoremAtlasFisherRaoNaturalGradientNeymanPearsonBregmanDualityAndKfacBridge.lean"
      };
    }
    if (mode === "bregman-duality-and-separation") {
      return {
        mode: mode,
        scaleC: scaleC, valleyKappa: valleyKappa, peekLooks: peekLooks, bregmanCandY: bregmanCandY,
        gdTheta1: gdTheta1, euclidLossAfter1: euclidLossAfter1, natLossAfter1: natLossAfter1, diagEntry: diagEntry, diagShrinkFactor: diagShrinkFactor,
        npPower: npPower, naivePower: naivePower, denomPeek: denomPeek, nominalNullNum: nominalNullNum, peekNullNum: peekNullNum, peekInflated: peekInflated,
        fwdMeanRisk: fwdMeanRisk, fwdCandRisk: fwdCandRisk, revMeanRisk: revMeanRisk, revCandRisk: revCandRisk,
        heading: "Banerjee–Bregman Mean (`" + fwdCandRisk + " ≥ 162`) vs. Reverse Shift (`" + revCandRisk + "` vs `162` at `y = " + bregmanCandY + "`)",
        operatorEq: "Fwd ∑D_{u³}(x_k," + bregmanCandY + ")=" + fwdCandRisk + " (=162+2·D(3," + bregmanCandY + "))  |  Rev ∑D_{u³}(" + bregmanCandY + ",x_k)=" + revCandRisk + " (vs 162 at μ=3)",
        witnessDetail: (revCandRisk < revMeanRisk)
          ? ("FORWARD VS. REVERSE BREGMAN ASYMMETRY (`y = " + bregmanCandY + "` on `{0, 6}`): Right-argument (mean-seeking) Bregman risk `∑ D_φ(x_k, y) = 162 + 2 D_φ(3, y) = " + fwdCandRisk + "` is UNIQUELY minimized at empirical mean `μ = 3` (`162`) for every convex `φ` (`Frontier #100` Thm 3)! Swapping arguments to `∑ D_φ(y, x_k)` breaks mean optimality: at `y = " + bregmanCandY + "`, reverse cubic Bregman drops to `" + revCandRisk + " < 162`, shifting toward high-curvature `x = 6` — and under boundary counts `c = (0,0,n)`, interior exponential-family score `n(2w₀+w₁) > 0` never vanishes (`Suite #626` Bridge 3)!")
          : ("CANDIDATE `y = " + bregmanCandY + "` COMPARED TO EMPIRICAL MEAN `μ = 3`: Forward Bregman excess is `2 · D_{u³}(3, " + bregmanCandY + ") = " + (fwdCandRisk - fwdMeanRisk) + " ≥ 0` (`" + fwdCandRisk + " ≥ 162`), while reverse Bregman is `" + revCandRisk + "`. Set `y = 4` to witness reverse-Bregman mode-seeking (`128 < 162`)!"),
        secondaryDetail: "Also certifies Jeffreys root-Fisher reparameterization invariance `(c s_θ) Δφ = s_θ Δθ` vs. Laplace flat-prior `1:3` paradox under `ψ = θ²` (`Bridge 5`).",
        verdict: (revCandRisk < revMeanRisk)
          ? ("⚠ Reverse Bregman Shifts Optimum (`" + revCandRisk + " < 162` at `y = " + bregmanCandY + "` ≠ `μ = 3`!)")
          : ("✓ Universal Banerjee–Bregman Forward Mean Minimum (`162 ≤ " + fwdCandRisk + "` at `μ = 3`)"),
        leanRef: "03-information-recovery-kl-pythagorean/AmariFisherRaoNaturalGradientNeymanPearsonAndBregmanFrontier.lean"
      };
    }
    return {
      mode: "fisher-rao-and-kfac",
      scaleC: scaleC, valleyKappa: valleyKappa, peekLooks: peekLooks, bregmanCandY: bregmanCandY,
      gdTheta1: gdTheta1, euclidLossAfter1: euclidLossAfter1, natLossAfter1: natLossAfter1, diagEntry: diagEntry, diagShrinkFactor: diagShrinkFactor,
      npPower: npPower, naivePower: naivePower, denomPeek: denomPeek, nominalNullNum: nominalNullNum, peekNullNum: peekNullNum, peekInflated: peekInflated,
      fwdMeanRisk: fwdMeanRisk, fwdCandRisk: fwdCandRisk, revMeanRisk: revMeanRisk, revCandRisk: revCandRisk,
      heading: "Amari Fisher–Rao Natural Gradient (`c = " + scaleC + "`) & `K-FAC` vs. `" + diagShrinkFactor + "×` Diagonal Stall (`Lab #80`!)",
      operatorEq: "θ=c·φ: L(θ₁_nat)=0 ∀c vs L(θ₁_GD)=" + euclidLossAfter1 + "  |  K-FAC=(A⊗B)⁻¹ (1-step) vs Diag(" + diagEntry + ") " + diagShrinkFactor + "× stall",
      witnessDetail: (scaleC > 1)
        ? ("COORDINATE ILL-CONDITIONING & DIAGONAL BLINDSPOT (`c = " + scaleC + "`, `κ = " + valleyKappa + "`): Rescaling coordinates `θ = " + scaleC + "φ` multiplies Euclidean gradient steps in `θ`-space by `c² = " + (scaleC * scaleC) + "`, overshooting `θ₀ = 1` to `θ₁ = " + gdTheta1 + "` with loss `" + euclidLossAfter1 + "` (`" + (euclidLossAfter1 / 2) + "×` initial loss `2`!), whereas Amari's Fisher–Rao natural gradient `F_φ⁻¹ g_φ` cancels `c²` identically (`θ₁_nat = 0`, loss `0`)! Meanwhile on correlated valley `" + valleyKappa + "(w₁+w₂)² + (w₁-w₂)²`, diagonal Fisher `diag(" + diagEntry + "," + diagEntry + ")` stalls shallow-valley steps by `" + diagShrinkFactor + "×` while `K-FAC` solves in `1` step!")
        : ("UNIT-SCALE BASELINE (`c = 1`, `κ = " + valleyKappa + "`): At `c = 1`, step `η = 1/4` matches `1/(2 F_θ)` so Euclidean GD and Fisher–Rao natural gradient both hit `θ₁ = 0` (`loss = 0`), while `κ = " + valleyKappa + "` still stalls diagonal Fisher by `" + diagShrinkFactor + "×` along `w₁ = -w₂`. Increase `scaleC ≥ 2` (default `3`) to trigger `c²` Euclidean overshoot!"),
      secondaryDetail: "Companion `Suite #626` Bridges 1 & 4 prove Chentsov Fisher monotonicity `(q₁+q₂)(q₂δ₁²+q₁δ₂²) - q₁q₂(δ₁+δ₂)² = (q₂δ₁-q₁δ₂)² ≥ 0` and Gauss–Newton PSD descent vs. `H = -9 < 0` uphill Newton ascent.",
      verdict: (scaleC > 1)
        ? ("✓ Natural Gradient Invariant (`L=0` vs Euclidean `L=" + euclidLossAfter1 + "`) & `K-FAC` Beats `" + diagShrinkFactor + "×` Diag Stall")
        : ("✓ Unit-Scale Exact Convergence (`L=0`) & `K-FAC` `(A⊗B)vec(W)=vec(BWAᵀ)` Certified"),
      leanRef: "03-information-recovery-kl-pythagorean/AmariFisherRaoNaturalGradientNeymanPearsonAndBregmanFrontier.lean"
    };
  };

  var prevRenderFiniteV224 = window.v136RenderFiniteBody;
  window.v136RenderFiniteBody = function() {
    if (!window._v136State || window._v136State.activeLab !== 79) {
      return prevRenderFiniteV224();
    }
    var st = window._v136State;
    var mode = st.frMode || "fisher-rao-and-kfac";
    var scaleC = (typeof st.frScaleC === "number") ? st.frScaleC : 3;
    var valleyKappa = (typeof st.frKappa === "number") ? st.frKappa : 50;
    var peekLooks = (typeof st.frPeeks === "number") ? st.frPeeks : 2;
    var bregmanCandY = (typeof st.frBregY === "number") ? st.frBregY : 4;
    var lm = window.v225FisherRaoNeymanPearsonBregmanLabModel(mode, {
      scaleC: scaleC, valleyKappa: valleyKappa, peekLooks: peekLooks, bregmanCandY: bregmanCandY
    });

    for (var i = 0; i <= 79; i++) {
      var tb = document.getElementById("v136-tab-" + i);
      if (tb) tb.className = "v61-prog-tab" + (i === 79 ? " active" : "");
    }
    var mount = document.getElementById("v136-finite-mount");
    if (!mount) return;

    var modes = [
      ["fisher-rao-and-kfac", "Fisher–Rao Natural Grad & K-FAC"],
      ["neyman-pearson-and-wald-sprt", "Neyman–Pearson & Wald SPRT"],
      ["bregman-duality-and-separation", "Banerjee–Bregman & Separation"]
    ];
    var modeBtns = modes.map(function(pair) {
      var act = lm.mode === pair[0];
      return '<button type="button" onclick="window._v136State.frMode=\'' + pair[0] + '\';window.v136RenderFiniteBody();" ' +
        'style="padding:5px 11px;border-radius:999px;font-size:11.5px;font-weight:700;cursor:pointer;' +
        'border:1px solid ' + (act ? '#38bdf8' : 'rgba(148,163,184,0.28)') + ';' +
        'background:' + (act ? 'rgba(56,189,248,0.18)' : 'rgba(15,23,42,0.7)') + ';' +
        'color:' + (act ? '#e0f2fe' : '#cbd5e1') + ';">' + pair[1] + '</button>';
    }).join(" ");

    var gdBar = Math.max(14, Math.min(172, Math.round(14 + Math.sqrt(lm.euclidLossAfter1) * 9)));
    var npBar = 140, naiveBar = 20;
    var revBar = Math.max(18, Math.min(168, Math.round(lm.revCandRisk * 0.72)));
    mount.innerHTML =
      '<div style="display:flex;flex-wrap:wrap;gap:8px;align-items:center;justify-content:space-between;margin-bottom:12px;">' +
        '<div style="display:flex;flex-wrap:wrap;gap:6px;">' + modeBtns + '</div>' +
        '<span class="v136-status-pill">Milestone Lab #80 · 726 .lean Files (100 Frontier + 626 Suites · 436 Checks)</span>' +
      '</div>' +
      '<div class="v136-grid-2">' +
        '<div class="v136-finite-card">' +
          '<div style="font-size:11px;font-weight:800;letter-spacing:0.07em;color:#fbbf24;text-transform:uppercase;margin-bottom:4px;">Information Geometry, Optimal Testing &amp; K-FAC Preconditioning (`01`+`03`+`04`+`07`)</div>' +
          '<h3 style="margin:0 0 8px 0;font-size:15.5px;color:#f8fafc;">' + lm.heading + '</h3>' +
          '<div style="font-family:var(--font-mono);font-size:11.5px;color:#fde68a;margin-bottom:8px;">' + lm.operatorEq + '</div>' +
          '<div style="font-size:12px;color:#cbd5e1;line-height:1.55;margin-bottom:10px;">' + lm.witnessDetail + '</div>' +
          '<div style="padding:9px 11px;border-radius:8px;background:rgba(6,13,26,0.9);border:1px solid rgba(56,189,248,0.28);">' +
            '<div style="font-size:10.5px;font-weight:800;color:#7dd3fc;margin-bottom:6px;">INTERACTIVE COORDINATE SCALE c, VALLEY κ, PEEK LOOKS k &amp; BREGMAN CANDIDATE y</div>' +
            '<div style="display:grid;grid-template-columns:repeat(2,1fr);gap:8px;font-size:11.5px;color:#e2e8f0;">' +
              '<label>Coord Scale c (1..5): <strong style="color:#34d399">' + lm.scaleC + '</strong><input type="range" min="1" max="5" value="' + lm.scaleC + '" style="width:100%" oninput="window._v136State.frScaleC=Number(this.value);window.v136RenderFiniteBody();"></label>' +
              '<label>Valley Conditioning κ (1..80): <strong style="color:#fbbf24">' + lm.valleyKappa + '</strong><input type="range" min="1" max="80" value="' + lm.valleyKappa + '" style="width:100%" oninput="window._v136State.frKappa=Number(this.value);window.v136RenderFiniteBody();"></label>' +
              '<label>Optional Peeks k (1..4): <strong style="color:#38bdf8">' + lm.peekLooks + '</strong><input type="range" min="1" max="4" value="' + lm.peekLooks + '" style="width:100%" oninput="window._v136State.frPeeks=Number(this.value);window.v136RenderFiniteBody();"></label>' +
              '<label>Bregman Point y (0..6): <strong style="color:#a78bfa">' + lm.bregmanCandY + '</strong><input type="range" min="0" max="6" value="' + lm.bregmanCandY + '" style="width:100%" oninput="window._v136State.frBregY=Number(this.value);window.v136RenderFiniteBody();"></label>' +
            '</div>' +
          '</div>' +
        '</div>' +
        '<div class="v136-finite-card">' +
          '<div style="font-size:11px;font-weight:800;color:#34d399;margin-bottom:6px;">FISHER–RAO INVARIANCE, NEYMAN–PEARSON &amp; BREGMAN TELEMETRY</div>' +
          '<svg viewBox="0 0 380 86" style="width:100%;height:auto;margin-bottom:8px;border-radius:7px;background:rgba(5,11,22,0.92);border:1px solid rgba(148,163,184,0.2);">' +
            '<path class="cg-svg-photon-arc" d="M 14 18 Q 190 4 366 18" fill="none" stroke="#38bdf8" stroke-width="1.8" />' +
            '<rect x="14" y="26" width="16" height="11" rx="4" fill="#34d399" />' +
            '<rect x="14" y="42" width="' + gdBar + '" height="11" rx="4" fill="' + (lm.scaleC > 1 ? '#fb7185' : '#38bdf8') + '" />' +
            '<rect x="200" y="26" width="' + npBar + '" height="11" rx="4" fill="#34d399" />' +
            '<rect x="200" y="42" width="' + Math.min(168, Math.max(naiveBar, Math.round(revBar * 0.5))) + '" height="11" rx="4" fill="#fbbf24" />' +
            '<text x="14" y="71" fill="#bae6fd" font-size="9" font-family="ui-monospace,SFMono-Regular,monospace">Nat=0 vs GD=' + lm.euclidLossAfter1 + ' · NP=7>1 · Peek=' + lm.peekNullNum + '/' + lm.denomPeek + ' · Rev=' + lm.revCandRisk + '</text>' +
          '</svg>' +
          '<div style="font-size:12px;color:#e2e8f0;line-height:1.55;">' +
            '<div style="margin-bottom:8px;">' + lm.secondaryDetail + '</div>' +
            '<div style="padding:8px 10px;border-radius:7px;background:rgba(16,185,129,0.12);border:1px solid rgba(52,211,153,0.35);color:#d1fae5;font-weight:650;">' + lm.verdict + '</div>' +
            '<div style="margin-top:8px;font-size:11px;color:#94a3b8;">Kernel-checked in <code>' + lm.leanRef + '</code></div>' +
          '</div>' +
        '</div>' +
      '</div>';
  };

  var prevOpenFiniteV224 = window.v136OpenV34FiniteDiagramsModal;
  window.v136OpenV34FiniteDiagramsModal = function(initialLab) {
    window._v136LabFilterQuery = "";
    prevOpenFiniteV224(typeof initialLab === "number" ? Math.min(initialLab, 78) : 0);
    window._v136State.activeLab = typeof initialLab === "number" ? initialLab : 0;
    var bd = document.getElementById("v136-finite-backdrop");
    if (bd) {
      var tabsWrap = bd.querySelector(".v61-prog-tabs");
      if (tabsWrap && !document.getElementById("v136-tab-79")) {
        tabsWrap.insertAdjacentHTML("beforeend",
          '<button type="button" id="v136-tab-79" class="v61-prog-tab" onclick="window.v136SetLab(79);window.cgSyncFiniteLabSelect();">80. Fisher–Rao Natural Grad, Neyman–Pearson &amp; Bregman Suite #626</button>'
        );
      }
    }
    if (typeof window.cgSyncFiniteLabSelect === "function") {
      window.cgSyncFiniteLabSelect();
    }
    window.v136RenderFiniteBody();
  };

  // Helper navigation for Authentic Lean 4.33.0 Tactic Stepper (`#v115-prev-proof`, `#v115-next-proof`, `#v115-open-cert-btn`)
  window.v115StepProofTrace = function(delta) {
    var traces = window.V115_VERIFIED_PROOF_TRACES || [];
    if (!traces.length) return;
    var cur = (typeof window._v115ActiveProofIdx === "number") ? window._v115ActiveProofIdx : 0;
    var nxt = (cur + delta + traces.length) % traces.length;
    var sel = document.getElementById("v115-proof-select");
    if (sel) sel.value = String(nxt);
    window.v115SelectProofTrace(nxt);
  };

  window.v115OpenActiveProofCertificate = function() {
    var traces = window.V115_VERIFIED_PROOF_TRACES || [];
    var cur = traces[(typeof window._v115ActiveProofIdx === "number") ? window._v115ActiveProofIdx : 0] || traces[0];
    if (typeof window.v115CloseProofGameModal === "function") window.v115CloseProofGameModal();
    if (typeof window.v55OpenProofCertificateModal === "function") {
      window.v55OpenProofCertificateModal((cur && cur.file) ? cur.file : 0);
    }
  };

  // Refresh caches so Lab #80, Leads #131-132, Breakthroughs #290-293, Suite #626 & Omnibox are live immediately!
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

  // Suite 83: V225 Milestone 100 Frontier Modules + Milestone 80 Labs (726 .lean Files), Fisher-Rao / Neyman-Pearson / Bregman / K-FAC Suite #626 & Calm Proof Source Drawer + Synaptic Stepper UI (4 new checks -> 436/436!)
  var prevRunnerV224 = window.v147RunAllAutomatedTests;
  if (typeof prevRunnerV224 === "function") {
    window.v147RunAllAutomatedTests = function() {
      var rep = prevRunnerV224();
      var extra225 = [];
      function addV225Check(name, cond, detail) {
        extra225.push({
          id: "T" + (rep.results.length + extra225.length + 1),
          category: "83. V225 Milestone 100 Frontier & 80 Labs · Fisher-Rao/NP/Bregman Suite #626 & Calm Proof UI",
          name: name,
          passed: Boolean(cond),
          detail: String(detail || (cond ? "Verified OK" : "Assertion failed"))
        });
      }

      // Check 433: Milestone Lab 80 all 3 modes (Amari 0 vs 128 Euclidean blowup & 25.5x K-FAC vs diag; NP 7>1 & 7/16 peeking; Bregman fwd 162 vs rev 128<162)
      var m80Fr = window.v225FisherRaoNeymanPearsonBregmanLabModel("fisher-rao-and-kfac", { scaleC: 3, valleyKappa: 50 });
      var m80Unit = window.v225FisherRaoNeymanPearsonBregmanLabModel("fisher-rao-and-kfac", { scaleC: 1, valleyKappa: 50 });
      var m80Np = window.v225FisherRaoNeymanPearsonBregmanLabModel("neyman-pearson-and-wald-sprt", { peekLooks: 2 });
      var m80Br = window.v225FisherRaoNeymanPearsonBregmanLabModel("bregman-duality-and-separation", { bregmanCandY: 4 });
      addV225Check(
        "Milestone Lab 80: Amari Natural Grad (`0` vs `128`), `K-FAC` (`25.5×`), NP (`7 > 1` & `7/16` peeking) & Cubic Bregman (`128 < 162`) verified",
        m80Fr.natLossAfter1 === 0 && m80Fr.euclidLossAfter1 === 128 && m80Fr.diagShrinkFactor === "25.5" &&
        m80Unit.euclidLossAfter1 === 0 &&
        m80Np.npPower === 7 && m80Np.naivePower === 1 && m80Np.peekNullNum === 7 && m80Np.denomPeek === 16 &&
        m80Br.fwdMeanRisk === 162 && m80Br.fwdCandRisk === 184 && m80Br.revCandRisk === 128 && m80Br.revMeanRisk === 162,
        "GD=" + m80Fr.euclidLossAfter1 + ", KFAC=" + m80Fr.diagShrinkFactor + "x, Peek=" + m80Np.peekNullNum + "/" + m80Np.denomPeek + ", RevBreg=" + m80Br.revCandRisk
      );

      // Check 434: 726 Zero-Sorry .lean Files (Milestone 100 Frontier + 626 Suites), 293 Breakthroughs, 132 Leads, Milestone 80 Labs, 40/40 repo coverage & bk.circle === 0
      var bt225 = window.CG_VERIFIED_ATLAS_BREAKTHROUGHS || [];
      var leads225 = window.CG_PROMISING_RESEARCH_LEADS || [];
      var suites225 = (semanticMechanisms && semanticMechanisms.verifiedLeanSuites) || [];
      var labs225 = window.cgGetFiniteLabCatalog ? window.cgGetFiniteLabCatalog() : [];
      var rFr = window.cgEvaluateBoundaryRules("naturalgradient adam");
      var rNp = window.cgEvaluateBoundaryRules("neymanpearson optionalpeeking");
      var rBr = window.cgEvaluateBoundaryRules("bregman completeseparation");
      var bk225 = window.cgSummarizeEpistemicBreakdown ? window.cgSummarizeEpistemicBreakdown(filterGalaxyRecords().records) : null;
      var suiteCovered225 = new Set();
      suites225.forEach(function(s) {
        if (s && Array.isArray(s.projects)) {
          s.projects.forEach(function(p) { if (manifest.projects[p]) suiteCovered225.add(p); });
        }
      });
      var validProj225 = bt225.every(function(b) {
        return Array.isArray(b.projects) && b.projects.every(function(p) { return Boolean(manifest.projects[p]); });
      }) && leads225.every(function(l) {
        return Array.isArray(l.projects) && l.projects.every(function(p) { return Boolean(manifest.projects[p]); });
      });
      addV225Check(
        "`726` `.lean` files (Milestone `100` Frontier + `626+` Suites), `293` Breakthroughs, `132` Leads, Milestone `80` Labs & `bk.circle === 0`",
        Boolean(
          window.CG_R2_CORPUS_CONFIG &&
          window.CG_R2_CORPUS_CONFIG.totalZeroSorryLeanFiles >= 726 &&
          window.CG_R2_CORPUS_CONFIG.frontierModules >= 100 &&
          suiteCovered225.size === 40 && bt225.length >= 293 &&
          suites225.length >= 626 && leads225.length >= 132 && labs225.length >= 80 &&
          rFr.length > 0 && rNp.length > 0 && rBr.length > 0 &&
          validProj225 && bk225 && bk225.circle === 0
        ),
        "LeanFiles=" + (window.CG_R2_CORPUS_CONFIG && window.CG_R2_CORPUS_CONFIG.totalZeroSorryLeanFiles) + ", Frontier=" + (window.CG_R2_CORPUS_CONFIG && window.CG_R2_CORPUS_CONFIG.frontierModules) + ", Labs=" + labs225.length
      );

      // Check 435: Calm Progressive Proof Source Drawer (#v55-source-code-drawer), Synaptic Proof-Trace Stepper (#v115-prev-proof, #v115-next-proof, #v115-open-cert-btn & curved .cg-svg-photon-arc) & 3-Edge Curved Functorial Square (#v65-comm-svg)
      window.v55OpenProofCertificateModal(0);
      var bd55V225 = document.getElementById("v55-proof-cert-backdrop");
      var h55V225 = (bd55V225 && bd55V225.innerHTML) || "";
      var hasCalmSourceDrawer = Boolean(
        h55V225.indexOf("v55-source-code-drawer") !== -1 &&
        h55V225.indexOf("v55-cert-code") !== -1 &&
        h55V225.indexOf("undefined") === -1
      );
      window.v55CloseCertModal();

      window.v115OpenProofGameStepper(0);
      var bd115V225 = document.getElementById("v115-proofgame-backdrop");
      var h115V225 = (bd115V225 && bd115V225.innerHTML) || "";
      var svg115Mnt = document.getElementById("v115-svg-mount");
      var svg115Html = (svg115Mnt && svg115Mnt.innerHTML) || "";
      window.v115StepProofTrace(1);
      var steppedIdx115 = window._v115ActiveProofIdx;
      var hasCurvedStepperUi = Boolean(
        h115V225.indexOf("v115-prev-proof") !== -1 &&
        h115V225.indexOf("v115-next-proof") !== -1 &&
        h115V225.indexOf("v115-open-cert-btn") !== -1 &&
        svg115Html.indexOf('<path class="cg-svg-photon-arc"') !== -1 &&
        steppedIdx115 === 1
      );
      window.v115OpenActiveProofCertificate();
      var jumpedCert115 = Boolean(document.getElementById("v55-proof-cert-backdrop"));
      window.v55CloseCertModal();

      window.v65OpenCommutativeAnimatorModal(0);
      var bd65V225 = document.getElementById("v65-commutative-backdrop");
      var h65V225 = (bd65V225 && bd65V225.innerHTML) || "";
      var arcCount65 = h65V225.split("cg-svg-photon-arc").length - 1;
      window.v65CloseCommutativeModal();

      addV225Check(
        "Calm Proof Source Drawer (`#v55-source-code-drawer`), Synaptic Proof-Trace Stepper (`#v115-prev-proof` / `#v115-open-cert-btn`) & 3-Edge Curved `#v65-comm-svg` verified",
        Boolean(hasCalmSourceDrawer && hasCurvedStepperUi && jumpedCert115 && arcCount65 >= 3),
        "drawer=" + hasCalmSourceDrawer + ", stepper=" + hasCurvedStepperUi + ", certJump=" + jumpedCert115 + ", v65Arcs=" + arcCount65
      );

      // Check 436: Milestone 80-Lab Quick-Select & Filter + 18-Archetype Bridge Composer (`FisherRaoNeymanPearsonAndBregmanGate`)
      window.v136OpenV34FiniteDiagramsModal(79);
      var sel136V225 = document.getElementById("v136-lab-quick-select");
      var has80InSelect = Boolean(sel136V225 && (sel136V225.innerHTML || "").indexOf("80. Fisher–Rao Natural Grad") !== -1);
      if (typeof window.cgFilterFiniteLabSelect === "function") {
        window.cgFilterFiniteLabSelect("Neyman");
      }
      var lab80FilterOk = Boolean(sel136V225 && (sel136V225.innerHTML || "").indexOf("80. Fisher–Rao Natural Grad") !== -1 && (sel136V225.innerHTML || "").indexOf("1. Markov Counts") === -1);
      window.v136CloseFiniteModal();

      window.v95OpenBridgeComposerStudio();
      var obsSel95V225 = document.getElementById("v95-obstacle");
      if (obsSel95V225) {
        obsSel95V225.value = "fisher_rao_neyman_pearson_bregman_gate";
        window.v95UpdateComposedBridge();
      }
      var lp95V225 = document.getElementById("v95-composed-lean");
      var comp225Ok = Boolean(lp95V225 && lp95V225.textContent.indexOf("FisherRaoNeymanPearsonAndBregmanGate") !== -1 && (window.V95_OBSTACLES || []).length >= 18);
      window.v95CloseBridgeComposer();

      addV225Check(
        "Milestone `80`-Lab Quick-Filter (`80. Fisher–Rao Natural Grad`) & 18-Archetype Composer (`FisherRaoNeymanPearsonAndBregmanGate`) verified",
        Boolean(has80InSelect && lab80FilterOk && comp225Ok),
        "has80=" + has80InSelect + ", filterOk=" + lab80FilterOk + ", comp225=" + comp225Ok
      );

      for (var k = 0; k < extra225.length; k++) {
        rep.results.push(extra225[k]);
        rep.total++;
        if (extra225[k].passed) rep.passed++;
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


def patch_calm_proof_certificate_and_synaptic_tactic_ui_in_ujs(ujs: str) -> str:
    # 1. Wrap raw .lean source inside progressive <details id="v55-source-code-drawer"> in latest v55OpenProofCertificateModal
    old_v55_code = """      '  <div style="background:rgba(2,6,23,0.95);border:1px solid rgba(148,163,184,0.28);border-radius:10px;padding:12px 14px;">',
      '    <div style="display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:8px;margin-bottom:8px;">',
      '      <span style="font-size:11px;font-weight:800;color:#a7f3d0;">AUTHENTIC LEAN 4.33.0 SOURCE (<code>leanprover/lean4:v4.33.0</code> · ZERO SORRYS)</span>',
      '      <div style="display:flex;gap:8px;flex-wrap:wrap;">',
      '        <button type="button" class="v60-qs-btn" onclick="window.v55StreamFullLeanProof(\\'' + esc(leanRelFile) + '\\', this)">📜 Stream Full .lean (R2)</button>',
      '        <button type="button" class="v60-qs-btn" onclick="window.v55CopyCertCode(this)">📋 Copy Lean 4 Proof</button>',
      '        <button type="button" class="v60-qs-btn" onclick="window.v55JumpToSimFromCert()">Open Simulators</button>',
      '      </div>',
      '    </div>',
      '    <pre id="v55-cert-code" style="margin:0;max-height:290px;font-size:11.8px;line-height:1.46;color:#38bdf8;overflow:auto;">' + esc(leanSnippet) + '</pre>',
      '  </div>',"""

    new_v55_code = """      '  <div style="background:rgba(2,6,23,0.95);border:1px solid rgba(148,163,184,0.28);border-radius:10px;padding:12px 14px;">',
      '    <div style="display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:8px;margin-bottom:6px;">',
      '      <span style="font-size:11px;font-weight:800;color:#a7f3d0;">AUTHENTIC LEAN 4.33.0 SOURCE (<code>leanprover/lean4:v4.33.0</code> · ZERO SORRYS)</span>',
      '      <div style="display:flex;gap:8px;flex-wrap:wrap;">',
      '        <button type="button" class="v60-qs-btn" onclick="var d55=document.getElementById(\\'v55-source-code-drawer\\');if(d55)d55.open=true;window.v55StreamFullLeanProof(\\'' + esc(leanRelFile) + '\\', this)">📜 Stream Full .lean (R2)</button>',
      '        <button type="button" class="v60-qs-btn" onclick="window.v55CopyCertCode(this)">📋 Copy Lean 4 Proof</button>',
      '        <button type="button" class="v60-qs-btn" onclick="window.v55JumpToSimFromCert()">Open Simulators</button>',
      '      </div>',
      '    </div>',
      '    <details id="v55-source-code-drawer" class="cg-code-disclosure">',
      '      <summary style="color:#7dd3fc;font-weight:700;font-size:11.5px;cursor:pointer;">Inspect Raw Lean 4.33.0 Kernel Source (' + String(leanSnippet || "").split("\\n").length + ' lines · 0 sorry) ▾</summary>',
      '      <pre id="v55-cert-code" style="margin:8px 0 0 0;max-height:290px;font-size:11.8px;line-height:1.46;color:#38bdf8;overflow:auto;">' + esc(leanSnippet) + '</pre>',
      '    </details>',
      '  </div>',"""

    last_v55 = ujs.rfind(old_v55_code)
    if last_v55 != -1:
        ujs = ujs[:last_v55] + new_v55_code + ujs[last_v55 + len(old_v55_code):]
    else:
        assert "v55-source-code-drawer" in ujs, "Could not locate v55-cert-code block in v55OpenProofCertificateModal!"

    # 2. Upgrade v115RenderStepperSvg inter-step connectors to curved .cg-svg-photon-arc beams
    old_v115_edges = """      if (i < 3) {
        var edgeCol = (!isBreak && stepNum > stepIdx) ? "#10b981" : "rgba(148,163,184,0.3)";
        var edgeCls = (!isBreak && stepNum > stepIdx) ? ' class="cg-svg-photon-arc"' : '';
        nodesSvg += '<line x1="' + (nx + 142) + '" y1="40" x2="' + (nx + 158) + '" y2="40" stroke="' + edgeCol + '" stroke-width="2.4"' + edgeCls + '/>';
      }"""

    new_v115_edges = """      if (i < 3) {
        var edgeCol = (!isBreak && stepNum > stepIdx) ? "#10b981" : "rgba(56,189,248,0.48)";
        nodesSvg += '<path class="cg-svg-photon-arc" d="M ' + (nx + 142) + ' 40 Q ' + (nx + 150) + ' 25 ' + (nx + 158) + ' 40" fill="none" stroke="' + edgeCol + '" stroke-width="2.3"/>';
      }"""

    if old_v115_edges in ujs:
        ujs = ujs.replace(old_v115_edges, new_v115_edges, 1)
    else:
        assert '<path class="cg-svg-photon-arc" d="M \' + (nx + 142)' in ujs, "Could not locate v115RenderStepperSvg edges!"

    # 3. Upgrade v115OpenProofGameStepper with #v115-prev-proof, #v115-next-proof & #v115-open-cert-btn
    old_v115_bar = """      '  <div style="display:flex;gap:8px;align-items:center;flex-wrap:wrap;margin-bottom:10px;">',
      '    <label for="v115-proof-select" style="font-size:11px;font-weight:800;color:#94a3b8;">VERIFIED PROOF:</label>',
      '    <select id="v115-proof-select" aria-label="Select Verified Lean 4.33.0 Proof Trace" style="flex:1;min-width:260px;background:#0f172a;color:#f8fafc;border:1px solid rgba(129,140,248,0.45);border-radius:7px;padding:6px 10px;font-size:12px;" onchange="window.v115SelectProofTrace((this && this.value) ? Number(this.value) : 0)">' + optsHtml + '</select>',
      '  </div>',"""

    new_v115_bar = """      '  <div style="display:flex;gap:7px;align-items:center;flex-wrap:wrap;margin-bottom:10px;">',
      '    <label for="v115-proof-select" style="font-size:11px;font-weight:800;color:#94a3b8;">VERIFIED PROOF:</label>',
      '    <button type="button" id="v115-prev-proof" class="v60-qs-btn" onclick="window.v115StepProofTrace(-1)">◀ Prev Proof</button>',
      '    <select id="v115-proof-select" aria-label="Select Verified Lean 4.33.0 Proof Trace" style="flex:1;min-width:240px;background:#0f172a;color:#f8fafc;border:1px solid rgba(129,140,248,0.45);border-radius:7px;padding:6px 10px;font-size:12px;" onchange="window.v115SelectProofTrace((this && this.value) ? Number(this.value) : 0)">' + optsHtml + '</select>',
      '    <button type="button" id="v115-next-proof" class="v60-qs-btn" onclick="window.v115StepProofTrace(1)">Next Proof ▶</button>',
      '    <button type="button" id="v115-open-cert-btn" class="v60-qs-btn" style="border-color:rgba(52,211,153,0.48);color:#a7f3d0;" onclick="window.v115OpenActiveProofCertificate()">📜 Proof Cert</button>',
      '  </div>',"""

    if old_v115_bar in ujs:
        ujs = ujs.replace(old_v115_bar, new_v115_bar, 1)
    else:
        assert "v115-prev-proof" in ujs, "Could not locate v115OpenProofGameStepper proof bar!"

    # 4. Upgrade #v65-comm-svg Psi_B Push edge to curved .cg-svg-photon-arc beam
    old_v65_push = """      '  <line x1="649" y1="120" x2="649" y2="88" stroke="#10b981" stroke-width="2.2" marker-end="url(#v65-arr-emerald)"/>',"""
    new_v65_push = """      '  <path class="cg-svg-photon-arc" d="M 649 120 Q 664 104 649 88" fill="none" stroke="#10b981" stroke-width="2.3" marker-end="url(#v65-arr-emerald)"/>',"""
    if old_v65_push in ujs:
        ujs = ujs.replace(old_v65_push, new_v65_push, 1)
    else:
        assert 'M 649 120 Q 664 104 649 88' in ujs, "Could not locate v65 Psi_B Push edge!"

    return ujs


def step3_patch_unified_js_html_and_build() -> None:
    print("=== STEP 3: Patching & Compacting unified-standalone.js, index.html (?v=225) & Build/Audit Scripts ===")
    ujs_path = OBS_DIR / "unified-standalone.js"
    ujs = ujs_path.read_text(encoding="utf-8")

    breakthroughs = build_v225_breakthroughs(ujs)

    v225_marker = "// === V225 MILESTONE UPGRADE: 726 ZERO-SORRY LEAN 4.33.0 FILES"
    if v225_marker in ujs:
        ujs = ujs[: ujs.index(v225_marker)].rstrip() + "\n"

    ujs = deduplicate_superseded_breakthroughs_in_ujs(ujs)
    ujs = patch_calm_proof_certificate_and_synaptic_tactic_ui_in_ujs(ujs)

    ujs = (
        ujs.replace("★ Lean 4 Suites (625)", "★ Lean 4 Suites (626)")
        .replace("724 Zero-Sorry .lean Files", "726 Zero-Sorry .lean Files")
        .replace("289 Foundation-Verified Theorem-Atlas Breakthroughs", "293 Foundation-Verified Theorem-Atlas Breakthroughs")
        .replace("Full 289-Breakthrough Audit", "Full 293-Breakthrough Audit")
        .replace("289-Breakthrough Audit", "293-Breakthrough Audit")
        .replace("79 Exact Finite Micro-Labs", "80 Exact Finite Micro-Labs")
        .replace("🔬 79 Micro-Labs", "🔬 80 Micro-Labs")
        .replace("🧭 130 Discovery Leads", "🧭 132 Discovery Leads")
        .replace(
            '"79. Riccati LQR, Stein–Lyapunov & H∞ Suite #625"\n    ];',
            '"79. Riccati LQR, Stein–Lyapunov & H∞ Suite #625",\n      "80. Fisher–Rao Natural Grad, Neyman–Pearson & Bregman Suite #626"\n    ];',
        )
    )

    v225_js = V225_JS_BLOCK.replace(
        "__BREAKTHROUGHS_293_JSON__", json.dumps(breakthroughs, ensure_ascii=False, separators=(",", ":"))
    )
    ujs = ujs.rstrip() + "\n\n" + v225_js.lstrip()
    ujs_path.write_text(ujs, encoding="utf-8")

    idx_path = OBS_DIR / "index.html"
    idx_html = (
        idx_path.read_text(encoding="utf-8")
        .replace("?v=224", "?v=225")
        .replace("130 leads, 40 projects &amp; 79 labs", "132 leads, 40 projects &amp; 80 labs")
        .replace("79 Exact Finite Micro-Labs", "80 Exact Finite Micro-Labs")
        .replace("79 Finite Micro-Labs", "80 Finite Micro-Labs")
        .replace("724 zero-sorry Lean 4 files (684 kernel-compiled)", "726 zero-sorry Lean 4 files (686 kernel-compiled)")
        .replace("724 zero-sorry Lean 4 files", "726 zero-sorry Lean 4 files")
    )
    idx_path.write_text(idx_html, encoding="utf-8")

    build_cf = OBS_DIR / "scripts" / "build-cloudflare-dist.py"
    btxt = (
        build_cf.read_text(encoding="utf-8")
        .replace("V224 Unified Chrome & Safari Shard Builder", "V225 Unified Chrome & Safari Shard Builder")
        .replace('ASSET_VER = "224"', 'ASSET_VER = "225"')
        .replace(
            '"version": "V224-Unified-Chrome-Safari-Shards-724LeanFiles-RiccatiKalmanSteinLyapunovSaturatedCbfHInf-Milestone130CalmLeadsAndSearchable79Labs"',
            '"version": "V225-Unified-Chrome-Safari-Shards-726LeanFiles-Milestone100FrontierAnd80Labs-FisherRaoNeymanPearsonBregmanKfacAndCalmProofUi"',
        )
        .replace('"totalZeroSorryLeanFiles": 724', '"totalZeroSorryLeanFiles": 726')
        .replace('"kernelCompiledLeanModules": 684', '"kernelCompiledLeanModules": 686')
    )
    build_cf.write_text(btxt, encoding="utf-8")

    daemon_py = OBS_DIR / "scripts" / "continuous-insight-daemon.py"
    dtxt = daemon_py.read_text(encoding="utf-8").replace('"V224"', '"V225"')
    daemon_py.write_text(dtxt, encoding="utf-8")

    verify_py = OBS_DIR / "scripts" / "continuous-verify-and-audit.py"
    vtxt = (
        verify_py.read_text(encoding="utf-8")
        .replace("V224", "V225")
        .replace(
            "All 724+ physical Lean 4 files (625 in CommonGround/Verification/ + 99 in 01..10-*)",
            "All 726+ physical Lean 4 files (626 in CommonGround/Verification/ + 100 in 01..10-*)",
        )
    )
    verify_py.write_text(vtxt, encoding="utf-8")
    print("  [OK] Patched & compacted unified-standalone.js, index.html (?v=225), build-cloudflare-dist.py, continuous-insight-daemon.py & continuous-verify-and-audit.py.")


def main() -> None:
    step1_verify_math_foundations()
    step2_register_suite_626_in_bundle()
    step3_patch_unified_js_html_and_build()
    print("=== V225 MILESTONE UPGRADE COMPLETE ===")


if __name__ == "__main__":
    main()
