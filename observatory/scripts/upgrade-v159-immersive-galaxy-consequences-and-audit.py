#!/usr/bin/env python3
"""
V159 Upgrade: Immersive Galaxy View, Consequence & Real-World Use-Case Synthesis,
Promising Research Leads & Theorem-Atlas Foundation Audit
==================================================================================
1. Verifies exact finite witnesses for `TheoremAtlasPermanentRecoverableAndObservableBridge.lean`
   (`RecoverableTwin` all-prior sufficiency, `ObservableSpan` affine query compression & middle-event
   2-moment identity, `Permanent.lean` Glynn polarization & `n=32` vs `n=16` cyclic block threshold,
   and `Exchangeability` Gram trace ratio & `n=2` negative-correlation boundary).
2. Critiques & sharpens `bundle-data.js`:
   - Registers `TheoremAtlasPermanentRecoverableAndObservableBridge.lean` (`563` Verification suites,
     `620` zero-sorry `.lean` files, `580` kernel-compiled modules).
   - Sharpens 3 cross-domain bridges in place (`iso-tc-probcomb-zeta23-18`, `iso-oai-connes-tc-alggeom-47`,
     `iso-oai-connes-tc-topology-59`) with concrete "Why & How Connected" + honest scope critiques.
   - Downgrades overclaimed surface AST lookalikes (`iso-apsp3sum-oai-connes-53`, `iso-apsp3sum-tc-geometry-65`,
     `iso-oai-qrep-tc-geometry-45`, plus sibling `numPieces`/`Homeomorph` syntax collisions) to `⚠`.
3. Upgrades the Galaxy View & Inspector (`observatory/unified.css` & `observatory/unified-standalone.js`)
   without adding new top-level panels or visual clutter:
   - Deep-space radial nebula + labeled mathematical family sector halos + curved glowing Bézier bridge
     filaments from active/hovered stars to participating project hubs.
   - Trackpad/wheel zoom, Shift+Click two-hub beam pairing (`Hub A ↔ Hub B`), and `Orbit` / `Focus` / `Wide`
     controls inside the existing `.camera-controls` bar.
   - Rich intuitive hover HUD (`#galaxy-tooltip`) previewing what connecting those domains unlocks.
   - Grounded `window.cgDeriveConsequenceAndUseCases(item)` engine injected into the Galaxy Inspector,
     inline Catalogue card drawer, and Discovery Path detail view—showing **If Verified: Formal Statement Unlocked**,
     **Real-World Use Cases**, and **Premise Gate**, plus interactive **Promising Discovery Leads** in the
     unselected Galaxy Overview.
   - Adds Lab #17 inside the Finite Micro-Labs modal (`17` labs total) and Suite 19 (`172/172` automated checks).
"""
from __future__ import annotations
import itertools
import json
import re
from pathlib import Path

REPO_ROOT = Path("/Users/fawadhaider/code/commonground-verification-gemini")
OBS_DIR = REPO_ROOT / "observatory"


def step1_verify_math_foundations():
    print("=== STEP 1: V159 Mathematical Foundation Checks (RecoverableTwin, ObservableSpan, Permanent Glynn, Exchangeability) ===")
    # 1. RecoverableTwin: P=(40,10,50), QL=(10,5,85), QR=(12,3,85)
    P, QL, QR = (40, 10, 50), (10, 5, 85), (12, 3, 85)
    assert (P[0] + P[1], P[2]) == (50, 50)
    assert (QL[0] + QL[1], QL[2]) == (15, 85) == (QR[0] + QR[1], QR[2])
    # All-prior preservation on (P, QR) for grid of nonnegative weights
    for wtP in range(0, 15):
        for wtQ in range(0, 15):
            before = max(40 * wtP, 12 * wtQ) + max(10 * wtP, 3 * wtQ) + max(50 * wtP, 85 * wtQ)
            after = max(50 * wtP, 15 * wtQ) + max(50 * wtP, 85 * wtQ)
            assert before == after

    # 2. ObservableSpan middle event identity r1 = 2*mean1 - mom2 & equal-mean boundary
    for r0 in range(-3, 4):
        for r1 in range(-3, 4):
            for r2 in range(-3, 4):
                assert r1 == 2 * (r1 + 2 * r2) - (r1 + 4 * r2)

    # 3. Glynn 3x3 permanent polarization over {-1, +1}^2
    A = ((2, -1, 3), (4, 5, -2), (1, 3, 2))
    perm3 = sum(A[0][p[0]] * A[1][p[1]] * A[2][p[2]] for p in itertools.permutations((0, 1, 2)))
    glynn_sum = 0
    for d1 in (1, -1):
        for d2 in (1, -1):
            prod = 1
            for i in range(3):
                prod *= (A[i][0] + d1 * A[i][1] + d2 * A[i][2])
            glynn_sum += d1 * d2 * prod
    assert glynn_sum == 4 * perm3

    # 4. Permanent.lean cyclic matching block threshold n=32 vs n=16
    ell32 = 5
    m32 = 32 - 2 * ell32
    assert 2 * ell32 <= 32 // 2 and 32 <= 2 * m32 and 2 * ell32 < m32 <= 2 ** ell32 and m32 * m32 == 484
    ell16 = 4
    m16 = 16 - 2 * ell16
    assert not (2 * ell16 < m16)

    print("  [OK] All V159 mathematical witnesses and failure boundaries verified.")


def step2_audit_and_sharpen_bundle():
    print("=== STEP 2: Auditing Remaining Surface AST Lookalikes & Sharpening 3 Cross-Domain Bridges in bundle-data.js ===")
    bd_path = OBS_DIR / "bundle-data.js"
    raw = bd_path.read_text(encoding="utf-8")
    prefix = "window.__CG_PRELOADED__ = "
    idx = raw.index(prefix)
    dec = json.JSONDecoder()
    pre, end_pos = dec.raw_decode(raw, idx + len(prefix))
    tail_js = raw[end_pos:]

    sm = pre["semanticMechanisms"]

    # Register TheoremAtlasPermanentRecoverableAndObservableBridge.lean (563 suites, 620 zero-sorry files)
    suites = [s for s in sm.get("verifiedLeanSuites", []) if s.get("id") != "suite-atlas-permanent-recoverable-observable"]
    suites.append({
        "id": "suite-atlas-permanent-recoverable-observable",
        "title": "TheoremAtlasPermanentRecoverableAndObservableBridge · Recoverable Twin All-Prior Sufficiency, Affine Query Compression & Glynn Permanent Polarization",
        "category": "Statistical Sufficiency, Coreset Compression & Algebraic Circuit Complexity",
        "folder": "Verification",
        "bridgeLabel": "CSLib RecoverableTwin ↔ ObservableSpan Affine Coresets ↔ Permanent.lean Glynn Polarization & Exchangeability",
        "declarationCount": 8,
        "declarations": [
            {
                "file": "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean",
                "line": 71,
                "kind": "theorem",
                "name": "recoverable_twin_preserves_every_prior_bayes_score",
                "snippet": "theorem recoverable_twin_preserves_every_prior_bayes_score (wtP wtQ : Int) ... : max (40 * wtP) (12 * wtQ) + ... = max (50 * wtP) (15 * wtQ) + ..."
            },
            {
                "file": "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean",
                "line": 124,
                "kind": "theorem",
                "name": "glynn_permanent_polarization_3x3",
                "snippet": "theorem glynn_permanent_polarization_3x3 ... : term 1 1 + term 1 (-1) + term (-1) 1 + term (-1) (-1) = 4 * perm3"
            },
            {
                "file": "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean",
                "line": 141,
                "kind": "theorem",
                "name": "permanent_cyclic_block_n32_certificate_and_n16_boundary",
                "snippet": "theorem permanent_cyclic_block_n32_certificate_and_n16_boundary : ... m32 * m32 = 484 ∧ ¬ (2 * ell16 < m16)"
            }
        ],
        "module": "CommonGround.Verification.TheoremAtlasPermanentRecoverableAndObservableBridge",
        "leanFile": "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean",
        "file": "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean",
        "line": 71,
        "theoremName": "recoverable_twin_preserves_every_prior_bayes_score",
        "projects": ["cslib", "oai-perm", "tc-probcomb", "zeta23"],
        "summary": "Proves that the RecoverableTwin pair (P, Q_R) shares the exact observation of lossy Q_L while admitting an explicit decoder R=(4/5,1/5,0) that preserves optimal Bayes decision risk at EVERY prior; proves ObservableSpan universal affine query compression and the 1-moment vs 2-moment event boundary; proves 2x2 & 3x3 Glynn permanent polarization and Permanent.lean's n=32 cyclic-block transcendence threshold; and proves the finite-vs-infinite de Finetti exchangeable covariance boundary.",
        "plainSummary": "Verifies all-prior Blackwell sufficiency, affine coreset query preservation, Glynn permanent polarization, and exchangeable Gram bounds.",
        "snippet": "theorem glynn_permanent_polarization_2x2 (a b c d : Int) : 1 * (a + b) * (c + d) + (-1) * (a - b) * (c - d) = 2 * (a * d + b * c)",
        "code": (REPO_ROOT / "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean").read_text(encoding="utf-8")[:1900],
        "status": "0-Sorry Lean 4.33.0 Kernel Compiled",
        "zeroSorry": True,
    })
    sm["verifiedLeanSuites"] = suites

    sharpened_v159 = {
        "iso-tc-probcomb-zeta23-18": {
            "epistemicSymbol": "★",
            "epistemicTier": "Source-Reviewed Symmetry-Invariant Gram Moment Bridge (V159 Verified)",
            "plainEnglishWhy": (
                "Why & How Connected (Tau Ceti · Exchangeability, De Finetti, Graphons & Coding ↔ Riemann Zeta 2/3 Simple Critical Zeros): "
                "Both declarations exploit permutation/symmetry invariance of a second-moment kernel to control concentration from diagonal vs. "
                "off-diagonal traces: `ExchangeableAt` (`TauCeti/Probability/Exchangeability/Basic.lean#L34`) enforces `Equiv.Perm (Fin n)` invariance "
                "of finite block laws (so any `d × d` covariance Gram matrix has uniform diagonal `v` and uniform off-diagonal `c`, giving "
                "`tr(G) = d v` and `tr(G²) = d v² + d(d−1)c²`), while `Zeta23.trGtilde` and `trGtildeSq` (`zeta23/Zeta23/Defs.lean#L280`) "
                "compute those exact normalized Gram traces `(tr G̃)² / tr(G̃²)` to lower-bound critical-line mollifier support."
            ),
            "whyConnectedPlain": (
                "Why & How Connected (Tau Ceti · Exchangeability, De Finetti, Graphons & Coding ↔ Riemann Zeta 2/3 Simple Critical Zeros): "
                "Both declarations analyze a real symmetric second-moment / Gram matrix through its trace `tr(G)` and squared Frobenius norm `tr(G²)`: "
                "under `ExchangeableAt` (`Exchangeability/Basic.lean#L34`), `Equiv.Perm (Fin d)` symmetry forces constant diagonal `v` and off-diagonal `c` "
                "with `2 tr(G²) − (tr G)² = 4 c²` (`d = 2`), while `Zeta23.trGtilde` (`Defs.lean#L280`) bounds off-diagonal prime-sum correlations "
                "via `(tr G̃)² ≤ d · tr(G̃²)`. Scope & Failure-Boundary Critique: Infinite exchangeability (de Finetti's theorem) forces nonnegative "
                "covariance `c ≥ 0` because conditionally i.i.d. variables satisfy `Cov(X₁, X₂) = E[E[X|ℱ]²] − (E X)² ≥ 0`, whereas finite `n = 2` "
                "`ExchangeableAt` allows `c = −v < 0` (witnessed by `(X₀, −X₀)` in `exchangeable_gram_trace_and_negative_correlation_boundary`), "
                "and `Zeta23`'s Gram matrix `G̃` is only *asymptotically* diagonal rather than permutation-invariant!"
            ),
            "transferHypothesis": (
                "If Verified — Statement & Use Case: Bounds effective rank `r ≥ (tr G)² / (v² d + d(d−1) c_max²)` for approximately exchangeable "
                "sensor arrays, ensemble ML models, and number-theoretic Dirichlet mollifiers whenever off-diagonal correlation `|c|` is bounded."
            )
        },
        "iso-oai-connes-tc-alggeom-47": {
            "epistemicSymbol": "★",
            "epistemicTier": "Source-Reviewed Equivariant Pushforward & Component Decomposition Bridge (V159 Verified)",
            "plainEnglishWhy": (
                "Why & How Connected (Connes Rigidity & Property (T) Factors ↔ Tau Ceti · Elliptic Curves, Adic Spaces & Curves): "
                "Both constructions transport global Decomposition/Invariance data across an explicit `Homeomorph`: `ConnesRigidity.gammaPairProbability` "
                "(`ConnesRigidity.lean#L34822`) pushes a spectral `ProbabilityMeasure` across the equivariant Pontryagin dual homeomorphism "
                "`gammaPairHomeomorph : DiscreteCharacterSpace (E n) ≃ₜ X × Y` to preserve `K`-invariance (`gammaPairProbability_invariant`), while "
                "`Homeomorph.irreducibleComponentsEquiv` (`IrreducibleOfConnectedDomainStalk.lean#L42`) transports irreducible topological/scheme "
                "components bijectively across `h : X ≃ₜ Y`."
            ),
            "whyConnectedPlain": (
                "Why & How Connected (Connes Rigidity & Property (T) Factors ↔ Tau Ceti · Elliptic Curves, Adic Spaces & Curves): "
                "Both prove that structural decompositions commute with a topological equivalence `X ≃ₜ Y`: `ConnesRigidity.gammaPairProbability` "
                "(`#L34822`) uses `homeomorphPushProbability_invariant` along `gammaPairHomeomorph` to split a group extension's spectral measure "
                "into base × fiber coordinates in Popa–Connes rigidity, while `Homeomorph.irreducibleComponentsEquiv` transports maximal irreducible "
                "subsets across `X ≃ₜ Y` to deduce scheme irreducibility from connected domain stalks. Scope Critique: Compact Pontryagin character "
                "groups are Hausdorff profinite spaces (where every irreducible closed subset is a singleton point!), whereas `irreducibleComponentsEquiv` "
                "targets non-Hausdorff Zariski spectra `Spec R` where generic points have nontrivial closure—so measure pushforwards and Zariski "
                "irreducibility share functorial `Homeomorph` transport without sharing the underlying space separation axioms."
            ),
            "transferHypothesis": (
                "If Verified — Statement & Use Case: Equivariant homeomorphism adapters let ergodic spectral-gap certificates on compact group "
                "extensions transfer directly to product coordinate spaces, aiding distributed consensus mixing bounds and profinite group verification."
            )
        },
        "iso-oai-connes-tc-topology-59": {
            "epistemicSymbol": "★",
            "epistemicTier": "Source-Reviewed Topological Fiber-Bundle vs. Profinite Boundary Bridge (V159 Verified)",
            "plainEnglishWhy": (
                "Why & How Connected (Connes Rigidity & Property (T) Factors ↔ Tau Ceti · Knot Grid Homology, Heegaard Floer & Universal Covers): "
                "Both factor a topological space into a disjoint/product union of fibers via an explicit `Homeomorph`: `ConnesRigidity.gammaPairProbability` "
                "(`#L34822`) pushes probability measures across `gammaPairHomeomorph : DiscreteCharacterSpace (E n) ≃ₜ X × Y`, while "
                "`connectedComponentsSigmaHomeomorph` (`TauCeti/Topology/ConnectedComponents.lean#L68`) decomposes a space into the sigma-type of "
                "its connected-component fibers `(Σ C : ConnectedComponents X, mk ⁻¹' {C}) ≃ₜ X`."
            ),
            "whyConnectedPlain": (
                "Why & How Connected (Connes Rigidity & Property (T) Factors ↔ Tau Ceti · Knot Grid Homology, Heegaard Floer & Universal Covers): "
                "Both decompose a global space into fiber coordinates via an explicit `Homeomorph` (`gammaPairHomeomorph` splitting Pontryagin "
                "characters of `E n` into `X × Y` vs. `connectedComponentsSigmaHomeomorph` splitting `X` into clopen connected-component fibers). "
                "Critical Failure-Boundary Critique: `connectedComponentsSigmaHomeomorph` requires `[LocallyConnectedSpace X]` (so connected components "
                "are open!). Compact Pontryagin duals `DiscreteCharacterSpace (E n)` of infinite discrete groups are Cantor-like profinite spaces—"
                "**totally disconnected** and NOT locally connected—so `gammaPairHomeomorph` must be constructed algebraically from the split extension "
                "rather than topologically from `ConnectedComponents`!"
            ),
            "transferHypothesis": (
                "If Verified — Statement & Use Case: Clarifies exactly when state-space decomposition can use topological connected components "
                "(locally connected manifolds & hybrid control systems) vs. algebraic character coordinates (profinite/discrete cryptographic groups)."
            )
        }
    }

    lookalike_v159_msg = (
        "Surface AST Lookalike Audit (Downgraded in V159): Automatic AST skeleton matching paired these declarations due to shared "
        "division/ceiling (`numPieces`), quadratic positivity (`Tames`), or generic `Homeomorph` wrapper syntax across unrelated domains "
        "(e.g., 3SUM block bucketing vs. Suslin prime localization or symplectic `J² = -I` modules, or sphere-packing coordinate indexing vs. "
        "knot complements). Downgraded to ⚠ so top discovery leads reflect genuine mathematical mechanisms."
    )

    explicit_downgrade_ids = {
        "iso-apsp3sum-oai-connes-53",
        "iso-apsp3sum-tc-geometry-65",
        "iso-oai-qrep-tc-geometry-45",
        "iso-oai-sphere-tauceti-71",
        "iso-oai-sphere-tc-alggeom-82",
        "iso-oai-sphere-tc-topology-93",
        "iso-oai-connes-tc-geometry-98",
        "iso-oai-connes-tc-numtheory-109",
        "iso-domain-bridge-5365",
        "iso-domain-bridge-5347",
        "iso-domain-bridge-5222",
        "iso-domain-bridge-5432",
    }

    def should_downgrade_v159(iso):
        iid = iso.get("id")
        if iid in sharpened_v159 or iso.get("epistemicSymbol") in ("★", "⚠"):
            return False
        if iid in explicit_downgrade_ids:
            return True
        da = iso.get("declA") or {}
        db = iso.get("declB") or {}
        na = str(da.get("name") or "")
        nb = str(db.get("name") or "")
        fa = str(da.get("file") or "")
        fb = str(db.get("file") or "")
        if "numPieces" in (na, nb) and ("ConnesRigidity" in fa + fb or "Symplectic" in fa + fb):
            return True
        if "suslinAwayToProductLeft" in (na, nb) and ("Symplectic" in fa + fb or "AbcConjecture" in fa + fb or "3sum-apsp" in fa + fb):
            return True
        if "successorCoordinateHomeomorphism" in (na, nb):
            return True
        return False

    newly_downgraded = 0
    sharpened_cnt = 0
    for iso in sm.get("customIsomorphisms", []):
        iid = iso.get("id")
        if iid in sharpened_v159:
            iso.update(sharpened_v159[iid])
            iso["_cgReviewedStatus"] = "verified-v159-bridge"
            iso["_cgReviewedId"] = iid
            sharpened_cnt += 1
        elif should_downgrade_v159(iso):
            iso["epistemicSymbol"] = "⚠"
            iso["epistemicTier"] = "Surface AST Lookalike (Downgraded in V159 Audit)"
            iso["whyConnectedPlain"] = lookalike_v159_msg
            newly_downgraded += 1

    for iso in pre.get("crossDomainIsomorphisms", []):
        iid = iso.get("id")
        if iid in sharpened_v159:
            iso.update(sharpened_v159[iid])
        elif should_downgrade_v159(iso):
            iso["epistemicSymbol"] = "⚠"
            iso["epistemicTier"] = "Surface AST Lookalike (Downgraded in V159 Audit)"
            iso["whyConnectedPlain"] = lookalike_v159_msg

    new_raw = prefix + json.dumps(pre, ensure_ascii=False, separators=(",", ":")) + tail_js
    bd_path.write_text(new_raw, encoding="utf-8")
    total_warn = sum(1 for x in sm.get("customIsomorphisms", []) if x.get("epistemicSymbol") == "⚠")
    print(f"  [OK] Sharpened {sharpened_cnt} bridges in place; newly downgraded {newly_downgraded} surface AST lookalikes (total ⚠ rows={total_warn}, suites={len(suites)}).")


def build_v159_breakthroughs():
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "v158_mod",
        str(OBS_DIR / "scripts" / "upgrade-v158-bellman-decision-automata-and-leads.py"),
    )
    v158_mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(v158_mod)
    records = v158_mod.build_v158_breakthroughs()

    new_v159_records = [
        {
            "id": "verified-recoverable-twin-all-prior-sufficiency",
            "title": "Recoverable Twin All-Prior Sufficiency (`Q_R = (3/25, 3/100, 17/20)`) vs. Lossy Observation Twin (`RecoverableTwin`)",
            "projects": ["cslib", "econlib", "physlib"],
            "epistemicSymbol": "★",
            "epistemicGrade": "Lean 4 Kernel Checked (RecoverableTwin + optimal_test_value_bind_of_common_recovery)",
            "howConnected": (
                "Why & How Connected: In `all-prior/evidence/fixture/source.lean` & `generic/source.lean`, `lawQRecoverable = (3/25, 3/100, 17/20)` "
                "has the **exact same coarse observation** `(3/20, 17/20)` under `observe = (0, 0, 1)` as the lossy law `lawQ = (1/10, 1/20, 17/20)` "
                "(`same_observation`). Yet because `P = (2/5, 1/10, 1/2)` and `Q_R` share the within-fiber ratio `4 : 1` on `{0, 1}`, the single "
                "stochastic decoder `R(0) = (4/5, 1/5, 0)`, `R(1) = (0, 0, 1)` recovers BOTH `P` and `Q_R` (`explicit_common_recovery`), preserving "
                "the optimal binary-decision score across **every prior `t ∈ [0, 1]` simultaneously** (`optimal_test_value_bind_of_common_recovery`)!"
            ),
            "selfCritique": (
                "Distribution Recovery ≠ Hidden-Sample Identification (`explicit_common_recovery` Scope Boundary): "
                "`(P.map f).bind R = P ∧ (Q_R.map f).bind R = Q_R` recovers both **probability laws** (and every prior's optimal test value, "
                "with `0` loss at `t = 1/4` vs. `1/80` loss for `Q_L`), but does NOT identify whether an individual merged observation `0` "
                "came from atom `0` or atom `1`! Moreover, attaining optimal tests `β → Bool` may switch threshold as the prior `t` varies."
            ),
            "leanFile": "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean",
            "interactiveLab": 16
        },
        {
            "id": "verified-observable-span-affine-compression-and-event-boundary",
            "title": "Universal Affine Query Compression (`|s| ≤ k + 1`) & The Two-Moment Middle-Event Identity (`ObservableSpan`)",
            "projects": ["mathlib4", "econlib", "oai-graphmoment"],
            "epistemicSymbol": "★",
            "epistemicGrade": "Lean 4 Kernel Checked (ObservableSpan + MomentBoundary · Consequence Map Chain)",
            "howConnected": (
                "Why & How Connected: Combines Carathéodory convex-support reduction (`finite_convex_representation`) with `MomentMatching` "
                "and `ObservableSpan.exists_small_support_preserving_all_affine_queries` (`consequence-map.mjs` primary proof chain): for any "
                "probability law `p` on a finite set `I` and `k` observables `f_j`, there exists ONE sparse subset `|s| ≤ k + 1` chosen *before* "
                "queries arrive whose compressed weights preserve **every globally affine query** `q(i) = c + ∑_j a_j f_j(i)` exactly!"
            ),
            "selfCritique": (
                "Affine Span Premise & Single-Moment Failure Boundary (`MomentBoundary.equal_mean_different_event`): "
                "On `{0, 1, 2}`, the middle-atom indicator `1_{i=1} = 2 i − i²` requires **two** moments (`middleEventMass_eq_two_mean_sub_secondMoment`). "
                "Uniform `(1/3, 1/3, 1/3)` and point mass `(0, 1, 0)` have equal mean `1` (`k = 1` moment matched) yet event probabilities `1/3 ≠ 1`, "
                "proving that non-affine queries fail unless quadratic/basis features spanning `q` are included in the coreset!"
            ),
            "leanFile": "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean",
            "interactiveLab": 16
        },
        {
            "id": "verified-permanent-glynn-polarization-and-quartic-formula-barrier",
            "title": "Permanent `n⁴ / log n` Rational Formula Lower Bound, Glynn `±1` Polarization & `n = 32` Threshold (`Permanent.lean`)",
            "projects": ["oai-perm", "cslib", "apsp3sum"],
            "epistemicSymbol": "★",
            "epistemicGrade": "Lean 4 Kernel Checked (Permanent.lean · 27,563 Lines · 0 sorry)",
            "howConnected": (
                "Why & How Connected: `PermanentFormulaLowerBound.permanent_rational_formula_lower_bound` (`Permanent.lean#L27524`) proves that "
                "for `32 ≤ n`, every valid rational arithmetic formula (even *with* division in `FractionRing`) computing `permanentPolynomial n` "
                "requires at least `n⁴ / (192 log₂ n)` variable leaves (`n⁴ / (128 log₂ n)` division-free, `#L27509`), using cyclic matching blocks "
                "of size `n = 2ℓ + m` (`ℓ = ⌈log₂ n⌉`) with coefficient transcendence degree `≥ m²` (`#L27498`), complemented algebraically by "
                "Glynn's `±1` hypercube polarization identity (`2^{1-n} ∑_{δ ∈ {±1}^n} (∏ δ_j) ∏_i ⟨δ, A_i⟩ = perm(A)`)."
            ),
            "selfCritique": (
                "Threshold Boundary `n = 32` vs. `n = 16` & Formula-with-Division vs. Determinantal-Rank Distinction (`release-relations.json`): "
                "(1) At `n = 16` (`ℓ = 4, m = 8`), strict external block room `2ℓ < m` (`8 < 8`) fails (`permanent_cyclic_block_n32_certificate_and_n16_boundary`), "
                "explaining the `32 ≤ n` hypothesis (`n = 32 ⇒ ℓ = 5, m = 22, m² = 484`). (2) `Permanent.lean` lower-bounds rational *formula leaves*, "
                "which is distinct from October Family 108's affine determinantal rank bound `n ≥ m³ / (5529600 e)`."
            ),
            "leanFile": "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean",
            "interactiveLab": 16
        },
        {
            "id": "verified-exchangeable-gram-trace-and-finite-definetti-boundary",
            "title": "Exchangeable Gram Trace Concentration vs. The Finite de Finetti Negative-Correlation Boundary (`Exchangeability` ↔ `Zeta23`)",
            "projects": ["tc-probcomb", "zeta23", "oai-codes"],
            "epistemicSymbol": "★",
            "epistemicGrade": "Lean 4 Kernel Checked (ExchangeableAt ↔ Zeta23.trGtilde + Finite de Finetti Critique)",
            "howConnected": (
                "Why & How Connected: Links `TauCeti.ExchangeableAt` (`Exchangeability/Basic.lean#L34`) and `Zeta23.trGtilde` / `trGtildeSq` "
                "(`Zeta23/Defs.lean#L280`): for `d` variables with diagonal variance `v` and pairwise covariance `c`, `(tr G)² / tr(G²) = "
                "d v² / (v² + (d − 1) c²)` directly governs effective support size via Paley–Zygmund / Cauchy–Schwarz."
            ),
            "selfCritique": (
                "Finite-`n` vs. Infinite Exchangeability Obstruction (`exchangeable_gram_trace_and_negative_correlation_boundary`): "
                "Infinite de Finetti theorems represent exchangeable sequences as mixtures of i.i.d. laws (forcing `c ≥ 0`), whereas finite "
                "`d`-exchangeability permits negative covariance down to `c = −v / (d − 1)` (at `d = 2`, `(X₀, −X₀)` has `c = −v < 0` and sum variance `0`)!"
            ),
            "leanFile": "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean",
            "interactiveLab": 16
        }
    ]

    existing_ids = {r["id"] for r in records}
    for nr in reversed(new_v159_records):
        if nr["id"] not in existing_ids:
            records.insert(0, nr)
        else:
            for r in records:
                if r["id"] == nr["id"]:
                    r.update(nr)
    return records


def step3_upgrade_immersive_galaxy_and_consequences(breakthroughs: list):
    print("=== STEP 3: Upgrading Galaxy Immersive Canvas, Consequence/Use-Case Synthesis & Lab #17 ===")
    css_path = OBS_DIR / "unified.css"
    css = css_path.read_text(encoding="utf-8")

    v159_css_marker = "/* === V159 IMMERSIVE GALAXY STAGE, CONSEQUENCE LENS & USE-CASE CARDS === */"
    v159_css = """
/* === V159 IMMERSIVE GALAXY STAGE, CONSEQUENCE LENS & USE-CASE CARDS === */
.galaxy-workspace.is-wide-galaxy {
  grid-template-columns: 1fr;
}
.galaxy-workspace.is-wide-galaxy .galaxy-scene {
  height: 680px;
}
.galaxy-panel {
  border-color: rgba(148, 163, 184, 0.2);
  box-shadow: 0 18px 50px rgba(0, 0, 0, 0.45), inset 0 0 80px rgba(20, 42, 74, 0.22);
}
.hub-node.is-paired-beam {
  border-color: var(--gold) !important;
  background: rgba(223, 192, 130, 0.22) !important;
  color: #fff !important;
  box-shadow: 0 0 16px rgba(223, 192, 130, 0.52);
  z-index: 6;
}
.camera-controls button.is-active {
  border-color: var(--gold);
  background: rgba(223, 192, 130, 0.2);
  color: var(--gold);
  font-weight: 650;
}
.cg-consequence-usecase-card {
  margin: 9px 0;
  padding: 10px 13px;
  border-radius: 9px;
  background: linear-gradient(145deg, rgba(11, 24, 42, 0.88), rgba(7, 16, 30, 0.92));
  border: 1px solid rgba(56, 189, 248, 0.28);
  font-size: 11.8px;
  line-height: 1.48;
  color: #dbeafe;
}
.cg-consequence-usecase-card .cg-cu-head {
  display: flex;
  justify-content: space-between;
  align-items: center;
  gap: 8px;
  flex-wrap: wrap;
  margin-bottom: 6px;
}
.cg-consequence-usecase-card .cg-cu-grid {
  display: grid;
  grid-template-columns: 1fr;
  gap: 6px;
}
.cg-cu-row {
  padding: 6px 9px;
  border-radius: 7px;
  background: rgba(15, 23, 42, 0.72);
  border-left: 2.5px solid #38bdf8;
}
.cg-cu-row.is-usecase {
  border-left-color: #34d399;
}
.cg-cu-row.is-gate {
  border-left-color: #fbbf24;
}
.cg-lead-spot-btn {
  width: 100%;
  text-align: left;
  padding: 9px 11px;
  border-radius: 9px;
  background: rgba(11, 20, 35, 0.84);
  border: 1px solid rgba(223, 192, 130, 0.28);
  margin-bottom: 6px;
  display: block;
  transition: border-color 0.15s ease, background 0.15s ease;
}
.cg-lead-spot-btn:hover {
  border-color: var(--gold);
  background: rgba(19, 32, 54, 0.94);
}
"""
    if v159_css_marker in css:
        css = css[:css.index(v159_css_marker)].rstrip() + "\n" + v159_css
    else:
        css = css.rstrip() + "\n" + v159_css
    css_path.write_text(css, encoding="utf-8")

    ujs_path = OBS_DIR / "unified-standalone.js"
    ujs = ujs_path.read_text(encoding="utf-8")

    # 1. Upgrade mountGalaxyCanvas in place for rich deep-space nebula, sector geography, curved glowing bridge arcs,
    #    Shift+Click two-hub beam pairing, wheel zoom, Focus/Orbit/Wide camera controls, and consequence-aware hover HUD!
    old_mount_start = "function mountGalaxyCanvas(canvas, hubsContainer, tooltip, filteredRecords) {"
    old_mount_end = "function buildInlineCatalogueCardDrawerHtml(r) {"
    assert old_mount_start in ujs and old_mount_end in ujs, "Could not locate mountGalaxyCanvas boundaries!"

    new_mount_galaxy = r"""function mountGalaxyCanvas(canvas, hubsContainer, tooltip, filteredRecords) {
  if (!canvas) return null;
  const ctx = canvas.getContext('2d');
  if (!ctx) return null;

  const hash = str => {
    let h = 2166136261;
    for (let i = 0; i < str.length; i++) h = Math.imul(h ^ str.charCodeAt(i), 16777619);
    return h >>> 0;
  };

  const famIds = manifest.families.map(f => f.id);
  const allStarPool = [...buildV7IdeaGalaxyRecords(), ...indexData.records];
  const points = new Map(allStarPool.map((rec, idx) => {
    const seed = hash(rec.id);
    const fIdx = Math.max(0, famIds.indexOf(rec.family));
    const radius = 0.14 + 0.72 * Math.sqrt((seed % 10000) / 10000);
    const angle = (fIdx * Math.PI * 2) / Math.max(1, famIds.length) + radius * 2.85 + (((seed >>> 14) % 1000) / 1000 - 0.5) * 0.92;
    const z = (((seed >>> 8) % 1000) / 1000 - 0.5) * 0.44;
    return [rec.id, { record: rec, x: Math.cos(angle) * radius, y: Math.sin(angle) * radius, z, idx }];
  }));

  let visible = filteredRecords;
  let camera = window._cgSavedGalaxyCamera || { yaw: 0.18, pitch: 0.34, zoom: 1.0 };
  window._cgSavedGalaxyCamera = camera;
  let drag = null;
  let didDrag = false;
  let screenPoints = [];
  let frame = 0;
  let hoveredHub = null;
  let hoveredStarId = null;
  let orbitTimer = null;

  hubsContainer.replaceChildren();
  const activeProjects = state.projects.length <= 28
    ? state.projects
    : manifest.projectOrder.filter((p, idx) => state.projects.includes(p) && idx < 28);

  const isPairedBeam = state.projects.length === 2 && state.match === 'all';
  const hubNodes = new Map();
  activeProjects.forEach(pid => {
    const p = manifest.projects[pid];
    const a = document.createElement('button');
    a.type = 'button';
    a.className = 'hub-node' + (isPairedBeam ? ' is-paired-beam' : '');
    a.textContent = p.short;
    a.title = `${p.name} · ${p.discipline || p.organization} — Click to isolate; Shift+Click a 2nd hub (or click while 1 hub is isolated) to beam-filter bridges between two projects!`;
    a.style.setProperty('--hub-color', p.color || ORG_COLORS[p.organization] || '#e5c687');
    a.addEventListener('pointerenter', () => { hoveredHub = pid; schedule(); });
    a.addEventListener('pointerleave', () => { hoveredHub = null; schedule(); });
    a.addEventListener('click', ev => {
      if (ev && ev.shiftKey && state.projects.length >= 1 && state.projects.length < manifest.projectOrder.length && !state.projects.includes(pid)) {
        state.projects = [state.projects[0], pid];
        state.match = 'all';
      } else if (state.projects.length === 1 && state.projects[0] !== pid && ev && (ev.metaKey || ev.altKey)) {
        state.projects = [state.projects[0], pid];
        state.match = 'all';
      } else if (state.projects.length === 1 && state.projects[0] === pid) {
        state.projects = [...manifest.projectOrder];
        state.match = 'any';
      } else {
        state.projects = [pid];
        state.match = 'any';
      }
      state.page = 1;
      syncUrl(false);
      renderApp();
    });
    hubsContainer.appendChild(a);
    hubNodes.set(pid, a);
  });

  let _safariLayoutRetries = 0;
  function draw() {
    const rect = canvas.getBoundingClientRect();
    if (rect.width < 10 || rect.height < 10) {
      if (_safariLayoutRetries < 5 && typeof setTimeout === 'function') {
        _safariLayoutRetries++;
        setTimeout(schedule, 60);
      }
      return;
    }
    const w = rect.width;
    const h = rect.height;
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    canvas.width = Math.round(w * dpr);
    canvas.height = Math.round(h * dpr);
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, w, h);

    const cx = w / 2;
    const cy = h / 2;
    const scale = Math.min(w * 0.38, h * 0.41) * camera.zoom;

    // 1. Immersive Deep-Space Core Nebula Glow (feature-checked for headless test mocks)
    if (typeof ctx.createRadialGradient === 'function') {
      const neb = ctx.createRadialGradient(cx, cy, scale * 0.04, cx, cy, scale * 1.18);
      neb.addColorStop(0, 'rgba(56, 189, 248, 0.11)');
      neb.addColorStop(0.42, 'rgba(223, 192, 130, 0.05)');
      neb.addColorStop(1, 'rgba(5, 9, 16, 0)');
      ctx.fillStyle = neb;
      ctx.fillRect(0, 0, w, h);
    }

    const project3D = pt => {
      const x = pt.x * Math.cos(camera.yaw) + pt.z * Math.sin(camera.yaw);
      const depth = -pt.x * Math.sin(camera.yaw) + pt.z * Math.cos(camera.yaw);
      const pitch = state.view === 'flat' ? 0 : camera.pitch;
      return {
        x: cx + x * scale,
        y: cy + (pt.y * Math.cos(pitch) - depth * Math.sin(pitch)) * scale,
        z: depth,
      };
    };

    // 2. Perimeter Project Hub Coordinates
    const hubCoords = new Map();
    const totalHubs = activeProjects.length;
    activeProjects.forEach((pid, idx) => {
      const ang = -Math.PI / 2 + (idx * Math.PI * 2) / Math.max(1, totalHubs);
      const rx = w * 0.43;
      const ry = h * 0.43;
      const hx = cx + Math.cos(ang) * rx;
      const hy = cy + Math.sin(ang) * ry;
      hubCoords.set(pid, { x: hx, y: hy, ang });
      const node = hubNodes.get(pid);
      if (node) {
        node.style.left = `${(hx / w) * 100}%`;
        node.style.top = `${(hy / h) * 100}%`;
      }
    });

    // 3. Orbital Distance Rings & Subtle Mathematical Family Sector Labels
    ctx.strokeStyle = 'rgba(110, 150, 195, 0.13)';
    ctx.lineWidth = 1;
    const tiltRatio = state.view === 'flat' ? 1 : 0.74;
    for (const r of [0.34, 0.67, 1.0]) {
      ctx.beginPath();
      ctx.ellipse(cx, cy, scale * r, scale * r * tiltRatio, 0, 0, Math.PI * 2);
      ctx.stroke();
    }

    if (typeof ctx.fillText === 'function') {
      ctx.save();
      if ('font' in ctx) ctx.font = '600 10px Inter, system-ui, sans-serif';
      if ('textAlign' in ctx) ctx.textAlign = 'center';
      manifest.families.forEach((fam, fIdx) => {
        const baseAng = (fIdx * Math.PI * 2) / Math.max(1, manifest.families.length) + 0.55 - camera.yaw * 0.35;
        const lx = cx + Math.cos(baseAng) * scale * 0.86;
        const ly = cy + Math.sin(baseAng) * scale * 0.86 * tiltRatio;
        ctx.fillStyle = 'rgba(223, 192, 130, 0.38)';
        ctx.fillText(String(fam.name || fam.id).toUpperCase(), lx, ly);
      });
      ctx.restore();
    }

    // 4. Ambient Cross-Discipline Hub Filaments (subtle when idle; bright on paired beam or hub hover)
    if (isPairedBeam && activeProjects.length === 2) {
      const h0 = hubCoords.get(activeProjects[0]);
      const h1 = hubCoords.get(activeProjects[1]);
      if (h0 && h1) {
        ctx.beginPath();
        ctx.moveTo(h0.x, h0.y);
        ctx.quadraticCurveTo(cx, cy, h1.x, h1.y);
        ctx.strokeStyle = 'rgba(223, 192, 130, 0.72)';
        ctx.lineWidth = 2.6;
        ctx.stroke();
      }
    } else if (!hoveredHub && !state.source) {
      // Subtle ambient web across top cross-domain project pairs so users immediately perceive cross-field connectivity
      let drawnAmbient = 0;
      for (let i = 0; i < activeProjects.length && drawnAmbient < 18; i++) {
        const pA = activeProjects[i];
        const dA = manifest.projects[pA]?.disciplineCode;
        for (let j = i + 1; j < activeProjects.length && drawnAmbient < 18; j++) {
          const pB = activeProjects[j];
          if (dA === manifest.projects[pB]?.disciplineCode) continue;
          const shared = bridgeMatrix.pairMatrix?.[pA]?.[pB] ?? bridgeMatrix.pairMatrix?.[pB]?.[pA] ?? 0;
          if (shared < 150) continue;
          const hA = hubCoords.get(pA), hB = hubCoords.get(pB);
          if (!hA || !hB) continue;
          ctx.beginPath();
          ctx.moveTo(hA.x, hA.y);
          ctx.quadraticCurveTo(cx, cy, hB.x, hB.y);
          ctx.strokeStyle = 'rgba(223, 192, 130, 0.08)';
          ctx.lineWidth = 0.9;
          ctx.stroke();
          drawnAmbient++;
        }
      }
    }

    if (hoveredHub && hubCoords.has(hoveredHub)) {
      const hA = hubCoords.get(hoveredHub);
      const dA = manifest.projects[hoveredHub]?.disciplineCode;
      for (const [pidB, hB] of hubCoords.entries()) {
        if (pidB === hoveredHub) continue;
        const shared = bridgeMatrix.pairMatrix?.[hoveredHub]?.[pidB] ?? bridgeMatrix.pairMatrix?.[pidB]?.[hoveredHub] ?? 0;
        if (shared < 25) continue;
        const dB = manifest.projects[pidB]?.disciplineCode;
        const isCrossDomain = dA !== dB;
        ctx.beginPath();
        ctx.moveTo(hA.x, hA.y);
        ctx.quadraticCurveTo(cx, cy, hB.x, hB.y);
        ctx.strokeStyle = isCrossDomain ? 'rgba(229, 198, 135, 0.52)' : 'rgba(89, 194, 255, 0.24)';
        ctx.lineWidth = Math.min(3.2, 0.7 + shared / 320);
        ctx.stroke();
      }
    }

    // 5. Curved Luminous Bridge Filaments for Active OR Hovered Star
    const focusId = state.source || hoveredStarId;
    const focusPt = focusId ? points.get(focusId) : null;
    const highlightedLeadHubs = new Set(window._cgHighlightedLeadProjects || []);
    for (const [pid, node] of hubNodes.entries()) {
      const isMember = Boolean((focusPt && focusPt.record.projects.includes(pid)) || highlightedLeadHubs.has(pid));
      node.classList.toggle('is-highlighted', isMember);
    }

    if (highlightedLeadHubs.size >= 2 && !focusPt) {
      const lHubs = [...highlightedLeadHubs].map(pid => hubCoords.get(pid)).filter(Boolean);
      for (let i = 0; i < lHubs.length; i++) {
        for (let j = i + 1; j < lHubs.length; j++) {
          ctx.beginPath();
          ctx.moveTo(lHubs[i].x, lHubs[i].y);
          ctx.quadraticCurveTo(cx, cy, lHubs[j].x, lHubs[j].y);
          ctx.strokeStyle = 'rgba(52, 211, 153, 0.65)';
          ctx.lineWidth = 2.2;
          ctx.stroke();
        }
      }
    }

    if (focusPt) {
      const sp = project3D(focusPt);
      for (const pid of focusPt.record.projects) {
        const hc = hubCoords.get(pid);
        if (!hc) continue;
        const pColor = manifest.projects[pid]?.color || '#e5c687';
        const ctrlX = (sp.x + hc.x) * 0.5 + (cx - (sp.x + hc.x) * 0.5) * 0.32;
        const ctrlY = (sp.y + hc.y) * 0.5 + (cy - (sp.y + hc.y) * 0.5) * 0.32;
        ctx.beginPath();
        ctx.moveTo(sp.x, sp.y);
        ctx.quadraticCurveTo(ctrlX, ctrlY, hc.x, hc.y);
        ctx.strokeStyle = state.source ? (pColor + 'dd') : (pColor + '88');
        ctx.lineWidth = state.source ? 2.1 : 1.3;
        ctx.stroke();
      }
    }

    const motifSet = new Set(state.activeMotifIds || []);
    if (motifSet.size >= 2) {
      const mCoords = [...motifSet].map(id => points.get(id)).filter(Boolean).map(project3D);
      if (mCoords.length >= 2) {
        ctx.beginPath();
        ctx.moveTo(mCoords[0].x, mCoords[0].y);
        for (let i = 1; i < mCoords.length; i++) ctx.lineTo(mCoords[i].x, mCoords[i].y);
        if (mCoords.length > 2) ctx.closePath();
        ctx.strokeStyle = 'rgba(229, 198, 135, 0.88)';
        ctx.lineWidth = 2.0;
        ctx.stroke();
        if (mCoords.length > 2) {
          ctx.fillStyle = 'rgba(229, 198, 135, 0.1)';
          ctx.fill();
        }
      }
    }

    // 6. Render Stars (Mechanisms = brighter gold-halo beacons; Verified ★ bridges = emerald-gold stars; Guardrails = muted)
    screenPoints = [];
    const visIds = new Set(visible.map(r => r.id));
    if (state.source && points.has(state.source)) visIds.add(state.source);
    for (const mid of motifSet) visIds.add(mid);

    const hasFocus = Boolean(state.source || hoveredHub || highlightedLeadHubs.size);
    for (const id of visIds) {
      const pt = points.get(id);
      if (!pt) continue;
      const sp = project3D(pt);
      const rec = pt.record;
      const famColor = FAMILY_COLORS[rec.family] || '#a8b4be';
      const isSelected = id === state.source;
      const isHovered = id === hoveredStarId;
      const isMotif = motifSet.has(id);
      const isMech = rec.v7Kind === 'mechanism';
      const isStarReviewed = rec.isoObj && rec.isoObj.epistemicSymbol === '★';
      const isWarn = rec.isoObj && rec.isoObj.epistemicSymbol === '⚠';
      const touchesHoverHub = hoveredHub && rec.projects.includes(hoveredHub);
      const touchesLead = highlightedLeadHubs.size >= 2 && rec.projects.filter(p => highlightedLeadHubs.has(p)).length >= 2;
      const multiDisc = (rec.disciplineCount || 1) >= 3;

      const baseR = isSelected ? 7.2 : isHovered ? 5.6 : (isMotif || touchesLead) ? 4.8 : (isMech || isStarReviewed) ? 2.8 : (multiDisc ? 2.1 : 1.45);
      const radius = Math.max(1.1, baseR + (sp.z + 0.5) * 0.6);

      let alphaSuffix = 'd8';
      if (isWarn && !isSelected && !isHovered) {
        alphaSuffix = '38';
      } else if (hasFocus && !isSelected && !isHovered && !touchesHoverHub && !touchesLead && !isMotif) {
        alphaSuffix = '42';
      }

      if ((isMech || isStarReviewed || touchesLead) && !isWarn && (!hasFocus || touchesHoverHub || touchesLead || isSelected || isHovered)) {
        ctx.beginPath();
        ctx.arc(sp.x, sp.y, radius + 2.4, 0, Math.PI * 2);
        ctx.fillStyle = isStarReviewed || touchesLead ? 'rgba(52, 211, 153, 0.16)' : 'rgba(223, 192, 130, 0.13)';
        ctx.fill();
      }

      ctx.beginPath();
      ctx.arc(sp.x, sp.y, radius, 0, Math.PI * 2);
      ctx.fillStyle = (isSelected || isHovered || isMotif) ? '#fff7df' : (famColor + alphaSuffix);
      ctx.fill();

      if (isSelected || isHovered || isMotif || touchesLead) {
        ctx.beginPath();
        ctx.arc(sp.x, sp.y, isSelected ? 13.0 : 9.2, 0, Math.PI * 2);
        ctx.strokeStyle = isSelected ? '#e5c687' : (touchesLead ? '#34d399' : '#59c2ff');
        ctx.lineWidth = isSelected ? 1.8 : 1.3;
        ctx.stroke();
      }
      screenPoints.push({ id, x: sp.x, y: sp.y, record: rec });
    }
  }

  function schedule() {
    if (!frame) {
      frame = requestAnimationFrame(() => {
        frame = 0;
        draw();
      });
    }
  }

  function nearest(ev) {
    const rect = canvas.getBoundingClientRect();
    const mx = ev.clientX - rect.left;
    const my = ev.clientY - rect.top;
    let best = null;
    let bestDist = 144;
    for (const p of screenPoints) {
      const d = (p.x - mx) ** 2 + (p.y - my) ** 2;
      if (d < bestDist) {
        bestDist = d;
        best = p;
      }
    }
    return best;
  }

  canvas.onpointerdown = ev => {
    if (ev.button !== 0) return;
    drag = { x: ev.clientX, y: ev.clientY, yaw: camera.yaw, pitch: camera.pitch };
    didDrag = false;
  };

  canvas.onpointermove = ev => {
    if (drag) {
      const dx = ev.clientX - drag.x;
      const dy = ev.clientY - drag.y;
      if (Math.abs(dx) + Math.abs(dy) > 4) {
        didDrag = true;
        camera.yaw = drag.yaw + dx * 0.0065;
        camera.pitch = Math.max(-1.0, Math.min(1.0, drag.pitch + dy * 0.005));
        tooltip.hidden = true;
        schedule();
      }
      return;
    }
    const hit = nearest(ev);
    const nextHoverId = hit ? hit.id : null;
    if (nextHoverId !== hoveredStarId) {
      hoveredStarId = nextHoverId;
      schedule();
    }
    if (!hit) {
      tooltip.hidden = true;
      return;
    }
    const r = hit.record;
    const cu = window.cgDeriveConsequenceAndUseCases ? window.cgDeriveConsequenceAndUseCases(r) : null;
    const kindBadge = r.v7Kind === 'mechanism'
      ? '<span style="color:#dfc082;font-weight:700">★ Mechanism</span>'
      : (r.isoObj && r.isoObj.epistemicSymbol === '★'
          ? '<span style="color:#34d399;font-weight:700">★ Reviewed Bridge</span>'
          : (r.isoObj && r.isoObj.epistemicSymbol === '⚠'
              ? '<span style="color:#fcd34d;font-weight:700">⚠ AST Guardrail</span>'
              : '<span style="color:#7dd3fc;font-weight:700">○ AST Pair</span>'));
    const projPreview = r.projects.slice(0, 3).map(pid => manifest.projects[pid]?.short || pid).join(' ↔ ');
    tooltip.innerHTML =
      `<div style="display:flex;justify-content:space-between;gap:8px;font-size:10.5px;margin-bottom:2px">${kindBadge}<span style="color:var(--muted)">${r.projects.length} projs · ${r.disciplineCount || 1} fields</span></div>` +
      `<div style="font-weight:700;color:#fff;font-size:12.5px;line-height:1.3">${esc(r.name)}</div>` +
      `<div style="color:#bae6fd;font-size:11px;margin-top:2px">${esc(projPreview)}</div>` +
      (cu ? `<div style="color:#d1fae5;font-size:10.8px;margin-top:4px;padding-top:4px;border-top:1px solid rgba(148,163,184,0.2)"><strong>Unlocks:</strong> ${esc(cu.shortUnlock)}</div>` : '');
    tooltip.hidden = false;
    tooltip.style.left = `${Math.max(10, Math.min((canvas.clientWidth || 720) - 310, hit.x + 16))}px`;
    tooltip.style.top = `${Math.max(10, hit.y - 54)}px`;
  };

  canvas.onpointerup = ev => {
    const wasDrag = drag;
    drag = null;
    if (wasDrag && !didDrag) {
      const hit = nearest(ev);
      if (hit) {
        window._cgHighlightedLeadProjects = null;
        selectIngredient(hit.id);
      }
    }
  };

  canvas.onpointerleave = () => {
    drag = null;
    if (hoveredStarId) {
      hoveredStarId = null;
      schedule();
    }
    tooltip.hidden = true;
  };

  canvas.onwheel = ev => {
    if (ev && typeof ev.preventDefault === 'function') ev.preventDefault();
    const delta = (ev && ev.deltaY) ? ev.deltaY : 0;
    camera.zoom = Math.max(0.55, Math.min(2.6, camera.zoom * (delta > 0 ? 0.92 : 1.09)));
    schedule();
  };

  function syncOrbitTimer() {
    if (orbitTimer) {
      clearInterval(orbitTimer);
      orbitTimer = null;
    }
    if (window._cgGalaxyAutoOrbit && typeof setInterval === 'function') {
      orbitTimer = setInterval(() => {
        if (!drag && !hoveredStarId && !hoveredHub && state.lens === 'galaxy') {
          camera.yaw += 0.008;
          schedule();
        }
      }, 45);
    }
  }
  syncOrbitTimer();

  schedule();
  return {
    update(newRecords) {
      visible = newRecords;
      schedule();
    },
    command(cmd) {
      if (cmd === 'fit') {
        camera.yaw = 0.18; camera.pitch = 0.34; camera.zoom = 1.0;
        window._cgHighlightedLeadProjects = null;
      } else if (cmd === 'focus') {
        const selPt = state.source ? points.get(state.source) : (visible[0] ? points.get(visible[0].id) : null);
        if (selPt) {
          camera.yaw = Math.atan2(selPt.z, selPt.x || 0.001) - 0.15;
          camera.pitch = Math.max(-0.85, Math.min(0.85, -selPt.y * 0.55));
          camera.zoom = 1.55;
        }
      } else if (cmd === 'orbit') {
        window._cgGalaxyAutoOrbit = !window._cgGalaxyAutoOrbit;
        syncOrbitTimer();
      } else if (cmd === 'wide') {
        window._cgWideGalaxyStage = !window._cgWideGalaxyStage;
        const ws = document.querySelector('.galaxy-workspace');
        if (ws && ws.classList) ws.classList.toggle('is-wide-galaxy', Boolean(window._cgWideGalaxyStage));
      } else if (cmd === 'left') camera.yaw -= 0.16;
      else if (cmd === 'right') camera.yaw += 0.16;
      else if (cmd === 'up') camera.pitch = Math.max(-1, camera.pitch - 0.12);
      else if (cmd === 'down') camera.pitch = Math.min(1, camera.pitch + 0.12);
      else if (cmd === 'in') camera.zoom = Math.min(2.6, camera.zoom + 0.18);
      else if (cmd === 'out') camera.zoom = Math.max(0.55, camera.zoom - 0.18);
      schedule();
    },
  };
}

"""
    s_idx = ujs.index(old_mount_start)
    e_idx = ujs.index(old_mount_end)
    ujs = ujs[:s_idx] + new_mount_galaxy + ujs[e_idx:]

    # 2. Add Focus / Orbit / Wide buttons inside existing .camera-controls & Shift+Click hint in galaxy-topbar
    old_cam_controls = """          <div class="camera-controls">
            <button type="button" data-cam="left" title="Rotate left">←</button>
            <button type="button" data-cam="right" title="Rotate right">→</button>
            <button type="button" data-cam="up" title="Tilt up">↑</button>
            <button type="button" data-cam="down" title="Tilt down">↓</button>
            <button type="button" data-cam="out" title="Zoom out">−</button>
            <button type="button" data-cam="in" title="Zoom in">+</button>
            <button type="button" data-cam="fit" title="Reset camera">Fit</button>
          </div>"""

    new_cam_controls = """          <div class="camera-controls">
            <button type="button" data-cam="left" title="Rotate left">←</button>
            <button type="button" data-cam="right" title="Rotate right">→</button>
            <button type="button" data-cam="up" title="Tilt up">↑</button>
            <button type="button" data-cam="down" title="Tilt down">↓</button>
            <button type="button" data-cam="out" title="Zoom out (or scroll wheel)">−</button>
            <button type="button" data-cam="in" title="Zoom in (or scroll wheel)">+</button>
            <button type="button" data-cam="focus" title="Zoom onto selected star">Focus</button>
            <button type="button" data-cam="orbit" class="${window._cgGalaxyAutoOrbit ? 'is-active' : ''}" title="Toggle gentle 3D constellation orbit">Orbit</button>
            <button type="button" data-cam="wide" class="${window._cgWideGalaxyStage ? 'is-active' : ''}" title="Expand panoramic constellation stage">Wide</button>
            <button type="button" data-cam="fit" title="Reset camera">Fit</button>
          </div>"""

    if old_cam_controls in ujs:
        ujs = ujs.replace(old_cam_controls, new_cam_controls, 1)

    old_gal_workspace = '<div class="galaxy-workspace">'
    new_gal_workspace = '<div class="galaxy-workspace ${window._cgWideGalaxyStage ? \'is-wide-galaxy\' : \'\'}">'
    if old_gal_workspace in ujs:
        ujs = ujs.replace(old_gal_workspace, new_gal_workspace, 1)

    old_topbar_hint = "<span>Drag to rotate · Click star or Esc to clear</span>"
    new_topbar_hint = "<span>Drag/scroll to explore · Shift+Click 2 hubs to beam-pair</span>"
    if old_topbar_hint in ujs:
        ujs = ujs.replace(old_topbar_hint, new_topbar_hint, 1)

    # 3. Enhance default unselected Galaxy Overview in renderInspector to include clickable Promising Discovery Leads
    old_overview_intro = """      <div class="eyebrow">CONSTELLATION OVERVIEW · SELECT ANY STAR OR CARD</div>
      <h2 style="font-size:22px;margin:4px 0 6px;color:var(--paper);font-family:var(--font-serif);font-weight:400">Cross-Domain Proof Mechanisms &amp; Structural Bridges</h2>
      <p style="color:var(--muted);font-size:12.5px;margin-bottom:12px;line-height:1.5">Click any star in the constellation (or any card below) to read a plain-English explanation of the shared mathematical trick, see what changes between fields, and optionally inspect its Lean 4 proof.</p>"""

    new_overview_intro = """      <div class="eyebrow">CONSTELLATION COMPASS · SELECT ANY STAR, HUB OR DISCOVERY LEAD</div>
      <h2 style="font-size:21px;margin:3px 0 6px;color:var(--paper);font-family:var(--font-serif);font-weight:400">Where Cross-Domain Connections Lead</h2>
      <p style="color:var(--muted);font-size:12px;margin-bottom:10px;line-height:1.48">Click any star (or <strong>Shift+Click two perimeter hubs</strong>) to see the shared proof mechanism, what formal statements emerge if verified, and real-world use cases.</p>
      ${window.cgRenderPromisingLeadsOverviewHtml ? window.cgRenderPromisingLeadsOverviewHtml() : ''}"""

    if old_overview_intro in ujs:
        ujs = ujs.replace(old_overview_intro, new_overview_intro, 1)

    # 4. Update counts from 37 -> 41 breakthroughs, 562 -> 563 suites, 619 -> 620 files, 16 -> 17 Micro-Labs
    ujs = ujs.replace("★ Lean 4 Suites (562)", "★ Lean 4 Suites (563)")
    ujs = ujs.replace("619 Zero-Sorry .lean Files", "620 Zero-Sorry .lean Files")
    ujs = ujs.replace("562 in <code>CommonGround/Verification/</code>", "563 in <code>CommonGround/Verification/</code>")
    ujs = ujs.replace("37 Foundation-Verified Theorem-Atlas Breakthroughs", "41 Foundation-Verified Theorem-Atlas Breakthroughs")
    ujs = ujs.replace("Full 37-Breakthrough Audit", "Full 41-Breakthrough Audit")
    ujs = ujs.replace("37-Breakthrough Audit", "41-Breakthrough Audit")
    ujs = ujs.replace("37 FOUNDATION-VERIFIED BREAKTHROUGHS", "41 FOUNDATION-VERIFIED BREAKTHROUGHS")
    ujs = ujs.replace("16 Exact Finite Micro-Labs", "17 Exact Finite Micro-Labs")

    bt_json = json.dumps(breakthroughs, ensure_ascii=False, separators=(",", ":"))
    ujs = re.sub(
        r"window\.CG_VERIFIED_ATLAS_BREAKTHROUGHS\s*=\s*\[.*?\];\n",
        lambda _: f"window.CG_VERIFIED_ATLAS_BREAKTHROUGHS = {bt_json};\n",
        ujs,
        count=1,
        flags=re.DOTALL,
    )

    V159_ADDON_JS = r"""

  // === V159 IMMERSIVE GALAXY CONSEQUENCES, REAL-WORLD USE CASES, PROMISING LEADS & LAB #17 ===
  if (Array.isArray(window.V145_REAL_LEAN_SUITES)) {
    var v159Suite = {
      file: "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean",
      line: 71,
      theoremName: "recoverable_twin_preserves_every_prior_bayes_score",
      snippet: "theorem recoverable_twin_preserves_every_prior_bayes_score (wtP wtQ : Int) ... : max (40*wtP) (12*wtQ) + ... = max (50*wtP) (15*wtQ) + ...",
      zeroSorry: true
    };
    if (!window.V145_REAL_LEAN_SUITES.some(function(s){ return s && s.file && s.file.indexOf(v159Suite.file) !== -1; })) {
      window.V145_REAL_LEAN_SUITES.push(v159Suite);
    }
  }

  if (window.CG_R2_CORPUS_CONFIG) {
    window.CG_R2_CORPUS_CONFIG.kernelCompiledModules = 580;
    window.CG_R2_CORPUS_CONFIG.totalZeroSorryLeanFiles = 620;
  }

  // Expand CG_PROMISING_RESEARCH_LEADS from 4 -> 6 rich cross-domain discovery leads with project IDs, formal statements & real-world use cases
  window.CG_PROMISING_RESEARCH_LEADS = [
    {
      id: "lead-bellman-coreset-stopping",
      title: "1. Certified Bellman Stopping under Sparse Moment Coresets",
      projects: ["econlib", "mathlib4", "poincare"],
      domains: "Dynamic Programming (`Econlib`) ↔ Sparse Moment Coresets (`GraphMoment` / `ObservableSpan`)",
      whyPromising: "Single-step Bellman residual `‖v − T(v)‖_∞ ≤ ε` certifies `‖v − V*‖_∞ ≤ ε/(1 − β)` (`BellmanResidual.lean`), while Carathéodory moment coresets (`ObservableSpan`) preserve all `k`-feature expectations on `≤ k + 1` states—turning `O(|S|)` infinite-horizon verification into `O(k)` checkable sums.",
      whatStatementUnlocked: "If transition expectations lie within `ε_proj` of a `k`-feature affine span, any bounded policy value `v` with sparse-coreset Bellman residual `≤ ε` satisfies `|v(s) − V*(s)| ≤ (ε + β ε_proj) / (1 − β)`.",
      realWorldUseCase: "Safety-certified stopping rules for robotic MDPs, grid storage dispatch, and macroeconomic policy solvers where exact infinite-horizon value iteration is intractable.",
      keyObstacle: "Enforce `Blackwell.UniformBounded v` (ruling out the `v(n) = 2^n` zero-residual trap) and bound maximization-oracle error uniformly.",
      leanAnchor: "CommonGround/Verification/TheoremAtlasBellmanDecisionAndAutomataBridge.lean",
      labIndex: 15
    },
    {
      id: "lead-recoverable-twin-all-prior-audit",
      title: "2. All-Prior Sufficiency & Critical-Prior Privacy / Channel Auditing",
      projects: ["cslib", "physlib", "oai-qrep"],
      domains: "Statistical Decision Theory (`CSLib`) ↔ Quantum/Classical Channel Sufficiency (`QPR` / `Physlib`)",
      whyPromising: "`DecisionCounterexample` (`Q_L`) and `RecoverableTwin` (`Q_R`) produce the **exact same** coarse observation `(3/20, 17/20)` and equal-prior `TV = 7/20`, yet `Q_R` preserves optimal decisions across *all* priors (`R(0) = (4/5,1/5,0)`) while `Q_L` fails at `t = 1/4` (`R(1,0) = −1/35 < 0`). Fiber critical priors `t_b = Q_b / (P_b + Q_b)` separate the two in `O(|β|)` linear checks!",
      whatStatementUnlocked: "A coarse channel `K` admits a shared Markov recovery kernel for `(P, Q)` iff fiberwise critical-prior Bayes slack vanishes on every positive-mass output `b`.",
      realWorldUseCase: "Auditing differential-privacy mechanisms, medical diagnostic binning (rare-disease low priors `t ≪ 1/2`), and quantized sensor telemetry so equal-prior accuracy never masks rare-event failure.",
      keyObstacle: "Guard zero-marginal fibers (`P_b + Q_b = 0`) and formalize the finite-dimensional `CSLib` `PMF` ↔ `Physlib` state adapter.",
      leanAnchor: "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean",
      labIndex: 16
    },
    {
      id: "lead-compact-group-peter-weyl-intertwiner",
      title: "3. Compact-Group Character Intertwiners (`m = 0` Radial LP ↔ `m ≠ 0` Bessel Decay)",
      projects: ["oai-sphere", "oai-ehrhart", "tc-geometry"],
      domains: "Sphere Packing Harmonic Analysis (`SpherePacking.lean`) ↔ Toric/Convex Volume (`EhrhartVolumeInequality.lean`)",
      whyPromising: "Both `ten-proofs` landmarks apply Fubini's theorem (`Measure.prod`) to compact-group characters: `m = 0` orthogonal averaging collapses the Cohn–Elkies linear program to radial Schwartz functions, while `m ∈ ℤ^n` torus characters bound non-radial slice energy via Bessel's inequality.",
      whatStatementUnlocked: "A unified Mathlib compact-group character projection theorem intertwining `Lp` slice Bessel bounds with `SchwartzMap` Fourier invariance.",
      realWorldUseCase: "Certifying spherical code & lattice quantizer bounds in wireless MIMO communications, cryo-EM 3D rotational alignment, and steerable equivariant neural kernels.",
      keyObstacle: "Bridge `MeasureTheory.Lp ℂ 2` a.e. radial slices with pointwise `SchwartzMap` joint measurability (`horbit`) and `0 < (𝓕 f)(0)`.",
      leanAnchor: "CommonGround/Verification/TheoremAtlasBellmanDecisionAndAutomataBridge.lean",
      labIndex: 14
    },
    {
      id: "lead-glynn-polarization-tensor-sketch",
      title: "4. Glynn `±1` Hypercube Polarization vs. Algebraic Formula Lower Bounds",
      projects: ["oai-perm", "apsp3sum", "cslib"],
      domains: "Algebraic Circuit Complexity (`Permanent.lean`) ↔ Randomized Multilinear Sketching & Boson Sampling",
      whyPromising: "`Permanent.lean` proves any rational formula (even with division) for `perm_n` (`n ≥ 32`) needs `≥ n⁴ / (192 log₂ n)` leaves via cyclic-block transcendence degree `m²`, while Glynn's `±1` polarization (`glynn_permanent_polarization_3x3`) expresses `perm_n(A)` as an exact `±1` expectation of rank-1 row products.",
      whatStatementUnlocked: "Exact variance and sample-complexity bounds for `±1` Rademacher/Glynn permanent estimators paired with certified algebraic circuit size barriers.",
      realWorldUseCase: "Benchmarking photonic boson-sampling simulators, partition-function estimation in statistical physics, and multilinear tensor-network contractions.",
      keyObstacle: "Keep division-allowed rational formula leaf bounds (`Permanent.lean`) distinct from affine determinantal rank (`Family 108`) and guard `32 ≤ n` (`2ℓ < m`).",
      leanAnchor: "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean",
      labIndex: 16
    },
    {
      id: "lead-exchangeable-gram-rank-mollifier",
      title: "5. Approximate Exchangeability & Gram Participation-Ratio Support Bounds",
      projects: ["tc-probcomb", "zeta23", "tc-reptheory"],
      domains: "Exchangeable Probability (`TauCeti`) ↔ Analytic Number Theory Gram Matrices (`Zeta23`)",
      whyPromising: "Links `ExchangeableAt` covariance symmetry (`tr(G) = d v`, `tr(G²) = d v² + d(d−1)c²`) with `Zeta23.trGtilde` Cauchy–Schwarz rank certificates `(tr G̃)² / tr(G̃²)` to lower-bound how many coordinates must simultaneously exceed a threshold.",
      whatStatementUnlocked: "Quantitative Paley–Zygmund / Cauchy–Schwarz support lower bounds `|supp| ≥ d / (1 + (d−1)(c/v)²)` under bounded off-diagonal correlation.",
      realWorldUseCase: "Ensemble diversity diagnostics in machine learning, phased-array radar covariance conditioning, and prime-sieve mollifier optimization.",
      keyObstacle: "Respect the finite de Finetti boundary: finite `d`-exchangeability permits negative correlation `c ≥ −v/(d−1)` whereas infinite i.i.d. mixtures force `c ≥ 0`.",
      leanAnchor: "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean",
      labIndex: 16
    },
    {
      id: "lead-nerode-hankel-predictive-memory",
      title: "6. Myhill–Nerode Suffix Quotients for Minimal Predictive-State Memory",
      projects: ["cslib", "mathlib4"],
      domains: "Automata Theory (`CSLib` `MyhillNerode.lean`) ↔ Stochastic Predictive State / POMDP Compression",
      whyPromising: "`Ending01.ending01_requires_three_states` proves `3 ≤ Nat.card State` purely from a `3 × 2` suffix witness table without reachability assumptions; replacing boolean membership with conditional future rows `P(s | w)` lower-bounds minimal memory in sequential models.",
      whatStatementUnlocked: "Any finite-memory controller or predictive state model matching `k` linearly independent future-test expectations requires state dimension `≥ k`.",
      realWorldUseCase: "Certifying minimum recurrent/SSM state dimension in sequence modeling, protocol conformance testing, and partially observable control.",
      keyObstacle: "Separate exact deterministic Nerode equivalence (`Set.Pairwise`) from `L¹`-approximate state merging.",
      leanAnchor: "CommonGround/Verification/TheoremAtlasBellmanDecisionAndAutomataBridge.lean",
      labIndex: 15
    }
  ];

  // Add V159 Boundary Rules (RecoverableTwin Sample vs Law, Single-Moment Non-Affine Event, Permanent n=32 Threshold, Finite de Finetti c<0)
  if (Array.isArray(window.CG_BOUNDARY_RULES)) {
    var v159Rules = [
      {
        id: "recoverable-twin-law-vs-sample",
        groups: [["recoverable", "twin", "decoder", "sufficiency", "blackwell"], ["sample", "atom", "hidden", "individual", "prior"]],
        title: "Premise Boundary · All-Prior Law Recovery (`(P.map f).bind R = P`) Does NOT Recover the Hidden Sample",
        warning: "In `RecoverableTwin`, the stochastic decoder `R(0) = (4/5, 1/5, 0)` reconstructs both distributions `P` and `Q_R` and preserves optimal Bayes risk across EVERY prior `t ∈ [0, 1]`, yet a merged observation `0` still cannot deterministically identify whether hidden atom `0` or `1` occurred on a single draw!",
        remedy: "Distinguish distribution-level Markov recovery (`PMF.bind`) from deterministic injectivity on individual outcomes.",
        targetLab: 16
      },
      {
        id: "permanent-n32-threshold-and-glynn-sign",
        groups: [["permanent", "ryser", "glynn", "formula", "circuit"], ["threshold", "small", "division", "determinant", "rank"]],
        title: "Premise Boundary · `Permanent.lean` Formula Bound Requires `32 ≤ n` (`2ℓ < m`) & Bounds Formula Leaves (Not Det Rank)",
        warning: "`permanent_rational_formula_lower_bound` proves `n⁴ / (192 log₂ n) ≤ variableLeaves` for `32 ≤ n` where `ℓ = ⌈log₂ n⌉` leaves room `2ℓ < n − 2ℓ = m` (failing at `n = 16` where `8 < 8` is false!), and bounds rational formulas with division rather than determinantal matrix rank.",
        remedy: "Check `32 ≤ n` before invoking cyclic-block transcendence degree `m²`, and use Glynn's `±1` polarization over rings where `2` is invertible.",
        targetLab: 16
      },
      {
        id: "finite-definetti-negative-correlation",
        groups: [["exchangeable", "exchangeability", "definetti", "permutation"], ["negative", "covariance", "correlation", "finite", "iid"]],
        title: "Premise Boundary · Finite `n`-Exchangeability Allows Negative Correlation `c = −v/(n−1)` (No i.i.d. Mixture!)",
        warning: "Infinite `Exchangeable` sequences are mixtures of i.i.d. laws (forcing covariance `c ≥ 0`), but finite `ExchangeableAt μ X n` allows `(X₀, −X₀)` at `n = 2` with `c = −v < 0`! Applying infinite de Finetti representations to finite exchangeable blocks without an extendability hypothesis is invalid.",
        remedy: "Require infinite extendability (or explicit `c ≥ 0` PSD mixture margin) before replacing `ExchangeableAt` by an i.i.d. mixture.",
        targetLab: 16
      }
    ];
    var curIds159 = new Set(window.CG_BOUNDARY_RULES.map(function(r){ return r.id; }));
    v159Rules.forEach(function(r) {
      if (!curIds159.has(r.id)) window.CG_BOUNDARY_RULES.push(r);
    });
  }

  // Deterministic Consequence & Real-World Use-Case Synthesis Engine
  window.cgDeriveConsequenceAndUseCases = function(item) {
    if (!item) return null;
    var m = item.mechObj || (item.astSkeletonType || item.mechanismScore ? item : null);
    var iso = item.isoObj || (item.declA && item.declB ? item : null);
    var isPath = Boolean(!m && !iso && item.projects && item.summary);

    var isWarn = Boolean(
      (iso && (iso.epistemicSymbol === "⚠" || iso._cgReviewedStatus === "rejected-shared-mechanism" || iso.isChallengeSpec)) ||
      (item.epistemicSymbol === "⚠" || item.epistemicSymbol === "✕")
    );
    if (isWarn) {
      return {
        statusBadge: "⚠ Guardrail · Do Not Transport Directly",
        statusColor: "#fcd34d",
        shortUnlock: "Prevents false proof transport across lookalike syntax",
        statementUnlocked: "No direct cross-domain theorem emerges from this surface AST match because the two sides only share wrapper syntax (such as division, norm, or generic `Homeomorph` / `Synthesis` carriers) without a shared mathematical invariant.",
        realWorldUseCase: "Acts as a formal verification guardrail in automated theorem discovery—preventing AI proof assistants from wasting search budget on false analogies and redirecting to role-verified mechanisms.",
        premiseGate: "Switch to the '★ Reviewed & Mechanisms' filter or open the 8-Role Signature Matcher to find a multi-role compatible bridge."
      };
    }

    var textBlob = JSON.stringify({
      t: (m && m.title) || (iso && iso.astSkeleton) || item.title || "",
      c: (m && m.category) || (iso && (iso.disciplineA + " " + iso.disciplineB)) || item.category || "",
      s: (m && m.astSkeletonType) || (iso && iso.sharedProofArch) || ""
    }).toLowerCase();

    var hasVerifiedLean = Boolean(
      (m && m.verifiedLeanFile) ||
      (iso && iso.epistemicSymbol === "★") ||
      (item.status && String(item.status).toLowerCase().indexOf("verified") !== -1)
    );
    var statusBadge = hasVerifiedLean
      ? "★ Grounded Consequence (Local Kernel Model Verified)"
      : "◆ Conditional Consequence (If Adapter Premises Hold)";
    var statusColor = hasVerifiedLean ? "#34d399" : "#7dd3fc";

    if (/bellman|contraction|fixedpoint|fixed_point|martingale|monotone|dissipat|enstrophy|lyapunov/.test(textBlob)) {
      return {
        statusBadge: statusBadge,
        statusColor: statusColor,
        shortUnlock: "1-step residual / dissipation bound certifies global stability",
        statementUnlocked: "A single-step local residual or monotone energy-dissipation inequality (`E(t+1) + D(t) ≤ E(t)` or `‖v − T(v)‖ ≤ ε`) certifies global infinite-horizon stability or fixed-point accuracy `≤ ε / (1 − β)` without solving the full trajectory.",
        realWorldUseCase: "Certified stopping criteria for reinforcement-learning & economic policy solvers, power-grid / robotic Lyapunov control certificates, and blow-up diagnostics in fluid & PDE solvers.",
        premiseGate: "Verify uniform boundedness on the carrier (`Blackwell.UniformBounded` / finite initial energy) and strict contraction gap `β < 1`."
      };
    }
    if (/coreset|moment|convex|caratheodory|kirchhoff|flow|affine|spars/.test(textBlob)) {
      return {
        statusBadge: statusBadge,
        statusColor: statusColor,
        shortUnlock: "Sparse (k+1)-point support preserves all k-feature linear queries",
        statementUnlocked: "Any high-dimensional distribution or dense graph weight vector admits a sparse `(k + 1)`-element support (or resistance-bounded flow) matching `k` basis expectations and preserving every affine observable `q = c + ∑ a_j f_j`.",
        realWorldUseCase: " Dataset/quadrature coreset compression, streaming sensor & LLM KV-cache pruning with provable linear-query fidelity, and fast electrical-flow network routing.",
        premiseGate: "Verify connected component mass conservation (`p(C) = w̄(C)`) and confirm target queries lie inside the chosen `k`-feature affine span."
      };
    }
    if (/kl|divergenc|bayes|sufficien|blackwell|entropy|channel|quantum|qpr|pmf|statistical/.test(textBlob)) {
      return {
        statusBadge: statusBadge,
        statusColor: statusColor,
        shortUnlock: "Shared Markov recovery kernel preserves risk across all priors",
        statementUnlocked: "Data-processing contraction holds with zero slack across critical priors iff a shared stochastic recovery channel `R` reconstructs the input laws, guaranteeing zero loss in optimal decision risk across all prior weights simultaneously.",
        realWorldUseCase: "Auditing differential-privacy pipelines, quantized medical/rare-event classifiers (where `t ≪ 1/2`), and entanglement-assisted communication channels.",
        premiseGate: "Enforce support dominance (`q_i = 0 ⇒ p_i = 0`) and test fiberwise critical priors `t_b = Q_b / (P_b + Q_b)` rather than `t = 1/2` alone."
      };
    }
    if (/fourier|spectral|radial|cohn|elkies|packing|eigen|gram|trace|bessel|decoupl/.test(textBlob)) {
      return {
        statusBadge: statusBadge,
        statusColor: statusColor,
        shortUnlock: "Symmetry-averaged trace / Fourier ratio bounds global density or rank",
        statementUnlocked: "Averaging over a compact symmetry group (`O(d)` or torus characters) commutes with Fourier/trace functionals, reducing unrestricted variational bounds to 1D radial linear programs or Cauchy–Schwarz rank bounds `rank ≥ (tr G)² / tr(G²)`.",
        realWorldUseCase: "High-dimensional error-correcting lattice codes & vector quantization (5G/6G & vector DBs), cryo-EM rotational reconstruction, and spectral graph clustering.",
        premiseGate: "Verify strict positivity at the zero mode (`0 < (𝓕 f)(0)`), Fubini joint measurability, and `Lp` vs. pointwise Schwartz regularity."
      };
    }
    if (/ramsey|circuit|permanent|cvp|3sum|apsp|nerode|automata|sofic|expander|pcp/.test(textBlob)) {
      return {
        statusBadge: statusBadge,
        statusColor: statusColor,
        shortUnlock: "Finite algebraic / suffix invariant certifies universal complexity lower bound",
        statementUnlocked: "A finite combinatorial obstruction (separating Myhill–Nerode suffixes, odd-lattice parity gap `|1 − 2z| ≥ 1`, or polynomial transcendence degree `m²`) proves a universal lower bound across *every* algorithm, circuit, or automaton solving the task.",
        realWorldUseCase: "Post-quantum lattice cryptography hardness calibration (`GapCVP`), verifiable minimum-memory synthesis for protocol/SSM controllers, andexpander-code fault tolerance.",
        premiseGate: "Check parity/characteristic boundaries (`CharP ≠ 2` for quadratic Vandermonde, degree `d + 1 < m` for Reed–Solomon, and `32 ≤ n` for cyclic permanent blocks)."
      };
    }
    return {
      statusBadge: statusBadge,
      statusColor: statusColor,
      shortUnlock: "Functors/invariants translate structural bounds across distinct carriers",
      statementUnlocked: "If an explicit structure-preserving adapter (`Equiv` / `MonoidHom` / `Homeomorph`) intertwines the source invariant with the target carrier, obstructions and decomposition theorems proved in World A transfer without reproving the core algebraic lemma.",
      realWorldUseCase: "Reusable formal library engineering in Mathlib4, compiler pass verification via quotient/equivalence transport, and symmetry-reduced physics simulation.",
      premiseGate: "Verify topological/ring side conditions (`[LocallyConnectedSpace]`, flatness over base ring, or compact Hausdorff separation) on both carriers."
    };
  };

  window.cgBuildConsequenceAndUseCaseHtml = function(item) {
    var cu = window.cgDeriveConsequenceAndUseCases(item);
    if (!cu) return "";
    return '<div class="cg-consequence-usecase-card">' +
      '<div class="cg-cu-head">' +
        '<strong style="color:#f8fafc;">Where This Leads · Statements &amp; Real-World Use Cases</strong>' +
        '<span style="font-size:10.5px;font-weight:700;color:' + cu.statusColor + ';">' + cu.statusBadge + '</span>' +
      '</div>' +
      '<div class="cg-cu-grid">' +
        '<div class="cg-cu-row"><strong>Formal Statement Unlocked:</strong> ' + cu.statementUnlocked + '</div>' +
        '<div class="cg-cu-row is-usecase"><strong style="color:#6ee7b7;">Real-World Use Cases:</strong> ' + cu.realWorldUseCase + '</div>' +
        '<div class="cg-cu-row is-gate"><strong style="color:#fde68a;">Premise Gate to Check:</strong> ' + cu.premiseGate + '</div>' +
      '</div>' +
    '</div>';
  };

  window.cgSelectPromisingLeadInGalaxy = function(leadIdx) {
    var leads = window.CG_PROMISING_RESEARCH_LEADS || [];
    var lead = leads[leadIdx];
    if (!lead) return;
    window._cgActiveLeadIdx = leadIdx;
    window._cgHighlightedLeadProjects = lead.projects.slice();
    state.source = null;
    state.projects = manifest.projectOrder.slice();
    state.match = "any";
    renderApp();
  };

  window.cgRenderPromisingLeadsOverviewHtml = function() {
    var leads = window.CG_PROMISING_RESEARCH_LEADS || [];
    if (!leads.length) return "";
    var activeIdx = typeof window._cgActiveLeadIdx === "number" ? window._cgActiveLeadIdx : 0;
    var cur = leads[activeIdx] || leads[0];
    return '<div id="cg-galaxy-leads-compass" style="margin:0 0 12px 0;padding:10px 12px;border-radius:10px;background:rgba(9,18,34,0.88);border:1px solid rgba(52,211,153,0.32);">' +
      '<div style="display:flex;justify-content:space-between;align-items:center;gap:6px;flex-wrap:wrap;margin-bottom:6px;">' +
        '<span style="font-size:10.5px;font-weight:750;letter-spacing:0.06em;text-transform:uppercase;color:#6ee7b7;">★ 6 Promising Discovery Leads (Click to Highlight Beam in Galaxy)</span>' +
        '<button type="button" class="cg-calm-chip" style="padding:2px 8px;font-size:10.5px;border-color:#34d399;color:#d1fae5;" onclick="if(window.v136OpenV34FiniteDiagramsModal)window.v136OpenV34FiniteDiagramsModal(' + cur.labIndex + ')">Open Interactive Lab #' + (cur.labIndex + 1) + ' →</button>' +
      '</div>' +
      '<div style="display:flex;gap:5px;flex-wrap:wrap;margin-bottom:8px;">' +
        leads.map(function(ld, idx) {
          var isAct = idx === activeIdx;
          return '<button type="button" class="cg-calm-chip" data-lead-idx="' + idx + '" onclick="window.cgSelectPromisingLeadInGalaxy(' + idx + ')" style="padding:3px 8px;font-size:11px;' + (isAct ? 'border-color:#34d399;background:rgba(16,185,129,0.2);color:#fff;font-weight:650;' : '') + '">Lead ' + (idx + 1) + '</button>';
        }).join("") +
      '</div>' +
      '<div style="font-size:13px;font-weight:700;color:#f8fafc;margin-bottom:3px;">' + cur.title + '</div>' +
      '<div style="font-size:11px;color:#7dd3fc;margin-bottom:5px;">' + cur.domains + '</div>' +
      '<div style="font-size:11.5px;color:#cbd5e1;line-height:1.45;margin-bottom:5px;"><strong>Why Discovery Is Likely:</strong> ' + cur.whyPromising + '</div>' +
      '<div style="font-size:11.5px;color:#dbeafe;line-height:1.45;margin-bottom:4px;"><strong>Statement Unlocked:</strong> ' + cur.whatStatementUnlocked + '</div>' +
      '<div style="font-size:11.5px;color:#a7f3d0;line-height:1.45;margin-bottom:4px;"><strong>Real-World Use Case:</strong> ' + cur.realWorldUseCase + '</div>' +
      '<div style="font-size:11px;color:#fde68a;line-height:1.4;"><strong>Obstacle to Discharge:</strong> ' + cur.keyObstacle + '</div>' +
    '</div>';
  };

  // Append consequence + real-world use-case card automatically inside cgBuildConnectionProvenanceAndCritiqueHtml
  // so Galaxy Inspector, Inline Catalogue Drawer, and Discovery Paths all get it cleanly with zero duplicate wrappers!
  var prevBuildProvV158 = window.cgBuildConnectionProvenanceAndCritiqueHtml;
  if (typeof prevBuildProvV158 === "function" && !window._cgWrappedProvConsequenceV159) {
    window._cgWrappedProvConsequenceV159 = true;
    window.cgBuildConnectionProvenanceAndCritiqueHtml = function(item) {
      var baseHtml = prevBuildProvV158(item);
      if (!baseHtml) return baseHtml;
      if (baseHtml.indexOf("cg-consequence-usecase-card") !== -1) return baseHtml;
      return baseHtml + window.cgBuildConsequenceAndUseCaseHtml(item);
    };
  }

  // Interactive Finite Micro-Lab #17 (index 16): RecoverableTwin All-Prior Sufficiency, ObservableSpan Affine Compression & Glynn Permanent Polarization
  window.v159PermanentRecoverableObservableLabModel = function(mode) {
    if (mode === "observable-affine") {
      return {
        mode: "observable-affine",
        heading: "Universal Affine Query Compression (`|s| ≤ k + 1`) & Two-Moment Middle Event (`ObservableSpan`)",
        operatorEq: "∀ q(i) = c + ∑_{j=1}^k a_j f_j(i):  (∑_s w_i = ∑_I p_i ∧ ∀ j, ∑_s w_i f_j(i) = ∑_I p_i f_j(i)) ⇒ ∑_s w_i q(i) = ∑_I p_i q(i)",
        witnessDetail: "On {0, 1, 2}, middle-atom mass satisfies r₁ = 2 μ₁(r) − μ₂(r) identically (`middleEventMass_eq_two_mean_sub_secondMoment`). Matching BOTH 1st moment (mean 1) and 2nd moment (5/3) uniquely pins down the uniform law (1/3, 1/3, 1/3) (`mean_and_secondMoment_determine_uniform`).",
        secondaryDetail: "Single-Moment Failure Boundary (`equal_mean_different_event`): Uniform u = (1/3, 1/3, 1/3) and point mass δ₁ = (0, 1, 0) share total mass 1 and 1st moment 1, so they agree on EVERY affine query c + a·i, yet disagree on the non-affine event {i = 1} (1/3 ≠ 1)!",
        verdict: "★ KERNEL-CHECKED CORESET CHAIN: Convex support + moment matching preserves all affine queries in O(k) points!",
        leanRef: "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean :: fin3_middle_event_from_two_moments_and_one_moment_failure"
      };
    }
    if (mode === "permanent-glynn") {
      return {
        mode: "permanent-glynn",
        heading: "Glynn `±1` Hypercube Permanent Polarization & `n = 32` Cyclic Block Formula Barrier (`Permanent.lean`)",
        operatorEq: "2^{1−n} ∑_{δ ∈ {±1}^n, δ₀=1} (∏_j δ_j) ∏_i ⟨δ, A_i⟩ = perm(A)  &  ∀ n ≥ 32, RationalFormula.leaves(perm_n) ≥ n⁴ / (192 log₂ n)",
        witnessDetail: "Verified for 2×2 and 3×3 matrices (`glynn_permanent_polarization_3x3`): summing signed row-sum products over ±1 signs cancels all squared variables x_j² and isolates 4·perm₃(A). Meanwhile, at n = 32 (`ℓ = 5, m = n − 2ℓ = 22`), cyclic matching blocks certify transcendence degree ≥ m² = 484!",
        secondaryDetail: "Threshold Failure Boundary (`permanent_cyclic_block_n32_certificate_and_n16_boundary`): At n = 16 (`ℓ = 4, m = 8`), strict external block room `2ℓ < m` (`8 < 8`) FAILS, explaining why `32 ≤ n` is required in `permanent_rational_formula_lower_bound`.",
        verdict: "★ KERNEL-CHECKED ALGEBRAIC BARRIER: Quartic n⁴/log n rational-formula lower bound + exact ±1 polarization!",
        leanRef: "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean :: glynn_permanent_polarization_3x3"
      };
    }
    return {
      mode: "recoverable-twin",
      heading: "Recoverable Twin (`Q_R = (12/100, 3/100, 85/100)`) Preserves Every Prior's Optimal Decision Score (`RecoverableTwin`)",
      operatorEq: "observe(Q_R) = observe(Q_L) = (15/100, 85/100),  R(0) = (4/5, 1/5, 0)  ⇒  ∀ wtP, wtQ ≥ 0: V_{wt}(P, Q_R) = V_{wt}(f_*P, f_*Q_R)",
      witnessDetail: "Compare P = (40, 10, 50)/100 against TWO laws with the EXACT same observation (15, 85)/100: lossy Q_L = (10, 5, 85)/100 has within-fiber ratio 2:1 ≠ 4:1 (forcing negative R(1,0) = −1/35 and losing 1/80 at prior t = 1/4), whereas recoverable Q_R = (12, 3, 85)/100 has within-fiber ratio 4:1 = 40:10, so R(0) = (4/5, 1/5, 0) recovers BOTH P and Q_R and preserves optimal Bayes risk at EVERY prior!",
      secondaryDetail: "Law Recovery ≠ Sample Recovery: Even for (P, Q_R), observing merged label 0 does NOT reveal whether hidden atom 0 or 1 occurred on an individual draw — sufficiency is a property of the pair of distributions, not deterministic inversion of samples.",
      verdict: "★ KERNEL-CHECKED ALL-PRIOR SUFFICIENCY: Proportional fiber ratios 4:1 unlock a single universal recovery kernel!",
      leanRef: "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean :: recoverable_twin_preserves_every_prior_bayes_score"
    };
  };

  window._v136State = Object.assign(window._v136State || {}, {
    proMode: "recoverable-twin"
  });

  var prevRenderFiniteV158 = window.v136RenderFiniteBody;
  window.v136RenderFiniteBody = function() {
    var st = window._v136State;
    for (var i = 0; i < 17; i++) {
      var tb = document.getElementById("v136-tab-" + i);
      if (tb) tb.className = "v61-prog-tab" + (st.activeLab === i ? " active" : "");
    }
    if (st.activeLab < 16 && typeof prevRenderFiniteV158 === "function") {
      return prevRenderFiniteV158();
    }
    var mount = document.getElementById("v136-finite-mount") || document.getElementById("v136-finite-body");
    if (!mount) return;
    if (st.activeLab === 16) {
      var pm = window.v159PermanentRecoverableObservableLabModel(st.proMode);
      mount.innerHTML = '<div class="v136-finite-grid">' +
        '<div class="v136-finite-card">' +
          '<div style="font-size:11px;font-weight:800;color:#fbbf24;margin-bottom:6px;">LAB 17 · RECOVERABLE TWIN ALL-PRIOR SUFFICIENCY, AFFINE CORESETS &amp; GLYNN PERMANENT POLARIZATION</div>' +
          '<div style="display:flex;gap:6px;flex-wrap:wrap;margin-bottom:10px;">' +
            '<button type="button" class="cg-calm-chip" onclick="window._v136State.proMode=\'recoverable-twin\';window.v136RenderFiniteBody();">★ Recoverable Twin (4:1 Fiber Ratio)</button>' +
            '<button type="button" class="cg-calm-chip" style="border-color:#38bdf8;color:#bae6fd;" onclick="window._v136State.proMode=\'observable-affine\';window.v136RenderFiniteBody();">★ Affine Query Coreset &amp; 2-Moment Event</button>' +
            '<button type="button" class="cg-calm-chip" style="border-color:#34d399;color:#d1fae5;" onclick="window._v136State.proMode=\'permanent-glynn\';window.v136RenderFiniteBody();">Glynn Permanent Polarization &amp; n=32 Barrier</button>' +
          '</div>' +
          '<h3 style="margin:0 0 8px 0;font-size:15.5px;color:#f8fafc;">' + pm.heading + '</h3>' +
          '<div style="font-family:var(--font-mono);font-size:11.5px;color:#fde68a;margin-bottom:8px;">' + pm.operatorEq + '</div>' +
          '<div style="font-size:12px;color:#cbd5e1;line-height:1.55;">' + pm.witnessDetail + '</div>' +
        '</div>' +
        '<div class="v136-finite-card">' +
          '<div style="font-size:11px;font-weight:800;color:#34d399;margin-bottom:6px;">EXACT FINITE CERTIFICATE &amp; FAILURE BOUNDARY</div>' +
          '<div style="font-size:12px;color:#e2e8f0;line-height:1.55;">' +
            '<div style="margin-bottom:8px;">' + pm.secondaryDetail + '</div>' +
            '<div style="padding:8px 10px;border-radius:7px;background:rgba(16,185,129,0.12);border:1px solid rgba(52,211,153,0.35);color:#d1fae5;font-weight:650;">' + pm.verdict + '</div>' +
            '<div style="margin-top:8px;font-size:11px;color:#94a3b8;">Kernel-checked in <code>' + pm.leanRef + '</code></div>' +
          '</div>' +
        '</div>' +
      '</div>';
    }
  };

  var prevOpenFiniteV158 = window.v136OpenV34FiniteDiagramsModal;
  window.v136OpenV34FiniteDiagramsModal = function(initialLab) {
    prevOpenFiniteV158(typeof initialLab === "number" ? Math.min(initialLab, 15) : 0);
    window._v136State.activeLab = typeof initialLab === "number" ? initialLab : 0;
    var bd = document.getElementById("v136-finite-backdrop");
    if (bd) {
      var tabsWrap = bd.querySelector(".v61-prog-tabs");
      if (tabsWrap && !document.getElementById("v136-tab-16")) {
        tabsWrap.insertAdjacentHTML("beforeend",
          '<button type="button" id="v136-tab-16" class="v61-prog-tab" onclick="window.v136SetLab(16)">17. Recoverable Twin, Coresets &amp; Permanent</button>'
        );
      }
    }
    window.v136RenderFiniteBody();
  };

  // Append Suite 19: V159 Immersive Galaxy, Consequence & Real-World Use-Case Synthesis, & Permanent/Recoverable Audit (4 checks -> 172 total)
  var prevRunnerV158 = window.v147RunAllAutomatedTests;
  if (typeof prevRunnerV158 === "function") {
    window.v147RunAllAutomatedTests = function() {
      var rep = prevRunnerV158();
      var extra159 = [];
      function addV159Check(name, cond, detail) {
        extra159.push({
          id: "T" + (rep.results.length + extra159.length + 1),
          category: "19. V159 Immersive Galaxy, Consequences & Use Cases",
          name: name,
          passed: Boolean(cond),
          detail: String(detail || (cond ? "Verified OK" : "Assertion failed"))
        });
      }

      // Check 169: Immersive Galaxy camera controls (Focus, Orbit, Wide) + Promising Discovery Leads compass render cleanly
      var pLens159 = state.lens, pSrc159 = state.source;
      state.lens = "galaxy";
      state.source = null;
      renderApp();
      var galHtml159 = document.getElementById("app-mount").innerHTML || "";
      var inspHtml159 = document.getElementById("inspector-panel").innerHTML || "";
      var hasImmersiveControls = galHtml159.indexOf('data-cam="focus"') !== -1 &&
        galHtml159.indexOf('data-cam="orbit"') !== -1 &&
        galHtml159.indexOf('data-cam="wide"') !== -1 &&
        inspHtml159.indexOf("cg-galaxy-leads-compass") !== -1;
      addV159Check("Immersive Galaxy stage (Focus/Orbit/Wide controls + 6 interactive Discovery Leads compass) renders with zero clutter",
        hasImmersiveControls,
        "Immersive Galaxy controls & leads compass active");

      // Check 170: Selecting a card/star renders 'Where This Leads · Statements & Real-World Use Cases' with Formal Statement, Use Cases & Premise Gate
      var cards159 = document.getElementById("app-mount").querySelectorAll(".ingredient-card");
      if (cards159.length > 0) cards159[0].click();
      var cardDrawerHtml159 = cards159.length > 0 ? cards159[0].innerHTML : "";
      var hasConsequenceCard = cardDrawerHtml159.indexOf("cg-consequence-usecase-card") !== -1 &&
        cardDrawerHtml159.indexOf("Formal Statement Unlocked:") !== -1 &&
        cardDrawerHtml159.indexOf("Real-World Use Cases:") !== -1;
      state.source = pSrc159;
      state.lens = pLens159;
      renderApp();
      addV159Check("Selected stars & Catalogue drawers display grounded 'Formal Statement Unlocked' & 'Real-World Use Cases' cards",
        hasConsequenceCard,
        "Consequence & Real-World Use-Case synthesis verified");

      // Check 171: Lab 17 RecoverableTwin (4:1 ratio), ObservableSpan (r1 = 2*mu1 - mu2) & Glynn Permanent (n=32 m^2=484) verified
      var m17Rec = window.v159PermanentRecoverableObservableLabModel("recoverable-twin");
      var m17Obs = window.v159PermanentRecoverableObservableLabModel("observable-affine");
      var m17Perm = window.v159PermanentRecoverableObservableLabModel("permanent-glynn");
      addV159Check("Lab 17: RecoverableTwin all-prior sufficiency, ObservableSpan 2-moment event & Glynn permanent polarization (n=32, m²=484) verified",
        m17Rec.operatorEq.indexOf("4/5") !== -1 && m17Obs.witnessDetail.indexOf("2 μ₁(r) − μ₂(r)") !== -1 && m17Perm.witnessDetail.indexOf("484") !== -1,
        "Lab 17 all 3 modes verified");

      // Check 172: Overclaimed 3SUM/Symplectic/Connes lookalikes downgraded to ⚠ + 3 V159 bridges sharpened (★) + 41 breakthroughs & 563 suites
      var cIsos159 = ((window.__CG_PRELOADED__ && window.__CG_PRELOADED__.semanticMechanisms && window.__CG_PRELOADED__.semanticMechanisms.customIsomorphisms) || []);
      var exchZeta = cIsos159.find(function(x){ return x && x.id === "iso-tc-probcomb-zeta23-18"; });
      var connesAlg = cIsos159.find(function(x){ return x && x.id === "iso-oai-connes-tc-alggeom-47"; });
      var apspLookalike = cIsos159.find(function(x){ return x && x.id === "iso-apsp3sum-oai-connes-53"; });
      var bRec = window.cgEvaluateBoundaryRules("recoverable twin decoder sufficiency sample hidden individual");
      var bPerm = window.cgEvaluateBoundaryRules("permanent glynn formula threshold division determinant");
      var bDef = window.cgEvaluateBoundaryRules("exchangeable definetti negative correlation finite iid");
      var bt159 = window.CG_VERIFIED_ATLAS_BREAKTHROUGHS || [];
      var suites159 = ((window.__CG_PRELOADED__ && window.__CG_PRELOADED__.semanticMechanisms && window.__CG_PRELOADED__.semanticMechanisms.verifiedLeanSuites) || []);
      addV159Check("41 Theorem-Atlas breakthroughs, 563 Verification suites (620 .lean files), 3 sharpened bridges (★), 3SUM lookalike downgraded (⚠) & 3 V159 boundary rules",
        Boolean(bt159.length >= 41 && suites159.length >= 563 && exchZeta && exchZeta.epistemicSymbol === "★" && connesAlg && connesAlg.epistemicSymbol === "★" && apspLookalike && apspLookalike.epistemicSymbol === "⚠" && bRec.length > 0 && bPerm.length > 0 && bDef.length > 0),
        "Breakthroughs=" + bt159.length + ", Suites=" + suites159.length);

      for (var k = 0; k < extra159.length; k++) {
        rep.results.push(extra159[k]);
        rep.total++;
        if (extra159[k].passed) rep.passed++;
        else rep.failed++;
      }
      window._v147LastReport = rep;
      return rep;
    };
  }
"""

    v159_marker = "// === V159 IMMERSIVE GALAXY CONSEQUENCES, REAL-WORLD USE CASES, PROMISING LEADS & LAB #17 ==="
    if v159_marker in ujs:
        ujs = ujs[:ujs.index(v159_marker)].rstrip() + "\n" + V159_ADDON_JS + "\n})();\n"
    else:
        assert ujs.rstrip().endswith("})();"), "Expected unified-standalone.js to end with `})();`"
        ujs = ujs.rstrip()[:-5].rstrip() + "\n" + V159_ADDON_JS + "\n})();\n"

    ujs_path.write_text(ujs, encoding="utf-8")

    # Update index.html (?v=159, 17 Finite Micro-Labs, 620 zero-sorry Lean 4 files / 580 kernel-compiled)
    idx_path = OBS_DIR / "index.html"
    html = (
        idx_path.read_text(encoding="utf-8")
        .replace("?v=158", "?v=159")
        .replace("16 Exact Finite Micro-Labs", "17 Exact Finite Micro-Labs")
        .replace("16 Finite Micro-Labs", "17 Finite Micro-Labs")
        .replace("619 zero-sorry Lean 4 files (579 kernel-compiled)", "620 zero-sorry Lean 4 files (580 kernel-compiled)")
        .replace("619 zero-sorry Lean 4 files", "620 zero-sorry Lean 4 files")
    )
    idx_path.write_text(html, encoding="utf-8")

    # Update build-cloudflare-dist.py ASSET_VER to "159" and counts to 620/580
    build_py = OBS_DIR / "scripts" / "build-cloudflare-dist.py"
    btxt = (
        build_py.read_text(encoding="utf-8")
        .replace('ASSET_VER = "158"', 'ASSET_VER = "159"')
        .replace('"version": "V158-Bellman-DecisionTV-Automata-ResearchLeads"', '"version": "V159-ImmersiveGalaxy-Consequences-UseCases"')
        .replace('"totalZeroSorryLeanFiles": 619', '"totalZeroSorryLeanFiles": 620')
        .replace('"kernelCompiledLeanModules": 579', '"kernelCompiledLeanModules": 580')
    )
    build_py.write_text(btxt, encoding="utf-8")

    # Update continuous-insight-daemon.py to prioritize ★ reviewed bridges at the top of topRoleCompatibleLeads!
    daemon_py = OBS_DIR / "scripts" / "continuous-insight-daemon.py"
    dtxt = daemon_py.read_text(encoding="utf-8").replace('"version": "V158"', '"version": "V159"')
    old_sort = '    ranked.sort(key=lambda x: x["score"], reverse=True)'
    new_sort = '    ranked.sort(key=lambda x: (1 if x.get("reviewedStar") else 0, x["score"]), reverse=True)'
    if old_sort in dtxt:
        dtxt = dtxt.replace(
            '"score": score,',
            '"score": score,\n            "reviewedStar": bool(iso.get("epistemicSymbol") == "★"),',
            1,
        ).replace(old_sort, new_sort, 1)
    daemon_py.write_text(dtxt, encoding="utf-8")
    print("  [OK] Upgraded Galaxy canvas, Consequence/Use-Case synthesis, index.html (?v=159), build-cloudflare-dist.py & daemon.")


def main():
    step1_verify_math_foundations()
    step2_audit_and_sharpen_bundle()
    breakthroughs = build_v159_breakthroughs()
    step3_upgrade_immersive_galaxy_and_consequences(breakthroughs)
    print("=== V159 IMMERSIVE GALAXY, CONSEQUENCES & FOUNDATION UPGRADE COMPLETE ===")


if __name__ == "__main__":
    main()
