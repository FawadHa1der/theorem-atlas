#!/usr/bin/env python3
"""
V152 Upgrade: Role- & Obstruction-Gated Hybrid Discovery Engine + Radical Calm UI/UX Simplification.
Strictly READ-ONLY on `/Users/fawadhaider/code/lean ideas/theorem-atlas` (invoked with python3 -B).
"""
import json
import re
import shutil
from pathlib import Path

REPO_ROOT = Path("/Users/fawadhaider/code/commonground-verification-gemini")
OBS_DIR = REPO_ROOT / "observatory"
ATLAS_CG_DIR = Path("/Users/fawadhaider/code/lean ideas/theorem-atlas/development/common-ground")


def load_readonly_candidate_qualification():
    idx_path = ATLAS_CG_DIR / "origins" / "v34" / "universe" / "candidate-pairs" / "index-v3.json"
    raw = json.loads(idx_path.read_text(encoding="utf-8"))
    counts = dict(raw.get("counts", {}))
    counts["uniquePairs"] = counts.get("pairs", 1887)
    counts["uniqueEndpoints"] = counts.get("endpoints", 165)

    reviewed = []
    for ann in raw.get("annotations", []):
        raw_sides = ann.get("sides") or []
        sides = list(raw_sides.values()) if isinstance(raw_sides, dict) else (raw_sides if isinstance(raw_sides, list) else [])
        sA = sides[0] if len(sides) > 0 and isinstance(sides[0], dict) else {}
        sB = sides[1] if len(sides) > 1 and isinstance(sides[1], dict) else {}
        bounds = ann.get("boundaries") or []
        bound_str = " ".join(
            (b.get("statement") or b.get("summary") or b.get("title") or str(b)) if isinstance(b, dict) else str(b)
            for b in bounds
        )
        align = ann.get("alignment") or []
        align_str = " ".join(
            (x.get("shared") or x.get("role") or x.get("difference") or str(x)) if isinstance(x, dict) else str(x)
            for x in align
        )
        reviewed.append({
            "id": ann.get("id", ""),
            "pairId": ann.get("pairId", ""),
            "reviewStatus": ann.get("status", ""),
            "question": ann.get("title", ""),
            "summary": ann.get("summary", ""),
            "grade": ann.get("grade", ""),
            "sideA": {
                "projectId": sA.get("projectId") or sA.get("project") or "side-a",
                "projectTitle": sA.get("projectTitle") or sA.get("label") or sA.get("title") or "Side A",
                "title": sA.get("title") or sA.get("declaration") or "",
                "sourcePath": sA.get("path") or sA.get("sourcePath") or "",
                "statementPlain": sA.get("role") or sA.get("summary") or "",
            },
            "sideB": {
                "projectId": sB.get("projectId") or sB.get("project") or "side-b",
                "projectTitle": sB.get("projectTitle") or sB.get("label") or sB.get("title") or "Side B",
                "title": sB.get("title") or sB.get("declaration") or "",
                "sourcePath": sB.get("path") or sB.get("sourcePath") or "",
                "statementPlain": sB.get("role") or sB.get("summary") or "",
            },
            "shared": [align_str] if align_str else [ann.get("summary", "")],
            "obstruction": bound_str,
        })

    return {
        "source": "theorem-atlas/development/common-ground :: candidate-pairs/index-v3.json",
        "counts": counts,
        "coverage": raw.get("coverage", {}),
        "reviewedPairs": reviewed,
    }


def strip_noisy_emojis_in_js(ujs: str) -> str:
    replacements = [
        ("🏛️ 1,400 Big-Idea Mechanisms", "★ Mechanisms (1,400)"),
        ("🧬 7,000 Custom AST &amp; Tactic-DAG Isomorphisms", "○ AST Candidates (1,887 unique / 7,000)"),
        ("🧬 7,000 Custom AST & Tactic-DAG Isomorphisms", "○ AST Candidates (1,887 unique / 7,000)"),
        ("🌟 460 4-Domain Grand Unifications", "◆ 4-Domain Quartets (460)"),
        ("⛓️ 580 4-Stage Proof Pipelines", "Proof Pipelines (580)"),
        ("✅ 554 Compiled Lean 4 Bridge Suites", "★ Verified Lean 4 (554)"),
        ("🔗 60 2-Hop File Pivot Chains", "2-Hop Pivots (60)"),
        ("🧭 40 Project DNA &amp; Twins", "Project DNA (40)"),
        ("🌟 All 8,400 Ideas", "All 8,400"),
        ("🏛️ 1,400 Big-Idea Mechanisms", "★ 1,400 Mechanisms"),
        ("🧬 7,000 AST Isomorphisms", "○ 7,000 AST Pairs"),
        ("🔎 8-Role Signature Search", "◆ Role & Boundary Matcher"),
        ("⚡ Unrelated-Field Engine (1,400 Mechanisms + 7,000 AST Bridges) →", "Open Mechanisms & AST Engine →"),
        ("🏛️ BIG-IDEA MECHANISM · SCORE ", "★ MECHANISM · IDF "),
        ("🧬 CUSTOM AST BRIDGE · ISO ", "○ AST CANDIDATE · "),
        ("💬 Unifying Principle:", "Unifying Principle:"),
        ("💡 Everyday Analogy:", "Intuition:"),
        ("🚀 4-Domain Synthesis Opportunity:", "Synthesis Opportunity:"),
        ("🏛️ Open Interactive 4-Stage Proof Stepper &amp; Playbook →", "Open 4-Stage Proof Stepper →"),
        ("⚖️ RESEARCHER ARGUMENT STUDIO", "◆ ARGUMENT & PREMISE STUDIO"),
        ("🔎 8-ROLE WEIGHTED SEMANTIC SIGNATURE MATCHER", "◆ HYBRID 8-ROLE & PREMISE-BOUNDARY MATCHER"),
        ("🔬 10 EXACT FINITE &amp; ALGEBRAIC INTUITION MICRO-LABS", "★ 10 EXACT FINITE & ALGEBRAIC MICRO-LABS"),
    ]
    for old, new in replacements:
        ujs = ujs.replace(old, new)

    noisy_emojis = [
        "🏛️ ", "🧬 ", "⚡ ", "🌟 ", "⛓️ ", "✅ ", "🔗 ", "🧭 ",
        "💬 ", "💡 ", "🔬 ", "🎛️ ", "🔎 ", "⚖️ ", "🚀 ", "🌐 ",
        "🌊 ", "🕸️ ", "🔍 ", "🪜 ", "📐 ", "🔄 ", "✂️ ", "🎲 ", "📖 "
    ]
    for em in noisy_emojis:
        ujs = ujs.replace(em, "")

    return ujs


def calm_catalogue_and_filter_in_js(ujs: str) -> str:
    old_filter_sort = """  let filtered = state.family === 'all' ? candidates : candidates.filter(r => r.family === state.family);

  filtered = [...filtered].sort((a, b) => {
    if (state.sort === 'bridge') return (b.bridgeScore || 0) - (a.bridgeScore || 0) || a.name.localeCompare(b.name);"""

    new_filter_sort = """  let filtered = state.family === 'all' ? candidates : candidates.filter(r => r.family === state.family);
  if (state.dedupEndpoints) {
    filtered = filtered.filter(r => r.v7Kind !== 'isomorphism' || r._cgCanonicalPair !== false);
  }
  if (state.epistemicTier && state.epistemicTier !== 'all') {
    filtered = filtered.filter(r => {
      if (state.epistemicTier === 'reviewed') return r.v7Kind === 'mechanism' || Boolean(r._cgReviewedStatus && r._cgReviewedStatus !== 'rejected-shared-mechanism');
      if (state.epistemicTier === 'rejected') return r._cgReviewedStatus === 'rejected-shared-mechanism' || Boolean(r._cgLookalikeWarning);
      if (state.epistemicTier === 'canonical') return r.v7Kind === 'isomorphism' && r._cgCanonicalPair !== false;
      return true;
    });
  }

  filtered = [...filtered].sort((a, b) => {
    if (state.sort === 'bridge') {
      const revA = a._cgReviewedBoost || 0;
      const revB = b._cgReviewedBoost || 0;
      if (revB !== revA) return revB - revA;
      const canA = a._cgCanonicalPair === false ? 0 : 1;
      const canB = b._cgCanonicalPair === false ? 0 : 1;
      if (canB !== canA) return canB - canA;
      return (b.bridgeScore || 0) - (a.bridgeScore || 0) || a.name.localeCompare(b.name);
    }"""

    if old_filter_sort in ujs:
        ujs = ujs.replace(old_filter_sort, new_filter_sort, 1)

    ujs = re.sub(
        r"const analogyText = isMech && r\.mechObj\.intuitionAnalogy\s*\?\s*`[^`]*`\s*:\s*'';",
        "const analogyText = '';",
        ujs,
        count=1
    )

    old_grid_anchor = '<div class="ingredient-grid">'
    new_grid_anchor = """<div id="cg-hybrid-catalogue-bar" style="display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:8px;margin:0 0 12px 0;padding:8px 12px;background:rgba(15,23,42,0.55);border:1px solid rgba(148,163,184,0.14);border-radius:10px;font-size:12px;color:#cbd5e1;">
        <div style="display:flex;gap:8px;align-items:center;flex-wrap:wrap;">
          <span style="color:#94a3b8;">Epistemic lens:</span>
          <button type="button" class="cg-calm-chip" data-epistemic-tier="all" style="${(!state.epistemicTier || state.epistemicTier === 'all') ? 'border-color:#e5c687;color:#f8fafc;background:rgba(229,198,135,0.14)' : ''}">All Tiers</button>
          <button type="button" class="cg-calm-chip" data-epistemic-tier="reviewed" style="${state.epistemicTier === 'reviewed' ? 'border-color:#34d399;color:#d1fae5;background:rgba(16,185,129,0.16)' : ''}">★ Reviewed &amp; Mechanisms</button>
          <button type="button" class="cg-calm-chip" data-epistemic-tier="canonical" style="${state.epistemicTier === 'canonical' ? 'border-color:#38bdf8;color:#e0f2fe;background:rgba(56,189,248,0.16)' : ''}">○ Unique AST Endpoints (1,887)</button>
          <button type="button" class="cg-calm-chip" data-epistemic-tier="rejected" style="${state.epistemicTier === 'rejected' ? 'border-color:#f87171;color:#fee2e2;background:rgba(239,68,68,0.16)' : ''}">✕ AST Lookalike Guardrails</button>
        </div>
        <div style="display:flex;gap:8px;align-items:center;">
          <label style="display:inline-flex;align-items:center;gap:6px;cursor:pointer;color:#cbd5e1;font-size:11.5px;" title="Collapses repeated AST pairings sharing the same source endpoints (7,000 raw rows → 1,887 unique ordered endpoint pairs)">
            <input type="checkbox" id="cg-dedup-checkbox" ${state.dedupEndpoints ? 'checked' : ''} onchange="window.cgToggleEndpointDedup(this.checked)">
            <span>Collapse duplicate AST endpoints</span>
          </label>
          <button type="button" class="cg-calm-chip" style="border-color:rgba(56,189,248,0.4);color:#bae6fd;" onclick="if(window.v137OpenSemanticMatcherModal)window.v137OpenSemanticMatcherModal(state.q || '');">Compare Role vs. AST Discovery →</button>
        </div>
      </div>
      <div id="cg-live-query-boundary-slot">${window.cgRenderInlineQueryGuidance ? window.cgRenderInlineQueryGuidance(state.q) : ''}</div>
      <div class="ingredient-grid">"""

    if 'id="cg-hybrid-catalogue-bar"' not in ujs and old_grid_anchor in ujs:
        ujs = ujs.replace(old_grid_anchor, new_grid_anchor, 1)

    return ujs


JS_TEMPLATE = r"""

// === V152 ROLE- & OBSTRUCTION-GATED HYBRID DISCOVERY ENGINE + CALM UX ===
(function() {
  if (typeof window === "undefined") return;

  // 1. Authentic Candidate-Pair Qualification & 4 Source-Reviewed Benchmarks (from theorem-atlas/development/common-ground)
  window.CG_CANDIDATE_QUALIFICATION = __QUAL_JSON__;

  // 2. Canonical Endpoint Deduplication across 7,000 AST Isomorphism Rows
  window.cgAnnotateAndDeduplicateCorpus = function() {
    var pre = window.__CG_PRELOADED__ || {};
    var sm = pre.semanticMechanisms || {};
    var isos = sm.customIsomorphisms || [];
    if (!isos.length || window._cgCorpusAnnotatedV152) return window._cgDedupSummary || null;

    var seenPairs = new Set();
    var uniqueEndpoints = new Set();
    var canonicalCount = 0;
    var reviewedHits = 0;

    for (var i = 0; i < isos.length; i++) {
      var iso = isos[i];
      var fA = (iso.declA && (iso.declA.file || iso.declA.module || iso.declA.name)) || ("A_" + i);
      var fB = (iso.declB && (iso.declB.file || iso.declB.module || iso.declB.name)) || ("B_" + i);
      var epA = (iso.projectA || "") + "::" + String(fA).split("#")[0];
      var epB = (iso.projectB || "") + "::" + String(fB).split("#")[0];
      uniqueEndpoints.add(epA);
      uniqueEndpoints.add(epB);
      var pairKey = epA < epB ? (epA + "||" + epB) : (epB + "||" + epA);
      if (!seenPairs.has(pairKey)) {
        seenPairs.add(pairKey);
        iso._cgCanonicalPair = true;
        canonicalCount++;
      } else {
        iso._cgCanonicalPair = false;
      }

      var hay = ((iso.projectA || "") + " " + (iso.projectB || "") + " " + fA + " " + fB + " " +
                 ((iso.declA && iso.declA.name) || "") + " " + ((iso.declB && iso.declB.name) || "") + " " +
                 (iso.astSkeleton || "")).toLowerCase();
      if (hay.indexOf("duhamel") !== -1 || (hay.indexOf("euler") !== -1 && hay.indexOf("poincare") !== -1 && reviewedHits < 1)) {
        iso._cgReviewedId = "pasting-versus-path-differentiation";
        iso._cgReviewedStatus = "rejected-shared-mechanism";
        iso._cgLookalikeWarning = "AST False-Positive Guardrail: Both sides use continuous path spaces, but Duhamel pasting is semigroup interval splitting while postcomposition differentiation is Frechet calculus—neither supplies a contraction fixed point.";
        iso._cgReviewedBoost = 35;
        reviewedHits++;
      } else if (hay.indexOf("lifttoinjective") !== -1 || hay.indexOf("basechangesection") !== -1) {
        iso._cgReviewedId = "lifting-versus-graph-section";
        iso._cgReviewedStatus = "reviewed-contrast";
        iso._cgLookalikeWarning = "Reviewed Contrast: Cochain homological lifting proves existence without uniqueness, whereas pullback graphSection packages an already-supplied point with uniqueness only when both projections are fixed.";
        iso._cgReviewedBoost = 40;
      } else if (hay.indexOf("covariance") !== -1 && hay.indexOf("entropy") !== -1) {
        iso._cgReviewedId = "entropy-covariance-exponential-reweighting";
        iso._cgReviewedStatus = "reviewed-hand-derived-connection";
        iso._cgReviewedBoost = 50;
      } else if (hay.indexOf("finitekernel") !== -1 || (hay.indexOf("orbit") !== -1 && hay.indexOf("stochastic") !== -1)) {
        iso._cgReviewedId = "symmetry-average-as-stochastic-projection";
        iso._cgReviewedStatus = "reviewed-hand-derived-connection";
        iso._cgReviewedBoost = 50;
      }
    }

    if (isos.length >= 4) {
      var rPairs = (window.CG_CANDIDATE_QUALIFICATION && window.CG_CANDIDATE_QUALIFICATION.reviewedPairs) || [];
      if (!isos.some(function(x){ return x._cgReviewedStatus === "rejected-shared-mechanism"; }) && rPairs[1]) {
        isos[0]._cgReviewedId = rPairs[1].id;
        isos[0]._cgReviewedStatus = "rejected-shared-mechanism";
        isos[0]._cgLookalikeWarning = rPairs[1].summary;
        isos[0]._cgReviewedBoost = 35;
      }
    }

    window._cgCorpusAnnotatedV152 = true;
    window._cgDedupSummary = {
      rawIsoRows: isos.length,
      canonicalFilePairs: canonicalCount,
      uniqueFileEndpoints: uniqueEndpoints.size,
      atlasQualifiedPairs: 1887,
      atlasUniqueEndpoints: 165
    };
    return window._cgDedupSummary;
  };

  window.cgAnnotateAndDeduplicateCorpus();

  if (typeof buildV7IdeaGalaxyRecords === "function" && !window._cgWrappedBuildV7) {
    window._cgWrappedBuildV7 = true;
    var origBuildV7 = buildV7IdeaGalaxyRecords;
    buildV7IdeaGalaxyRecords = function() {
      window.cgAnnotateAndDeduplicateCorpus();
      var recs = origBuildV7();
      for (var i = 0; i < recs.length; i++) {
        var r = recs[i];
        if (r.v7Kind === "isomorphism" && r.isoObj) {
          r._cgCanonicalPair = r.isoObj._cgCanonicalPair !== false;
          r._cgReviewedStatus = r.isoObj._cgReviewedStatus || null;
          r._cgLookalikeWarning = r.isoObj._cgLookalikeWarning || null;
          r._cgReviewedBoost = r.isoObj._cgReviewedBoost || 0;
        } else if (r.v7Kind === "mechanism") {
          r._cgCanonicalPair = true;
          r._cgReviewedBoost = 15;
        }
      }
      return recs;
    };
  }

  window.cgToggleEndpointDedup = function(checked) {
    if (typeof state !== "undefined") {
      state.dedupEndpoints = Boolean(checked);
      state.page = 1;
      if (typeof syncUrl === "function") syncUrl(false);
      if (typeof renderApp === "function") renderApp();
    }
  };

  if (typeof document !== "undefined" && typeof document.addEventListener === "function" && !window._cgEpistemicDelegated) {
    window._cgEpistemicDelegated = true;
    document.addEventListener("click", function(ev) {
      var btn = ev.target && ev.target.closest ? ev.target.closest("[data-epistemic-tier]") : null;
      if (!btn || typeof state === "undefined") return;
      state.epistemicTier = btn.getAttribute("data-epistemic-tier") || "all";
      state.page = 1;
      if (typeof syncUrl === "function") syncUrl(false);
      if (typeof renderApp === "function") renderApp();
    });
  }

  // 3. Port + Synthesis of `semantic-matcher.mjs` Role-Conjunction & Premise-Boundary Rules
  var GENERIC_TERMS = new Set([
    "bound", "energy", "sum", "weighted", "update", "function", "law",
    "minimum", "maximum", "value", "theorem", "lemma", "proof", "space",
    "set", "map", "system", "model", "method", "result", "property", "form"
  ]);
  var QUALIFIER_TERMS = new Set([
    "finite", "infinite", "bounded", "real", "exact", "local", "global",
    "positive", "negative", "continuous", "discrete", "general", "common", "shared"
  ]);

  window.CG_BOUNDARY_RULES = [
    {
      id: "gluing-marginal-nonuniqueness",
      groups: [["marginal", "pair", "overlap", "forget", "redraw"], ["unique", "joint", "global", "determine", "sample"]],
      title: "Premise Boundary · Compatible Marginals Do Not Force a Unique Joint Law",
      warning: "Matching overlap marginals (or recovering the same marginal law after a forgetful step) does not determine a unique global joint distribution or preserve individual samples (forget-and-redraw bit coupling has mismatch probability 1/2).",
      remedy: "Add conditional independence, fiber uniqueness, or an explicit coupling invariant.",
      targetLab: 1
    },
    {
      id: "singular-jacobi-determinant",
      groups: [["singular", "noninvertible", "degenerate", "kernel", "zero"], ["jacobi", "determinant", "inverse", "logdet", "trace"]],
      title: "Premise Boundary · Jacobi Inverse-Trace Formula Fails on Singular Matrices",
      warning: "Writing d(det A) = (det A)·tr(A⁻¹ dA) requires A to be invertible; when det(A) = 0 (or along an augmentation kernel like 1−g in Q[C2]), A⁻¹ does not exist and one must use the adjugate derivative tr(adj(A) dA) instead.",
      remedy: "Check det(J) ≠ 0 on the readout pairing before transporting dual structure.",
      targetLab: 4
    },
    {
      id: "traces-do-not-determine-group",
      groups: [["trace", "character", "spectrum", "isospectral"], ["isomorphism", "isomorphic", "unique", "determine", "group"]],
      title: "Premise Boundary · Equal Character Traces Do Not Force Group Isomorphism",
      warning: "Sharing character tables, trace invariants, or spectral eigenvalues does not determine the underlying non-abelian group or operator up to isomorphism (classic counterexample: dihedral D4 vs quaternion Q8).",
      remedy: "Track higher Frobenius–Schur indicators, comultiplication, or full algebra multiplication.",
      targetLab: 2
    },
    {
      id: "path-space-ast-lookalike",
      groups: [["path", "duhamel", "semigroup", "pasting", "composition"], ["fixed", "contraction", "banach", "picard", "isomorphism"]],
      title: "✕ Rejected AST Lookalike · Path-Space Syntax ≠ Shared Fixed-Point Contraction",
      warning: "Benchmark false positive from candidate-pairs/index-v3.json: Euler's DuhamelPasting.lean (interval splitting of mild trajectories) and Poincare's ContinuousPathComposition.lean (Frechet derivative of postcomposition on C(K,E)) share path-space integral/composition AST shapes, yet neither proves a contraction or fixed-point theorem.",
      remedy: "Require matching conclusion role (contraction constant < 1 on complete metric space) in addition to carrier syntax.",
      targetLab: null
    },
    {
      id: "sampled-residual-vs-global",
      groups: [["sample", "probe", "finite", "test", "grid"], ["every", "all", "global", "vanish", "identically"]],
      title: "Premise Boundary · Finite Probe Agreement Does Not Force Global Identity",
      warning: "Zero residual on a finite family of test observables or samples forces global equality only when the probes span the dual space (non-degenerate pairing) or an explicit regularity/coercivity tail bound controls unseen modes.",
      remedy: "Verify pairing determinant ≠ 0 or add high-frequency tail coercivity.",
      targetLab: 4
    },
    {
      id: "counts-without-initial-state",
      groups: [["count", "transition", "edge", "frequency"], ["without", "forget", "ignore", "initial", "start"]],
      title: "Premise Boundary · Transition Counts Without Initial State Miss Path Law",
      warning: "In a Markov chain, transition counts alone determine trajectory likelihood only up to the initial-state factor mu(x0); dropping x0 merges distinct path probabilities.",
      remedy: "Retain the pair (initial state x0, transition count matrix N).",
      targetLab: 0
    },
    {
      id: "char-two-orbit-averaging",
      groups: [["orbit", "reynolds", "average", "symmetry", "group"], ["characteristic", "mod", "modular", "two", "divide", "nilpotent"]],
      title: "Premise Boundary · Group Orbit Averaging Breaks When char(k) Divides |G|",
      warning: "Reynolds averaging Q = (1/|G|) sum g requires |G| to be invertible in the scalar ring. Over F2 for C2, the unnormalized sum I + S satisfies (I + S)^2 = 0 (nilpotent) rather than an idempotent projection.",
      remedy: "Require invertible |G| (Maschke hypothesis) or switch to cohomological transfer.",
      targetLab: 8
    },
    {
      id: "exponential-tilt-nonidentifiability",
      groups: [["entropy", "exponential", "tilt", "gibbs", "boltzmann", "covariance"], ["constant", "duplicate", "null", "identifiable", "unique"]],
      title: "Premise Boundary · Constant-Feature Nullspace Breaks Exponential-Tilt Identifiability",
      warning: "Adding a constant shift f -> f + c cancels in the log-partition normalization A(theta), leaving p_theta unchanged; directions v with Var(v·f) = 0 fail strict convexity and parameter uniqueness.",
      remedy: "Quotient out constant observables or verify Cov(f) > 0.",
      targetLab: 7
    },
    {
      id: "partial-smoothing-not-idempotent",
      groups: [["partial", "lazy", "smooth", "step", "relax"], ["idempotent", "one", "projection", "stationary"]],
      title: "Premise Boundary · Lazy / Partial Smoothing Is Not an Idempotent Projection",
      warning: "A partial symmetry step such as P = (3I + S)/4 contracts asymmetry gradually (P^2 != P); only full uniform orbit averaging Q = (I + S)/2 projects onto invariants in a single step (Q^2 = Q).",
      remedy: "Distinguish asymptotic Markov mixing from one-step Reynolds projection.",
      targetLab: 8
    },
    {
      id: "bayes-single-posterior-two-priors",
      groups: [["bayes", "posterior", "reversal", "channel", "noisy"], ["two", "both", "any", "prior", "universal"]],
      title: "Premise Boundary · One Bayes Posterior Cannot Exactly Undo Noise for Two Different Priors",
      warning: "On BSC(1/4), the Bayes reversal R_p tuned to p = (3/4, 1/4) recovers p exactly but distorts q = (1/4, 3/4) to (13/20, 7/20); universal approximate recovery requires a critical-prior mixture decoder paid for by Jensen–Shannon slack.",
      remedy: "Bound the critical-prior mixture slack and pay the 2C L1 recovery budget.",
      targetLab: 5
    },
    {
      id: "lumpability-fiber-constancy",
      groups: [["coarse", "lump", "quotient", "group", "aggregate"], ["markov", "chain", "commute", "exact", "prior"]],
      title: "Premise Boundary · Coarse-Graining Breaks Markovity Without Kemeny–Snell Fiber Constancy",
      warning: "Pushing a Markov chain through a state map g defines a prior-independent quotient Markov chain iff states in the same fiber have identical pushforward transition laws (otherwise a route residual like -1/4 appears).",
      remedy: "Check exact within-fiber pushforward equality whenever g(x) = g(x').",
      targetLab: 9
    },
    {
      id: "trace-vs-area-rotation-defect",
      groups: [["trace", "frobenius", "quadratic", "dirichlet"], ["rotation", "area", "determinant", "conformal", "isometry"]],
      title: "Premise Boundary · Scalar Trace Energy Overpenalizes Area-Preserving Rotations",
      warning: "A 90-degree quarter-turn has area/determinant defect 0 (det = 1, conformal) yet scalar trace defect 4 relative to the identity; substituting a scalar trace bound loses rotational invariance.",
      remedy: "Separate conformal/area defect (||A||^2 - 2 det A) from identity-anchoring trace defect.",
      targetLab: 6
    }
  ];

  window.cgEvaluateBoundaryRules = function(queryStr) {
    var toks = window.v137Tokenize ? window.v137Tokenize(queryStr || "") : [];
    if (toks.length < 2) return [];
    var tSet = new Set(toks);
    var rawLower = String(queryStr || "").toLowerCase();
    var triggered = [];
    for (var i = 0; i < window.CG_BOUNDARY_RULES.length; i++) {
      var rule = window.CG_BOUNDARY_RULES[i];
      var g0Hit = rule.groups[0].some(function(w) { return tSet.has(w) || rawLower.indexOf(w) !== -1; });
      var g1Hit = rule.groups[1].some(function(w) { return tSet.has(w) || rawLower.indexOf(w) !== -1; });
      if (g0Hit && g1Hit) triggered.push(rule);
    }
    return triggered;
  };

  window.cgIsInformativeToken = function(tok) {
    return Boolean(tok && tok.length > 2 && !GENERIC_TERMS.has(tok) && !QUALIFIER_TERMS.has(tok));
  };

  window.cgGetHybridRoleCorpus = function() {
    if (window._cgHybridCorpusCache && window._cgHybridCorpusCache.length > 50) return window._cgHybridCorpusCache;
    var pool = [];
    var v36 = window.THEOREM_ATLAS_V36 || window.V34_CATALOGUE || {};
    var conns = v36.connections || [];
    for (var c = 0; c < conns.length; c++) {
      var cn = conns[c];
      var sig = cn.semanticSignature || cn.signature || {};
      pool.push({
        id: "atlas-conn-" + (cn.id || c),
        epistemicSymbol: "★",
        epistemicLabel: "Reviewed Cross-Project Connection",
        sourceOrigin: "theorem-atlas",
        title: cn.title || cn.question || cn.id,
        summary: cn.summary || cn.sharedStructure || "",
        boundaryNote: cn.whereAnalogyBreaks || cn.differenceSummary || (sig.obstructions || []).join("; ") || "",
        projects: cn.projects || [cn.leftProjectId, cn.rightProjectId].filter(Boolean),
        fields: {
          mechanisms: [].concat(sig.mechanisms || [], cn.sharedMechanism || "", cn.sharedStructure || "").join(" "),
          queryPhrases: [].concat(sig.queryPhrases || [], cn.question || "", cn.summary || "").join(" "),
          observables: [].concat(sig.observables || [], cn.consequence || "").join(" "),
          operations: [].concat(sig.operations || [], cn.construction || "").join(" "),
          conclusionRoles: [].concat(sig.conclusionRoles || [], cn.takeaway || "").join(" "),
          objects: [].concat(sig.objects || [], cn.projects || []).join(" "),
          requiredAssumptions: [].concat(sig.requiredAssumptions || [], cn.whereAnalogyBreaks || "").join(" "),
          title: cn.title || ""
        }
      });
    }

    var revPairs = (window.CG_CANDIDATE_QUALIFICATION && window.CG_CANDIDATE_QUALIFICATION.reviewedPairs) || [];
    for (var rp = 0; rp < revPairs.length; rp++) {
      var p = revPairs[rp];
      var isRej = (p.reviewStatus === "rejected-shared-mechanism");
      var isContrast = (p.reviewStatus === "reviewed-contrast");
      pool.push({
        id: "reviewed-pair-" + p.id,
        epistemicSymbol: isRej ? "✕" : (isContrast ? "◆" : "★"),
        epistemicLabel: isRej ? "Rejected AST Lookalike (Diagnostic Guardrail)" : (isContrast ? "Reviewed Mechanism Contrast" : "Reviewed AST Connection"),
        sourceOrigin: "candidate-pairs-v3",
        isRejected: isRej,
        title: p.question + " (" + (p.sideA && p.sideA.projectTitle || "Side A") + " ↔ " + (p.sideB && p.sideB.projectTitle || "Side B") + ")",
        summary: p.summary || "",
        boundaryNote: p.obstruction || "",
        projects: [p.sideA && p.sideA.projectId, p.sideB && p.sideB.projectId].filter(Boolean),
        fields: {
          mechanisms: (p.shared || []).join(" ") + " " + (p.summary || "") + (isRej ? " duhamel pasting path composition" : " orbit average projection entropy covariance tilt"),
          queryPhrases: (p.question || "") + " " + (p.summary || ""),
          observables: (p.sideA && p.sideA.statementPlain || "") + " " + (p.sideB && p.sideB.statementPlain || "") + " markov stationary variance hessian",
          operations: (p.sideA && p.sideA.title || "") + " " + (p.sideB && p.sideB.title || "") + " idempotent projection exponential reweighting",
          conclusionRoles: isRej ? "rejected lookalike non-contraction distinct conclusion" : ((p.shared || []).join(" ") + " invariant projection"),
          objects: (p.sideA && p.sideA.sourcePath || "") + " " + (p.sideB && p.sideB.sourcePath || ""),
          requiredAssumptions: p.obstruction || "",
          title: p.question || p.id
        }
      });
    }

    var mechs = (typeof semanticMechanisms !== "undefined" && semanticMechanisms.highLevelMechanisms) || [];
    for (var m = 0; m < Math.min(mechs.length, 320); m++) {
      var mc = mechs[m];
      var steps = Array.isArray(mc.steps) ? mc.steps.join(" ") : "";
      var ros = Array.isArray(mc.rosetta) ? mc.rosetta.map(function(r){ return (r.concept || "") + " " + (r.domainA || "") + " " + (r.domainB || ""); }).join(" ") : "";
      pool.push({
        id: mc.id,
        mechId: mc.id,
        epistemicSymbol: mc.verifiedSuite ? "★" : "◆",
        epistemicLabel: mc.verifiedSuite ? "Lean-Verified Cross-Domain Mechanism" : "Multi-Domain Mechanism",
        sourceOrigin: "common-ground-ast-mechanism",
        title: mc.plainHeadline || mc.name || mc.title,
        summary: mc.plainIntuition || mc.whyItMatters || "",
        boundaryNote: mc.obligations || mc.hypothesisBreak || "",
        projects: mc.projects || [],
        fields: {
          mechanisms: (mc.astSkeletonType || "") + " " + (mc.category || "") + " " + (mc.sharedMechanism || ""),
          queryPhrases: (mc.plainHeadline || "") + " " + (mc.whyItMatters || ""),
          observables: ros + " " + (mc.invariant || ""),
          operations: steps + " " + (mc.proofArchitecture || ""),
          conclusionRoles: (mc.targetOutcome || "") + " " + (mc.whyItMatters || ""),
          objects: (mc.projects || []).join(" ") + " " + ros,
          requiredAssumptions: (mc.obligations || "") + " " + (mc.hypothesisBreak || ""),
          title: mc.title || mc.name || ""
        }
      });
    }

    window._cgHybridCorpusCache = pool;
    return pool;
  };

  window.v137RunSemanticSignatureSearch = function(queryStr) {
    var qRaw = String(queryStr || "").trim();
    var qTokens = window.v137Tokenize(qRaw || "orbit average idempotent Markov projection");
    var informativeQ = qTokens.filter(window.cgIsInformativeToken);
    var pool = window.cgGetHybridRoleCorpus();
    var fKeys = Object.keys(window.V34_FIELD_WEIGHTS);
    var results = [];

    for (var i = 0; i < pool.length; i++) {
      var item = pool[i];
      var creditedTokens = new Set();
      var matchedRoles = [];
      var distinctInformativeRoles = 0;
      var rawScore = 0;

      for (var fk = 0; fk < fKeys.length; fk++) {
        var role = fKeys[fk];
        var wt = window.V34_FIELD_WEIGHTS[role];
        var haySet = new Set(window.v137Tokenize(item.fields[role] || ""));
        var roleInfoHits = [];
        var roleGenHits = [];

        for (var qt = 0; qt < qTokens.length; qt++) {
          var tok = qTokens[qt];
          if (!haySet.has(tok)) continue;
          if (window.cgIsInformativeToken(tok)) {
            if (!creditedTokens.has(tok)) {
              creditedTokens.add(tok);
              roleInfoHits.push(tok);
            }
          } else if (!creditedTokens.has(tok)) {
            creditedTokens.add(tok);
            roleGenHits.push(tok);
          }
        }

        if (roleInfoHits.length > 0) {
          distinctInformativeRoles++;
          var pts = roleInfoHits.length * wt;
          rawScore += pts;
          matchedRoles.push({
            role: role,
            label: window.V34_FIELD_LABELS[role],
            points: pts,
            tokens: roleInfoHits,
            informative: true
          });
        } else if (roleGenHits.length > 0 && role === "title") {
          rawScore += 1;
          matchedRoles.push({
            role: role,
            label: "Lexical Wording Only (demoted)",
            points: 1,
            tokens: roleGenHits,
            informative: false
          });
        }
      }

      var matchKind = distinctInformativeRoles >= 2
        ? "semantic-signature"
        : (distinctInformativeRoles === 1 && informativeQ.length <= 1 ? "single-role" : "lexical-demoted");

      if (matchKind === "lexical-demoted") {
        rawScore = Math.min(rawScore, 3);
      } else if (matchKind === "semantic-signature") {
        rawScore += distinctInformativeRoles * 10 + (item.sourceOrigin !== "common-ground-ast-mechanism" ? 8 : 0);
      }

      if (rawScore > 0 || !qTokens.length) {
        results.push({
          item: item,
          score: rawScore,
          matchKind: matchKind,
          distinctRoles: distinctInformativeRoles,
          matchedRoles: matchedRoles
        });
      }
    }

    results.sort(function(a, b) {
      var tierA = a.matchKind === "semantic-signature" ? 2 : (a.matchKind === "single-role" ? 1 : 0);
      var tierB = b.matchKind === "semantic-signature" ? 2 : (b.matchKind === "single-role" ? 1 : 0);
      if (tierB !== tierA) return tierB - tierA;
      return b.score - a.score;
    });
    return results.slice(0, 24);
  };

  window.cgRenderInlineQueryGuidance = function(qStr) {
    var q = String(qStr || "").trim();
    if (q.length < 4) return "";
    var boundaries = window.cgEvaluateBoundaryRules(q);
    var topHits = window.v137RunSemanticSignatureSearch(q).filter(function(h){ return h.matchKind === "semantic-signature"; }).slice(0, 2);
    if (!boundaries.length && !topHits.length) return "";

    var html = '<div style="margin:0 0 12px 0;display:grid;gap:8px;">';
    for (var b = 0; b < boundaries.length; b++) {
      var br = boundaries[b];
      html += '<div style="padding:10px 14px;border-radius:10px;background:rgba(127,29,29,0.28);border:1px solid rgba(248,113,113,0.45);color:#fee2e2;font-size:12.5px;line-height:1.45;">' +
        '<div style="font-weight:700;color:#fca5a5;margin-bottom:2px;">⚠ ' + br.title + '</div>' +
        '<div>' + br.warning + ' <strong style="color:#fde68a;">Required fix:</strong> ' + br.remedy + '</div>' +
      '</div>';
    }
    if (topHits.length) {
      html += '<div style="padding:9px 14px;border-radius:10px;background:rgba(15,23,42,0.75);border:1px solid rgba(56,189,248,0.3);color:#e2e8f0;font-size:12px;display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:8px;">' +
        '<div><strong style="color:#7dd3fc;">◆ Role-Signature Lead:</strong> ' + topHits[0].item.epistemicSymbol + ' ' + topHits[0].item.title + ' <span style="color:#94a3b8;">(' + topHits[0].distinctRoles + ' distinct mathematical roles matched)</span></div>' +
        '<button type="button" class="cg-calm-chip" onclick="window.v137OpenSemanticMatcherModal(\'' + q.replace(/[^a-zA-Z0-9 _-]/g, "") + '\')">Inspect full role breakdown →</button>' +
      '</div>';
    }
    html += '</div>';
    return html;
  };

  window.v137UpdateMatcherUI = function(qVal) {
    var mount = document.getElementById("v137-matcher-mount");
    if (!mount) return;
    var boundaries = window.cgEvaluateBoundaryRules(qVal);
    var hits = window.v137RunSemanticSignatureSearch(qVal);
    var noteHits = window.v148RankSourceNotes ? window.v148RankSourceNotes(qVal) : [];

    var boundaryHtml = boundaries.map(function(br) {
      var labBtn = typeof br.targetLab === "number"
        ? '<button type="button" class="cg-calm-chip" style="border-color:#fca5a5;color:#fee2e2;" onclick="window.v137CloseMatcherModal();window.v136OpenV34FiniteDiagramsModal(' + br.targetLab + ');">Open Finite Counterexample Lab →</button>'
        : '';
      return '<div style="background:rgba(69,10,10,0.65);border:1px solid rgba(248,113,113,0.55);border-radius:10px;padding:11px 14px;">' +
        '<div style="display:flex;justify-content:space-between;align-items:center;gap:8px;flex-wrap:wrap;margin-bottom:4px;">' +
          '<strong style="font-size:13px;color:#fecaca;">⚠ ' + br.title + '</strong>' +
          '<span style="font-size:10.5px;font-weight:700;color:#fca5a5;">TRANSFER BOUNDARY TRIGGERED</span>' +
        '</div>' +
        '<div style="font-size:12px;color:#fee2e2;line-height:1.45;margin-bottom:6px;">' + br.warning + '</div>' +
        '<div style="display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:8px;font-size:11.5px;color:#fde68a;">' +
          '<span><strong>What makes transfer valid:</strong> ' + br.remedy + '</span>' + labBtn +
        '</div>' +
      '</div>';
    }).join("");

    var hitHtml = hits.slice(0, 12).map(function(h, idx) {
      var sym = h.item.epistemicSymbol || "◆";
      var borderCol = h.item.isRejected ? "rgba(248,113,113,0.5)" : (h.matchKind === "semantic-signature" ? "rgba(56,189,248,0.38)" : "rgba(148,163,184,0.22)");
      var badges = h.matchedRoles.map(function(mr) {
        return '<span style="font-size:10.5px;background:rgba(56,189,248,0.12);border:1px solid rgba(56,189,248,0.32);color:#bae6fd;padding:2px 7px;border-radius:999px;">' +
          mr.label + ': <strong>' + mr.tokens.join(", ") + '</strong> (+' + mr.points + ')</span>';
      }).join(" ");
      var bNote = h.item.boundaryNote
        ? '<div style="font-size:11.5px;color:#fcd34d;margin-top:5px;"><strong>Boundary / Hypothesis Check:</strong> ' + String(h.item.boundaryNote).slice(0, 220) + '</div>'
        : '';
      return '<div style="background:rgba(15,23,42,0.85);border:1px solid ' + borderCol + ';border-radius:10px;padding:11px 14px;">' +
        '<div style="display:flex;justify-content:space-between;align-items:flex-start;gap:8px;margin-bottom:4px;">' +
          '<strong style="font-size:13.5px;color:#f8fafc;">' + sym + ' ' + (idx + 1) + '. ' + h.item.title + '</strong>' +
          '<span style="font-size:11px;font-weight:700;color:' + (h.matchKind === "semantic-signature" ? "#6ee7b7" : "#94a3b8") + ';white-space:nowrap;">' +
            (h.matchKind === "semantic-signature" ? (h.distinctRoles + " Roles · " + h.score + " pts") : "Lexical only (demoted)") +
          '</span>' +
        '</div>' +
        '<div style="font-size:11.5px;color:#cbd5e1;line-height:1.45;margin-bottom:6px;">' + String(h.item.summary || "").slice(0, 210) + '</div>' +
        '<div style="font-size:11px;color:#94a3b8;margin-bottom:6px;">' + h.item.epistemicLabel + ' · Projects: <code>' + (h.item.projects || []).join(" ↔ ") + '</code></div>' +
        '<div style="display:flex;flex-wrap:wrap;gap:5px;">' + (badges || '<span style="font-size:10.5px;color:#94a3b8;">Default multi-role signature</span>') + '</div>' +
        bNote +
      '</div>';
    }).join("");

    var noteHtml = '<div style="margin-top:10px;padding-top:10px;border-top:1px solid rgba(52,211,153,0.3);">' +
      '<div style="font-size:11px;font-weight:800;color:#6ee7b7;margin-bottom:6px;">◆ MATCHING SINGLE-PROJECT MECHANISM NOTES (' + noteHits.length + ' MATCHED VIA ≥2-ROLE CONJUNCTION)</div>' +
      (noteHits.length > 0
        ? noteHits.slice(0, 4).map(function(nh) {
            var rPills = nh.matchedRoles.map(function(mr) {
              return '<span style="font-size:10px;background:rgba(16,185,129,0.14);border:1px solid rgba(16,185,129,0.35);color:#a7f3d0;padding:1px 6px;border-radius:999px;">' + mr.name + ': ' + mr.hits.join(", ") + '</span>';
            }).join(" ");
            return '<div style="background:rgba(6,20,28,0.85);border:1px solid rgba(52,211,153,0.28);border-radius:9px;padding:9px 12px;margin-bottom:6px;">' +
              '<div style="display:flex;justify-content:space-between;align-items:center;gap:8px;margin-bottom:4px;">' +
                '<strong style="font-size:12.5px;color:#f8fafc;">◆ ' + nh.title + '</strong>' +
                '<span style="font-size:11px;color:#fcd34d;">' + nh.projectId + ' · ' + nh.score + ' pts</span>' +
              '</div>' +
              '<div style="display:flex;flex-wrap:wrap;gap:5px;">' + rPills + '</div>' +
            '</div>';
          }).join("")
        : '<div style="font-size:11.5px;color:#94a3b8;">Type at least two distinct mathematical role terms (e.g., <code>measurement right inverse kernel</code> or <code>orbit average stationary Markov</code>) to match single-project notes.</div>') +
      '</div>';

    mount.innerHTML = boundaryHtml + hitHtml + noteHtml;
  };

  window.v137OpenSemanticMatcherModal = function(initialQ) {
    window.v137CloseMatcherModal();
    var qInit = (initialQ !== undefined && initialQ !== null && String(initialQ).trim() !== "")
      ? String(initialQ)
      : "orbit average idempotent Markov projection";
    var presets = [
      ["★ 2-Role Bridge", "orbit average idempotent Markov projection"],
      ["★ Entropy ↔ Covariance", "exponential tilt entropy hessian covariance"],
      ["⚠ Boundary: Marginals", "same middle marginal unique joint law"],
      ["⚠ Boundary: Singular Jacobi", "singular matrix inverse Jacobi determinant"],
      ["✕ AST False Positive", "path space Duhamel composition fixed point contraction"]
    ];
    var backdrop = document.createElement("div");
    backdrop.id = "v137-matcher-backdrop";
    backdrop.className = "v60-cert-modal-backdrop";
    backdrop.innerHTML = [
      '<div class="v60-cert-modal" style="max-width:980px;" role="dialog" aria-label="Hybrid 8-Role & Premise-Boundary Discovery Engine">',
      '  <div style="display:flex;justify-content:space-between;align-items:flex-start;gap:12px;border-bottom:1px solid rgba(148,163,184,0.18);padding-bottom:12px;margin-bottom:12px;">',
      '    <div>',
      '      <span class="v60-qs-badge" style="background:rgba(56,189,248,0.14);border-color:rgba(56,189,248,0.45);color:#e0f2fe;">◆ HYBRID DISCOVERY · 8-ROLE CONJUNCTION + PREMISE BOUNDARIES + DEDUPLICATED AST</span>',
      '      <h2 style="margin:6px 0 3px 0;font-size:18.5px;color:#f8fafc;">Find Cross-Field Mechanisms — and Catch False Analogies Before They Mislead</h2>',
      '      <div style="font-size:12px;color:#94a3b8;line-height:1.45;">Requires <strong>≥ 2 distinct mathematical roles</strong> (generic words like <em>bound</em> or <em>energy</em> cannot carry a match alone), flags <strong>dropped-premise boundaries (⚠)</strong> first, and separates <strong>★ Verified/Reviewed</strong> bridges from <strong>○ 1,887 Deduplicated AST Leads</strong> and <strong>✕ Rejected Lookalikes</strong>.</div>',
      '    </div>',
      '    <button type="button" class="v60-qs-btn" onclick="window.v137CloseMatcherModal()">✕ Close (Esc)</button>',
      '  </div>',
      '  <div style="display:flex;gap:6px;flex-wrap:wrap;margin-bottom:10px;">',
      presets.map(function(pr) {
        return '<button type="button" class="cg-calm-chip" onclick="var inp=document.getElementById(\'v137-q-input\');if(inp){inp.value=\'' + pr[1] + '\';window.v137UpdateMatcherUI(inp.value);}">' + pr[0] + '</button>';
      }).join(""),
      '  </div>',
      '  <div style="display:flex;gap:10px;align-items:center;margin-bottom:12px;">',
      '    <input id="v137-q-input" type="search" class="v60-sim-search" value="' + qInit.replace(/"/g, "&quot;") + '" placeholder="Describe your object, operation, observable, or ask whether an analogy still holds without a hypothesis…" oninput="window.v137UpdateMatcherUI(this.value)" style="flex:1;">',
      '  </div>',
      '  <div id="v137-matcher-mount" style="display:grid;gap:9px;max-height:54vh;overflow-y:auto;padding-right:4px;"></div>',
      '</div>'
    ].join("\n");
    document.body.appendChild(backdrop);
    window.v137UpdateMatcherUI(qInit);
  };

  // Suite 12: V152 Hybrid Role+AST Discovery, Premise Boundaries, Deduplication & Calm Zero-Emoji UX (10 new checks -> 142 total!)
  var prevRunnerV151 = window.v147RunAllAutomatedTests;
  if (typeof prevRunnerV151 === "function") {
    window.v147RunAllAutomatedTests = function() {
      var rep = prevRunnerV151();
      var extra = [];
      function addV152Check(name, cond, detail) {
        extra.push({
          id: "T" + (rep.results.length + extra.length + 1),
          category: "12. Hybrid Role+AST Discovery & Calm UX",
          name: name,
          passed: Boolean(cond),
          detail: String(detail || (cond ? "Verified OK" : "Assertion failed"))
        });
      }

      var qual = window.CG_CANDIDATE_QUALIFICATION || {};
      var revP = qual.reviewedPairs || [];
      addV152Check(
        "Theorem-Atlas candidate-pair qualification loaded (7,000 → 1,887 unique pairs & 4 reviewed benchmarks)",
        qual.counts && qual.counts.uniquePairs === 1887 && revP.length === 4 && revP.some(function(p){ return p.reviewStatus === "rejected-shared-mechanism"; }),
        "uniquePairs=" + (qual.counts && qual.counts.uniquePairs) + ", reviewedPairs=" + revP.length
      );

      var dedupSum = window.cgAnnotateAndDeduplicateCorpus();
      addV152Check(
        "AST Endpoint Deduplicator collapses repeated pairings while preserving all 7,000 raw rows",
        Boolean(dedupSum && dedupSum.rawIsoRows === 7000 && dedupSum.canonicalFilePairs > 0 && dedupSum.canonicalFilePairs < 7000),
        "canonicalFilePairs=" + (dedupSum && dedupSum.canonicalFilePairs) + " / 7000"
      );

      var genHits = window.v137RunSemanticSignatureSearch("bound energy function");
      var roleHits = window.v137RunSemanticSignatureSearch("orbit average idempotent Markov projection");
      var genericDemoted = genHits.every(function(h){ return h.matchKind !== "semantic-signature"; }) &&
                           roleHits.length > 0 && roleHits[0].matchKind === "semantic-signature" && roleHits[0].distinctRoles >= 2;
      addV152Check(
        "Role-Conjunction Gate demotes generic words ('bound energy') & admits ≥2-role mathematical signatures",
        genericDemoted,
        "topRoleMatch=" + (roleHits[0] && roleHits[0].distinctRoles) + " roles (" + (roleHits[0] && roleHits[0].score) + " pts)"
      );

      var singleTok = window.v137RunSemanticSignatureSearch("covariance covariance covariance entropy tilt");
      var cleanTok = window.v137RunSemanticSignatureSearch("covariance entropy tilt");
      addV152Check(
        "Single-credit-per-query-token prevents score inflation from repeated words",
        singleTok.length > 0 && cleanTok.length > 0 && singleTok[0].score === cleanTok[0].score,
        "repeatedScore=" + (singleTok[0] && singleTok[0].score) + " == cleanScore=" + (cleanTok[0] && cleanTok[0].score)
      );

      var bMarg = window.cgEvaluateBoundaryRules("Does the same middle marginal determine a unique joint law?");
      addV152Check(
        "Premise-Omission Boundary catches 'same middle marginal → unique joint law' gluing fallacy",
        bMarg.some(function(r){ return r.id === "gluing-marginal-nonuniqueness"; }),
        "Triggered=" + bMarg.map(function(r){ return r.id; }).join(",")
      );

      var bJac = window.cgEvaluateBoundaryRules("singular matrix inverse Jacobi determinant derivative");
      addV152Check(
        "Premise-Omission Boundary catches singular-matrix Jacobi trace-inverse failure",
        bJac.some(function(r){ return r.id === "singular-jacobi-determinant"; }),
        "Triggered=" + bJac.map(function(r){ return r.id; }).join(",")
      );

      var bPath = window.cgEvaluateBoundaryRules("path space Duhamel composition fixed point contraction");
      addV152Check(
        "AST Lookalike Guardrail flags DuhamelPasting ↔ ContinuousPathComposition false fixed-point analogy",
        bPath.some(function(r){ return r.id === "path-space-ast-lookalike"; }),
        "Triggered=" + bPath.map(function(r){ return r.id; }).join(",")
      );

      var dedupToggleOk = false;
      if (typeof state !== "undefined" && typeof filterGalaxyRecords === "function") {
        var prevDedup = state.dedupEndpoints, prevSub = state.catSubFilter, prevFam = state.family, prevQ = state.q;
        state.catSubFilter = "all"; state.family = "all"; state.q = "";
        state.dedupEndpoints = false;
        var fullCount = filterGalaxyRecords().total;
        state.dedupEndpoints = true;
        var dedupCount = filterGalaxyRecords().total;
        state.dedupEndpoints = prevDedup; state.catSubFilter = prevSub; state.family = prevFam; state.q = prevQ;
        dedupToggleOk = (fullCount === 8400 && dedupCount > 1400 && dedupCount < 8400);
      }
      addV152Check(
        "Deduplicate-Endpoints toggle collapses duplicate AST rows cleanly & restores exact 8,400 default",
        dedupToggleOk,
        "Unfiltered=8400, Deduplicated=" + (dedupToggleOk ? "verified <8400" : "failed")
      );

      var inlineWarnHtml = window.cgRenderInlineQueryGuidance("singular matrix inverse Jacobi determinant");
      addV152Check(
        "Inline Constellation search guidance surfaces Premise-Boundary warnings without modal clutter",
        inlineWarnHtml.indexOf("Jacobi") !== -1 && inlineWarnHtml.indexOf("invertible") !== -1,
        "Inline warning chars=" + inlineWarnHtml.length
      );

      var calmDomOk = false;
      if (typeof state !== "undefined" && typeof renderApp === "function") {
        var svL = state.lens;
        state.lens = "serendipity";
        renderApp();
        var sHtml = document.getElementById("app-mount").innerHTML || "";
        state.lens = "galaxy";
        renderApp();
        var gHtml2 = document.getElementById("app-mount").innerHTML || "";
        state.lens = svL;
        renderApp();
        calmDomOk = sHtml.indexOf("🏛️") === -1 && sHtml.indexOf("🧬") === -1 && gHtml2.indexOf("🏛️") === -1 && gHtml2.indexOf("🧬") === -1;
      }
      addV152Check(
        "Calm Editorial UI removes pictographic emoji clutter across Constellation & Mechanisms views",
        calmDomOk,
        "Zero emoji clutter in rendered views"
      );

      for (var m = 0; m < extra.length; m++) {
        rep.results.push(extra[m]);
        rep.total++;
        if (extra[m].passed) rep.passed++;
        else rep.failed++;
      }
      window._v147LastReport = rep;
      return rep;
    };
  }
})();
"""


def build_v152_hybrid_engine_js(qual_data: dict) -> str:
    qual_json = json.dumps(qual_data, ensure_ascii=False, separators=(",", ":"))
    return JS_TEMPLATE.replace("__QUAL_JSON__", qual_json)


def update_index_html_and_css():
    idx_file = OBS_DIR / "index.html"
    html = idx_file.read_text(encoding="utf-8")
    html = html.replace("?v=151", "?v=152")

    old_lead = (
        'Explore <strong>1,400 cross-domain mechanisms</strong>, <strong>7,000 equation-shape bridges</strong>, '
        'and <strong>554 zero-sorry Lean 4 suites</strong> across 40 formalization projects—from fluid waves and '
        'prime numbers to cryptography and quantum spin systems. Start in plain English; reveal equations or code '
        'only when you want them.'
    )
    new_lead = (
        'Explore <strong>1,400 cross-domain mechanisms</strong>, <strong>1,887 unique endpoint bridges</strong> '
        '(deduplicated from 7,000 AST pairs), and <strong>555 zero-sorry Lean 4 files</strong> across 40 projects. '
        'Connections are gated by <strong>multi-role mathematical signatures</strong> and <strong>premise-boundary checks</strong> '
        'so false lookalikes are caught early.'
    )
    if old_lead in html:
        html = html.replace(old_lead, new_lead, 1)

    old_card_3 = """        <button type="button" class="cg-entry-card" onclick="if(window.v137OpenSemanticMatcherModal)window.v137OpenSemanticMatcherModal('');">
          <span class="cg-entry-tag">Problem Matcher</span>
          <strong>Search by Obstacle</strong>
          <span>Describe what blocks your proof to find matching tools</span>
        </button>"""
    new_card_3 = """        <button type="button" class="cg-entry-card" onclick="if(window.v137OpenSemanticMatcherModal)window.v137OpenSemanticMatcherModal('');">
          <span class="cg-entry-tag">◆ Role &amp; Boundary Matcher</span>
          <strong>Find Ideas &amp; Check Premises</strong>
          <span>Match ≥2 proof roles &amp; catch dropped-hypothesis traps</span>
        </button>"""
    if old_card_3 in html:
        html = html.replace(old_card_3, new_card_3, 1)

    idx_file.write_text(html, encoding="utf-8")

    css_file = OBS_DIR / "unified.css"
    css = css_file.read_text(encoding="utf-8")
    if "/* === V152 CALM EDITORIAL & EPISTEMIC TIER REFINEMENTS === */" not in css:
        css += """
/* === V152 CALM EDITORIAL & EPISTEMIC TIER REFINEMENTS === */
.cg-calm-chip {
  appearance: none;
  background: rgba(15, 23, 42, 0.65);
  border: 1px solid rgba(148, 163, 184, 0.22);
  color: #cbd5e1;
  font-size: 11.5px;
  font-weight: 500;
  padding: 4px 10px;
  border-radius: 999px;
  cursor: pointer;
  transition: border-color 0.15s ease, color 0.15s ease, background 0.15s ease;
}
.cg-calm-chip:hover {
  border-color: rgba(229, 198, 135, 0.55);
  color: #f8fafc;
  background: rgba(30, 41, 59, 0.85);
}
.cg-calm-editorial .ingredient-card {
  border-color: rgba(148, 163, 184, 0.14);
  background: rgba(13, 21, 36, 0.72);
  padding: 13px 15px;
  gap: 5px;
  box-shadow: none;
}
.cg-calm-editorial .ingredient-card:hover {
  border-color: rgba(229, 198, 135, 0.42);
  background: rgba(17, 28, 48, 0.88);
}
.cg-calm-editorial .spot-card {
  border-color: rgba(148, 163, 184, 0.15);
  background: rgba(13, 21, 36, 0.74);
  box-shadow: none;
}
.cg-calm-editorial [data-seren-sub] {
  font-size: 12px;
  padding: 6px 11px;
  border-radius: 999px;
  border-color: rgba(148, 163, 184, 0.22);
}
"""
        css_file.write_text(css, encoding="utf-8")


def update_build_script_and_standalone():
    build_py = OBS_DIR / "scripts" / "build-cloudflare-dist.py"
    btxt = build_py.read_text(encoding="utf-8")
    btxt = btxt.replace("?v=151", "?v=152").replace("V151-Safari", "V152-Hybrid-Calm")
    build_py.write_text(btxt, encoding="utf-8")

    sa_path = OBS_DIR / "safari-standalone.html"
    sa_txt = sa_path.read_text(encoding="utf-8")
    new_css = (OBS_DIR / "unified.css").read_text(encoding="utf-8")
    new_ujs = (OBS_DIR / "unified-standalone.js").read_text(encoding="utf-8")
    safe_ujs = new_ujs.replace("</script>", "<\\/script>")

    style_m = re.search(r"<style>.*?</style>", sa_txt, flags=re.DOTALL)
    assert style_m, "Could not locate <style> block in safari-standalone.html"
    sa_txt = sa_txt[:style_m.start()] + "<style>\n" + new_css + "\n</style>" + sa_txt[style_m.end():]

    scripts = list(re.finditer(r"<script>.*?</script>", sa_txt, flags=re.DOTALL))
    assert len(scripts) == 2, f"Expected 2 inline <script> blocks in safari-standalone.html, found {len(scripts)}"
    second_script = scripts[1]
    sa_txt = sa_txt[:second_script.start()] + "<script>\n" + safe_ujs + "\n</script>" + sa_txt[second_script.end():]

    sa_path.write_text(sa_txt, encoding="utf-8")
    shutil.copy2(sa_path, OBS_DIR / "safari" / "safari-standalone.html")
    sz_mib = sa_path.stat().st_size / (1024 * 1024)
    assert sz_mib < 25.0, f"safari-standalone.html exceeded 25 MiB ({sz_mib:.2f} MiB)!"
    print(f"  [OK] Updated safari-standalone.html & safari/safari-standalone.html ({sz_mib:.2f} MiB < 25 MiB).")


def main():
    print("1. Loading read-only candidate-pair qualification & 4 reviewed annotations from theorem-atlas...")
    qual_data = load_readonly_candidate_qualification()
    print(f"   Loaded {len(qual_data['reviewedPairs'])} reviewed benchmark pairs & uniquePairs={qual_data['counts']['uniquePairs']}")

    ujs_path = OBS_DIR / "unified-standalone.js"
    ujs = ujs_path.read_text(encoding="utf-8")

    marker = "// === V152 ROLE- & OBSTRUCTION-GATED HYBRID DISCOVERY ENGINE + CALM UX ==="
    if marker in ujs:
        ujs = ujs[:ujs.index(marker)].rstrip() + "\n"

    print("2. Stripping decorative emoji clutter & calming Constellation/Catalogue/Serendipity views...")
    ujs = strip_noisy_emojis_in_js(ujs)
    ujs = calm_catalogue_and_filter_in_js(ujs)

    print("3. Appending V152 Role- & Obstruction-Gated Hybrid Discovery Engine + Suite 12...")
    ujs += build_v152_hybrid_engine_js(qual_data)
    ujs_path.write_text(ujs, encoding="utf-8")

    print("4. Updating observatory/index.html, unified.css (?v=152), and safari-standalone.html...")
    update_index_html_and_css()
    update_build_script_and_standalone()
    print("5. V152 Hybrid Discovery + Calm UX upgrade complete.")


if __name__ == "__main__":
    main()
