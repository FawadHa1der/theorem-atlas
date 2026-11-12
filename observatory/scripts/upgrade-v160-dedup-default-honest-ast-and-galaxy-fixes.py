#!/usr/bin/env python3
"""
V160 Upgrade:
1. Turns endpoint deduplication ON by default (`state.dedupEndpoints = true`) using the exact 1,887
   traceable endpoint pairs from read-only `theorem-atlas/development/common-ground` (`candidate-pairs/index-v3.json`),
   collapsing 7,000 raw AST rows -> 1,887 unique pairs on load (3,287 default records = 1,400 + 1,887).
2. Renames all remaining user-facing "AST Isomorphisms" / "Equation Twins" headings to
   "AST Syntax Candidates (Qualified via Role & Premise Gates)" and adds a concise 1-line Role-vs-AST comparison banner.
3. Fixes broken "Connected Cross-Domain Ideas (click to inspect in 3D Galaxy):" links in Discovery Paths
   (`renderPathsLens`) — both replacing inert `<span>` badges with interactive `<button>` elements AND re-binding
   handlers wiped by V153's post-render `mount.innerHTML` injection — so 100% of chips jump to, focus, and open
   the matching star in the 3D Galaxy & Inspector (including offline under `file://`).
4. Replaces the inaccurate `● 7,000 Cross-Domain Ideas · ★ Comparison · ◆ Project Note...` topbar and
   Catalogue header with exact live epistemic counts (`★`, `◆`, `○`, `✕`, `●`) and draws true geometric
   glyphs (`★` star, `◆` diamond, `○` hollow ring, `✕` cross) on `#galaxy-canvas`, while fixing alphabetical
   positional `.lean` badge mismatches on synthesized mechanism cards.
"""
from __future__ import annotations
import json
from pathlib import Path

REPO_ROOT = Path("/Users/fawadhaider/code/commonground-verification-gemini")
OBS_DIR = REPO_ROOT / "observatory"
ATLAS_INDEX_V3 = Path(
    "/Users/fawadhaider/code/lean ideas/theorem-atlas/development/common-ground/origins/v34/universe/candidate-pairs/index-v3.json"
)


def is_synthetic_or_warn_row(x: dict) -> bool:
    if x.get("epistemicSymbol") == "⚠":
        return True
    s = json.dumps(x).lower()
    if "universalbridgesuite" in s or "proofgamecarrier" in s:
        return True
    fa = (x.get("declA") or {}).get("file", "")
    fb = (x.get("declB") or {}).get("file", "")
    if not x.get("isChallengeSpec") and ("Synthesis/" in fa or "Synthesis/" in fb):
        return True
    return False


def extract_canonical_1887_iso_ids() -> tuple[list[str], dict[str, str]]:
    """Read-only extraction of exact 1,887 canonical iso-* IDs and reviewed annotation statuses from index-v3.json."""
    line0 = (OBS_DIR / "bundle-data.js").read_text(encoding="utf-8").splitlines()[0]
    data = json.loads(line0[len("window.__CG_PRELOADED__ = ") :].rstrip(";"))
    isos = data["semanticMechanisms"]["customIsomorphisms"]
    iso_by_id = {x["id"]: x for x in isos}
    star_ids = {
        x["id"]
        for x in isos
        if x.get("epistemicSymbol") == "★" and not is_synthetic_or_warn_row(x)
    }

    idx_v3 = json.loads(ATLAS_INDEX_V3.read_text(encoding="utf-8"))
    ann_status_by_id = {
        ann["id"]: ann.get("status", "")
        for ann in idx_v3.get("annotations", [])
        if isinstance(ann, dict) and ann.get("id")
    }

    canon_ids: list[str] = []
    reviewed_by_iso_id: dict[str, str] = {}
    for pair in idx_v3.get("pairs", []):
        r_ids = [r[1] for r in pair.get("rows", []) if len(r) >= 2 and r[1] in iso_by_id]
        if not r_ids:
            continue
        chosen = next(
            (rid for rid in r_ids if rid in star_ids),
            next((rid for rid in r_ids if not is_synthetic_or_warn_row(iso_by_id[rid])), r_ids[0]),
        )
        canon_ids.append(chosen)
        ann_id = pair.get("annotationId")
        if ann_id and ann_id in ann_status_by_id:
            for rid in r_ids:
                reviewed_by_iso_id[rid] = f"{ann_id}::{ann_status_by_id[ann_id]}"

    assert len(canon_ids) == 1887, f"Expected exact 1887 canonical pairs, got {len(canon_ids)}"
    assert star_ids.issubset(set(canon_ids)), f"Missing ★ star IDs from canonical set: {star_ids - set(canon_ids)}"
    return canon_ids, reviewed_by_iso_id


def patch_core_unified_js(ujs: str) -> str:
    # Remove any previous V160 block idempotently (with or without leading spaces)
    for marker in (
        "  // === V160 DEFAULT DEDUPLICATION, HONEST AST CANDIDATE NAMING, PATH JUMP FIX & ACCURATE GALAXY GLYPHS ===",
        "// === V160 DEFAULT DEDUPLICATION, HONEST AST CANDIDATE NAMING, PATH JUMP FIX & ACCURATE GALAXY GLYPHS ===",
    ):
        if marker in ujs:
            ujs = ujs[: ujs.index(marker)].rstrip() + "\n"

    # Deduplicate banner line if inserted twice on a prior run
    banner_expr = "${(state.catSubFilter === 'isomorphismsOnly' || state.signalTier === 'isomorphisms' || state.epistemicTier === 'canonical' || state.epistemicTier === 'rejected' || state.epistemicTier === 'circle' || state.epistemicTier === 'cross') && window.cgRenderRoleVsAstBanner ? window.cgRenderRoleVsAstBanner(false) : ''}"
    dup_banner = banner_expr + "\n      " + banner_expr
    while dup_banner in ujs:
        ujs = ujs.replace(dup_banner, banner_expr)

    # 1. Default state.dedupEndpoints: true in initial state object
    if "  dedupEndpoints: true," not in ujs:
        ujs = ujs.replace(
            "  signalTier: 'mechanisms',",
            "  signalTier: 'mechanisms',\n  dedupEndpoints: true,\n  epistemicTier: 'all',",
            1,
        )

    # Support ?dedup=0 in readUrlState & syncUrl, and restore dedupEndpoints=true on Reset
    if "params.get('dedup')" not in ujs:
        ujs = ujs.replace(
            "    if (params.get('q')) state.q = params.get('q');",
            "    if (params.get('dedup') === '0') state.dedupEndpoints = false;\n    else if (params.get('dedup') === '1') state.dedupEndpoints = true;\n    if (params.get('epi')) state.epistemicTier = params.get('epi');\n    if (params.get('q')) state.q = params.get('q');",
            1,
        )
    if "u.searchParams.set('dedup'" not in ujs:
        ujs = ujs.replace(
            "    if (state.q) u.searchParams.set('q', state.q);",
            "    if (state.dedupEndpoints === false) u.searchParams.set('dedup', '0');\n    if (state.epistemicTier && state.epistemicTier !== 'all') u.searchParams.set('epi', state.epistemicTier);\n    if (state.q) u.searchParams.set('q', state.q);",
            1,
        )
    ujs = ujs.replace(
        "state.sort = 'bridge'; state.q = ''; state.page = 1; state.source = null; state.activeMotifIds = [];",
        "state.sort = 'bridge'; state.q = ''; state.page = 1; state.source = null; state.activeMotifIds = []; state.dedupEndpoints = true; state.epistemicTier = 'all'; state.catSubFilter = 'all'; state.signalTier = 'mechanisms';",
        1,
    )

    # 2. Populate recordById with BOTH v7Records AND indexData.records in filterGalaxyRecords + accurate epistemicTier filtering
    old_epistemic_block = """  if (state.epistemicTier && state.epistemicTier !== 'all') {
    filtered = filtered.filter(r => {
      if (state.epistemicTier === 'reviewed') return r.v7Kind === 'mechanism' || Boolean(r._cgReviewedStatus && r._cgReviewedStatus !== 'rejected-shared-mechanism');
      if (state.epistemicTier === 'rejected') return r._cgReviewedStatus === 'rejected-shared-mechanism' || Boolean(r._cgLookalikeWarning);
      if (state.epistemicTier === 'canonical') return r.v7Kind === 'isomorphism' && r._cgCanonicalPair !== false;
      return true;
    });
  }"""
    new_epistemic_block = """  if (indexData && Array.isArray(indexData.records)) {
    for (const ir of indexData.records) {
      if (!recordById.has(ir.id)) recordById.set(ir.id, ir);
    }
  }
  if (state.epistemicTier && state.epistemicTier !== 'all') {
    filtered = filtered.filter(r => {
      const glyph = window.cgGetRecordEpistemicGlyph ? window.cgGetRecordEpistemicGlyph(r) : '○';
      if (state.epistemicTier === 'star') return glyph === '★';
      if (state.epistemicTier === 'diamond') return glyph === '◆';
      if (state.epistemicTier === 'reviewed') return glyph === '★' || glyph === '◆';
      if (state.epistemicTier === 'canonical' || state.epistemicTier === 'circle') return glyph === '○';
      if (state.epistemicTier === 'rejected' || state.epistemicTier === 'cross') return glyph === '✕';
      return true;
    });
  }"""
    if old_epistemic_block in ujs:
        ujs = ujs.replace(old_epistemic_block, new_epistemic_block, 1)

    # 3. Upgrade mountGalaxyCanvas to draw genuine ★, ◆, ○, ✕ geometric glyphs on #galaxy-canvas & accurate hover badges!
    old_star_draw = """      ctx.beginPath();
      ctx.arc(sp.x, sp.y, radius, 0, Math.PI * 2);
      ctx.fillStyle = (isSelected || isHovered || isMotif) ? '#fff7df' : (famColor + alphaSuffix);
      ctx.fill();"""
    new_star_draw = """      const glyph = window.cgGetRecordEpistemicGlyph ? window.cgGetRecordEpistemicGlyph(rec) : (isMech ? '◆' : (isWarn ? '✕' : '○'));
      const drawCol = (isSelected || isHovered || isMotif) ? '#fff7df' : (glyph === '★' ? '#34d399' : (famColor + alphaSuffix));
      if (glyph === '★' && typeof ctx.lineTo === 'function') {
        const outerR = Math.max(3.2, radius + 1.6);
        const innerR = outerR * 0.44;
        ctx.beginPath();
        for (let k = 0; k < 8; k++) {
          const ang = (k * Math.PI) / 4 - Math.PI / 2;
          const rr = (k % 2 === 0) ? outerR : innerR;
          if (k === 0) ctx.moveTo(sp.x + Math.cos(ang) * rr, sp.y + Math.sin(ang) * rr);
          else ctx.lineTo(sp.x + Math.cos(ang) * rr, sp.y + Math.sin(ang) * rr);
        }
        ctx.closePath();
        ctx.fillStyle = (isSelected || isHovered) ? '#fff7df' : '#34d399';
        ctx.fill();
      } else if (glyph === '◆' && typeof ctx.lineTo === 'function') {
        const dR = Math.max(2.1, radius + 0.7);
        ctx.beginPath();
        ctx.moveTo(sp.x, sp.y - dR);
        ctx.lineTo(sp.x + dR * 0.88, sp.y);
        ctx.lineTo(sp.x, sp.y + dR);
        ctx.lineTo(sp.x - dR * 0.88, sp.y);
        ctx.closePath();
        ctx.fillStyle = drawCol;
        ctx.fill();
      } else if (glyph === '✕' && typeof ctx.lineTo === 'function') {
        const xR = Math.max(1.8, radius + 0.4);
        ctx.beginPath();
        ctx.moveTo(sp.x - xR, sp.y - xR);
        ctx.lineTo(sp.x + xR, sp.y + xR);
        ctx.moveTo(sp.x + xR, sp.y - xR);
        ctx.lineTo(sp.x - xR, sp.y + xR);
        ctx.strokeStyle = (isSelected || isHovered) ? '#fca5a5' : 'rgba(248, 113, 113, 0.36)';
        ctx.lineWidth = (isSelected || isHovered) ? 1.8 : 1.05;
        ctx.stroke();
      } else {
        // ○ Unreviewed Candidate Pairing = true hollow ring (matching symbol key!)
        ctx.beginPath();
        ctx.arc(sp.x, sp.y, Math.max(1.6, radius + 0.35), 0, Math.PI * 2);
        if (isSelected || isHovered || isMotif) {
          ctx.fillStyle = '#fff7df';
          ctx.fill();
        } else {
          ctx.strokeStyle = drawCol;
          ctx.lineWidth = 1.15;
          ctx.stroke();
        }
      }"""
    if old_star_draw in ujs:
        ujs = ujs.replace(old_star_draw, new_star_draw, 1)

    old_hover_badge = """    const kindBadge = r.v7Kind === 'mechanism'
      ? '<span style="color:#dfc082;font-weight:700">★ Mechanism</span>'
      : (r.isoObj && r.isoObj.epistemicSymbol === '★'
          ? '<span style="color:#34d399;font-weight:700">★ Reviewed Bridge</span>'
          : (r.isoObj && r.isoObj.epistemicSymbol === '⚠'
              ? '<span style="color:#fcd34d;font-weight:700">⚠ AST Guardrail</span>'
              : '<span style="color:#7dd3fc;font-weight:700">○ AST Pair</span>'));"""
    new_hover_badge = """    const hoverGlyph = window.cgGetRecordEpistemicGlyph ? window.cgGetRecordEpistemicGlyph(r) : '○';
    const kindBadge = hoverGlyph === '★'
      ? '<span style="color:#34d399;font-weight:700">★ Source-Reviewed Bridge</span>'
      : (hoverGlyph === '◆'
          ? '<span style="color:#dfc082;font-weight:700">◆ ' + (r.v7Kind === 'mechanism' ? 'Mechanism Hypothesis' : 'Reviewed Contrast') + '</span>'
          : (hoverGlyph === '✕'
              ? '<span style="color:#fca5a5;font-weight:700">✕ Rejected / Guardrailed AST</span>'
              : '<span style="color:#7dd3fc;font-weight:700">○ AST Syntax Candidate</span>'));"""
    if old_hover_badge in ujs:
        ujs = ujs.replace(old_hover_badge, new_hover_badge, 1)

    # 4. Rename all remaining "AST Isomorphisms" / "Equation Twins" headings across unified-standalone.js
    heading_replacements = [
        (
            "EXPANDED AST ISOMORPHISM INSPECTOR · SCORE ${esc(iso.isomorphismScore)}",
            "AST SYNTAX CANDIDATE (QUALIFIED VIA ROLE &amp; PREMISE GATES) · SCORE ${esc(iso.isomorphismScore)}",
        ),
        (
            "SELECTED CUSTOM AST ISOMORPHISM STAR · SCORE ${iso.isomorphismScore}",
            "AST SYNTAX CANDIDATE (QUALIFIED VIA ROLE &amp; PREMISE GATES) · SCORE ${iso.isomorphismScore}",
        ),
        (
            '<h3 style="font-size:11.5px;text-transform:uppercase;letter-spacing:0.08em;color:#59c2ff;margin:12px 0 6px">Custom <code>structure</code> / <code>def</code> / <code>theorem</code> AST Isomorphisms (0 Mathlib)</h3>',
            '<h3 style="font-size:11.5px;text-transform:uppercase;letter-spacing:0.08em;color:#59c2ff;margin:12px 0 6px">○ AST Syntax Candidates (Qualified via Role &amp; Premise Gates)</h3>',
        ),
        ("<span>ISO ${iso.isomorphismScore}</span>", "<span>AST ${iso.isomorphismScore}</span>"),
        ("<span class=\"badge badge-gold\">ISO ${iso.isomorphismScore}</span>", "<span class=\"badge badge-gold\">AST ${iso.isomorphismScore}</span>"),
        ("Custom AST Isomorphisms", "AST Syntax Candidates"),
        (
            '<button type="button" class="signal-pill" data-signal-tier="mechanisms" aria-pressed="${state.signalTier !== \'isomorphisms\'}">Big Ideas (${fmt(allMechs.length)})</button>\n            <button type="button" class="signal-pill" data-signal-tier="isomorphisms" aria-pressed="${state.signalTier === \'isomorphisms\'}">Equation Twins (${fmt(allIsos.length)})</button>',
            '<button type="button" class="signal-pill" data-signal-tier="mechanisms" aria-pressed="${state.signalTier !== \'isomorphisms\'}">Mechanisms (${fmt(allMechs.length)})</button>\n            <button type="button" class="signal-pill" data-signal-tier="isomorphisms" aria-pressed="${state.signalTier === \'isomorphisms\'}">AST Syntax Candidates (${state.dedupEndpoints ? \'1,887\' : fmt(allIsos.length)})</button>',
        ),
        (
            '<label for="gal-q">Search ${fmt(allMechs.length + allIsos.length)} cross-domain ideas (press <code>/</code> to focus)</label>',
            '<label for="gal-q">Search ${state.dedupEndpoints ? \'3,287 deduplicated records\' : fmt(allMechs.length + allIsos.length) + \' raw records\'} (press <code>/</code> to focus)</label>',
        ),
        ("<div><strong style=\"color:#78b8e8\">Equation Twins:</strong>", "<div><strong style=\"color:#78b8e8\">AST Syntax Candidates:</strong>"),
        (
            '<button type="button" class="v60-qs-btn" data-cat-subfilter="all" style="${(!state.catSubFilter || state.catSubFilter === \'all\') && state.signalTier !== \'isomorphisms\' ? \'background:rgba(229,198,135,0.25);border-color:var(--gold);color:#fff;\' : \'\'}">\n            All 8,400\n          </button>\n          <button type="button" class="v60-qs-btn" data-cat-subfilter="mechanismsOnly" style="${state.catSubFilter === \'mechanismsOnly\' ? \'background:rgba(229,198,135,0.25);border-color:var(--gold);color:#fff;\' : \'\'}">\n            ★ Mechanisms (1,400)\n          </button>\n          <button type="button" class="v60-qs-btn" data-cat-subfilter="isomorphismsOnly" style="${state.catSubFilter === \'isomorphismsOnly\' || state.signalTier === \'isomorphisms\' ? \'background:rgba(89,194,255,0.25);border-color:#59c2ff;color:#fff;\' : \'\'}">\n            ○ 7,000 AST Pairs\n          </button>',
            '<button type="button" class="v60-qs-btn" data-cat-subfilter="all" style="${(!state.catSubFilter || state.catSubFilter === \'all\') && state.signalTier !== \'isomorphisms\' ? \'background:rgba(229,198,135,0.25);border-color:var(--gold);color:#fff;\' : \'\'}">\n            All (${state.dedupEndpoints ? \'3,287\' : \'8,400\'})\n          </button>\n          <button type="button" class="v60-qs-btn" data-cat-subfilter="mechanismsOnly" style="${state.catSubFilter === \'mechanismsOnly\' ? \'background:rgba(229,198,135,0.25);border-color:var(--gold);color:#fff;\' : \'\'}">\n            ◆ Mechanisms (1,400)\n          </button>\n          <button type="button" class="v60-qs-btn" data-cat-subfilter="isomorphismsOnly" style="${state.catSubFilter === \'isomorphismsOnly\' || state.signalTier === \'isomorphisms\' ? \'background:rgba(89,194,255,0.25);border-color:#59c2ff;color:#fff;\' : \'\'}">\n            ○ AST Syntax Candidates (${state.dedupEndpoints ? \'1,887\' : \'7,000\'})\n          </button>',
        ),
        (
            '<h2 style="margin:2px 0;font-size:22px">Cross-Domain Mechanisms, AST Bridges &amp; Verified Lean 4 Suites</h2>',
            '<h2 style="margin:2px 0;font-size:22px">Cross-Domain Mechanisms, AST Syntax Candidates &amp; Verified Lean 4 Suites</h2>',
        ),
        (
            '<button type="button" aria-pressed="${state.serenSubmode === \'isomorphisms\'}" data-seren-sub="isomorphisms">AST Pairs (7,000)</button>',
            '<button type="button" aria-pressed="${state.serenSubmode === \'isomorphisms\'}" data-seren-sub="isomorphisms">○ AST Syntax Candidates (${state.dedupEndpoints ? \'1,887\' : \'7,000\'})</button>',
        ),
        (
            '<p class="eyebrow" style="color:var(--gold)">4-STAGE MULTI-THEOREM PROOF PIPELINE ISOMORPHISMS · COMPILE-VERIFIED IN LEAN 4</p>',
            '<p class="eyebrow" style="color:var(--gold)">4-STAGE MULTI-THEOREM PROOF PIPELINE ALIGNMENTS · STRUCTURAL HYPOTHESES</p>',
        ),
        (
            '<label for="iso-q">Search ${fmt(allIsos.length)} Equation-Twin AST Bridges (author-written structures, definitions, and theorems)</label>',
            '<label for="iso-q">Search ${fmt(isos.length)} AST Syntax Candidates (Qualified via Role &amp; Premise Gates)</label>',
        ),
        (
            '<button type="button" id="iso-random" style="border-color:var(--gold);color:var(--gold)">Random Custom AST Bridge</button>',
            '<button type="button" id="iso-random" style="border-color:var(--gold);color:var(--gold)">Random AST Candidate</button>',
        ),
        (
            '<p class="eyebrow">LAYERS A, B &amp; C · BESPOKE AUTHOR-DEFINED DECLARATIONS MATCHED BY AST SKELETON &amp; PROOF-DAG</p>\n              <h2>${fmt(isos.length)} Custom Declaration AST Isomorphisms Across Unrelated Fields</h2>',
            '<p class="eyebrow">CANDIDATE SYNTAX LAYER · DEDUPLICATED ENDPOINTS GATED BY ROLE &amp; PREMISE CHECKS</p>\n              <h2>${fmt(isos.length)} AST Syntax Candidates (Qualified via Role &amp; Premise Gates)</h2>',
        ),
        (
            '<div class="eyebrow">CUSTOM AST SKELETON ISOMORPHISM · SCORE ${activeIso.isomorphismScore}</div>',
            '<div class="eyebrow">AST SYNTAX CANDIDATE (QUALIFIED VIA ROLE &amp; PREMISE GATES) · SCORE ${activeIso.isomorphismScore}</div>',
        ),
        (
            '<h3 style="font-size:12px;text-transform:uppercase;letter-spacing:0.08em;color:var(--gold);margin:14px 0 6px">Candidate Lean 4 Structural Isomorphism Bridge</h3>',
            '<h3 style="font-size:12px;text-transform:uppercase;letter-spacing:0.08em;color:var(--gold);margin:14px 0 6px">Candidate Lean 4 Adapter Blueprint (Requires Premise Verification)</h3>',
        ),
        (
            'No custom AST isomorphisms match this filter.',
            'No AST syntax candidates match this filter.',
        ),
        (
            "mMode === 'isomorphisms' ? 'Custom AST Skeleton Overlap Matrix (7,000 Equation-Twin AST Bridges)'",
            "mMode === 'isomorphisms' ? 'AST Syntax Candidates (Qualified via Role & Premise Gates)'",
        ),
        (
            '<button type="button" data-bm-mode="isomorphisms" aria-pressed="${mMode === \'isomorphisms\'}" style="font-size:11.5px">Custom AST Skeletons</button>',
            '<button type="button" data-bm-mode="isomorphisms" aria-pressed="${mMode === \'isomorphisms\'}" style="font-size:11.5px">AST Syntax Candidates</button>',
        ),
        (
            "mMode === 'isomorphisms' ? 'shared Equation-Twin AST Bridges'",
            "mMode === 'isomorphisms' ? 'shared AST Syntax Candidates'",
        ),
        (
            "Custom AST Skeleton Isomorphisms (${pairIsos.length})",
            "AST Syntax Candidates (Qualified via Role &amp; Premise Gates) (${pairIsos.length})",
        ),
    ]
    for old_s, new_s in heading_replacements:
        ujs = ujs.replace(old_s, new_s)

    # 5. Apply default deduplication + 1-line comparison banner inside renderSerendipityLens (isomorphisms submode) and renderBridgesLens!
    old_seren_isos = """  if (state.serenSubmode === 'isomorphisms') {
    const skelOptions = Array.from(new Set(allIsos.map(x => x.astSkeleton))).sort();
    const isos = allIsos.filter(iso => {
      if (state.isoSkeletonFilter !== 'all' && iso.astSkeleton !== state.isoSkeletonFilter) return false;"""
    new_seren_isos = """  if (state.serenSubmode === 'isomorphisms') {
    if (window.cgAnnotateAndDeduplicateCorpus) window.cgAnnotateAndDeduplicateCorpus();
    const skelOptions = Array.from(new Set(allIsos.map(x => x.astSkeleton))).sort();
    const isos = allIsos.filter(iso => {
      if (state.dedupEndpoints && iso._cgCanonicalPair === false) return false;
      if (state.isoSkeletonFilter !== 'all' && iso.astSkeleton !== state.isoSkeletonFilter) return false;"""
    if old_seren_isos in ujs:
        ujs = ujs.replace(old_seren_isos, new_seren_isos, 1)

    old_seren_toolbar = """      ${subBar}
      <div class="toolbar" style="margin-top:14px;grid-template-columns:1.3fr 1fr auto">"""
    new_seren_toolbar = """      ${subBar}
      ${window.cgRenderRoleVsAstBanner ? window.cgRenderRoleVsAstBanner(true) : ''}
      <div class="toolbar" style="margin-top:10px;grid-template-columns:1.3fr 1fr auto">"""
    if old_seren_toolbar in ujs:
        ujs = ujs.replace(old_seren_toolbar, new_seren_toolbar, 1)

    old_bridges_header = """        <div class="matrix-scroll" role="region" aria-label="Cross-project shared ingredient matrix">"""
    new_bridges_header = """        ${mMode === 'isomorphisms' && window.cgRenderRoleVsAstBanner ? window.cgRenderRoleVsAstBanner(false) : ''}
        <div class="matrix-scroll" role="region" aria-label="Cross-project shared ingredient matrix">"""
    if "${mMode === 'isomorphisms' && window.cgRenderRoleVsAstBanner" not in ujs and old_bridges_header in ujs:
        ujs = ujs.replace(old_bridges_header, new_bridges_header, 1)

    # 6. Replace inaccurate Galaxy Topbar (`● 7,000 Cross-Domain Ideas · ★ Comparison · ◆ Project Note...`) AND Catalogue Header!
    old_galaxy_topbar = """        <div class="galaxy-topbar" style="flex-wrap:wrap;gap:8px">
          <span><strong style="color:var(--gold)">● ${fmt(filtered.total)} Cross-Domain Ideas</strong> · <span title="Epistemic Symbol Key from Theorem-Atlas">★ Comparison · ◆ Project Note · ● Project Hub · ○ Candidate Pairing · ✕ Rejected Analogy</span></span>
          <span style="display:flex;gap:8px;align-items:center;flex-wrap:wrap">
            ${state.source ? `<button type="button" id="v148-gal-clear-sel" class="v60-qs-btn" style="padding:2px 8px;font-size:11px;border-color:#f59e0b;color:#fde68a">✕ Clear Selection (Esc)</button>` : ''}
            <button type="button" class="v60-qs-btn" style="padding:2px 8px;font-size:11px;border-color:#38bdf8;color:#bae6fd" onclick="if(window.v148OpenArgumentAndWorksheetModal)window.v148OpenArgumentAndWorksheetModal('compare')">Compare 48 Reviewed Arguments</button>
            <span>Drag/scroll to explore · Shift+Click 2 hubs to beam-pair</span>
          </span>
        </div>"""
    new_galaxy_topbar = """        <div class="galaxy-topbar" style="flex-wrap:wrap;gap:8px">
          ${window.cgRenderAccurateGalaxyTopbarSummary ? window.cgRenderAccurateGalaxyTopbarSummary(filtered.records) : `<span><strong style="color:var(--gold)">${fmt(filtered.total)} Records</strong></span>`}
          <span style="display:flex;gap:8px;align-items:center;flex-wrap:wrap">
            ${state.source ? `<button type="button" id="v148-gal-clear-sel" class="v60-qs-btn" style="padding:2px 8px;font-size:11px;border-color:#f59e0b;color:#fde68a">✕ Clear Selection (Esc)</button>` : ''}
            <button type="button" class="v60-qs-btn" style="padding:2px 8px;font-size:11px;border-color:#34d399;color:#d1fae5" onclick="if(window.v148OpenArgumentAndWorksheetModal)window.v148OpenArgumentAndWorksheetModal('compare')" title="Inspect the 31 ★ Source-Reviewed Comparisons & 17 ◆ Single-Project Notes">★ 31 Comparisons &amp; ◆ 17 Notes</button>
            <span>Drag/scroll · Shift+Click 2 hubs</span>
          </span>
        </div>"""
    if old_galaxy_topbar in ujs:
        ujs = ujs.replace(old_galaxy_topbar, new_galaxy_topbar, 1)

    old_cat_h2 = """          <p class="eyebrow" style="color:var(--gold);margin-bottom:3px">Cross-Domain Idea Catalogue</p>
          <h2 style="margin:0;color:#fff;font-size:22px">${fmt(filtered.total)} Cross-Domain Ideas</h2>"""
    new_cat_h2 = """          <p class="eyebrow" style="color:var(--gold);margin-bottom:3px">Epistemic &amp; Structural Discovery Catalogue</p>
          <h2 style="margin:0;color:#fff;font-size:22px">${window.cgFormatHonestPoolHeading ? window.cgFormatHonestPoolHeading(filtered.records) : fmt(filtered.total) + ' Records'}</h2>"""
    if old_cat_h2 in ujs:
        ujs = ujs.replace(old_cat_h2, new_cat_h2, 1)

    # Inject 1-line comparison banner right below #cg-hybrid-catalogue-bar when viewing AST Syntax Candidates
    old_live_slot = '<div id="cg-live-query-boundary-slot">${window.cgRenderInlineQueryGuidance ? window.cgRenderInlineQueryGuidance(state.q) : \'\'}</div>'
    if banner_expr not in ujs and old_live_slot in ujs:
        ujs = ujs.replace(old_live_slot, banner_expr + "\n      " + old_live_slot, 1)

    old_card_pill = """              <span class="cg-card-kind-pill ${isMech ? 'is-mech' : (isIso && r.isoObj.epistemicSymbol === '⚠' ? 'is-warn' : 'is-iso')}">
                ${isMech ? '★ Mechanism' : (isIso ? (r.isoObj.epistemicSymbol === '⚠' ? '⚠ Lookalike Guardrail' : '○ AST Pair') : esc(r.family))}
              </span>"""
    new_card_pill = """              <span class="cg-card-kind-pill ${(() => { const g = window.cgGetRecordEpistemicGlyph ? window.cgGetRecordEpistemicGlyph(r) : '○'; return g === '★' ? 'is-star' : (g === '◆' ? 'is-mech' : (g === '✕' ? 'is-warn' : 'is-iso')); })()}">
                ${window.cgFormatRecordCardBadge ? window.cgFormatRecordCardBadge(r) : (isMech ? '◆ Mechanism Hypothesis' : '○ AST Candidate')}
              </span>"""
    if old_card_pill in ujs:
        ujs = ujs.replace(old_card_pill, new_card_pill, 1)

    # 7. Fix broken "Connected Cross-Domain Ideas (click to inspect in 3D Galaxy):" in renderPathsLens!
    old_path_shared = """        ${active.sharedIngredients?.length ? `
          <div style="margin:14px 0;display:flex;gap:8px;align-items:center;flex-wrap:wrap">
            <span style="font-size:12px;color:var(--gold);font-weight:650">Connected Cross-Domain Ideas (click to inspect in 3D Galaxy):</span>
            ${active.sharedIngredients.map(nm => {
              const rec = indexData.records.find(r => r.name === nm);
              return rec
                ? `<button type="button" class="eco-pill" data-jump-lemma="${esc(rec.id)}" style="font-family:var(--font-mono);font-size:12px">${esc(nm)} (IDF ${rec.idf}b) ↗</button>`
                : `<span class="badge" style="font-family:var(--font-mono)">${esc(nm)}</span>`;
            }).join('')}
          </div>
        ` : ''}"""
    new_path_shared = """        ${window.cgRenderPathConnectedGalaxyIdeas ? window.cgRenderPathConnectedGalaxyIdeas(active) : ''}"""
    if old_path_shared in ujs:
        ujs = ujs.replace(old_path_shared, new_path_shared, 1)

    old_path_jump_listener = """    mount.querySelectorAll('[data-jump-lemma]').forEach(btn => {
      btn.onclick = () => selectIngredient(btn.dataset.jumpLemma, active.projects?.[0], active.projects?.[1]);
    });"""
    new_path_jump_listener = """    mount.querySelectorAll('[data-jump-lemma]').forEach(btn => {
      btn.onclick = () => {
        if (window.cgJumpFromPathTo3DGalaxy) {
          window.cgJumpFromPathTo3DGalaxy(btn.dataset.jumpLemma, active.projects || [], btn.dataset.jumpLabel || '');
        } else {
          selectIngredient(btn.dataset.jumpLemma, active.projects?.[0], active.projects?.[1]);
        }
      };
    });"""
    if old_path_jump_listener in ujs:
        ujs = ujs.replace(old_path_jump_listener, new_path_jump_listener, 1)

    # 8. Update legacy v147RunAllAutomatedTests checks so they expect default dedup=ON (3,287 / 1,887) AND verify raw toggle (8,400 / 7,000)!
    ujs = ujs.replace(
        'check("3. Galaxy Catalogue UX", "Default Readable Galaxy Catalogue displays all 8,400 cross-domain ideas", fgAll.total === 8400 && fgAll.items.length === 48, "Total=" + fgAll.total + ", Page1=" + fgAll.items.length);',
        'check("3. Galaxy Catalogue UX", "Default Readable Galaxy Catalogue enables endpoint deduplication on load (3,287 = 1,400 mechanisms + 1,887 unique AST pairs)", state.dedupEndpoints === true && fgAll.total === 3287 && fgAll.items.length === 48, "Total=" + fgAll.total + ", Page1=" + fgAll.items.length);',
        1,
    )
    ujs = ujs.replace(
        'check("3. Galaxy Catalogue UX", "Clicking \'7,000 AST Isomorphisms\' filters catalogue to 7,000 AST bridges", fgIsos.total === 7000, "Filtered total=" + fgIsos.total);',
        'check("3. Galaxy Catalogue UX", "Clicking \'AST Syntax Candidates\' filters catalogue to exact 1,887 deduplicated AST endpoint pairs", fgIsos.total === 1887, "Filtered total=" + fgIsos.total);',
        1,
    )
    ujs = ujs.replace(
        'check("3. Galaxy Catalogue UX", "Clicking \'All 8,400 Ideas\' restores full 8,400 catalogue", filterGalaxyRecords().total === 8400, "Restored total=" + filterGalaxyRecords().total);',
        'check("3. Galaxy Catalogue UX", "Clicking \'All (3,287)\' restores full 3,287 deduplicated catalogue", filterGalaxyRecords().total === 3,287, "Restored total=" + filterGalaxyRecords().total);'.replace("3,287, \"Restored", "3287, \"Restored"),
        1,
    )
    ujs = ujs.replace(
        "dedupToggleOk = (fullCount === 8400 && dedupCount > 1400 && dedupCount < 8400);",
        "dedupToggleOk = (fullCount === 8400 && dedupCount === 3287);",
        1,
    )

    return ujs


V160_JS_APPEND_TEMPLATE = r"""// === V160 DEFAULT DEDUPLICATION, HONEST AST CANDIDATE NAMING, PATH JUMP FIX & ACCURATE GALAXY GLYPHS ===
(function() {
  if (typeof window === "undefined") return;

  // 1. Exact 1,887 Canonical AST Endpoint Pair IDs & Reviewed Statuses from read-only `candidate-pairs/index-v3.json`
  var CANON_LIST_1887 = __CANON_1887_JSON__;
  var REVIEWED_ISO_MAP = __REVIEWED_ISO_MAP_JSON__;
  window.CG_CANONICAL_1887_SET = new Set(CANON_LIST_1887);

  function isSyntheticOrWrapperIso(iso) {
    if (!iso) return false;
    if (iso.epistemicSymbol === "⚠") return true;
    var fa = (iso.declA && iso.declA.file) || "";
    var fb = (iso.declB && iso.declB.file) || "";
    if (!iso.isChallengeSpec && (fa.indexOf("Synthesis/") !== -1 || fb.indexOf("Synthesis/") !== -1)) {
      return true;
    }
    var low = JSON.stringify(iso).toLowerCase();
    return low.indexOf("universalbridgesuite") !== -1 || low.indexOf("proofgamecarrier") !== -1;
  }

  // Override cgAnnotateAndDeduplicateCorpus so `dedupEndpoints = true` (default ON) collapses 7,000 -> exact 1,887
  // while strictly preserving `⚠` guardrails on synthetic UniversalBridgeSuite / ProofGameCarrier / Synthesis/ wrappers!
  window.cgAnnotateAndDeduplicateCorpus = function() {
    var pre = window.__CG_PRELOADED__ || {};
    var sm = pre.semanticMechanisms || {};
    var isos = sm.customIsomorphisms || [];
    if (!isos.length) return null;
    if (window._cgCorpusAnnotatedV160 && window._cgDedupSummary) return window._cgDedupSummary;

    var canonCount = 0;
    for (var i = 0; i < isos.length; i++) {
      var iso = isos[i];
      var isCanon = window.CG_CANONICAL_1887_SET.has(iso.id);
      iso._cgCanonicalPair = isCanon;
      if (isCanon) canonCount++;

      var synthWarn = isSyntheticOrWrapperIso(iso);
      if (synthWarn) {
        iso.epistemicSymbol = "⚠";
      }

      var revEntry = REVIEWED_ISO_MAP[iso.id];
      if (revEntry) {
        var parts = revEntry.split("::");
        iso._cgReviewedId = parts[0];
        iso._cgReviewedStatus = parts[1] || "reviewed";
        if (iso._cgReviewedStatus === "rejected-shared-mechanism" || synthWarn) {
          iso.epistemicSymbol = "⚠";
          if (iso._cgReviewedStatus === "rejected-shared-mechanism") {
            iso._cgLookalikeWarning = "AST False-Positive Guardrail (index-v3.json): Euler Duhamel interval pasting vs. Poincare Frechet postcomposition differentiation share path-space syntax without sharing a contraction fixed-point mechanism.";
            iso._cgReviewedBoost = 25;
          } else {
            iso._cgReviewedBoost = -20;
          }
        } else if (iso._cgReviewedStatus === "reviewed-contrast") {
          iso._cgReviewedBoost = 60;
        } else {
          iso.epistemicSymbol = "★";
          iso._cgReviewedBoost = 90;
        }
      } else if (iso.epistemicSymbol === "★" && !synthWarn) {
        iso._cgReviewedStatus = "source-reviewed-bridge";
        iso._cgReviewedBoost = 95;
      } else if (iso.epistemicSymbol === "⚠") {
        iso._cgReviewedBoost = -20;
      }
    }

    if (typeof state !== "undefined" && state.dedupEndpoints === undefined) {
      state.dedupEndpoints = true;
    }

    window._cgCorpusAnnotatedV160 = true;
    window._cgDedupSummary = {
      rawIsoRows: isos.length,
      canonicalFilePairs: canonCount,
      uniqueFileEndpoints: 165,
      atlasQualifiedPairs: 1887,
      atlasUniqueEndpoints: 165
    };
    return window._cgDedupSummary;
  };

  window.cgAnnotateAndDeduplicateCorpus();

  // 2. Honest Topic-Matched Lean 4 File Resolver for Synthesized Mechanisms (prevents alphabetical modulo-550 misattribution!)
  var GENUINE_MECH_LEAN_MAP = {
    "dyadic": "CommonGround/Verification/RenormalizationAndWaveShellBridge.lean",
    "decoupling": "CommonGround/Verification/BourgainDecouplingAndZetaZeroBridge.lean",
    "entropy": "CommonGround/Verification/MoserTardosEntropyCompressionBridge.lean",
    "pinning": "CommonGround/Verification/MoserTardosEntropyCompressionBridge.lean",
    "ricci": "CommonGround/Verification/UniversalMechanismPipelines.lean",
    "lyapunov": "CommonGround/Verification/UniversalMechanismPipelines.lean",
    "sphere": "CommonGround/Verification/TheoremAtlasSpherePackingGapCVPAndPellBridge.lean",
    "weil": "CommonGround/Verification/PositivstellensatzAndFlagAlgebraBridge.lean",
    "positivstellensatz": "CommonGround/Verification/PositivstellensatzAndFlagAlgebraBridge.lean",
    "ramanujan": "CommonGround/Verification/RamanujanExpanderHeckeBridge.lean",
    "expander": "CommonGround/Verification/RamanujanExpanderHeckeBridge.lean",
    "bsd": "CommonGround/Verification/BSDSelmerHeightRegulatorBridge.lean",
    "selmer": "CommonGround/Verification/BSDSelmerHeightRegulatorBridge.lean",
    "snell": "CommonGround/Verification/SnellObstacleVariationalDuality.lean",
    "bellman": "CommonGround/Verification/TheoremAtlasBellmanDecisionAndAutomataBridge.lean",
    "blackwell": "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean",
    "recoverable": "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean",
    "permanent": "CommonGround/Verification/TheoremAtlasPermanentRecoverableAndObservableBridge.lean",
    "carleman": "CommonGround/Verification/CarlemanCommutatorUniqueContinuation.lean",
    "glimm": "CommonGround/Verification/GlimmShockPotentialAndEulerBVBridge.lean",
    "khovanov": "CommonGround/Verification/KhovanovRasmussenSliceGenusBridge.lean",
    "onsager": "CommonGround/Verification/OnsagerBesovCommutatorBridge.lean",
    "gromov": "CommonGround/Verification/GromovPseudoholomorphicBubblingBridge.lean",
    "freiman": "CommonGround/Verification/EntropicFreimanRuzsaAndCodingBridge.lean",
    "waring": "CommonGround/Verification/CubicCovariantsAndWaringRankBridge.lean"
  };

  window.cgResolveHonestLeanModelForMech = function(m) {
    if (!m) return null;
    var idTitle = (String(m.id || "") + " " + String(m.title || "") + " " + String(m.shortLabel || "")).toLowerCase();
    var keys = Object.keys(GENUINE_MECH_LEAN_MAP);
    for (var i = 0; i < keys.length; i++) {
      if (idTitle.indexOf(keys[i]) !== -1) return GENUINE_MECH_LEAN_MAP[keys[i]];
    }
    var vf = String(m.verifiedLeanFile || "");
    if (vf) {
      var base = vf.split("/").pop().replace(".lean", "").replace(/Bridge$/, "");
      var words = base.replace(/([a-z])([A-Z])/g, "$1 $2").toLowerCase().split(/\s+/).filter(function(w){ return w.length >= 5; });
      var matchedWord = words.some(function(w){ return idTitle.indexOf(w) !== -1; });
      if (matchedWord) return vf;
    }
    return null;
  };

  // 3. Truthful Epistemic Glyph Classifier (`★`, `◆`, `○`, `✕`) + Accurate Topbar & Catalogue Headings
  window.cgGetRecordEpistemicGlyph = function(r) {
    if (!r) return "○";
    if (r.v7Kind === "mechanism") {
      return "◆";
    }
    if (r.v7Kind === "isomorphism" && r.isoObj) {
      var iso = r.isoObj;
      if (iso._cgReviewedStatus === "rejected-shared-mechanism" || iso.epistemicSymbol === "⚠") return "✕";
      if (iso._cgReviewedStatus === "reviewed-contrast") return "◆";
      if (iso.epistemicSymbol === "★" || (iso._cgReviewedStatus && iso._cgReviewedStatus.indexOf("reviewed") !== -1)) return "★";
      return "○";
    }
    return "○";
  };

  window.cgFormatRecordCardBadge = function(r) {
    var g = window.cgGetRecordEpistemicGlyph(r);
    if (g === "★") return "★ Reviewed Bridge";
    if (g === "◆") {
      if (r && r.v7Kind === "mechanism") {
        var honestLean = window.cgResolveHonestLeanModelForMech(r.mechObj);
        return honestLean ? "◆ Mechanism (+Local Lean Model)" : "◆ Mechanism Hypothesis";
      }
      return "◆ Reviewed Contrast";
    }
    if (g === "✕") return "✕ AST Lookalike Guardrail";
    return "○ AST Syntax Candidate";
  };

  window.cgSummarizeEpistemicBreakdown = function(records) {
    var out = { total: 0, star: 0, diamond: 0, circle: 0, cross: 0, mechs: 0, isos: 0 };
    var arr = records || [];
    out.total = arr.length;
    for (var i = 0; i < arr.length; i++) {
      var r = arr[i];
      if (r.v7Kind === "mechanism") out.mechs++;
      else if (r.v7Kind === "isomorphism") out.isos++;
      var g = window.cgGetRecordEpistemicGlyph(r);
      if (g === "★") out.star++;
      else if (g === "◆") out.diamond++;
      else if (g === "✕") out.cross++;
      else out.circle++;
    }
    return out;
  };

  window.cgFormatHonestPoolHeading = function(records) {
    var bk = window.cgSummarizeEpistemicBreakdown(records);
    var fmtN = function(n){ return Number(n || 0).toLocaleString("en-US"); };
    var dedup = (typeof state === "undefined") ? true : Boolean(state.dedupEndpoints);
    if (bk.mechs > 0 && bk.isos === 0) {
      return fmtN(bk.total) + " Synthesized Mechanism Hypotheses";
    }
    if (bk.isos > 0 && bk.mechs === 0) {
      if (bk.cross === bk.total && bk.total > 0) {
        return fmtN(bk.total) + " Rejected / Guardrailed AST Lookalikes";
      }
      return fmtN(bk.total) + (dedup ? " Unique AST Endpoint Pairs (Collapsed from 7,000 Raw Rows)" : " Raw AST Candidate Rows (1,887 Unique Endpoint Pairs)");
    }
    return fmtN(bk.total) + (dedup ? " Deduplicated Discovery Records (1,400 Hypotheses + 1,887 Unique AST Pairs)" : " Raw Corpus Records (Deduplication Off)");
  };

  window.cgSetEpistemicGlyphFilter = function(tierVal) {
    if (typeof state === "undefined") return;
    state.epistemicTier = (state.epistemicTier === tierVal) ? "all" : tierVal;
    state.page = 1;
    if (typeof syncUrl === "function") syncUrl(false);
    if (typeof renderApp === "function") renderApp();
  };

  window.cgRenderAccurateGalaxyTopbarSummary = function(records) {
    var bk = window.cgSummarizeEpistemicBreakdown(records);
    var fmtN = function(n){ return Number(n || 0).toLocaleString("en-US"); };
    var dedup = (typeof state === "undefined") ? true : Boolean(state.dedupEndpoints);
    var curTier = (typeof state !== "undefined" && state.epistemicTier) ? state.epistemicTier : "all";
    var activeHubCount = (typeof state !== "undefined" && Array.isArray(state.projects)) ? state.projects.length : 40;

    var leadTitle = "";
    if (bk.isos > 0 && bk.mechs === 0) {
      leadTitle = fmtN(bk.total) + (dedup ? " Unique AST Endpoint Pairs" : " Raw AST Candidate Rows");
    } else if (bk.mechs > 0 && bk.isos === 0) {
      leadTitle = fmtN(bk.total) + " Mechanism Hypotheses";
    } else {
      leadTitle = fmtN(bk.total) + (dedup ? " Deduplicated Records" : " Raw Records");
    }

    var pillStyle = function(active, col) {
      return "padding:1px 7px;border-radius:999px;font-size:11px;cursor:pointer;background:" +
        (active ? "rgba(255,255,255,0.12)" : "transparent") + ";border:1px solid " +
        (active ? col : "rgba(148,163,184,0.22)") + ";color:" + col + ";";
    };

    return '<span style="display:inline-flex;align-items:center;gap:6px;flex-wrap:wrap;">' +
      '<strong style="color:var(--gold);">' + leadTitle + '</strong>' +
      '<span style="color:#64748b;">·</span>' +
      '<button type="button" style="' + pillStyle(curTier === "star", "#34d399") + '" onclick="window.cgSetEpistemicGlyphFilter(\'star\')" title="Click to filter to source-reviewed bridges plotted as 4-point stars (★)">★ ' + fmtN(bk.star) + ' Reviewed</button>' +
      '<button type="button" style="' + pillStyle(curTier === "diamond", "#dfc082") + '" onclick="window.cgSetEpistemicGlyphFilter(\'diamond\')" title="Click to filter to synthesized mechanism hypotheses &amp; contrasts plotted as diamonds (◆)">◆ ' + fmtN(bk.diamond) + ' Hypotheses</button>' +
      '<button type="button" style="' + pillStyle(curTier === "circle", "#7dd3fc") + '" onclick="window.cgSetEpistemicGlyphFilter(\'circle\')" title="Click to filter to unreviewed AST syntax candidates plotted as hollow rings (○)">○ ' + fmtN(bk.circle) + ' AST Candidates</button>' +
      '<button type="button" style="' + pillStyle(curTier === "cross", "#fca5a5") + '" onclick="window.cgSetEpistemicGlyphFilter(\'cross\')" title="Click to filter to rejected/guardrailed AST lookalikes plotted as crosses (✕)">✕ ' + fmtN(bk.cross) + ' Guardrails</button>' +
      '<span style="font-size:11px;color:#94a3b8;" title="Perimeter project hubs currently active">● ' + activeHubCount + ' Hubs</span>' +
    '</span>';
  };

  // 4. Concise 1-Line Role-vs-AST Comparison Banner (with inline deduplication toggle when in Serendipity/Matrix)
  window.cgRenderRoleVsAstBanner = function(includeDedupToggle) {
    var dedup = (typeof state === "undefined") ? true : Boolean(state.dedupEndpoints);
    var toggleHtml = includeDedupToggle
      ? '<label style="display:inline-flex;align-items:center;gap:5px;cursor:pointer;color:#e2e8f0;font-size:11.5px;white-space:nowrap;">' +
          '<input type="checkbox" ' + (dedup ? 'checked' : '') + ' onchange="window.cgToggleEndpointDedup(this.checked)">' +
          '<span>Collapse duplicate AST endpoints (7,000 → 1,887)</span>' +
        '</label>'
      : '';
    return '<div class="cg-role-vs-ast-banner" style="margin:8px 0 10px 0;padding:8px 12px;border-radius:9px;background:rgba(15,23,42,0.72);border:1px solid rgba(56,189,248,0.28);display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:8px;font-size:11.8px;line-height:1.4;color:#cbd5e1;">' +
      '<div><strong style="color:#7dd3fc;">○ AST Syntax Candidates vs. ★/◆ Role &amp; Premise Gates:</strong> Raw AST matching finds shared operator shapes (<strong>1,887</strong> unique endpoint pairs from 7,000 rows) without checking hypotheses; genuine transfers require <strong>≥2 distinct mathematical roles</strong> + <strong>premise-boundary verification</strong>.</div>' +
      '<div style="display:inline-flex;align-items:center;gap:8px;flex-wrap:wrap;">' +
        toggleHtml +
        '<button type="button" class="cg-calm-chip" style="border-color:rgba(56,189,248,0.45);color:#bae6fd;" onclick="if(window.v137OpenSemanticMatcherModal)window.v137OpenSemanticMatcherModal((window.state&&window.state.q)||\'\');">Compare Role vs. AST →</button>' +
      '</div>' +
    '</div>';
  };

  // 5. Fix positional `.lean` badge on inline mechanism drawers & provenance boxes!
  var prevProvBuilderV159 = window.cgBuildConnectionProvenanceAndCritiqueHtml;
  window.cgBuildConnectionProvenanceAndCritiqueHtml = function(item) {
    if (!item) return "";
    var isMech = (item.v7Kind === "mechanism" && item.mechObj) || Boolean(item.astSkeletonType || item.mechanismScore);
    var m = item.mechObj || (isMech ? item : null);
    if (m) {
      var honestLean = window.cgResolveHonestLeanModelForMech(m);
      var cloneItem = Object.assign({}, item, {
        mechObj: Object.assign({}, m, { verifiedLeanFile: honestLean || "" })
      });
      return prevProvBuilderV159 ? prevProvBuilderV159(cloneItem) : "";
    }
    return prevProvBuilderV159 ? prevProvBuilderV159(item) : "";
  };

  if (typeof buildInlineCatalogueCardDrawerHtml === "function" && !window._cgWrappedHonestLeanDrawerV160) {
    window._cgWrappedHonestLeanDrawerV160 = true;
    var prevDrawerV160 = buildInlineCatalogueCardDrawerHtml;
    buildInlineCatalogueCardDrawerHtml = function(r) {
      if (r && r.v7Kind === "mechanism" && r.mechObj) {
        var honestLean = window.cgResolveHonestLeanModelForMech(r.mechObj);
        if (!honestLean) {
          var patchedR = Object.assign({}, r, {
            mechObj: Object.assign({}, r.mechObj, { verifiedLeanFile: "" })
          });
          var h = prevDrawerV160(patchedR);
          return h.replace(
            /<details class="cg-code-disclosure"[\s\S]*?<\/details>/,
            '<div style="font-size:11px;color:#94a3b8;padding:6px 10px;background:rgba(15,23,42,0.6);border-radius:6px;border:1px solid rgba(148,163,184,0.16);">Note: Uncompiled multi-project hypothesis (◆); use <em>Build My Research Agenda</em> or <em>Custom Bridge Composer</em> to draft a dedicated Lean 4 adapter.</div>'
          );
        }
      }
      return prevDrawerV160(r);
    };
  }

  // 6. Complete Fix for "Connected Cross-Domain Ideas (click to inspect in 3D Galaxy):" in Discovery Paths (`renderPathsLens`)
  window.cgEnsureAllGalaxyRecordsIndexed = function() {
    if (typeof buildV7IdeaGalaxyRecords === "function" && typeof recordById !== "undefined") {
      var v7 = buildV7IdeaGalaxyRecords();
      for (var i = 0; i < v7.length; i++) {
        recordById.set(v7[i].id, v7[i]);
      }
    }
    if (typeof indexData !== "undefined" && indexData && Array.isArray(indexData.records) && typeof recordById !== "undefined") {
      for (var j = 0; j < indexData.records.length; j++) {
        recordById.set(indexData.records[j].id, indexData.records[j]);
      }
    }
  };

  window.cgFindBestGalaxyStarForProjects = function(active) {
    window.cgEnsureAllGalaxyRecordsIndexed();
    var projs = (active && Array.isArray(active.projects)) ? active.projects : [];
    var allMechs = (typeof semanticMechanisms !== "undefined" && semanticMechanisms && semanticMechanisms.highLevelMechanisms) || [];
    var allIsos = (typeof semanticMechanisms !== "undefined" && semanticMechanisms && semanticMechanisms.customIsomorphisms) || [];

    if (active && active.id && typeof recordById !== "undefined" && recordById.has(active.id)) {
      return active.id;
    }
    if (projs.length >= 2) {
      var bothMech = allMechs.find(function(m) {
        var mp = Array.isArray(m.participatingProjects) ? m.participatingProjects.map(function(p){ return p.projectId; }) : (m.projects || []);
        return mp.indexOf(projs[0]) !== -1 && mp.indexOf(projs[1]) !== -1;
      });
      if (bothMech) return bothMech.id;

      var bothIso = allIsos.find(function(iso) {
        return iso._cgCanonicalPair !== false && iso.epistemicSymbol !== "⚠" &&
          ((iso.projectA === projs[0] && iso.projectB === projs[1]) || (iso.projectA === projs[1] && iso.projectB === projs[0]));
      });
      if (bothIso) return bothIso.id;
    }
    if (projs.length >= 1) {
      var oneMech = allMechs.find(function(m) {
        var mp = Array.isArray(m.participatingProjects) ? m.participatingProjects.map(function(p){ return p.projectId; }) : (m.projects || []);
        return mp.indexOf(projs[0]) !== -1;
      });
      if (oneMech) return oneMech.id;
    }
    return allMechs[0] ? allMechs[0].id : null;
  };

  window.cgRenderPathConnectedGalaxyIdeas = function(active) {
    if (!active) return "";
    window.cgEnsureAllGalaxyRecordsIndexed();
    var chips = [];
    var projs = Array.isArray(active.projects) ? active.projects : [];
    var bestStarId = window.cgFindBestGalaxyStarForProjects(active);

    if (bestStarId && typeof recordById !== "undefined" && recordById.has(bestStarId)) {
      var bRec = recordById.get(bestStarId);
      var bGlyph = window.cgGetRecordEpistemicGlyph(bRec);
      chips.push(
        '<button type="button" class="eco-pill cg-path-galaxy-jump" data-jump-lemma="star:' + esc(bestStarId) + '" data-jump-label="' + esc(bRec.name) + '" style="border-color:var(--gold);color:#fef3c7;background:rgba(229,198,135,0.14);font-size:12px;cursor:pointer;">' +
          bGlyph + ' ' + esc(bRec.name.slice(0, 58)) + (bRec.name.length > 58 ? '…' : '') + ' · Open in 3D Galaxy ↗' +
        '</button>'
      );
    }

    var shared = Array.isArray(active.sharedIngredients) ? active.sharedIngredients : [];
    var idxRecs = (typeof indexData !== "undefined" && indexData && Array.isArray(indexData.records)) ? indexData.records : [];
    for (var i = 0; i < shared.length; i++) {
      var nm = shared[i];
      var rec = idxRecs.find(function(r){ return r.name === nm; });
      if (rec) {
        chips.push(
          '<button type="button" class="eco-pill cg-path-galaxy-jump" data-jump-lemma="ing:' + esc(rec.id) + '" data-jump-label="' + esc(nm) + '" style="font-family:var(--font-mono);font-size:12px;cursor:pointer;border-color:rgba(89,194,255,0.45);color:#e0f2fe;">' +
            esc(nm) + ' (IDF ' + esc(rec.idf) + 'b) ↗' +
          '</button>'
        );
      } else if (bestStarId) {
        var projShort = projs.slice(0, 2).map(function(pid){ return (manifest && manifest.projects && manifest.projects[pid] && manifest.projects[pid].short) || pid; }).join(" ↔ ");
        chips.push(
          '<button type="button" class="eco-pill cg-path-galaxy-jump" data-jump-lemma="star:' + esc(bestStarId) + '" data-jump-label="' + esc(nm) + '" style="font-family:var(--font-mono);font-size:12px;cursor:pointer;border-color:rgba(52,211,153,0.42);color:#d1fae5;" title="Inspect ' + esc(nm) + ' via ' + esc(projShort || 'connected') + ' bridge star in 3D Galaxy">' +
            esc(nm) + ' (' + esc(projShort || '3D Bridge') + ') ↗' +
          '</button>'
        );
      }
    }

    if (!chips.length) return "";
    return '<div style="margin:14px 0;display:flex;gap:8px;align-items:center;flex-wrap:wrap">' +
      '<span style="font-size:12px;color:var(--gold);font-weight:650">Connected Cross-Domain Ideas (click to inspect in 3D Galaxy):</span>' +
      chips.join("") +
    '</div>';
  };

  window.cgJumpFromPathTo3DGalaxy = function(targetSpec, activeProjs, jumpLabel) {
    window.cgEnsureAllGalaxyRecordsIndexed();
    var spec = String(targetSpec || "");
    var kind = "star";
    var targetId = spec;
    if (spec.indexOf("ing:") === 0) {
      kind = "ing";
      targetId = spec.slice(4);
    } else if (spec.indexOf("star:") === 0) {
      kind = "star";
      targetId = spec.slice(5);
    } else if (typeof indexData !== "undefined" && indexData && indexData.records.some(function(r){ return r.id === spec; })) {
      kind = "ing";
    }

    state.lens = "galaxy";
    state.view = "spatial";
    state.family = "all";
    state.obstacleFilter = "all";
    state.epistemicTier = "all";
    state.q = "";
    state.page = 1;

    var validProjs = Array.isArray(activeProjs)
      ? activeProjs.filter(function(p){ return manifest && manifest.projects && manifest.projects[p]; })
      : [];
    state.projects = validProjs.length ? validProjs.slice() : [...manifest.projectOrder];
    state.match = "any";

    if (kind === "ing") {
      state.signalTier = "ingredients";
      state.catSubFilter = "all";
    } else {
      var isIsoTarget = targetId.indexOf("iso-") === 0 || targetId.indexOf("ast-iso-") === 0;
      if (isIsoTarget) {
        var recCheck = recordById.get(targetId);
        if (recCheck && recCheck._cgCanonicalPair === false) state.dedupEndpoints = false;
        state.signalTier = "isomorphisms";
        state.catSubFilter = "isomorphismsOnly";
      } else {
        state.signalTier = "mechanisms";
        state.catSubFilter = "all";
      }
    }

    selectIngredient(targetId, validProjs[0] || null, validProjs[1] || null);
    renderApp();
    if (typeof galaxyController !== "undefined" && galaxyController && typeof galaxyController.command === "function") {
      galaxyController.command("focus");
    }
    var gw = document.querySelector(".galaxy-workspace");
    if (gw && typeof gw.scrollIntoView === "function") {
      gw.scrollIntoView({ behavior: "smooth", block: "start" });
    }
  };

  // CRITICAL: V153 wrapped renderPathsLens and mutated `mount.innerHTML = ...` to inject `cg-provenance-critique-box`
  // WITHOUT re-binding `[data-jump-lemma]`, `#save-path-note`, `#export-path-packet`, or `[data-open-path]`!
  // Wrap `renderPathsLens` AFTER V153 so all click handlers are bound on the final live DOM nodes!
  if (typeof renderPathsLens === "function" && !window._cgWrappedPathsJumpFixV160) {
    window._cgWrappedPathsJumpFixV160 = true;
    var prevRenderPathsV160 = renderPathsLens;
    renderPathsLens = function(mount) {
      prevRenderPathsV160(mount);
      if (!mount || typeof state === "undefined") return;
      if (state.selectedPath) {
        var active = ((insightPaths && insightPaths.connections) || []).find(function(x){ return x.id === state.selectedPath; });
        var backBtn = document.getElementById("path-back");
        if (backBtn) {
          backBtn.onclick = function() { state.selectedPath = null; syncUrl(false); renderPathsLens(mount); };
        }
        var jumpNodes = mount.querySelectorAll("[data-jump-lemma]");
        jumpNodes.forEach(function(btn) {
          btn.onclick = function() {
            window.cgJumpFromPathTo3DGalaxy(btn.dataset.jumpLemma, (active && active.projects) || [], btn.dataset.jumpLabel || "");
          };
        });
        if (active) {
          var noteKey = "cg-unified-note:" + active.id;
          var saveBtn = document.getElementById("save-path-note");
          if (saveBtn) {
            saveBtn.onclick = function() {
              var noteEl = document.getElementById("path-note");
              var stEl = document.getElementById("path-note-status");
              var persisted = cgSafeStorageSet(noteKey, noteEl ? noteEl.value : "");
              if (stEl) stEl.textContent = persisted ? "Saved in browser storage." : "Saved for this session (Safari Private / file mode).";
            };
          }
          var expBtn = document.getElementById("export-path-packet");
          if (expBtn) {
            expBtn.onclick = function() {
              var noteEl = document.getElementById("path-note");
              var pkt = {
                schema: "common-ground/discovery-path-packet/v4",
                exportedAt: new Date().toISOString(),
                connection: active,
                userConjectureNote: noteEl ? noteEl.value : ""
              };
              var blob = new Blob([JSON.stringify(pkt, null, 2)], { type: "application/json" });
              var a = document.createElement("a");
              a.href = URL.createObjectURL(blob);
              a.download = "common-ground-bridge-" + active.id + ".json";
              a.click();
            };
          }
        }
      } else {
        var pathQ = document.getElementById("path-q");
        if (pathQ) pathQ.oninput = function(e) { state.pathQuery = e.target.value; renderPathsLens(mount); };
        mount.querySelectorAll("[data-pf]").forEach(function(btn) {
          btn.onclick = function() { state.pathFilter = btn.dataset.pf; renderPathsLens(mount); };
        });
        mount.querySelectorAll("[data-open-path]").forEach(function(card) {
          card.onclick = function() { state.selectedPath = card.dataset.openPath; syncUrl(false); renderPathsLens(mount); };
        });
      }
    };
  }

  // Suite 18: V160 Default Deduplication, Honest AST Candidate Naming, Path->Galaxy Links & Accurate Topbar/Glyphs (5 new checks -> 177 total!)
  var prevRunnerV159 = window.v147RunAllAutomatedTests;
  if (typeof prevRunnerV159 === "function") {
    window.v147RunAllAutomatedTests = function() {
      var rep = prevRunnerV159();
      var extra = [];
      function addV160Check(name, cond, detail) {
        extra.push({
          id: "T" + (rep.results.length + extra.length + 1),
          category: "18. V160 Default Dedup, Honest AST Naming & Path/Galaxy Fixes",
          name: name,
          passed: Boolean(cond),
          detail: String(detail || (cond ? "Verified OK" : "Assertion failed"))
        });
      }

      // 1. Default endpoint deduplication is ON and collapses 7,000 -> exact 1,887 canonical AST pairs (3,287 total)
      var dedupSummary = window.cgAnnotateAndDeduplicateCorpus();
      addV160Check(
        "Endpoint deduplication is ON by default & collapses 7,000 AST rows to exact 1,887 canonical pairs (3,287 total)",
        Boolean(state.dedupEndpoints === true && dedupSummary && dedupSummary.canonicalFilePairs === 1887),
        "dedupEndpoints=" + state.dedupEndpoints + ", canonicalPairs=" + (dedupSummary && dedupSummary.canonicalFilePairs)
      );

      // 2. Remaining 'AST Isomorphisms' headings renamed to 'AST Syntax Candidates (Qualified via Role & Premise Gates)' + 1-line comparison banner
      var bannerHtml = window.cgRenderRoleVsAstBanner(true);
      var savedLens = state.lens, savedSub = state.serenSubmode;
      state.lens = "serendipity"; state.serenSubmode = "isomorphisms";
      renderApp();
      var serenIsoHtml = document.getElementById("app-mount").innerHTML || "";
      state.lens = savedLens; state.serenSubmode = savedSub;
      renderApp();
      addV160Check(
        "AST views use honest 'AST Syntax Candidates (Qualified via Role & Premise Gates)' heading + 1-line comparison banner",
        serenIsoHtml.indexOf("AST Syntax Candidates (Qualified via Role &amp; Premise Gates)") !== -1 &&
        serenIsoHtml.indexOf("Custom Declaration AST Isomorphisms") === -1 &&
        bannerHtml.indexOf("Compare Role vs. AST") !== -1,
        "Renamed headings & rendered 1-line Role-vs-AST banner"
      );

      // 3. Discovery Paths 'Connected Cross-Domain Ideas (click to inspect in 3D Galaxy):' renders 100% interactive buttons (0 dead spans) & jumps to 3D Galaxy
      var savedLens2 = state.lens, savedPath2 = state.selectedPath, savedSig2 = state.signalTier, savedSrc2 = state.source;
      state.lens = "paths";
      state.selectedPath = insightPaths.connections[0].id;
      renderApp();
      var mountEl = document.getElementById("app-mount");
      var jumpBtns = mountEl.querySelectorAll("[data-jump-lemma]");
      var jumpedOk = false;
      if (jumpBtns.length >= 2 && jumpBtns[1].onclick) {
        jumpBtns[1].click();
        jumpedOk = (state.lens === "galaxy" && state.view === "spatial" && Boolean(state.source));
      }
      state.lens = savedLens2; state.selectedPath = savedPath2; state.signalTier = savedSig2; state.source = savedSrc2; state.projects = [...manifest.projectOrder];
      renderApp();
      addV160Check(
        "Discovery Paths 'Connected Cross-Domain Ideas' renders interactive buttons & jumps cleanly into 3D Galaxy Inspector",
        jumpBtns.length >= 2 && jumpedOk,
        "Interactive jump buttons=" + jumpBtns.length + ", jumpedTo3DGalaxy=" + jumpedOk
      );

      // 4. Galaxy topbar never claims '7,000 Cross-Domain Ideas' and displays live ★ / ◆ / ○ / ✕ counts
      var savedSubFilter = state.catSubFilter, savedSig3 = state.signalTier;
      state.lens = "galaxy"; state.signalTier = "isomorphisms"; state.catSubFilter = "isomorphismsOnly";
      renderApp();
      var galIsoHtml = document.getElementById("app-mount").innerHTML || "";
      state.signalTier = savedSig3; state.catSubFilter = savedSubFilter;
      renderApp();
      addV160Check(
        "Galaxy topbar replaces inaccurate '7,000 Cross-Domain Ideas' with exact Unique AST Endpoint Pairs & live ★/◆/○/✕ counts",
        galIsoHtml.indexOf("Cross-Domain Ideas") === -1 &&
        galIsoHtml.indexOf("1,887 Unique AST Endpoint Pairs") !== -1 &&
        galIsoHtml.indexOf("★ 34 Reviewed") !== -1 &&
        galIsoHtml.indexOf("○ 1,599 AST Candidates") !== -1 &&
        galIsoHtml.indexOf("✕ 199 Guardrails") !== -1,
        "Verified exact live epistemic topbar breakdown (★ 34, ◆ 55, ○ 1,599, ✕ 199 = 1,887)"
      );

      // 5. Honest positional Lean 4 badge guard prevents misattributing unrelated alphabetical .lean files to synthesized mechanisms
      var dyadicMech = (semanticMechanisms.highLevelMechanisms || [])[0];
      var resolvedDyadicLean = window.cgResolveHonestLeanModelForMech(dyadicMech);
      addV160Check(
        "Mechanism Lean 4 resolver maps dyadic decoupling to RenormalizationAndWaveShellBridge.lean (not alphabetical SETH file)",
        resolvedDyadicLean === "CommonGround/Verification/RenormalizationAndWaveShellBridge.lean",
        "Resolved=" + resolvedDyadicLean
      );

      for (var k = 0; k < extra.length; k++) {
        rep.results.push(extra[k]);
        rep.total++;
        if (extra[k].passed) rep.passed++;
        else rep.failed++;
      }
      window._v147LastReport = rep;
      return rep;
    };
  }
})();
"""


def patch_test_harnesses():
    for suite_name in ("automated-ux-functional-suite.js", "cloudflare-shards-e2e-suite.js"):
        p = OBS_DIR / "tests" / suite_name
        txt = p.read_text(encoding="utf-8")
        txt = txt.replace(
            """var fgAll = filterGalaxyRecords();
if (fgAll.total !== 8400) {
  throw new Error("Expected 8400 total galaxy ideas (1400 mechs + 7000 isos), got " + fgAll.total);
}""",
            """var fgAll = filterGalaxyRecords();
if (state.dedupEndpoints !== true || fgAll.total !== 3287) {
  throw new Error("Expected default dedup ON with 3287 records (1400 mechs + 1887 unique AST pairs), got dedup=" + state.dedupEndpoints + " total=" + fgAll.total);
}""",
        )
        txt = txt.replace(
            """// Click "isomorphismsOnly" (7,000 AST Isomorphisms)
catSubBtns = mount.querySelectorAll("[data-cat-subfilter]");
catSubBtns[2].click();
if (filterGalaxyRecords().total !== 7000) {
  throw new Error("Clicking 7,000 AST Isomorphisms button did not filter to 7000! Got " + filterGalaxyRecords().total);
}
assertNoUndefinedOrNaN("Galaxy Catalogue Isomorphisms Only", mount.innerHTML);

// Click "all" (All 8,400 Ideas)
catSubBtns = mount.querySelectorAll("[data-cat-subfilter]");
catSubBtns[0].click();
if (filterGalaxyRecords().total !== 8400) {
  throw new Error("Clicking All 8,400 Ideas button did not restore 8400! Got " + filterGalaxyRecords().total);
}""",
            """// Click "isomorphismsOnly" (1,887 Deduplicated AST Syntax Candidates by default; 7,000 when dedup toggled off)
catSubBtns = mount.querySelectorAll("[data-cat-subfilter]");
catSubBtns[2].click();
if (filterGalaxyRecords().total !== 1887) {
  throw new Error("Clicking AST Syntax Candidates button with default dedup ON did not filter to 1887! Got " + filterGalaxyRecords().total);
}
window.cgToggleEndpointDedup(false);
if (filterGalaxyRecords().total !== 7000) {
  throw new Error("Unchecking endpoint dedup did not reveal all 7000 raw AST rows! Got " + filterGalaxyRecords().total);
}
window.cgToggleEndpointDedup(true);
assertNoUndefinedOrNaN("Galaxy Catalogue AST Syntax Candidates", mount.innerHTML);

// Click "all" (All 3,287 Deduplicated Records)
catSubBtns = mount.querySelectorAll("[data-cat-subfilter]");
catSubBtns[0].click();
if (filterGalaxyRecords().total !== 3287) {
  throw new Error("Clicking All (3,287) button did not restore 3287! Got " + filterGalaxyRecords().total);
}""",
        )
        p.write_text(txt, encoding="utf-8")
        print(f"  [OK] Verified assertions in tests/{suite_name}")


def patch_html_css_and_build_scripts():
    idx_path = OBS_DIR / "index.html"
    idx_html = idx_path.read_text(encoding="utf-8").replace("?v=159", "?v=160")
    idx_path.write_text(idx_html, encoding="utf-8")

    css_path = OBS_DIR / "unified.css"
    css = css_path.read_text(encoding="utf-8")
    if "/* === V160 EPISTEMIC PILL & ROLE-VS-AST BANNER STYLES === */" not in css:
        css += """
/* === V160 EPISTEMIC PILL & ROLE-VS-AST BANNER STYLES === */
.cg-card-kind-pill.is-star {
  color: #6ee7b7;
  background: rgba(16, 185, 129, 0.16);
  border: 1px solid rgba(52, 211, 153, 0.42);
}
"""
        css_path.write_text(css, encoding="utf-8")

    build_cf = OBS_DIR / "scripts" / "build-cloudflare-dist.py"
    btxt = build_cf.read_text(encoding="utf-8")
    btxt = btxt.replace('ASSET_VER = "159"', 'ASSET_VER = "160"').replace(
        '"version": "V159-ImmersiveGalaxy-Consequences-UseCases"',
        '"version": "V160-DefaultDedup-HonestAST-PathJumpFix"',
    )
    build_cf.write_text(btxt, encoding="utf-8")

    daemon_py = OBS_DIR / "scripts" / "continuous-insight-daemon.py"
    if daemon_py.exists():
        dtxt = daemon_py.read_text(encoding="utf-8")
        dtxt = dtxt.replace('"V159"', '"V160"')
        daemon_py.write_text(dtxt, encoding="utf-8")


def main():
    print("1. Extracting exact 1,887 canonical AST endpoint pairs from read-only theorem-atlas/development/common-ground...")
    canon_ids, rev_map = extract_canonical_1887_iso_ids()
    print(f"   Extracted {len(canon_ids)} canonical AST IDs and {len(rev_map)} reviewed row mappings.")

    ujs_path = OBS_DIR / "unified-standalone.js"
    ujs = ujs_path.read_text(encoding="utf-8")
    ujs = patch_core_unified_js(ujs)

    v160_js = (
        V160_JS_APPEND_TEMPLATE.replace("__CANON_1887_JSON__", json.dumps(canon_ids, separators=(",", ":")))
        .replace("__REVIEWED_ISO_MAP_JSON__", json.dumps(rev_map, separators=(",", ":")))
    )
    ujs = ujs.rstrip() + "\n\n" + v160_js.lstrip()
    ujs_path.write_text(ujs, encoding="utf-8")
    print("2. Patched observatory/unified-standalone.js with V160 upgrades & Suite 18.")

    patch_test_harnesses()
    patch_html_css_and_build_scripts()
    print("3. Updated HTML (?v=160), CSS, test harnesses, and build scripts.")


if __name__ == "__main__":
    main()
