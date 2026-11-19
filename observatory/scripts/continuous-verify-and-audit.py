#!/usr/bin/env python3
"""
Deterministic Zero-Clutter Mathematical, Lean 4.33.0 Kernel & Unified Browser Shard Verification Harness (V248).
Verifies:
1. All 772+ physical Lean 4 files (649 in CommonGround/Verification/ + 123 in 01..10-*) have 0 `sorry`/`admit`/`sorryAx`
   tokens outside comments (with NO 25 MiB cap on `.lean` files — large `.lean` files stream via Cloudflare R2 `/api/lean/*`)
   AND compile cleanly through the real Lean 4.33.0 kernel (`compile-all-lean4.py`).
2. Reconstructs `bundle-data.js` from the 8 tracked `<16 MiB` shards and builds `dist-cloudflare/` if absent in CI.
3. Verifies end-to-end connection integrity & zero clutter:
   - 0 legacy `upgrade-v*.py` scripts and 0 `.pyc` / `__pycache__` artifacts;
   - entire unsharded `bundle-data.js` is < 16.20 MiB UTF-8 bytes;
   - 0 unmounted ghost repository IDs, 0 `‖c‖h‖a‖r‖` corrupted strings, 0 `127.0.0.1`/`localhost` dead links,
     and 0 `Solved Open Instance` / `Hodge Sextic` strings across `bundle-data.js`;
   - exact 1-to-1 bijection between `verifiedLeanSuites` and `CommonGround/Verification/*.lean` with ground-truth title & triad alignment;
   - 100% of `highLevelMechanisms[*].verifiedBridgeFile` and `insightPaths.connections[*].verifiedLeanFile` resolve on disk;
   - 100% of `proofPipelines` map `projectA` & `projectB` to canonical 40-project IDs, and 100% of `customIsomorphisms` (`isoMetaPools` / `_x`),
     `highLevelMechanisms` (`fieldPools` / `_mx`), `proofPipelines` (`pipelinePools`), `grandTrinities`, `verifiedLeanSuites` (`suitePools` / `_sp`),
     `customSearchIndex` (`csiPools` / `_cx`), and `insightPaths.connections` (`pathPools` / `_ix`) resolve valid lossless pool indices;
   - `README.md` contains 0 legacy forbidden strings and 100% resolving relative `./...` links.
4. Confirms no legacy forked `safari-standalone.html` or `observatory/safari/` artifacts exist, and verifies all unified
   Chrome + Safari routes resolve CSS + all 8 untruncated `<25 MiB` shards + `unified-standalone.js`.
5. Runs `observatory/tests/run-tests.sh` (all automated UX, DOM click, mathematical, WebKit JSC `file://` & Node CI checks).
"""
import json
import re
import subprocess
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
OBS_DIR = REPO_ROOT / "observatory"
LIMIT_BYTES = 25 * 1024 * 1024  # Applies ONLY to Cloudflare Pages static web assets (NOT .lean files!)


def ensure_bundle_reconstructed():
    if not (OBS_DIR / "bundle-data.js").exists():
        subprocess.run(["python3", "-B", str(OBS_DIR / "scripts" / "reconstruct-bundle-data.py")], check=True)
    if not (OBS_DIR / "dist-cloudflare" / "index.html").exists():
        subprocess.run(["python3", "-B", str(OBS_DIR / "scripts" / "build-cloudflare-dist.py")], check=True)


def check_lean_corpus_and_kernel():
    subprocess.run(["python3", "-B", str(OBS_DIR / "scripts" / "compile-all-lean4.py")], check=True)


def check_end_to_end_connections_and_clutter():
    obsolete_upgrades = list((OBS_DIR / "scripts").glob("upgrade-v*.py"))
    assert not obsolete_upgrades, f"Obsolete upgrade-v*.py clutter scripts must not exist: {obsolete_upgrades[:5]}"
    pyc_files = [p for p in REPO_ROOT.rglob("*.pyc") if ".git" not in p.parts]
    assert not pyc_files, f"Bytecode .pyc files detected (violates Zero Bytecode rule): {pyc_files[:5]}"

    raw_bytes = (OBS_DIR / "bundle-data.js").stat().st_size
    assert raw_bytes < int(15.0 * 1024 * 1024), f"Expected sub-15.0 MiB bundle-data.js, got {raw_bytes / (1024*1024):.2f} MiB!"
    raw = (OBS_DIR / "bundle-data.js").read_text(encoding="utf-8")
    for bad_str in ("127.0.0.1", "localhost:", "Solved Open Instance", "Hodge Sextic", "window.V145_REAL_LEAN_SUITES ="):
        assert bad_str not in raw, f"Legacy/clutter string {bad_str!r} reintroduced into bundle-data.js!"
    assert not re.search(r"‖[^‖\s]‖[^‖\s]‖", raw), "Character-corrupted ‖c‖h‖a‖r‖ string reintroduced into bundle-data.js!"
    ghost_rx = re.compile(
        r"\b(?:probability-lean|aks|optlib|category-theory-lean|pfr|group-theory-lean|"
        r"graph-theory-lean|combinatorics-lean|algebra-lean|formal-conjectures|number-theory-lean)\b"
    )
    ghost_m = ghost_rx.search(raw)
    assert not ghost_m, f"Unmounted ghost repository ID reintroduced into bundle-data.js: {ghost_m.group(0)!r}"
    prefix = "window.__CG_PRELOADED__ = "
    preloaded, _ = json.JSONDecoder().raw_decode(raw, raw.index(prefix) + len(prefix))
    canon_projs = set(preloaded["manifest"]["projectOrder"])
    sm = preloaded["semanticMechanisms"]
    suites = sm.get("verifiedLeanSuites", [])
    suite_pools = sm.get("suitePools") or {}
    assert len(suite_pools.get("blbls") or []) >= 300 and len(suite_pools.get("tns") or []) >= 250, (
        "Lossless suitePools missing or truncated!"
    )
    for sv in suites:
        if "_sp" in sv:
            sp_vec = sv["_sp"]
            if len(sp_vec) > 0 and sp_vec[0] >= 0:
                assert 0 <= sp_vec[0] < len(suite_pools["blbls"]), f"Out-of-bounds _sp[0] on {sv.get('id')}"
            if len(sp_vec) > 3 and sp_vec[3] >= 0:
                assert 0 <= sp_vec[3] < len(suite_pools["tns"]), f"Out-of-bounds _sp[3] on {sv.get('id')}"
    disk_verif = sorted(str(p.relative_to(REPO_ROOT)) for p in (REPO_ROOT / "CommonGround" / "Verification").glob("*.lean"))
    suite_files = sorted(s.get("leanFile") or "" for s in suites)
    assert suite_files == disk_verif, (
        f"verifiedLeanSuites ({len(suite_files)}) is not in 1-to-1 bijection with CommonGround/Verification/*.lean ({len(disk_verif)})!"
    )
    assert len(suites) >= 650, f"Expected >= 650 verifiedLeanSuites in V249+, got {len(suites)}!"
    assert suites and "Williams" in (suites[0].get("title") or ""), "verifiedLeanSuites[0] ground-truth title alignment broken!"
    assert (suites[0].get("projects") or [None])[0] == "apsp3sum", "verifiedLeanSuites[0] ground-truth triad alignment broken!"
    covered_suite_projs = {p for s in suites for p in (s.get("projects") or []) if p in canon_projs}
    assert covered_suite_projs == canon_projs, f"verifiedLeanSuites missing canonical projects: {canon_projs - covered_suite_projs}"

    sn_pool = sm.get("snippetPool") or []
    assert len(sn_pool) >= 2800, "Lossless semanticMechanisms.snippetPool missing or truncated!"
    csi_pools = preloaded.get("csiPools") or {}
    csi_fns = csi_pools.get("fns") or []
    assert (
        len(csi_pools.get("files") or []) > 900
        and len(csi_pools.get("evidences") or []) >= 700
        and len(csi_fns) >= 4500
    ), "Lossless csiPools.files / evidences / fns missing or truncated!"
    for r in preloaded.get("customSearchIndex", []):
        if "_cx" in r and len(r["_cx"]) > 0 and r["_cx"][0] >= 0:
            assert 0 <= r["_cx"][0] < len(csi_fns), f"Out-of-bounds _cx[0] (fns) on {r.get('name')}"
    tr_pools = sm.get("trinityPools") or {}
    tr_dm_meta = tr_pools.get("dmMeta") or {}
    assert len(tr_pools.get("domains") or []) > 900 and len(tr_dm_meta.get("projs") or []) >= 35, (
        "Lossless trinityPools.domains / dmMeta missing or truncated!"
    )
    for gt in sm.get("grandTrinities", []):
        assert "unifyingEquation" not in gt, f"Unreferenced dead key unifyingEquation reintroduced on {gt.get('id')}!"
    for fam in preloaded.get("constellationCatalog", {}).get("families", []):
        for dead_fk in ("scopeNotes", "comparatorConfigurations", "tags", "shards", "manuscripts", "sharedIngredientCount"):
            assert dead_fk not in fam, (
                f"Unreferenced dead constellationCatalog.families key {dead_fk!r} reintroduced on {fam.get('id')}!"
            )

    mech_pools = sm.get("mechPools") or {}
    part_items = mech_pools.get("partItems") or []
    part_meta = mech_pools.get("partMeta") or {}
    mech_pbs = mech_pools.get("playbooks") or []
    mech_fp = mech_pools.get("fieldPools") or {}
    vbridges_pool = mech_fp.get("vbridges") or []
    mf_projs = mech_fp.get("projs") or []
    mf_names = mech_fp.get("names") or []
    mf_pints = mech_fp.get("pints") or []
    mf_otags = mech_fp.get("otags") or []
    mf_slabels = mech_fp.get("slabels") or []
    mf_whys = mech_fp.get("whys") or []
    mf_sstructs = mech_fp.get("sstructs") or []
    mf_obls = mech_fp.get("obls") or []
    assert (
        len(part_items) > 3500 and len(mech_pbs) >= 150 and len(part_meta.get("files") or []) >= 400
        and len(vbridges_pool) >= 300 and len(mf_projs) >= 100
        and len(mech_pools.get("stepStrs") or []) >= 400
    ), "Lossless mechPools / fieldPools / stepStrs missing or truncated!"
    dead_mech_keys = (
        "tacticStepper",
        "openConjectureAttackTree",
        "dualityDictionary",
        "threeHopChain",
        "constantOptimizer",
        "personaExplanations",
        "counterexampleTests",
        "targetAstPatched",
        "sourceAstBefore",
        "plainEnglishHeadline",
        "headline",
    )
    mech_keys = (
        "_rp", "_ps", "_an", "_id", "_td", "_vs", "_ast", "_eg",
        "_df", "_ct", "_vl", "_vb", "_tg", "_nh", "_lt", "_oc",
        "_cs", "_da",
    )
    for m in sm.get("highLevelMechanisms", []):
        mv = dict(m)
        if "_mx" in m:
            mx = m["_mx"]
            for ki, kk in enumerate(mech_keys):
                if ki < len(mx) and isinstance(mx[ki], int) and mx[ki] >= 0:
                    mv[kk] = mx[ki]
            if len(mx) > 18 and mx[18] >= 0:
                assert 0 <= mx[18] < len(mf_projs), f"Out-of-bounds _mx[18] (projs) on {m.get('id')}"
            if len(mx) > 19 and mx[19] >= 0:
                assert 0 <= mx[19] < len(mf_names), f"Out-of-bounds _mx[19] (names) on {m.get('id')}"
            if len(mx) > 20 and mx[20] >= 0:
                assert 0 <= mx[20] < len(mf_pints), f"Out-of-bounds _mx[20] (pints) on {m.get('id')}"
            if len(mx) > 21 and mx[21] >= 0:
                assert 0 <= mx[21] < len(mf_otags), f"Out-of-bounds _mx[21] (otags) on {m.get('id')}"
            if len(mx) > 22 and mx[22] >= 0:
                assert 0 <= mx[22] < len(mf_slabels), f"Out-of-bounds _mx[22] (slabels) on {m.get('id')}"
            if len(mx) > 23 and mx[23] >= 0:
                assert 0 <= mx[23] < len(mf_whys), f"Out-of-bounds _mx[23] (whys) on {m.get('id')}"
            if len(mx) > 24 and mx[24] >= 0:
                assert 0 <= mx[24] < len(mf_sstructs), f"Out-of-bounds _mx[24] (sstructs) on {m.get('id')}"
            if len(mx) > 25 and mx[25] >= 0:
                assert 0 <= mx[25] < len(mf_obls), f"Out-of-bounds _mx[25] (obls) on {m.get('id')}"
        bf = mv.get("verifiedBridgeFile") or (vbridges_pool[mv["_vb"]] if isinstance(mv.get("_vb"), int) else None)
        if bf:
            assert (REPO_ROOT / bf).exists(), f"Broken highLevelMechanisms.verifiedBridgeFile: {bf}"
        if "_pp" in mv:
            assert all(0 <= idx < len(part_items) for idx in mv["_pp"]), f"Out-of-bounds _pp index on {m.get('id')}"
        if "_rp" in mv:
            assert 0 <= mv["_rp"] < len(mech_pbs), f"Out-of-bounds _rp index on {m.get('id')}"
        for dead_k in dead_mech_keys:
            assert dead_k not in m, f"Stale ghost-project or synthetic field {dead_k!r} reintroduced on mechanism {m.get('id')}!"
    pipe_pools = sm.get("pipelinePools") or {}
    pipe_stages = pipe_pools.get("stages") or []
    assert len(pipe_stages) >= 200 and len(pipe_pools.get("stageStrs") or []) >= 200, (
        "Lossless pipelinePools.stages / stageStrs missing or truncated!"
    )
    for pp in sm.get("proofPipelines", []):
        assert pp.get("projectA") in canon_projs and pp.get("projectB") in canon_projs, (
            f"Broken or non-canonical proofPipeline projects on {pp.get('id')}: {pp.get('projectA')} <-> {pp.get('projectB')}"
        )
        if "_st" in pp:
            assert 0 <= pp["_st"] < len(pipe_stages), f"Out-of-bounds _st index on {pp.get('id')}"
    path_pools = preloaded.get("insightPaths", {}).get("pathPools") or {}
    ep_pool = path_pools.get("endpoints") or []
    ep_meta = path_pools.get("epMeta") or {}
    db_pool = path_pools.get("discBridges") or []
    pp_vleans = path_pools.get("vleans") or []
    pp_mids = path_pools.get("mids") or []
    assert (
        len(ep_pool) > 3500 and len(db_pool) >= 100 and len(ep_meta.get("paths") or []) >= 400
        and len(pp_vleans) >= 250 and len(pp_mids) >= 500
    ), "Lossless pathPools missing or truncated!"
    conn_keys = (
        "_td", "_cv", "_ls", "_sm", "_rw", "_db", "_tl", "_an",
        "_si", "_rl", "_ds", "_kd", "_wm", "_oc", "_pjs", "_vl",
        "_hr", "_fms", "_ct", "_st",
    )
    for c in preloaded.get("insightPaths", {}).get("connections", []):
        cv = dict(c)
        if "_ix" in c:
            ix = c["_ix"]
            for ki, kk in enumerate(conn_keys):
                if ki < len(ix) and isinstance(ix[ki], int) and ix[ki] >= 0:
                    cv[kk] = ix[ki]
            if len(ix) > 20 and ix[20] >= 0:
                assert 0 <= ix[20] < len(pp_mids), f"Out-of-bounds _ix[20] (mids) on {c.get('id')}"
        vf = cv.get("verifiedLeanFile") or (pp_vleans[cv["_vl"]] if isinstance(cv.get("_vl"), int) else None)
        if vf:
            assert (REPO_ROOT / vf).exists(), f"Broken insightPaths.connections.verifiedLeanFile: {vf}"
        if "_ep" in cv:
            assert all(0 <= idx < len(ep_pool) for idx in cv["_ep"]), f"Out-of-bounds _ep index on {c.get('id')}"
        if "_db" in cv:
            assert 0 <= cv["_db"] < len(db_pool), f"Out-of-bounds _db index on {c.get('id')}"
        for dead_ck in ("sourceAstBefore", "conjecture", "intuitionAnalogy", "headline", "targetProject"):
            assert dead_ck not in c, f"Unreferenced duplicate field {dead_ck!r} reintroduced into insightPaths.connections!"
    assert "verificationSuiteBridges" not in sm, "Unreferenced verificationSuiteBridges clutter reintroduced!"
    dp = sm.get("isoDeclPool") or []
    dm = sm.get("declMeta") or {}
    w1 = sm.get("isoWhy1Pool") or []
    w2 = sm.get("isoWhy2Pool") or []
    tp = sm.get("isoTierPool") or []
    imp = sm.get("isoMetaPools") or {}
    i_sk = imp.get("skels") or []
    i_pn = imp.get("pnames") or []
    i_pj = imp.get("projs") or []
    i_es = imp.get("syms") or []
    i_mi = imp.get("mids") or []
    assert (
        len(dp) > 3000 and len(dm.get("files") or []) >= 400 and len(w1) > 200 and len(w2) > 700
        and len(tp) > 200 and len(i_sk) >= 20 and len(i_pn) == 40
        and len(i_pj) == 40 and len(i_es) >= 3 and len(i_mi) >= 900
    ), "Lossless isomorphism pools missing or truncated!"
    iso_keys = (
        "_pA", "_pB", "_es", "_mi", "_dA", "_dB", "_w1", "_w2",
        "_et", "_sk", "_pa", "_pAN", "_pBN", "_dcA", "_dcB", "_oc",
        "_tdA", "_tdB", "_kd", "_so", "_wm", "_tb", "_mA", "_mB",
    )
    for iso in sm.get("customIsomorphisms", []):
        iv = dict(iso)
        if "_x" in iso:
            xv = iso["_x"]
            for ki, kk in enumerate(iso_keys):
                if ki < len(xv) and isinstance(xv[ki], int) and xv[ki] >= 0:
                    iv[kk] = xv[ki]
        assert "targetProject" not in iso, f"Dead unreferenced targetProject reintroduced on {iso.get('id')}!"
        assert "declA" in iv or (isinstance(iv.get("_dA"), int) and 0 <= iv["_dA"] < len(dp)), f"Invalid _dA on {iso.get('id')}"
        assert "declB" in iv or (isinstance(iv.get("_dB"), int) and 0 <= iv["_dB"] < len(dp)), f"Invalid _dB on {iso.get('id')}"
        if "_pA" in iv:
            assert 0 <= iv["_pA"] < len(i_pj), f"Invalid _pA on {iso.get('id')}"
        if "_pB" in iv:
            assert 0 <= iv["_pB"] < len(i_pj), f"Invalid _pB on {iso.get('id')}"
        if "_es" in iv:
            assert 0 <= iv["_es"] < len(i_es), f"Invalid _es on {iso.get('id')}"
        if "_mi" in iv:
            assert 0 <= iv["_mi"] < len(i_mi), f"Invalid _mi on {iso.get('id')}"
        if "_w1" in iv:
            assert 0 <= iv["_w1"] < len(w1), f"Invalid _w1 on {iso.get('id')}"
        if "_w2" in iv:
            assert 0 <= iv["_w2"] < len(w2), f"Invalid _w2 on {iso.get('id')}"
        if "_et" in iv:
            assert 0 <= iv["_et"] < len(tp), f"Invalid _et on {iso.get('id')}"
        if "_sk" in iv:
            assert 0 <= iv["_sk"] < len(i_sk), f"Invalid _sk on {iso.get('id')}"
        es_val = iv.get("epistemicSymbol") or (i_es[iv["_es"]] if isinstance(iv.get("_es"), int) else None)
        if es_val == "⚠":
            assert "transferHypothesis" not in iv and "transferBlueprint" not in iv and "_tb" not in iv, (
                f"Contradicted optimistic transferHypothesis/transferBlueprint clutter found on ⚠ lookalike {iso.get('id')}!"
            )
    for disc in preloaded.get("unrelatedBridges", {}).get("discoveries", []):
        ct = disc.get("conjectureTemplate") or ""
        assert "AllBridges.lean" not in ct, f"Generic AllBridges.lean reference found in unrelatedBridges {disc.get('id')}!"

    readme_txt = (REPO_ROOT / "README.md").read_text(encoding="utf-8")
    for forbidden in ("hodge.computer", "hodge-computer", "arXiv:2603.29157", "sextics"):
        assert forbidden not in readme_txt, f"Forbidden legacy reference {forbidden!r} found in README.md!"
    for rel_link in re.findall(r"\]\((\./[^)#?]+)", readme_txt):
        target = (REPO_ROOT / rel_link).resolve()
        assert target.exists(), f"Broken relative link {rel_link} in README.md -> {target}"
    print(
        f"  [OK] End-to-end connection bijection verified: {len(suites)} suites == {len(disk_verif)} CommonGround/Verification/*.lean, "
        f"bundle={raw_bytes/(1024*1024):.2f} MiB (<15.0 MiB!), {len(sn_pool)} unique snippets, {len(sm.get('proofPipelines', []))} canonical pipelines, "
        f"{len(dp)} pooled decls, {len(i_sk)} iso skels, {len(part_items)} mech items, {len(ep_pool)} path endpoints, "
        f"0 ghost repo IDs, 0 127.0.0.1 links, 0 ‖c‖h‖a‖r‖ corruptions, 0 broken .lean refs, README clean."
    )


def check_unified_static_assets():
    assert not (OBS_DIR / "safari-standalone.html").exists(), "Obsolete safari-standalone.html fork must not exist!"
    assert not (OBS_DIR / "safari").exists(), "Obsolete observatory/safari/ fork directory must not exist!"

    routes = [
        OBS_DIR / "index.html",
        OBS_DIR / "universe" / "sources" / "index.html",
        OBS_DIR / "preview" / "v20" / "index.html",
        OBS_DIR / "dist-cloudflare" / "index.html",
        OBS_DIR / "dist-cloudflare" / "universe" / "sources" / "index.html",
    ]
    ref_rx = re.compile(r'(?:src|href)="([^"#?]+)(?:\?[^"]*)?"')
    for html_file in routes:
        assert html_file.exists(), f"Missing route HTML: {html_file}"
        txt = html_file.read_text(encoding="utf-8")
        assert "bundle-data.js" not in txt, f"Monolithic bundle-data.js still referenced in {html_file}!"
        assert "safari-standalone" not in txt, f"Obsolete safari-standalone reference found in {html_file}!"
        refs = ref_rx.findall(txt)
        checked = 0
        for r in refs:
            if r.startswith(("./", "../")) and r not in ("./", "../"):
                target = (html_file.parent / r).resolve()
                assert target.exists(), f"Broken relative asset {r} in {html_file} -> {target}"
                assert target.stat().st_size < LIMIT_BYTES, f"Static web asset {target} exceeds 25 MiB Pages cap!"
                checked += 1
        assert checked >= 10, f"Expected >= 10 resolved assets (CSS + 8 shards + app JS) in {html_file}, got {checked}"
        print(f"  [OK] Unified Chrome/Safari route {html_file.relative_to(OBS_DIR)} resolved {checked} untruncated assets (all < 25 MiB).")


def main():
    print("=== Running V249 End-to-End Lean 4.33.0 Kernel & Unified Chrome/Safari Observatory Audit ===")
    ensure_bundle_reconstructed()
    check_lean_corpus_and_kernel()
    check_end_to_end_connections_and_clutter()
    check_unified_static_assets()
    subprocess.run(["bash", str(OBS_DIR / "tests" / "run-tests.sh")], check=True)
    print("=== ALL V248 CONTINUOUS VERIFICATION CHECKS PASSED (EXIT 0) ===")


if __name__ == "__main__":
    main()
