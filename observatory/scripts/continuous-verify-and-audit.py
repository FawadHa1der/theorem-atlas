#!/usr/bin/env python3
"""
Deterministic Zero-Clutter Mathematical, Lean 4.33.0 Kernel & Unified Browser Shard Verification Harness (V245).
Verifies:
1. All 766+ physical Lean 4 files (646 in CommonGround/Verification/ + 120 in 01..10-*) have 0 `sorry`/`admit`/`sorryAx`
   tokens outside comments (with NO 25 MiB cap on `.lean` files — large `.lean` files stream via Cloudflare R2 `/api/lean/*`)
   AND compile cleanly through the real Lean 4.33.0 kernel (`compile-all-lean4.py`).
2. Reconstructs `bundle-data.js` from the 8 tracked `<16 MiB` shards and builds `dist-cloudflare/` if absent in CI.
3. Verifies end-to-end connection integrity & zero clutter:
   - 0 legacy `upgrade-v*.py` scripts and 0 `.pyc` / `__pycache__` artifacts;
   - entire unsharded `bundle-data.js` is < 20.20 MiB UTF-8 bytes;
   - 0 unmounted ghost repository IDs, 0 `‖c‖h‖a‖r‖` corrupted strings, 0 `127.0.0.1`/`localhost` dead links,
     and 0 `Solved Open Instance` / `Hodge Sextic` strings across `bundle-data.js`;
   - exact 1-to-1 bijection between `verifiedLeanSuites` and `CommonGround/Verification/*.lean` with ground-truth title & triad alignment;
   - 100% of `highLevelMechanisms[*].verifiedBridgeFile` and `insightPaths.connections[*].verifiedLeanFile` resolve on disk;
   - 100% of `proofPipelines` map `projectA` & `projectB` to canonical 40-project IDs, and 100% of `customIsomorphisms`,
     `highLevelMechanisms` (`fieldPools`), `proofPipelines` (`pipelinePools`), `grandTrinities`, `customSearchIndex`, and `insightPaths.connections` resolve valid lossless pool indices;
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
    assert raw_bytes < int(20.2 * 1024 * 1024), f"Expected sub-20.2 MiB bundle-data.js, got {raw_bytes / (1024*1024):.2f} MiB!"
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
    disk_verif = sorted(str(p.relative_to(REPO_ROOT)) for p in (REPO_ROOT / "CommonGround" / "Verification").glob("*.lean"))
    suite_files = sorted(s.get("leanFile") or "" for s in suites)
    assert suite_files == disk_verif, (
        f"verifiedLeanSuites ({len(suite_files)}) is not in 1-to-1 bijection with CommonGround/Verification/*.lean ({len(disk_verif)})!"
    )
    assert suites and "Williams" in (suites[0].get("title") or ""), "verifiedLeanSuites[0] ground-truth title alignment broken!"
    assert (suites[0].get("projects") or [None])[0] == "apsp3sum", "verifiedLeanSuites[0] ground-truth triad alignment broken!"
    covered_suite_projs = {p for s in suites for p in (s.get("projects") or []) if p in canon_projs}
    assert covered_suite_projs == canon_projs, f"verifiedLeanSuites missing canonical projects: {canon_projs - covered_suite_projs}"

    sn_pool = sm.get("snippetPool") or []
    assert len(sn_pool) >= 2800, "Lossless semanticMechanisms.snippetPool missing or truncated!"
    csi_pools = preloaded.get("csiPools") or {}
    assert len(csi_pools.get("files") or []) > 900, "Lossless csiPools.files missing or truncated!"
    tr_pools = sm.get("trinityPools") or {}
    assert len(tr_pools.get("domains") or []) > 900, "Lossless trinityPools.domains missing or truncated!"
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
    assert (
        len(part_items) > 3500 and len(mech_pbs) >= 150 and len(part_meta.get("files") or []) >= 400 and len(vbridges_pool) >= 300
    ), "Lossless mechPools / fieldPools missing or truncated!"
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
    for m in sm.get("highLevelMechanisms", []):
        bf = m.get("verifiedBridgeFile") or (vbridges_pool[m["_vb"]] if isinstance(m.get("_vb"), int) else None)
        if bf:
            assert (REPO_ROOT / bf).exists(), f"Broken highLevelMechanisms.verifiedBridgeFile: {bf}"
        if "_pp" in m:
            assert all(0 <= idx < len(part_items) for idx in m["_pp"]), f"Out-of-bounds _pp index on {m.get('id')}"
        if "_rp" in m:
            assert 0 <= m["_rp"] < len(mech_pbs), f"Out-of-bounds _rp index on {m.get('id')}"
        for dead_k in dead_mech_keys:
            assert dead_k not in m, f"Stale ghost-project or synthetic field {dead_k!r} reintroduced on mechanism {m.get('id')}!"
    pipe_pools = sm.get("pipelinePools") or {}
    pipe_stages = pipe_pools.get("stages") or []
    assert len(pipe_stages) >= 200, "Lossless pipelinePools.stages missing or truncated!"
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
    assert len(ep_pool) > 3500 and len(db_pool) >= 100 and len(ep_meta.get("paths") or []) >= 400, "Lossless pathPools missing or truncated!"
    for c in preloaded.get("insightPaths", {}).get("connections", []):
        vf = c.get("verifiedLeanFile")
        if vf:
            assert (REPO_ROOT / vf).exists(), f"Broken insightPaths.connections.verifiedLeanFile: {vf}"
        if "_ep" in c:
            assert all(0 <= idx < len(ep_pool) for idx in c["_ep"]), f"Out-of-bounds _ep index on {c.get('id')}"
        if "_db" in c:
            assert 0 <= c["_db"] < len(db_pool), f"Out-of-bounds _db index on {c.get('id')}"
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
    assert (
        len(dp) > 3000 and len(dm.get("files") or []) >= 400 and len(w1) > 200 and len(w2) > 700
        and len(tp) > 200 and len(i_sk) >= 20 and len(i_pn) == 40
    ), "Lossless isomorphism pools missing or truncated!"
    for iso in sm.get("customIsomorphisms", []):
        assert "targetProject" not in iso, f"Dead unreferenced targetProject reintroduced on {iso.get('id')}!"
        assert "declA" in iso or (isinstance(iso.get("_dA"), int) and 0 <= iso["_dA"] < len(dp)), f"Invalid _dA on {iso.get('id')}"
        assert "declB" in iso or (isinstance(iso.get("_dB"), int) and 0 <= iso["_dB"] < len(dp)), f"Invalid _dB on {iso.get('id')}"
        if "_w1" in iso:
            assert 0 <= iso["_w1"] < len(w1), f"Invalid _w1 on {iso.get('id')}"
        if "_w2" in iso:
            assert 0 <= iso["_w2"] < len(w2), f"Invalid _w2 on {iso.get('id')}"
        if "_et" in iso:
            assert 0 <= iso["_et"] < len(tp), f"Invalid _et on {iso.get('id')}"
        if "_sk" in iso:
            assert 0 <= iso["_sk"] < len(i_sk), f"Invalid _sk on {iso.get('id')}"
        if iso.get("epistemicSymbol") == "⚠":
            assert "transferHypothesis" not in iso and "transferBlueprint" not in iso and "_tb" not in iso, (
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
        f"bundle={raw_bytes/(1024*1024):.2f} MiB (<21.5 MiB!), {len(sn_pool)} unique snippets, {len(sm.get('proofPipelines', []))} canonical pipelines, "
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
    print("=== Running V244 End-to-End Lean 4.33.0 Kernel & Unified Chrome/Safari Observatory Audit ===")
    ensure_bundle_reconstructed()
    check_lean_corpus_and_kernel()
    check_end_to_end_connections_and_clutter()
    check_unified_static_assets()
    subprocess.run(["bash", str(OBS_DIR / "tests" / "run-tests.sh")], check=True)
    print("=== ALL V244 CONTINUOUS VERIFICATION CHECKS PASSED (EXIT 0) ===")


if __name__ == "__main__":
    main()
