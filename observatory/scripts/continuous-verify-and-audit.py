#!/usr/bin/env python3
"""
Deterministic Zero-Clutter Mathematical, Lean 4.33.0 Kernel & Unified Browser Shard Verification Harness (V232).
Verifies:
1. All 740+ physical Lean 4 files (633 in CommonGround/Verification/ + 107 in 01..10-*) have 0 `sorry`/`admit`/`sorryAx`
   tokens outside comments (with NO 25 MiB cap on `.lean` files — large `.lean` files stream via Cloudflare R2 `/api/lean/*`)
   AND compile cleanly through the real Lean 4.33.0 kernel (`compile-all-lean4.py`).
2. Reconstructs `bundle-data.js` from the 8 tracked `<16 MiB` shards and builds `dist-cloudflare/` if absent in CI.
3. Verifies end-to-end connection integrity & zero clutter:
   - 0 legacy `upgrade-v*.py` scripts and 0 `.pyc` / `__pycache__` artifacts;
   - exact 1-to-1 bijection between `verifiedLeanSuites` and `CommonGround/Verification/*.lean`;
   - 100% of `highLevelMechanisms[*].verifiedBridgeFile` and `insightPaths.connections[*].verifiedLeanFile` resolve on disk;
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

    raw = (OBS_DIR / "bundle-data.js").read_text(encoding="utf-8")
    prefix = "window.__CG_PRELOADED__ = "
    preloaded, _ = json.JSONDecoder().raw_decode(raw, raw.index(prefix) + len(prefix))
    sm = preloaded["semanticMechanisms"]
    suites = sm.get("verifiedLeanSuites", [])
    disk_verif = sorted(str(p.relative_to(REPO_ROOT)) for p in (REPO_ROOT / "CommonGround" / "Verification").glob("*.lean"))
    suite_files = sorted(s.get("leanFile") or "" for s in suites)
    assert suite_files == disk_verif, (
        f"verifiedLeanSuites ({len(suite_files)}) is not in 1-to-1 bijection with CommonGround/Verification/*.lean ({len(disk_verif)})!"
    )

    for m in sm.get("highLevelMechanisms", []):
        bf = m.get("verifiedBridgeFile")
        if bf:
            assert (REPO_ROOT / bf).exists(), f"Broken highLevelMechanisms.verifiedBridgeFile: {bf}"
    for c in preloaded.get("insightPaths", {}).get("connections", []):
        vf = c.get("verifiedLeanFile")
        if vf:
            assert (REPO_ROOT / vf).exists(), f"Broken insightPaths.connections.verifiedLeanFile: {vf}"

    readme_txt = (REPO_ROOT / "README.md").read_text(encoding="utf-8")
    for forbidden in ("hodge.computer", "hodge-computer", "arXiv:2603.29157", "sextics"):
        assert forbidden not in readme_txt, f"Forbidden legacy reference {forbidden!r} found in README.md!"
    for rel_link in re.findall(r"\]\((\./[^)#?]+)", readme_txt):
        target = (REPO_ROOT / rel_link).resolve()
        assert target.exists(), f"Broken relative link {rel_link} in README.md -> {target}"
    print(
        f"  [OK] End-to-end connection bijection verified: {len(suites)} suites == {len(disk_verif)} CommonGround/Verification/*.lean, "
        f"0 broken mechanism/path .lean refs, 0 clutter scripts, 0 .pyc files, README clean."
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
    print("=== Running V232 End-to-End Lean 4.33.0 Kernel & Unified Chrome/Safari Observatory Audit ===")
    ensure_bundle_reconstructed()
    check_lean_corpus_and_kernel()
    check_end_to_end_connections_and_clutter()
    check_unified_static_assets()
    subprocess.run(["bash", str(OBS_DIR / "tests" / "run-tests.sh")], check=True)
    print("=== ALL V232 CONTINUOUS VERIFICATION CHECKS PASSED (EXIT 0) ===")


if __name__ == "__main__":
    main()
