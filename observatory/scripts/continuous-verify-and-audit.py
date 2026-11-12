#!/usr/bin/env python3
"""
Deterministic Zero-Clutter Mathematical, Lean 4.33.0 Kernel & Unified Browser Shard Verification Harness (V181).
Verifies:
1. All 639+ physical Lean 4 files (582 in CommonGround/Verification/ + 57 in 01..10-*) have 0 `sorry`/`admit`/`sorryAx`
   tokens outside comments (with NO 25 MiB cap on `.lean` files — large `.lean` files stream via Cloudflare R2 `/api/lean/*`)
   AND compile cleanly through the real Lean 4.33.0 kernel (`compile-all-lean4.py`).
2. Reconstructs `bundle-data.js` from the 8 tracked `<16 MiB` shards if absent in CI.
3. Confirms no legacy forked `safari-standalone.html` or `observatory/safari/` artifacts exist, and verifies all unified
   Chrome + Safari routes resolve CSS + all 8 untruncated `<25 MiB` shards + `unified-standalone.js`.
4. Runs `observatory/tests/run-tests.sh` (all automated UX, DOM click, mathematical, WebKit JSC `file://` & Node CI checks).
"""
import re
import subprocess
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
OBS_DIR = REPO_ROOT / "observatory"
LIMIT_BYTES = 25 * 1024 * 1024  # Applies ONLY to Cloudflare Pages static web assets (NOT .lean files!)


def ensure_bundle_reconstructed():
    if not (OBS_DIR / "bundle-data.js").exists():
        subprocess.run(["python3", "-B", str(OBS_DIR / "scripts" / "reconstruct-bundle-data.py")], check=True)


def check_lean_corpus_and_kernel():
    subprocess.run(["python3", "-B", str(OBS_DIR / "scripts" / "compile-all-lean4.py")], check=True)


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
    print("=== Running V181 End-to-End Lean 4.33.0 Kernel & Unified Chrome/Safari Observatory Audit ===")
    ensure_bundle_reconstructed()
    check_lean_corpus_and_kernel()
    check_unified_static_assets()
    subprocess.run(["bash", str(OBS_DIR / "tests" / "run-tests.sh")], check=True)
    print("=== ALL V181 CONTINUOUS VERIFICATION CHECKS PASSED (EXIT 0) ===")


if __name__ == "__main__":
    main()
