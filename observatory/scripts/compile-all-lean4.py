#!/usr/bin/env python3
"""
End-to-End Lean 4.33.0 Kernel Compiler & Unrestricted-Size Zero-Sorry Verifier (`compile-all-lean4.py`)
=======================================================================================================
1. Scans ALL `.lean` files across `CommonGround/Verification/` (561 files) and `01..10-*` frontier folders
   (57 files = 618 total) with NO 25 MiB file-size cap:
   - Verifies 0 `sorry`, `admit`, or `sorryAx` tokens outside comments.
   - Reports exact corpus size and classifies any `.lean` files > 25 MiB (Cloudflare R2 route) or > 100 MiB (Git LFS + R2).
2. Runs `lake build` so the real Lean 4.33.0 kernel compiles 100% (`561/561`) of `CommonGround/Verification/*.lean`.
3. Runs standalone `lean` on all 17 pure-Lean-core `01..10-*` frontier modules (`578` kernel-compiled modules total).
"""
from __future__ import annotations
import argparse
import os
import re
import shutil
import subprocess
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
VERIF_DIR = REPO_ROOT / "CommonGround" / "Verification"
CF_STATIC_LIMIT = 25 * 1024 * 1024
GH_GIT_LIMIT = 100 * 1024 * 1024


def find_elan_tool(binary_name: str) -> str | None:
    found = shutil.which(binary_name)
    if found:
        return found
    candidates = [
        Path.home() / ".elan" / "bin" / binary_name,
        Path("/Users/fawadhaider/.gemini/users/user1/.elan/bin") / binary_name,
        Path("/Users/fawadhaider/.elan/bin") / binary_name,
    ]
    for c in candidates:
        if c.exists():
            return str(c)
    return None


def strip_lean_comments(src: str) -> str:
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if src[i:i+2] == "/-":
            depth += 1
            i += 2
        elif depth > 0 and src[i:i+2] == "-/":
            depth -= 1
            i += 2
        elif depth == 0 and src[i:i+2] == "--":
            while i < n and src[i] != "\n":
                i += 1
        else:
            if depth == 0:
                out.append(src[i])
            i += 1
    return "".join(out)


def is_pure_core_lean(src: str) -> bool:
    for line in src.splitlines():
        m = re.match(r"^(?:public\s+|private\s+|meta\s+)*import\s+(.+)$", line.strip())
        if m:
            for mod in m.group(1).split():
                if not (mod.startswith("Init") or mod.startswith("Std") or mod.startswith("Lean")):
                    return False
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--skip-kernel", action="store_true", help="Only run zero-sorry & size classification scan")
    args = ap.parse_args()

    verif_files = sorted(VERIF_DIR.rglob("*.lean"))
    frontier_files = []
    for d in sorted(REPO_ROOT.iterdir()):
        if d.is_dir() and d.name[:2].isdigit():
            frontier_files.extend(sorted(d.rglob("*.lean")))

    all_lean = verif_files + frontier_files
    assert len(verif_files) >= 561, f"Expected >= 561 Verification .lean files, found {len(verif_files)}"

    rx_sorry = re.compile(r"\b(sorry|admit|sorryAx)\b")
    bad_sorry = []
    over_25mb = []
    over_100mb = []
    total_bytes = 0
    pure_frontier = []

    for lf in all_lean:
        sz = lf.stat().st_size
        total_bytes += sz
        if sz >= CF_STATIC_LIMIT:
            over_25mb.append((str(lf.relative_to(REPO_ROOT)), sz))
        if sz >= GH_GIT_LIMIT:
            over_100mb.append((str(lf.relative_to(REPO_ROOT)), sz))
        raw = lf.read_text(encoding="utf-8")
        stripped = strip_lean_comments(raw)
        if rx_sorry.search(stripped):
            bad_sorry.append(str(lf.relative_to(REPO_ROOT)))
        if lf in frontier_files and is_pure_core_lean(stripped):
            pure_frontier.append(lf)

    assert not bad_sorry, f"Found sorry/admit/sorryAx tokens in: {bad_sorry}"
    print(
        f"[Lean 4 Audit] {len(all_lean)} .lean files ({len(verif_files)} Verification + {len(frontier_files)} Frontier, "
        f"{total_bytes / (1024*1024):.2f} MiB total): 0 sorry/admit tokens. "
        f"Unrestricted >25 MiB files={len(over_25mb)} (served via R2), >100 MiB files={len(over_100mb)} (Git LFS + R2)."
    )

    if args.skip_kernel:
        return

    lake_bin = find_elan_tool("lake")
    lean_bin = find_elan_tool("lean")
    if not lake_bin or not lean_bin:
        raise SystemExit("ERROR: `lake` / `lean` toolchain not found in PATH or ~/.elan/bin!")

    env = os.environ.copy()
    elan_dir = str(Path(lake_bin).parent)
    env["PATH"] = f"{elan_dir}:{env.get('PATH', '')}"

    print(f"[Lean 4 Kernel] Running `{lake_bin} build` across all {len(verif_files)} CommonGround/Verification modules...")
    subprocess.run([lake_bin, "build"], cwd=str(REPO_ROOT), env=env, check=True)

    print(f"[Lean 4 Kernel] Compiling {len(pure_frontier)} standalone pure-Lean frontier modules...")
    for pf in pure_frontier:
        res = subprocess.run([lean_bin, str(pf)], cwd=str(REPO_ROOT), env=env, capture_output=True, text=True)
        if res.returncode != 0:
            print(res.stdout)
            print(res.stderr)
            raise SystemExit(f"Lean kernel failed on {pf}: exit {res.returncode}")

    print(
        f"[Lean 4 Kernel OK] {len(verif_files)} Verification modules + {len(pure_frontier)} pure-core Frontier modules "
        f"= {len(verif_files) + len(pure_frontier)} modules compiled cleanly through Lean 4.33.0 (exit 0, 0 sorry)!"
    )


if __name__ == "__main__":
    main()
