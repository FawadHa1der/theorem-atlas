#!/usr/bin/env python3
"""
Cloudflare R2 Unrestricted-Size Lean 4 Corpus Sync (`sync-lean-to-r2.py` · V157)
=================================================================================
Since `.lean` files have NO 25 MiB restriction (and monolithic proofs in corpora like
`ten-proofs` can grow to tens or hundreds of megabytes), Cloudflare Pages' 25 MiB static
per-file cap is bypassed cleanly by storing `.lean` artifacts in Cloudflare R2 (`$0` egress)
and streaming them from `/api/lean/<path>` via Cloudflare Pages Functions!

Features:
- Computes SHA-256 hashes for all `.lean` files (`CommonGround/Verification/` + `01..10-*` + optional `--extra-dir`).
- Writes `observatory/dist-cloudflare/lean-corpus-manifest.json` (< 250 KB, safe for Pages static hosting)
  so the UI & `/api/lean/[[path]]` know exact byte sizes, SHA-256 digests, and theorem counts.
- Incremental sync: skips unchanged objects unless `--force` is passed, minimizing R2 Class A PUT operations.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
OBS_DIR = REPO_ROOT / "observatory"
CF_DIR = OBS_DIR / "dist-cloudflare"
MANIFEST_PATH = CF_DIR / "lean-corpus-manifest.json"
STATE_CACHE = OBS_DIR / "logs" / "r2-uploaded-sha256.json"


def collect_lean_files() -> list[Path]:
    files = sorted((REPO_ROOT / "CommonGround" / "Verification").rglob("*.lean"))
    for d in sorted(REPO_ROOT.iterdir()):
        if d.is_dir() and d.name[:2].isdigit():
            files.extend(sorted(d.rglob("*.lean")))
    large_dir = REPO_ROOT / "archive" / "large-lean"
    if large_dir.exists():
        files.extend(sorted(large_dir.rglob("*.lean")))
    return files


def build_manifest(files: list[Path], bucket: str) -> dict:
    entries = []
    total_bytes = 0
    over_25_mib = 0
    for lf in files:
        rel = lf.relative_to(REPO_ROOT).as_posix()
        raw = lf.read_bytes()
        sz = len(raw)
        total_bytes += sz
        if sz >= 25 * 1024 * 1024:
            over_25_mib += 1
        sha = hashlib.sha256(raw).hexdigest()
        entries.append({
            "path": rel,
            "bytes": sz,
            "sha256": sha,
            "exceedsPages25MiBCap": sz >= 25 * 1024 * 1024,
            "apiUrl": f"/api/lean/{rel}",
        })
    return {
        "bucket": bucket,
        "totalFiles": len(entries),
        "totalBytes": total_bytes,
        "totalMiB": round(total_bytes / (1024 * 1024), 3),
        "filesOver25MiB": over_25_mib,
        "files": entries,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bucket", default=os.environ.get("R2_BUCKET_NAME", "common-ground-lean-corpus"))
    ap.add_argument("--manifest-only", action="store_true", help="Write lean-corpus-manifest.json without uploading to R2")
    ap.add_argument("--dry-run", action="store_true", help="Print R2 uploads that would run without calling wrangler")
    ap.add_argument("--only-over-25mb", action="store_true", help="Only upload .lean files >= 25 MiB to R2")
    ap.add_argument("--force", action="store_true", help="Re-upload all files even if SHA-256 matches cached state")
    args = ap.parse_args()

    CF_DIR.mkdir(parents=True, exist_ok=True)
    STATE_CACHE.parent.mkdir(parents=True, exist_ok=True)

    files = collect_lean_files()
    manifest = build_manifest(files, args.bucket)
    MANIFEST_PATH.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    print(
        f"[R2 Manifest] Wrote {MANIFEST_PATH.relative_to(REPO_ROOT)} "
        f"({manifest['totalFiles']} .lean files, {manifest['totalMiB']} MiB, >25MiB={manifest['filesOver25MiB']})."
    )

    if args.manifest_only:
        return

    prev_hashes = {}
    if STATE_CACHE.exists() and not args.force:
        try:
            prev_hashes = json.loads(STATE_CACHE.read_text(encoding="utf-8"))
        except Exception:
            prev_hashes = {}

    to_upload = []
    for item in manifest["files"]:
        if args.only_over_25mb and not item["exceedsPages25MiBCap"]:
            continue
        if not args.force and prev_hashes.get(item["path"]) == item["sha256"]:
            continue
        to_upload.append(item)

    if args.dry_run:
        print(f"[R2 Dry Run] Would upload {len(to_upload)}/{manifest['totalFiles']} .lean objects to R2 bucket `{args.bucket}`.")
        return

    wrangler = shutil.which("wrangler") or "npx"
    uploaded = 0
    for item in to_upload:
        src_file = REPO_ROOT / item["path"]
        key = f"{args.bucket}/{item['path']}"
        cmd = (
            [wrangler, "r2", "object", "put", key, "--file", str(src_file), "--content-type", "text/plain; charset=utf-8", "--remote"]
            if wrangler != "npx"
            else ["npx", "--yes", "wrangler@4", "r2", "object", "put", key, "--file", str(src_file), "--content-type", "text/plain; charset=utf-8", "--remote"]
        )
        subprocess.run(cmd, cwd=str(REPO_ROOT), check=True)
        prev_hashes[item["path"]] = item["sha256"]
        uploaded += 1

    STATE_CACHE.write_text(json.dumps(prev_hashes, indent=2), encoding="utf-8")
    print(f"[R2 Sync OK] Uploaded {uploaded} changed/new .lean files to R2 bucket `{args.bucket}`.")


if __name__ == "__main__":
    main()
