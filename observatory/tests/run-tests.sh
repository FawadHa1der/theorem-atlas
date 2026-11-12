#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OBS_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
REPO_ROOT="$(cd "$OBS_DIR/.." && pwd)"
JSC="/System/Library/Frameworks/JavaScriptCore.framework/Versions/Current/Helpers/jsc"

if [ -e "$OBS_DIR/safari-standalone.html" ] || [ -d "$OBS_DIR/safari" ]; then
  echo "ERROR: Obsolete Safari standalone fork files detected in $OBS_DIR!" >&2
  exit 1
fi

if [ ! -f "$OBS_DIR/bundle-data.js" ]; then
  echo "=== Reconstructing observatory/bundle-data.js from 8 tracked <16 MiB shards ==="
  python3 -B "$OBS_DIR/scripts/reconstruct-bundle-data.py"
fi

if [ -x "$JSC" ] && [ "$REPO_ROOT" = "/Users/fawadhaider/code/commonground-verification-gemini" ]; then
  echo "=== 1. Running Automated UX, DOM Click, WebKit & Mathematical Test Suite in WebKit JSC ==="
  "$JSC" "$OBS_DIR/tests/automated-ux-functional-suite.js"

  echo "=== 2. Running Automated UX, DOM Click, WebKit & Mathematical Test Suite on 8 Stack-Safe Shards (<25 MiB each) ==="
  "$JSC" "$OBS_DIR/tests/cloudflare-shards-e2e-suite.js"

  echo "=== 3. Running Unified observatory/index.html + 8 Untruncated Shards E2E Under Strict Safari file:// Origin in WebKit JSC ==="
  python3 -B "$OBS_DIR/tests/unified-file-origin-e2e.py"
fi

if command -v node >/dev/null 2>&1; then
  echo "=== Running Cross-Platform Headless Node VM CI Suite (Linux & macOS Parity) ==="
  node "$OBS_DIR/tests/node-ci-runner.mjs"
elif [ ! -x "$JSC" ]; then
  echo "ERROR: Neither WebKit jsc nor Node.js found to execute headless JS suites!" >&2
  exit 1
fi

echo "=== Verifying All Cloudflare Pages Static Assets & Unified Shards Are Strictly Under 25 MiB (Note: .lean files have NO 25 MiB cap and stream via R2) ==="
OBS_DIR_ENV="$OBS_DIR" python3 -B -c '
import os
from pathlib import Path
obs = Path(os.environ["OBS_DIR_ENV"])
cf = obs / "dist-cloudflare"
limit = 25 * 1024 * 1024
files = [p for p in cf.rglob("*") if p.is_file()] + sorted((obs / "chunks").glob("*.js"))
for p in sorted(files):
    sz = p.stat().st_size
    assert sz < limit, f"Cloudflare static asset exceeds 25 MiB limit: {p} ({sz} bytes)"
    rel = p.relative_to(obs)
    print(f"  OK {str(rel):54s}: {sz/(1024*1024):6.2f} MiB (< 25 MiB)")
print(f"ALL {len(files)} CLOUDFLARE PAGES STATIC ASSETS & UNIFIED BROWSER SHARDS VERIFIED < 25 MiB!")
'
echo "ALL_AUTOMATED_UX_SAFARI_AND_CLOUDFLARE_TESTS_PASSED_OK"
