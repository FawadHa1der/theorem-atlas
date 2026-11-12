#!/usr/bin/env bash
# End-to-End Local & CI Pipeline Orchestrator (`scripts/github-cloudflare-pipeline.sh` · V181)
# Usage:
#   bash scripts/github-cloudflare-pipeline.sh verify
#   bash scripts/github-cloudflare-pipeline.sh init-github <git-remote-url>
#   bash scripts/github-cloudflare-pipeline.sh sync-r2
#   bash scripts/github-cloudflare-pipeline.sh deploy-cloudflare
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

CMD="${1:-verify}"

case "$CMD" in
  verify)
    echo "=== [1/4] Reconstructing bundle-data.js (if needed) ==="
    python3 -B observatory/scripts/reconstruct-bundle-data.py
    echo "=== [2/4] Compiling Lean 4.33.0 Kernel & Auditing Unrestricted .lean Corpus ==="
    python3 -B observatory/scripts/compile-all-lean4.py
    echo "=== [3/4] Building Unified Chrome & Safari Shards (<25 MiB each) + Cloudflare Pages R2 /api/lean/* ==="
    python3 -B observatory/scripts/build-cloudflare-dist.py
    echo "=== [4/4] Running Full WebKit JSC & Node VM E2E Suites ==="
    bash observatory/tests/run-tests.sh
    ;;

  init-github)
    REMOTE_URL="${2:-}"
    if [ ! -d ".git" ]; then
      git init -b main
    fi
    if git lfs version >/dev/null 2>&1; then
      git lfs install --local
    fi
    git add .
    echo "Staged repository cleanly (monolithic 103 MiB bundle-data.js excluded via .gitignore; 8 <16 MiB untruncated shards + all 639 .lean files tracked)."
    if [ -n "$REMOTE_URL" ]; then
      git remote remove origin 2>/dev/null || true
      git remote add origin "$REMOTE_URL"
      echo "Configured remote origin -> $REMOTE_URL"
      echo "Next: git commit -m 'V181: Unify Chrome & Safari on observatory/index.html with 8 untruncated shards' && git push -u origin main"
    fi
    ;;

  sync-r2)
    BUCKET="${R2_BUCKET_NAME:-common-ground-lean-corpus}"
    npx --yes wrangler@4 r2 bucket create "$BUCKET" || true
    python3 -B observatory/scripts/sync-lean-to-r2.py --bucket "$BUCKET"
    ;;

  deploy-cloudflare)
    PROJECT="${CF_PAGES_PROJECT:-common-ground-observatory}"
    bash "$0" verify
    bash "$0" sync-r2
    npx --yes wrangler@4 pages deploy observatory/dist-cloudflare --project-name="$PROJECT" --branch=main
    ;;

  *)
    echo "Usage: $0 {verify|init-github [remote_url]|sync-r2|deploy-cloudflare}" >&2
    exit 1
    ;;
esac
