# Common Ground Cross-Domain Mathematical Observatory (`GEMINI.md`)

Project-wide instructions for autonomous cloud runs (`@google/gemini-cli` in GitHub Actions), GitHub Codespaces, and local CLI sessions.

## Core Architectural & Verification Invariants

1. **Zero Bytecode & Read-Only Reference Rule**
   - Always pass `-B` to `python3` (`PYTHONDONTWRITEBYTECODE=1`).
   - Treat any reference checkout (`.theorem-atlas-ref` in CI or `/Users/fawadhaider/code/lean ideas/theorem-atlas` locally) as **strictly read-only**; never create, modify, or delete files inside it.

2. **Zero-Sorry Lean 4.33.0 Kernel Gate**
   - Toolchain: `leanprover/lean4:v4.33.0` (`lean-toolchain`).
   - Every `.lean` module across `CommonGround/Verification/` and `01-*` through `10-*` must contain **zero** `sorry`, `admit`, or `sorryAx` tokens outside comments and must pass `python3 -B observatory/scripts/compile-all-lean4.py`.
   - Before importing any cross-domain bridge or mathematical mechanism, verify ambient section assumptions and formalize both a positive witness and an explicit premise-failure counterexample in Lean 4.

3. **Unified Chrome, Safari & Cloudflare 8-Shard Pipeline (`observatory/index.html`)**
   - Live production URL: `https://common-ground-atlas.com` (Cloudflare Pages project `common-ground-observatory` + Cloudflare R2 bucket `common-ground-lean-corpus` bound as `LEAN_CORPUS_BUCKET`).
   - Chrome and Safari share the exact same entrypoint (`observatory/index.html`) and the 8 untruncated `< 16 MiB` data shards in `observatory/chunks/`.
   - **Never** reintroduce `safari-standalone.html`, `observatory/safari/`, or `build-safari-standalone.py`.
   - Note that `observatory/bundle-data.js` (~103 MiB) is reconstructed locally/in-CI via `python3 -B observatory/scripts/reconstruct-bundle-data.py` and is gitignored; after editing `observatory/bundle-data.js` or `observatory/unified-standalone.js`, always run `python3 -B observatory/scripts/build-cloudflare-dist.py` so the 8 tracked shards in `observatory/chunks/` carry every update.

4. **Calm Epistemic UX & Clean Documentation**
   - Do not add new top-level panels or visual clutter to the Observatory UI; refine existing cards, provenance badges (`★` source-reviewed, `◆` mechanism/contrast, `○` unreviewed AST candidate, `⚠`/`✕` lookalike guardrail), and finite micro-labs in place.
   - Keep `README.md` free of legacy `hodge.computer`, `hodge-computer`, `arXiv:2603.29157`, and `sextics` references, and ensure every relative `./...` link resolves on disk.

5. **Mandatory Pre-Commit Gate**
   - Always run `python3 -B observatory/scripts/build-cloudflare-dist.py` followed by `python3 -B observatory/scripts/continuous-verify-and-audit.py` and confirm exit code `0` before finishing.
