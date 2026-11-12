# GitHub + Cloudflare Pages & R2 CI/CD Pipeline (`V157`)

This repository is wired end-to-end for automated **Lean 4.33.0 kernel verification**, **headless UI/UX & provenance regression testing**, **GitHub source hosting**, and **Cloudflare Pages + Cloudflare R2 deployment**—with **no 25 MiB restriction on `.lean` files**.

## 1. Architecture: How Unrestricted-Size `.lean` Files & Shards Flow

1. **GitHub Repository (`< 100 MiB` standard Git + Git LFS for `> 100 MiB` files)**
   - Standard Git pushes on GitHub warn above `50 MiB` and hard-block individual files at `100.00 MiB` ([About large files on GitHub](https://docs.github.com/en/repositories/working-with-files/managing-large-files/about-large-files-on-github)).
   - Instead of tracking the `99.94 MiB` monolithic `observatory/bundle-data.js` at the razor's edge of GitHub's `100 MiB` block, Git tracks the 8 deterministic `< 16 MiB` shards in `observatory/chunks/*.js`, and `observatory/scripts/reconstruct-bundle-data.py` reconstructs `bundle-data.js` in `< 1.5s` during CI or local builds—using **0 GiB of Git LFS bandwidth**.
   - All `.lean` files up to `100 MiB` push directly in standard Git (`*.lean text eol=lf` in `.gitattributes`). Any monolithic `.lean` files or compressed proof archives exceeding `100 MiB` placed under `archive/large-lean/**` or `*.lean.zst` automatically route through Git LFS ([About billing for Git Large File Storage](https://docs.github.com/en/billing/managing-billing-for-git-large-file-storage/about-billing-for-git-large-file-storage)).

2. **Cloudflare Pages (`< 25 MiB` static web shards) + Cloudflare R2 (`> 25 MiB` unrestricted `.lean` files)**
   - Cloudflare Pages enforces a `25 MiB` maximum size per static asset and explicitly recommends Cloudflare R2 for larger files ([Limits · Cloudflare Pages docs](https://developers.cloudflare.com/pages/platform/limits/)).
   - `observatory/scripts/build-cloudflare-dist.py` compiles the web app into `observatory/dist-cloudflare/` with 8 WebKit stack-safe `.concat(...)` shards (`9.8–15.8 MiB` each), `lean-corpus-manifest.json`, `/functions/api/health.js`, and `/functions/api/lean/[[path]].js`.
   - `observatory/scripts/sync-lean-to-r2.py` incrementally uploads `.lean` files of **any size** (`> 25 MiB`, `> 100 MiB`, or multi-GiB, deduplicated by SHA-256) to R2 bucket `common-ground-lean-corpus`, and `/functions/api/lean/[[path]].js` streams them with HTTP `Range` support and `$0` egress ([Pricing · Cloudflare R2 docs](https://developers.cloudflare.com/r2/pricing/)).

3. **Continuous Verification (`ci-verify.yml` & `deploy-cloudflare.yml`)**
   - Installs `leanprover/lean4:v4.33.0` via `elan` (caching `~/.elan` and `.lake`), runs `observatory/scripts/compile-all-lean4.py` (`lake build` across all `561` `CommonGround/Verification/*.lean` modules + `lean` across `17` pure-core frontier modules = `578` kernel-compiled modules, plus a `0-sorry` scan across all `618+` `.lean` files of any size), and runs all `165` headless DOM/UX/math assertions in `observatory/tests/node-ci-runner.mjs`.

## 2. One-Time Setup Steps

1. **Create Cloudflare R2 Bucket & API Token**
   - In the Cloudflare Dashboard → **R2 Object Storage**, create bucket `common-ground-lean-corpus`.
   - Create a Cloudflare API Token with **Cloudflare Pages: Edit** and **Workers R2 Storage: Edit** permissions, and copy your **Account ID**.

2. **Push to GitHub & Add Repository Secrets**
   ```bash
   bash scripts/github-cloudflare-pipeline.sh init-github git@github.com:<your-user>/<your-repo>.git
   git commit -m "V157: Calm UX, 578-module Lean 4.33.0 kernel build & Cloudflare Pages/R2 CI/CD"
   git push -u origin main
   ```
   In GitHub → **Settings → Secrets and variables → Actions**, add:
   - `CLOUDFLARE_API_TOKEN`
   - `CLOUDFLARE_ACCOUNT_ID`

3. **Run Local End-to-End Verification or Manual Deploy Anytime**
   ```bash
   # Verify Lean 4.33.0 kernel build + shards + all 165 WebKit JSC & Node VM E2E checks
   bash scripts/github-cloudflare-pipeline.sh verify

   # Sync unrestricted-size .lean corpus to R2 + deploy Pages
   bash scripts/github-cloudflare-pipeline.sh deploy-cloudflare
   ```

## 3. Monthly Cost Estimate

| Component | Hobby / Public Repo Tier | Heavy Private Repo + Large (`50–100 GB`) `.lean` Corpus | Official Source |
| :--- | :--- | :--- | :--- |
| **GitHub Repo & Actions CI** | **$0 / mo** (unlimited Actions minutes on public repos; private Free plan includes `$12/mo` credit = `2,000` Linux 2-core x64 min at `$0.006/min` + `500 MB` artifacts + `10 GB` cache) | **$0 – $4 / mo** (GitHub Pro `$4/mo` includes `$18/mo` credit = `3,000` Linux x64 min; cached `lake build` + Node E2E takes ~2–3 min/push) | [GitHub Plans & Pricing](https://github.com/pricing), [Actions runner pricing](https://docs.github.com/en/billing/reference/actions-runner-pricing), [About billing for GitHub Actions](https://docs.github.com/en/billing/managing-billing-for-github-actions/about-billing-for-github-actions) |
| **GitHub Git LFS (`> 100 MiB` `.lean` files)** | **$0 / mo** (`10 GiB` storage + `10 GiB/mo` bandwidth included free on Free & Pro; `.lean` files `< 100 MiB` use standard Git = `0` LFS) | **$0 – $3.50 / mo** (only if storing `50 GiB` of single `> 100 MiB` `.lean` blobs in Git LFS at `$0.07/GiB-mo` over `10 GiB`; `$0.0875/GiB` bandwidth over `10 GiB`) | [About billing for Git Large File Storage](https://docs.github.com/en/billing/managing-billing-for-git-large-file-storage/about-billing-for-git-large-file-storage) |
| **Cloudflare Pages Static Hosting** | **$0 / mo** (unlimited static asset requests & `$0` bandwidth, `500` builds/mo, `20,000` static files `< 25 MiB`) | **$0 / mo** (`500` builds/mo covers ~16 deploys/day; Pro `$20/mo` only needed if exceeding `500` builds/mo or `20,000` static files) | [Limits · Cloudflare Pages docs](https://developers.cloudflare.com/pages/platform/limits/), [Pricing · Cloudflare Workers docs](https://developers.cloudflare.com/workers/platform/pricing/) |
| **Cloudflare Pages Functions (`/api/lean/*`)** | **$0 / mo** (`100,000` dynamic Function requests/day free; static shard requests are always free & uncounted) | **$0 – $5 / mo** (Workers Paid `$5/mo` includes `10M` Function requests/mo + `30M` CPU ms) | [Pricing · Cloudflare Workers docs](https://developers.cloudflare.com/workers/platform/pricing/), [Limits · Cloudflare Workers docs](https://developers.cloudflare.com/workers/platform/limits/) |
| **Cloudflare R2 (`> 25 MiB` `.lean` Storage & Streaming)** | **$0 / mo** (`10 GB-month` storage, `1M` Class A writes/mo, `10M` Class B reads/mo, **$0 egress**; current 618-file `.lean` corpus is `< 5 MB`) | **$0.60 – $1.35 / mo** for `50–100 GB` of large `.lean` files (`(50–100 - 10) GB × $0.015/GB-mo`, `$0` egress fees) | [Pricing · Cloudflare R2 docs](https://developers.cloudflare.com/r2/pricing/) |
| **Estimated Monthly Total** | **$0.00 / month** | **~$0.60 – $6.35 / month** (`~$9.85/mo` with GitHub Pro + Workers Paid + `50 GB` R2) | — |
