#!/usr/bin/env python3
"""
Deterministic Bundle Reconstructor (`reconstruct-bundle-data.py` · V157)
========================================================================
Reconstructs monolithic `observatory/bundle-data.js` (~99.94 MiB) in <1.5s from the
8 tracked stack-safe shards in `observatory/chunks/` (<16 MiB each).

Why this exists:
- GitHub blocks standard Git pushes containing files >= 100.00 MiB (`bundle-data.js` is 99.94 MiB).
- Keeping `observatory/chunks/*.js` tracked in Git and reconstructing `bundle-data.js` on demand
  eliminates GitHub push rejections AND consumes 0 GiB of Git LFS bandwidth in CI!
"""
import argparse
import json
from pathlib import Path

OBS_DIR = Path(__file__).resolve().parent.parent
CHUNKS_DIR = OBS_DIR / "chunks"
OUT_PATH = OBS_DIR / "bundle-data.js"


def extract_json_arg(js_text: str, marker: str):
    idx = js_text.index(marker) + len(marker)
    dec = json.JSONDecoder()
    val, end_idx = dec.raw_decode(js_text, idx)
    return val, js_text[end_idx:]


def reconstruct(force: bool = False) -> Path:
    if OUT_PATH.exists() and not force:
        print(f"[reconstruct-bundle-data] {OUT_PATH.name} already exists ({OUT_PATH.stat().st_size / (1024*1024):.2f} MiB); skipping (use --force to overwrite).")
        return OUT_PATH

    s1 = (CHUNKS_DIR / "bundle-shard-1-core.js").read_text(encoding="utf-8")
    core, tail = extract_json_arg(s1, "window.__CG_PRELOADED__ = ")
    tail_js = tail.lstrip(";")

    mechs = []
    mech_pools = None
    for name in ("bundle-shard-2a-mechanisms.js", "bundle-shard-2b-mechanisms.js"):
        raw_m = (CHUNKS_DIR / name).read_text(encoding="utf-8")
        if "semanticMechanisms.mechPools=" in raw_m:
            mech_pools, raw_m = extract_json_arg(raw_m, "semanticMechanisms.mechPools=")
        arr, _ = extract_json_arg(raw_m, ".concat(")
        mechs.extend(arr)

    isos = []
    for name in ("bundle-shard-3a-isomorphisms.js", "bundle-shard-3b-isomorphisms.js", "bundle-shard-3c-isomorphisms.js"):
        arr, _ = extract_json_arg((CHUNKS_DIR / name).read_text(encoding="utf-8"), ".concat(")
        isos.extend(arr)

    conns = []
    extra_suites = []
    path_pools = None
    for name in ("bundle-shard-4a-paths.js", "bundle-shard-4b-paths.js"):
        raw_shard = (CHUNKS_DIR / name).read_text(encoding="utf-8")
        if "insightPaths.pathPools=" in raw_shard:
            path_pools, raw_shard = extract_json_arg(raw_shard, "insightPaths.pathPools=")
        arr, rem = extract_json_arg(raw_shard, ".concat(")
        conns.extend(arr)
        if "verifiedLeanSuites.concat(" in rem:
            s_arr, _ = extract_json_arg(rem, "verifiedLeanSuites.concat(")
            extra_suites.extend(s_arr)

    core["semanticMechanisms"]["highLevelMechanisms"] = mechs
    if mech_pools is not None:
        core["semanticMechanisms"]["mechPools"] = mech_pools
    core["semanticMechanisms"]["customIsomorphisms"] = isos
    if extra_suites:
        core["semanticMechanisms"]["verifiedLeanSuites"] = list(core["semanticMechanisms"].get("verifiedLeanSuites", [])) + extra_suites
    core["insightPaths"]["connections"] = conns
    if path_pools is not None:
        core["insightPaths"]["pathPools"] = path_pools

    out_text = "window.__CG_PRELOADED__ = " + json.dumps(core, ensure_ascii=False, separators=(",", ":")) + ";"
    if tail_js.strip():
        out_text += "\n" + tail_js.strip() + "\n"
    else:
        out_text += "\n"

    OUT_PATH.write_text(out_text, encoding="utf-8")
    print(
        f"[reconstruct-bundle-data] Rebuilt {OUT_PATH.name} ({OUT_PATH.stat().st_size / (1024*1024):.2f} MiB): "
        f"mechanisms={len(mechs)}, isomorphisms={len(isos)}, paths={len(conns)}, suites={len(core['semanticMechanisms'].get('verifiedLeanSuites', []))}"
    )
    return OUT_PATH


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--force", action="store_true", help="Always overwrite observatory/bundle-data.js")
    args = ap.parse_args()
    reconstruct(force=args.force)


if __name__ == "__main__":
    main()
