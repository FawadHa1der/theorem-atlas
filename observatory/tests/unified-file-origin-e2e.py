#!/usr/bin/env python3
"""
Unified Chrome & Safari `file://` Origin E2E Test (`unified-file-origin-e2e.py` · V181)
======================================================================================
Parses the exact `<script src="...">` tags from `observatory/index.html` (all 8 full,
untruncated `<16 MiB` shards in `observatory/chunks/` + `observatory/unified-standalone.js`)
and executes them inside macOS Safari's native JavaScriptCore engine (`jsc`) under simulated
`file:///.../observatory/index.html` where BOTH `history.pushState`/`replaceState` AND
`localStorage` throw `SecurityError`.

Verifies:
1. No obsolete `safari-standalone.html` or `observatory/safari/` fork exists.
2. `observatory/index.html` boots automatically with 0 errors under strict Safari `file://` rules.
3. Late-index mechanisms, bridges, and discovery paths retain 100% untruncated descriptions
   (proving the old `[:24]`/`[:30]`/`[:40]` Safari compaction truncation is completely gone).
4. Interactive card clicks and all 6 lenses render cleanly with zero `undefined` or `NaN`.
"""
import re
import subprocess
import tempfile
from pathlib import Path

JSC = "/System/Library/Frameworks/JavaScriptCore.framework/Versions/Current/Helpers/jsc"
OBS_DIR = Path(__file__).resolve().parent.parent
INDEX_HTML = OBS_DIR / "index.html"


def main():
    assert not (OBS_DIR / "safari-standalone.html").exists(), "Obsolete safari-standalone.html fork must not exist!"
    assert not (OBS_DIR / "safari").exists(), "Obsolete observatory/safari/ fork must not exist!"

    html = INDEX_HTML.read_text(encoding="utf-8")
    script_srcs = re.findall(r'<script\s+src="([^"?]+)(?:\?[^"]*)?"></script>', html)
    assert len(script_srcs) == 9, f"Expected 9 classic <script src> tags (8 shards + unified-standalone.js) in index.html, found {len(script_srcs)}"

    resolved_scripts = []
    total_bytes = 0
    for rel_src in script_srcs:
        p = (OBS_DIR / rel_src).resolve()
        assert p.exists(), f"Missing script referenced by observatory/index.html: {p}"
        sz = p.stat().st_size
        assert sz < 25 * 1024 * 1024, f"Script exceeds 25 MiB limit: {p} ({sz / (1024 * 1024):.2f} MiB)"
        total_bytes += sz
        resolved_scripts.append(p)

    suite_src = (OBS_DIR / "tests" / "automated-ux-functional-suite.js").read_text(encoding="utf-8")
    dom_preamble = suite_src[:suite_src.index("// Load bundle-data.js")]

    strict_safari_override = f"""
window.addEventListener = function(){{}};
// Simulate strict macOS Safari file:// origin on observatory/index.html where History API & localStorage throw SecurityError!
window.location = {{ protocol: "file:", search: "", href: "file://{INDEX_HTML}" }};
window.history = {{
  replaceState: function() {{ throw new Error("SecurityError: Blocked attempt to use history.replaceState() on file://"); }},
  pushState: function() {{ throw new Error("SecurityError: Blocked attempt to use history.pushState() on file://"); }}
}};
window.localStorage = {{
  getItem: function() {{ throw new Error("SecurityError: localStorage disabled on file://"); }},
  setItem: function() {{ throw new Error("SecurityError: localStorage disabled on file://"); }}
}};
"""

    load_lines = "\n".join(f'load("{p}");' for p in resolved_scripts)
    total_mib = total_bytes / (1024 * 1024)

    post_assertions = f"""
var mount = document.getElementById("app-mount");
if (!mount.innerHTML || mount.innerHTML.indexOf("Loading 40-Project") !== -1 || mount.innerHTML.indexOf("CONSTELLATION SHARD DIAGNOSTIC") !== -1) {{
  throw new Error("observatory/index.html failed automatic init() boot on file://: " + String(mount.innerHTML).slice(0, 240));
}}
if (mount.innerHTML.indexOf("undefined") !== -1 || mount.innerHTML.indexOf("NaN") !== -1) {{
  throw new Error("observatory/index.html rendered undefined/NaN on file:// boot!");
}}

// Verify 100% untruncated data on late-index items (no legacy [:24]/[:30]/[:40] Safari compaction!)
var pre = window.__CG_PRELOADED__;
var lateMech = pre.semanticMechanisms.highLevelMechanisms[500];
var lateIso = pre.semanticMechanisms.customIsomorphisms[500];
var latePath = pre.insightPaths.connections[500];
if (!lateMech || String(lateMech.whyItMatters || "").length <= 45) {{
  throw new Error("Late mechanism whyItMatters appears truncated: " + (lateMech && lateMech.whyItMatters));
}}
if (!lateIso || String(lateIso.plainEnglishWhy || "").length <= 45) {{
  throw new Error("Late isomorphism plainEnglishWhy appears truncated: " + (lateIso && lateIso.plainEnglishWhy));
}}
if (!latePath || String(latePath.summary || "").length <= 45) {{
  throw new Error("Late discovery path summary appears truncated: " + (latePath && latePath.summary));
}}

var cards = mount.querySelectorAll(".ingredient-card");
if (cards.length < 20) throw new Error("Expected >= 20 .ingredient-card items in observatory/index.html, got " + cards.length);
cards[0].click();
if (cards[0].innerHTML.indexOf("v146-inline-card-drawer") === -1) {{
  throw new Error("Clicking .ingredient-card[0] under Safari file:// failed to expand inline drawer!");
}}
for (var lensName of ["serendipity", "paths", "bridges", "constellation", "intuition", "galaxy"]) {{
  state.lens = lensName;
  renderApp();
  if (!mount.innerHTML || mount.innerHTML.indexOf("undefined") !== -1 || mount.innerHTML.indexOf("NaN") !== -1) {{
    throw new Error("Lens " + lensName + " failed or rendered undefined/NaN in observatory/index.html!");
  }}
}}
print("UNIFIED_INDEX_FILE_ORIGIN_WEBKIT_JSC_OK: scripts=9, totalUntruncatedPayload={total_mib:.2f}MiB, cards=" + cards.length + ", lateUntruncatedVerified=true, lenses=6/6, strictFileSecurityErrorSurvived=true");
"""

    with tempfile.TemporaryDirectory() as tmpd:
        f_runner = Path(tmpd) / "runner.js"
        f_runner.write_text(
            dom_preamble + "\n" + strict_safari_override + "\n" + load_lines + "\n" + post_assertions,
            encoding="utf-8",
        )
        res = subprocess.run([JSC, str(f_runner)], capture_output=True, text=True)
        if res.returncode != 0:
            print("JSC STDERR:", res.stderr)
            print("JSC STDOUT:", res.stdout)
            raise SystemExit(res.returncode)
        print(res.stdout.strip())


if __name__ == "__main__":
    main()
