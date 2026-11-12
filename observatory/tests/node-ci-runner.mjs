#!/usr/bin/env node
/**
 * Cross-Platform Headless Node.js VM E2E Test Runner (`node-ci-runner.mjs` · V181)
 * ================================================================================
 * Runs identically on Ubuntu Linux (GitHub Actions CI) and macOS with ZERO external npm packages!
 *
 * Memory-safe process isolation:
 *   Each 103 MiB Observatory suite runs in its own isolated child Node process with
 *   `--max-old-space-size=6144` so the OS reclaims 100% of V8 heap memory between suites
 *   and never hits Node's default 2 GiB V8 heap limit on GitHub Actions `ubuntu-latest`.
 *
 * Executes:
 *   1. `automated-ux-functional-suite.js` (against reconstructed `bundle-data.js`)
 *   2. `cloudflare-shards-e2e-suite.js` (against the 8 `<25 MiB` Cloudflare Pages shards)
 *   3. Unified `observatory/index.html` + 8 untruncated shards strict `file://` SecurityError survival test
 */
import { execFileSync } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import vm from "node:vm";
import { fileURLToPath } from "node:url";

const __filename = fileURLToPath(import.meta.url);
const TESTS_DIR = path.dirname(__filename);
const OBS_DIR = path.resolve(TESTS_DIR, "..");
const REPO_ROOT = path.resolve(OBS_DIR, "..");

function remapRepoPaths(codeStr) {
  return codeStr.replaceAll("/Users/fawadhaider/code/commonground-verification-gemini", REPO_ROOT);
}

function makeBaseSandbox() {
  const sandbox = {
    console,
    Math,
    Date,
    JSON,
    Object,
    Array,
    String,
    Number,
    Boolean,
    RegExp,
    Set,
    Map,
    WeakMap,
    WeakSet,
    Symbol,
    Error,
    TypeError,
    RangeError,
    URIError,
    Promise,
    Uint8Array,
    Int32Array,
    Float64Array,
    parseInt,
    parseFloat,
    isNaN,
    isFinite,
    encodeURIComponent,
    decodeURIComponent,
    setTimeout,
    clearTimeout,
    print: (...args) => console.log(...args),
  };
  sandbox.globalThis = sandbox;
  return sandbox;
}

function runJscSuiteInNodeVm(label, suiteFilePath) {
  console.log(`\n=== [Node VM] ${label} ===`);
  const sandbox = makeBaseSandbox();
  const ctx = vm.createContext(sandbox);
  sandbox.load = (targetPath) => {
    const resolved = remapRepoPaths(String(targetPath));
    const src = fs.readFileSync(resolved, "utf8");
    vm.runInContext(src, ctx, { filename: resolved });
  };

  const suiteCode = remapRepoPaths(fs.readFileSync(suiteFilePath, "utf8"));
  vm.runInContext(suiteCode, ctx, { filename: suiteFilePath });
}

function runUnifiedIndexFileOriginSuite() {
  console.log("\n=== [Node VM] 3. Unified Chrome & Safari file:// SecurityError E2E on observatory/index.html + 8 Shards ===");
  if (fs.existsSync(path.join(OBS_DIR, "safari-standalone.html")) || fs.existsSync(path.join(OBS_DIR, "safari"))) {
    throw new Error("Obsolete Safari standalone fork files still exist in observatory/!");
  }
  const indexPath = path.join(OBS_DIR, "index.html");
  const html = fs.readFileSync(indexPath, "utf8");
  const scriptMatches = [...html.matchAll(/<script\s+src="([^"?]+)(?:\?[^"]*)?"><\/script>/g)];
  if (scriptMatches.length !== 9) {
    throw new Error(`Expected 9 classic <script src> tags in observatory/index.html, found ${scriptMatches.length}`);
  }

  const suiteSrc = fs.readFileSync(path.join(TESTS_DIR, "automated-ux-functional-suite.js"), "utf8");
  const domPreamble = suiteSrc.slice(0, suiteSrc.indexOf("// Load bundle-data.js"));

  const sandbox = makeBaseSandbox();
  const ctx = vm.createContext(sandbox);

  vm.runInContext(domPreamble, ctx, { filename: "dom-preamble.js" });
  vm.runInContext(
    `
    window.addEventListener = function(){};
    window.location = { protocol: "file:", search: "", href: "file:///observatory/index.html" };
    window.history = {
      replaceState: function() { throw new Error("SecurityError: Blocked attempt to use history.replaceState() on file://"); },
      pushState: function() { throw new Error("SecurityError: Blocked attempt to use history.pushState() on file://"); }
    };
    window.localStorage = {
      getItem: function() { throw new Error("SecurityError: localStorage disabled on file://"); },
      setItem: function() { throw new Error("SecurityError: localStorage disabled on file://"); }
    };
    `,
    ctx,
    { filename: "safari-file-security-override.js" }
  );

  let totalBytes = 0;
  for (const m of scriptMatches) {
    const absScript = path.resolve(OBS_DIR, m[1]);
    totalBytes += fs.statSync(absScript).size;
    vm.runInContext(fs.readFileSync(absScript, "utf8"), ctx, { filename: absScript });
  }
  const totalMiB = (totalBytes / (1024 * 1024)).toFixed(2);

  vm.runInContext(
    `
    var mount = document.getElementById("app-mount");
    if (!mount.innerHTML || mount.innerHTML.indexOf("Loading 40-Project") !== -1 || mount.innerHTML.indexOf("CONSTELLATION SHARD DIAGNOSTIC") !== -1) {
      throw new Error("observatory/index.html failed automatic init() boot on file://!");
    }
    if (mount.innerHTML.indexOf("undefined") !== -1 || mount.innerHTML.indexOf("NaN") !== -1) {
      throw new Error("observatory/index.html rendered undefined/NaN on file:// boot!");
    }
    var pre = window.__CG_PRELOADED__;
    if (String(pre.semanticMechanisms.highLevelMechanisms[500].whyItMatters || "").length <= 45 ||
        String(pre.semanticMechanisms.customIsomorphisms[500].plainEnglishWhy || "").length <= 45 ||
        String(pre.insightPaths.connections[500].summary || "").length <= 45) {
      throw new Error("Late-index strings appear truncated!");
    }
    var cards = mount.querySelectorAll(".ingredient-card");
    if (cards.length < 20) throw new Error("Expected >= 20 .ingredient-card items, got " + cards.length);
    cards[0].click();
    if (cards[0].innerHTML.indexOf("v146-inline-card-drawer") === -1) {
      throw new Error("Clicking .ingredient-card[0] under file:// failed to expand inline drawer!");
    }
    for (var lensName of ["serendipity", "paths", "bridges", "constellation", "intuition", "galaxy"]) {
      state.lens = lensName;
      renderApp();
      if (!mount.innerHTML || mount.innerHTML.indexOf("undefined") !== -1 || mount.innerHTML.indexOf("NaN") !== -1) {
        throw new Error("Lens " + lensName + " failed in observatory/index.html!");
      }
    }
    print("UNIFIED_INDEX_FILE_ORIGIN_NODE_VM_OK: scripts=9, totalUntruncatedPayload=${totalMiB}MiB, cards=" + cards.length + ", lenses=6/6");
    `,
    ctx,
    { filename: "unified-file-assertions.js" }
  );
}

const suiteArg = process.argv.find((a) => a.startsWith("--suite="));
if (suiteArg) {
  const which = suiteArg.split("=")[1];
  if (which === "1") {
    runJscSuiteInNodeVm("1. Local Monolithic Bundle Automated UX & Math Suite", path.join(TESTS_DIR, "automated-ux-functional-suite.js"));
  } else if (which === "2") {
    runJscSuiteInNodeVm("2. Cloudflare 8-Shard (<25 MiB) Automated UX & Math Suite", path.join(TESTS_DIR, "cloudflare-shards-e2e-suite.js"));
  } else if (which === "3") {
    runUnifiedIndexFileOriginSuite();
  } else {
    throw new Error(`Unknown --suite=${which}`);
  }
} else {
  for (const s of ["1", "2", "3"]) {
    execFileSync(process.execPath, ["--max-old-space-size=6144", __filename, `--suite=${s}`], {
      stdio: "inherit",
      env: { ...process.env, NODE_OPTIONS: "--max-old-space-size=6144" },
    });
  }
  console.log("\nNODE_CI_ALL_E2E_SUITES_PASSED_OK");
}
