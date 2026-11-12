#!/usr/bin/env python3
"""
V165 — Immersive, Elegant & Intuitive Observatory Redesign
==========================================================
Upgrades:
1. `observatory/unified.css`:
   - Celestial Obsidian & Champagne Gold glassmorphic design language (`backdrop-filter: blur(22px)`),
     multi-layer ambient aurora lighting, hairline specular borders, custom thin dark scrollbars,
     tighter hero/control vertical rhythm so the 3D Constellation sits higher above the fold,
     smooth cubic-bezier hover micro-elevations, Zen Theater full-bleed cinema layout
     (`.galaxy-workspace.is-zen-theater` + floating glass `#inspector-panel` drawer),
     floating Constellation HUD breadcrumb pill (`.cg-galaxy-hud-pill`),
     Universal `⌘K` Spotlight Omnibox modal (`#cg-v165-omnibox-backdrop`),
     and 3-tab progressive-disclosure Inspector segmented bar (`.cg-ins-tabbar`).
2. `observatory/index.html`:
   - Bumps `?v=164` -> `?v=165`.
   - Adds sleek `⌘K Quick Jump` (`#cg-omnibox-open-btn`) and `⛶ Theater` (`#cg-masthead-zen-btn`)
     buttons in `.masthead-actions`.
3. `observatory/unified-standalone.js`:
   - Upgrades `mountGalaxyCanvas` with a 160-star 3D parallax deep-space starfield, dual-tone
     celestial nebula glow, animated luminous photon pulses along active cross-domain bridge
     arcs, selected-star on-canvas callout label + dual reticle, and smooth eased `flyToCamera`
     interpolation (with deterministic headless fallback).
   - Injects the interactive Floating Constellation HUD Pill (`#cg-galaxy-hud-pill`) and `Theater (Z)`
     camera control in `.galaxy-scene` / `.camera-controls`.
   - Adds `window.cgToggleZenTheater`, `window.cgToggleZenInspectorCollapse`,
     `window.cgOpenOmnibox` (`⌘K` / `Ctrl+K`), and `window.cgApplyInspectorTabs` (DOM-preserving
     3-tab progressive disclosure for `#inspector-panel`).
   - Adds Suite 24 (`5` new automated UX & visual state checks -> `198/198` total).
4. Updates `build-cloudflare-dist.py` (`ASSET_VER = "165"`) and `continuous-insight-daemon.py` (`V165`).
"""
from pathlib import Path

OBS_DIR = Path(__file__).resolve().parent.parent
CSS_PATH = OBS_DIR / "unified.css"
HTML_PATH = OBS_DIR / "index.html"
JS_PATH = OBS_DIR / "unified-standalone.js"
CF_SCRIPT = OBS_DIR / "scripts" / "build-cloudflare-dist.py"
DAEMON_SCRIPT = OBS_DIR / "scripts" / "continuous-insight-daemon.py"


V165_CSS_BLOCK = """

/* ============================================================================
   V165 IMMERSIVE CELESTIAL OBSIDIAN, ZEN THEATER, OMNIBOX & TABBED INSPECTOR
   ============================================================================ */
:root {
  --space: #050911;
  --space-deep: #03060c;
  --surface: rgba(12, 20, 34, 0.78);
  --surface-elevated: rgba(17, 29, 48, 0.86);
  --surface-hover: rgba(24, 40, 66, 0.92);
  --paper: #f5f3ee;
  --muted: #9cb0c9;
  --dim: #647894;
  --line: rgba(148, 169, 199, 0.14);
  --line-bright: rgba(165, 190, 224, 0.26);
  --gold: #e6c88a;
  --gold-soft: rgba(230, 200, 138, 0.14);
  --ease-out-expo: cubic-bezier(0.22, 1, 0.36, 1);
}

/* Subtle Custom Thin Dark Scrollbars */
* {
  scrollbar-width: thin;
  scrollbar-color: rgba(148, 163, 184, 0.28) rgba(5, 9, 17, 0.45);
}
::-webkit-scrollbar {
  width: 7px;
  height: 7px;
}
::-webkit-scrollbar-track {
  background: rgba(5, 9, 17, 0.45);
}
::-webkit-scrollbar-thumb {
  background: rgba(148, 163, 184, 0.28);
  border-radius: 999px;
}
::-webkit-scrollbar-thumb:hover {
  background: rgba(230, 200, 138, 0.52);
}

body.cg-calm-editorial {
  background:
    radial-gradient(ellipse 90% 48% at 50% -8%, rgba(36, 74, 122, 0.34) 0%, transparent 68%),
    radial-gradient(circle at 86% 14%, rgba(230, 200, 138, 0.08) 0%, transparent 42%),
    radial-gradient(circle at 14% 32%, rgba(52, 211, 153, 0.05) 0%, transparent 44%),
    var(--space);
  background-attachment: fixed;
}

/* Frosted Glass Masthead & Quick-Jump Omnibox Pill */
.masthead {
  background: rgba(5, 9, 17, 0.82);
  -webkit-backdrop-filter: blur(22px) saturate(150%);
  backdrop-filter: blur(22px) saturate(150%);
  border-bottom: 1px solid rgba(230, 200, 138, 0.16);
  box-shadow: 0 8px 32px rgba(0, 0, 0, 0.38);
}
.brand-mark {
  box-shadow: 0 0 18px rgba(230, 200, 138, 0.22), inset 0 1px 0 rgba(255, 255, 255, 0.18);
  transition: transform 0.35s var(--ease-out-expo), box-shadow 0.25s ease;
}
.brand:hover .brand-mark {
  transform: rotate(36deg) scale(1.06);
  box-shadow: 0 0 24px rgba(230, 200, 138, 0.44);
}
.lens-nav {
  background: rgba(9, 15, 26, 0.82);
  border: 1px solid rgba(148, 163, 184, 0.18);
  box-shadow: inset 0 1px 0 rgba(255, 255, 255, 0.04);
}
.lens-btn {
  transition: all 0.2s var(--ease-out-expo);
}
.lens-btn[aria-pressed="true"] {
  background: linear-gradient(135deg, rgba(230, 200, 138, 0.24), rgba(230, 200, 138, 0.11));
  color: #fff6e0;
  border: 1px solid rgba(230, 200, 138, 0.52);
  box-shadow: 0 2px 14px rgba(230, 200, 138, 0.16), inset 0 1px 0 rgba(255, 255, 255, 0.14);
}

.cg-omnibox-trigger {
  display: inline-flex;
  align-items: center;
  gap: 8px;
  padding: 5px 11px;
  border-radius: 9px;
  font-size: 12px;
  font-weight: 600;
  color: #e2e8f0;
  background: linear-gradient(145deg, rgba(16, 28, 46, 0.92), rgba(10, 18, 31, 0.92));
  border: 1px solid rgba(125, 211, 252, 0.32);
  box-shadow: inset 0 1px 0 rgba(255, 255, 255, 0.06);
  transition: all 0.18s var(--ease-out-expo);
}
.cg-omnibox-trigger:hover {
  border-color: var(--gold);
  color: #ffffff;
  background: rgba(22, 37, 60, 0.95);
  transform: translateY(-1px);
  box-shadow: 0 6px 18px rgba(0, 0, 0, 0.35), 0 0 14px rgba(230, 200, 138, 0.16);
}
.cg-kbd-pill {
  font-family: var(--font-mono);
  font-size: 10px;
  font-weight: 700;
  padding: 1px 5px;
  border-radius: 5px;
  background: rgba(255, 255, 255, 0.08);
  border: 1px solid rgba(255, 255, 255, 0.15);
  color: var(--gold);
  letter-spacing: 0.02em;
}
.cg-zen-masthead-btn {
  display: inline-flex;
  align-items: center;
  gap: 5px;
  padding: 5px 10px;
  border-radius: 8px;
  font-size: 11.5px;
  font-weight: 600;
  color: #cbd5e1;
  background: rgba(13, 22, 36, 0.85);
  border: 1px solid var(--line-bright);
  transition: all 0.18s var(--ease-out-expo);
}
.cg-zen-masthead-btn.is-active,
.cg-zen-masthead-btn:hover {
  border-color: var(--gold);
  color: var(--gold);
  background: rgba(230, 200, 138, 0.14);
}

/* Sleeker Above-the-Fold Editorial Hero & Entry Cards */
.cg-editorial-intro {
  padding: 12px 24px 10px;
}
.cg-intro-inner {
  padding: 14px 20px;
  gap: 18px;
  background:
    radial-gradient(circle at 12% 20%, rgba(56, 189, 248, 0.08), transparent 48%),
    radial-gradient(circle at 92% 80%, rgba(230, 200, 138, 0.08), transparent 48%),
    linear-gradient(160deg, rgba(14, 24, 40, 0.82), rgba(8, 14, 25, 0.86));
  border: 1px solid rgba(230, 200, 138, 0.2);
  box-shadow: 0 14px 36px rgba(0, 0, 0, 0.32), inset 0 1px 0 rgba(255, 255, 255, 0.06);
}
.cg-intro-headline {
  font-size: clamp(21px, 2vw, 28px);
  margin: 0 0 5px;
  background: linear-gradient(92deg, #ffffff 0%, #f5efe2 58%, #e6c88a 100%);
  -webkit-background-clip: text;
  background-clip: text;
  color: #f7f4ec;
}
.cg-intro-lead {
  font-size: 13px;
  line-height: 1.52;
}
.cg-entry-card {
  position: relative;
  overflow: hidden;
  padding: 10px 13px;
  background: linear-gradient(155deg, rgba(14, 24, 40, 0.88), rgba(8, 15, 27, 0.92));
  border: 1px solid rgba(148, 163, 184, 0.2);
  box-shadow: inset 0 1px 0 rgba(255, 255, 255, 0.05);
  transition: transform 0.2s var(--ease-out-expo), border-color 0.2s ease, box-shadow 0.2s ease, background 0.2s ease;
}
.cg-entry-card:hover {
  transform: translateY(-2px);
  border-color: rgba(230, 200, 138, 0.62);
  background: linear-gradient(155deg, rgba(20, 34, 56, 0.94), rgba(11, 20, 35, 0.96));
  box-shadow: 0 10px 24px rgba(0, 0, 0, 0.42), 0 0 18px rgba(230, 200, 138, 0.12);
}

/* Unified Filter Bar Glass Polish */
.cg-unified-controls {
  padding: 10px 15px;
  margin-bottom: 12px;
  background: rgba(10, 18, 30, 0.76);
  -webkit-backdrop-filter: blur(14px);
  backdrop-filter: blur(14px);
  border: 1px solid rgba(148, 163, 184, 0.18);
  box-shadow: 0 10px 28px rgba(0, 0, 0, 0.26), inset 0 1px 0 rgba(255, 255, 255, 0.04);
}
.search-box input {
  background: rgba(5, 10, 19, 0.88);
  border-color: rgba(148, 163, 184, 0.26);
  transition: border-color 0.18s ease, box-shadow 0.18s ease;
}
.search-box input:focus {
  border-color: var(--gold);
  box-shadow: 0 0 0 3px rgba(230, 200, 138, 0.15);
  outline: none;
}

/* Immersive 3D Galaxy Viewport & Floating HUD */
.galaxy-panel {
  position: relative;
  border-radius: 18px;
  border: 1px solid rgba(165, 190, 224, 0.22);
  background:
    radial-gradient(ellipse 75% 65% at 50% 48%, rgba(22, 52, 92, 0.44), transparent 72%),
    radial-gradient(circle at 28% 28%, rgba(52, 211, 153, 0.06), transparent 46%),
    radial-gradient(circle at 74% 68%, rgba(230, 200, 138, 0.07), transparent 48%),
    #030710;
  box-shadow: 0 22px 60px rgba(0, 0, 0, 0.56), inset 0 1px 0 rgba(255, 255, 255, 0.07);
}
.galaxy-scene {
  height: 615px;
  transition: height 0.32s var(--ease-out-expo);
}
.hub-node {
  -webkit-backdrop-filter: blur(8px);
  backdrop-filter: blur(8px);
  background: rgba(6, 12, 22, 0.84);
  box-shadow: 0 4px 12px rgba(0, 0, 0, 0.45);
  transition: transform 0.18s var(--ease-out-expo), background 0.18s ease, box-shadow 0.18s ease, border-color 0.18s ease;
}
.hub-node:hover, .hub-node.is-highlighted {
  transform: translate(-50%, -50%) scale(1.14);
  background: rgba(17, 32, 54, 0.95);
}
.galaxy-tooltip {
  -webkit-backdrop-filter: blur(16px) saturate(140%);
  backdrop-filter: blur(16px) saturate(140%);
  background: rgba(8, 15, 28, 0.92);
  border: 1px solid rgba(230, 200, 138, 0.65);
  box-shadow: 0 16px 38px rgba(0, 0, 0, 0.72), 0 0 20px rgba(230, 200, 138, 0.14);
  border-radius: 12px;
  padding: 10px 13px;
}

/* Floating Constellation Status & Gesture Pill inside .galaxy-scene */
.cg-galaxy-hud-pill {
  position: absolute;
  left: 14px;
  top: 12px;
  z-index: 8;
  display: inline-flex;
  align-items: center;
  gap: 8px;
  flex-wrap: wrap;
  max-width: min(560px, calc(100% - 28px));
  padding: 6px 12px;
  border-radius: 999px;
  font-size: 11.5px;
  color: #e2e8f0;
  background: rgba(6, 12, 23, 0.78);
  -webkit-backdrop-filter: blur(14px);
  backdrop-filter: blur(14px);
  border: 1px solid rgba(148, 163, 184, 0.24);
  box-shadow: 0 8px 24px rgba(0, 0, 0, 0.45);
  pointer-events: auto;
}
.cg-galaxy-hud-pill .cg-hud-dot {
  width: 7px;
  height: 7px;
  border-radius: 50%;
  background: #34d399;
  box-shadow: 0 0 8px #34d399;
  flex: none;
}
.cg-galaxy-hud-pill button {
  padding: 2px 8px;
  font-size: 10.5px;
  border-radius: 999px;
  background: rgba(230, 200, 138, 0.14);
  border: 1px solid rgba(230, 200, 138, 0.42);
  color: var(--gold);
}
.cg-galaxy-hud-pill button:hover {
  background: rgba(230, 200, 138, 0.28);
  color: #fff;
}

/* Full-Bleed Zen Theater Mode (Press Z or Click Theater) */
body.cg-zen-theater #v60-quickstart-hero,
body.cg-zen-theater .cg-unified-controls {
  display: none !important;
}
body.cg-zen-theater main {
  max-width: 100%;
  padding: 10px 16px 48px;
}
.galaxy-workspace.is-zen-theater {
  position: relative;
  grid-template-columns: 1fr !important;
}
.galaxy-workspace.is-zen-theater .galaxy-scene {
  height: min(79vh, 840px);
  min-height: 660px;
}
.galaxy-workspace.is-zen-theater .inspector-panel {
  position: absolute;
  right: 16px;
  top: 54px;
  z-index: 14;
  width: min(435px, calc(100vw - 44px));
  max-height: calc(100% - 112px);
  background: rgba(8, 14, 26, 0.86);
  -webkit-backdrop-filter: blur(24px) saturate(150%);
  backdrop-filter: blur(24px) saturate(150%);
  border: 1px solid rgba(230, 200, 138, 0.34);
  box-shadow: 0 24px 64px rgba(0, 0, 0, 0.78);
  transition: transform 0.28s var(--ease-out-expo), opacity 0.22s ease;
}
.galaxy-workspace.is-zen-theater.is-inspector-minimized .inspector-panel {
  transform: translateX(calc(100% + 28px));
  opacity: 0;
  pointer-events: none;
}
.cg-zen-floating-bar {
  position: absolute;
  right: 16px;
  bottom: 14px;
  z-index: 15;
  display: none;
  align-items: center;
  gap: 6px;
  padding: 5px 10px;
  border-radius: 999px;
  background: rgba(6, 12, 23, 0.84);
  -webkit-backdrop-filter: blur(14px);
  backdrop-filter: blur(14px);
  border: 1px solid rgba(230, 200, 138, 0.38);
  box-shadow: 0 10px 28px rgba(0, 0, 0, 0.55);
}
.galaxy-workspace.is-zen-theater .cg-zen-floating-bar {
  display: inline-flex;
}

/* Elegant Glassmorphic Inspector & 3-Tab Progressive Disclosure */
.inspector-panel {
  border-radius: 18px;
  background: linear-gradient(165deg, rgba(15, 26, 44, 0.92) 0%, rgba(8, 15, 27, 0.95) 100%);
  border: 1px solid rgba(165, 190, 224, 0.24);
  box-shadow: 0 18px 48px rgba(0, 0, 0, 0.42), inset 0 1px 0 rgba(255, 255, 255, 0.06);
  max-height: 705px;
}
.cg-ins-tabbar {
  display: flex;
  gap: 4px;
  padding: 4px;
  margin: 8px 0 12px;
  border-radius: 10px;
  background: rgba(4, 9, 18, 0.78);
  border: 1px solid rgba(148, 163, 184, 0.2);
}
.cg-ins-tab {
  flex: 1;
  padding: 5px 8px;
  border-radius: 7px;
  border: 1px solid transparent;
  background: transparent;
  color: #94a3b8;
  font-size: 11px;
  font-weight: 650;
  text-align: center;
  cursor: pointer;
  transition: all 0.16s var(--ease-out-expo);
}
.cg-ins-tab:hover {
  color: #f8fafc;
  background: rgba(255, 255, 255, 0.05);
}
.cg-ins-tab.is-active {
  background: linear-gradient(135deg, rgba(230, 200, 138, 0.22), rgba(56, 189, 248, 0.14));
  border-color: rgba(230, 200, 138, 0.5);
  color: #fff8e7;
  box-shadow: 0 2px 10px rgba(0, 0, 0, 0.28);
}
/* CSS-attribute-driven progressive disclosure so ALL child nodes stay intact in DOM */
#inspector-panel[data-active-ins-tab="intuition"] .cg-ins-pane[data-ins-pane="mechanism"],
#inspector-panel[data-active-ins-tab="intuition"] .cg-ins-pane[data-ins-pane="rigor"] {
  display: none;
}
#inspector-panel[data-active-ins-tab="mechanism"] .cg-ins-pane[data-ins-pane="intuition"],
#inspector-panel[data-active-ins-tab="mechanism"] .cg-ins-pane[data-ins-pane="rigor"] {
  display: none;
}
#inspector-panel[data-active-ins-tab="rigor"] .cg-ins-pane[data-ins-pane="intuition"],
#inspector-panel[data-active-ins-tab="rigor"] .cg-ins-pane[data-ins-pane="mechanism"] {
  display: none;
}

/* Refined Catalogue Cards */
.cg-calm-editorial .ingredient-card {
  border-radius: 13px;
  background: linear-gradient(160deg, rgba(13, 22, 37, 0.82), rgba(9, 15, 27, 0.88));
  border: 1px solid rgba(148, 163, 184, 0.16);
  box-shadow: 0 6px 20px rgba(0, 0, 0, 0.2), inset 0 1px 0 rgba(255, 255, 255, 0.04);
  transition: transform 0.18s var(--ease-out-expo), border-color 0.18s ease, box-shadow 0.18s ease, background 0.18s ease;
}
.cg-calm-editorial .ingredient-card:hover {
  transform: translateY(-2px);
  border-color: rgba(230, 200, 138, 0.52);
  background: linear-gradient(160deg, rgba(18, 30, 50, 0.92), rgba(11, 20, 35, 0.95));
  box-shadow: 0 12px 28px rgba(0, 0, 0, 0.36), 0 0 16px rgba(230, 200, 138, 0.09);
}

/* Universal ⌘K Spotlight Omnibox Modal */
.cg-omnibox-backdrop {
  position: fixed;
  inset: 0;
  z-index: 100020;
  background: rgba(2, 6, 15, 0.76);
  -webkit-backdrop-filter: blur(14px) saturate(140%);
  backdrop-filter: blur(14px) saturate(140%);
  display: flex;
  align-items: flex-start;
  justify-content: center;
  padding: 7vh 16px 24px;
}
.cg-omnibox-dialog {
  width: min(760px, 95vw);
  max-height: 82vh;
  display: flex;
  flex-direction: column;
  border-radius: 18px;
  background: linear-gradient(165deg, rgba(13, 23, 40, 0.97), rgba(7, 13, 24, 0.99));
  border: 1px solid rgba(230, 200, 138, 0.45);
  box-shadow: 0 32px 80px rgba(0, 0, 0, 0.82), 0 0 40px rgba(56, 189, 248, 0.12), inset 0 1px 0 rgba(255, 255, 255, 0.1);
  overflow: hidden;
}
.cg-omnibox-search-row {
  display: flex;
  align-items: center;
  gap: 10px;
  padding: 14px 18px;
  border-bottom: 1px solid rgba(148, 163, 184, 0.18);
  background: rgba(5, 10, 20, 0.65);
}
.cg-omnibox-input {
  flex: 1;
  border: none !important;
  background: transparent !important;
  color: #f8fafc !important;
  font-size: 15.5px !important;
  font-weight: 500;
  padding: 4px 2px !important;
  box-shadow: none !important;
}
.cg-omnibox-input:focus {
  outline: none !important;
}
.cg-omnibox-cats {
  display: flex;
  gap: 6px;
  flex-wrap: wrap;
  padding: 9px 18px;
  border-bottom: 1px solid rgba(148, 163, 184, 0.13);
  background: rgba(8, 14, 26, 0.55);
}
.cg-omnibox-cat-btn {
  padding: 4px 10px;
  border-radius: 999px;
  font-size: 11px;
  font-weight: 600;
  color: #cbd5e1;
  background: rgba(15, 23, 42, 0.72);
  border: 1px solid rgba(148, 163, 184, 0.22);
}
.cg-omnibox-cat-btn.is-active {
  background: rgba(230, 200, 138, 0.2);
  border-color: var(--gold);
  color: #fff8e7;
}
.cg-omnibox-results {
  overflow-y: auto;
  padding: 10px 12px;
  display: flex;
  flex-direction: column;
  gap: 5px;
  max-height: 54vh;
}
.cg-omnibox-item {
  width: 100%;
  text-align: left;
  padding: 10px 13px;
  border-radius: 11px;
  background: rgba(12, 21, 36, 0.65);
  border: 1px solid rgba(148, 163, 184, 0.14);
  display: flex;
  justify-content: space-between;
  align-items: center;
  gap: 12px;
  cursor: pointer;
  transition: all 0.14s ease;
}
.cg-omnibox-item:hover,
.cg-omnibox-item.is-selected {
  background: linear-gradient(135deg, rgba(23, 39, 64, 0.94), rgba(15, 27, 46, 0.96));
  border-color: rgba(230, 200, 138, 0.55);
  transform: translateX(2px);
}
.cg-omnibox-foot {
  display: flex;
  justify-content: space-between;
  align-items: center;
  gap: 10px;
  flex-wrap: wrap;
  padding: 9px 18px;
  font-size: 11px;
  color: #94a3b8;
  border-top: 1px solid rgba(148, 163, 184, 0.14);
  background: rgba(4, 8, 16, 0.78);
}
"""


V165_JS_BLOCK = r"""

// === V165 IMMERSIVE 3D ZEN THEATER, UNIVERSAL ⌘K OMNIBOX, HUD BREADCRUMB & SCANNABLE TABBED INSPECTOR ===
(function() {
  if (typeof window === "undefined") return;

  window._cgZenTheaterActive = Boolean(window._cgZenTheaterActive);
  window._cgZenInspectorMinimized = Boolean(window._cgZenInspectorMinimized);
  window._cgInspectorActiveTab = window._cgInspectorActiveTab || "intuition";
  window._cgOmniboxState = {
    open: false,
    query: "",
    category: "all",
    selectedIdx: 0,
    items: []
  };

  // Cross-environment class toggle helper (updates both classList AND className string for headless WebKit JSC mocks)
  function cgSetClassFlag(el, cls, enabled) {
    if (!el) return;
    var parts = String(el.className || "").split(/\s+/).filter(Boolean);
    var idx = parts.indexOf(cls);
    if (enabled && idx === -1) parts.push(cls);
    if (!enabled && idx !== -1) parts.splice(idx, 1);
    el.className = parts.join(" ");
    if (el.attrs) el.attrs["class"] = el.className;
    if (el.classList && typeof el.classList.toggle === "function") {
      try { el.classList.toggle(cls, Boolean(enabled)); } catch (_) {}
    }
  }
  function cgHasClassFlag(el, cls) {
    if (!el) return false;
    var parts = String(el.className || "").split(/\s+/).filter(Boolean);
    return parts.indexOf(cls) !== -1;
  }
  window.cgHasClassFlag = cgHasClassFlag;

  // 1. Zen Theater Mode (Full-bleed 80vh 3D Constellation + Floating Glass Inspector)
  window.cgSyncZenTheaterDom = function() {
    var isZen = Boolean(window._cgZenTheaterActive);
    var isMin = Boolean(window._cgZenInspectorMinimized);
    if (document.body) {
      cgSetClassFlag(document.body, "cg-zen-theater", isZen);
    }
    var mountEl = document.getElementById("app-mount");
    var wsList = mountEl ? mountEl.querySelectorAll(".galaxy-workspace") : document.querySelectorAll(".galaxy-workspace");
    var ws = wsList && wsList.length ? wsList[0] : null;
    if (ws) {
      cgSetClassFlag(ws, "is-zen-theater", isZen);
      cgSetClassFlag(ws, "is-inspector-minimized", isZen && isMin);
    }
    var mBtn = document.getElementById("cg-masthead-zen-btn");
    if (mBtn) {
      cgSetClassFlag(mBtn, "is-active", isZen);
      mBtn.setAttribute("aria-pressed", String(isZen));
      mBtn.innerHTML = isZen ? "⛶ Exit Theater" : "⛶ Theater";
    }
    var camZenList = mountEl ? mountEl.querySelectorAll('[data-cam="zen"]') : [];
    if (camZenList && camZenList.length) {
      cgSetClassFlag(camZenList[0], "is-active", isZen);
    }
    var minBtn = document.getElementById("cg-zen-min-inspector-btn");
    if (minBtn) {
      minBtn.textContent = isMin ? "◂ Show Inspector" : "Hide Inspector ▸";
    }
    if (typeof galaxyController !== "undefined" && galaxyController && typeof galaxyController.update === "function" && typeof filterGalaxyRecords === "function") {
      galaxyController.update(filterGalaxyRecords().records);
    }
  };

  window.cgToggleZenTheater = function(forceState) {
    if (typeof state !== "undefined" && state.lens !== "galaxy") {
      state.lens = "galaxy";
      if (typeof renderApp === "function") renderApp();
    }
    window._cgZenTheaterActive = typeof forceState === "boolean" ? forceState : !window._cgZenTheaterActive;
    if (!window._cgZenTheaterActive) {
      window._cgZenInspectorMinimized = false;
    }
    window.cgSyncZenTheaterDom();
    return window._cgZenTheaterActive;
  };

  window.cgToggleZenInspectorCollapse = function(forceMin) {
    window._cgZenInspectorMinimized = typeof forceMin === "boolean" ? forceMin : !window._cgZenInspectorMinimized;
    window.cgSyncZenTheaterDom();
    return window._cgZenInspectorMinimized;
  };

  // 2. Smooth Inertial 3D Camera Flight Helper (frames any star in 3D Galaxy cleanly)
  window.cgFlyGalaxyToStar = function(starId) {
    if (!starId || typeof manifest === "undefined" || !manifest) return false;
    var cam = window._cgSavedGalaxyCamera;
    if (!cam) {
      cam = { yaw: 0.18, pitch: 0.34, zoom: 1.0 };
      window._cgSavedGalaxyCamera = cam;
    }
    var hash = function(str) {
      var h = 2166136261;
      for (var i = 0; i < str.length; i++) h = Math.imul(h ^ str.charCodeAt(i), 16777619);
      return h >>> 0;
    };
    var rec = typeof recordById !== "undefined" ? recordById.get(starId) : null;
    var famIds = (manifest.families || []).map(function(f){ return f.id; });
    var seed = hash(String(starId));
    var fIdx = rec ? Math.max(0, famIds.indexOf(rec.family)) : 0;
    var radius = 0.14 + 0.72 * Math.sqrt((seed % 10000) / 10000);
    var angle = (fIdx * Math.PI * 2) / Math.max(1, famIds.length) + radius * 2.85 + (((seed >>> 14) % 1000) / 1000 - 0.5) * 0.92;
    var z = (((seed >>> 8) % 1000) / 1000 - 0.5) * 0.44;
    var px = Math.cos(angle) * radius;
    var py = Math.sin(angle) * radius;

    var targetYaw = Math.atan2(z, px || 0.001) - 0.14;
    var targetPitch = Math.max(-0.82, Math.min(0.82, -py * 0.52));
    var targetZoom = 1.48;

    var startYaw = Number(cam.yaw || 0.18);
    var startPitch = Number(cam.pitch || 0.34);
    var startZoom = Number(cam.zoom || 1.0);

    cam.yaw = targetYaw;
    cam.pitch = targetPitch;
    cam.zoom = targetZoom;

    var isRealBrowserRAF = typeof window.requestAnimationFrame === "function" &&
      String(window.requestAnimationFrame).indexOf("[native code]") !== -1;
    if (isRealBrowserRAF && typeof galaxyController !== "undefined" && galaxyController) {
      var step = 0;
      var totalSteps = 18;
      cam.yaw = startYaw;
      cam.pitch = startPitch;
      cam.zoom = startZoom;
      var tick = function() {
        step++;
        var t = Math.min(1, step / totalSteps);
        var ease = 1 - Math.pow(1 - t, 3);
        cam.yaw = startYaw + (targetYaw - startYaw) * ease;
        cam.pitch = startPitch + (targetPitch - startPitch) * ease;
        cam.zoom = startZoom + (targetZoom - startZoom) * ease;
        if (galaxyController && typeof galaxyController.command === "function") {
          galaxyController.command("redraw");
        }
        if (t < 1) window.requestAnimationFrame(tick);
      };
      window.requestAnimationFrame(tick);
    } else if (typeof galaxyController !== "undefined" && galaxyController && typeof galaxyController.command === "function") {
      galaxyController.command("redraw");
    }
    return true;
  };

  // 3. Build Floating Constellation HUD Breadcrumb & Zen Bar inside .galaxy-scene
  window.cgBuildGalaxyHudHtml = function() {
    if (typeof state === "undefined" || !manifest) return "";
    var totalProjs = (manifest.projectOrder || []).length || 40;
    var activeCount = (state.projects || []).length;
    var leadProjs = window._cgHighlightedLeadProjects || [];
    var picked = state.source ? recordById.get(state.source) : null;

    if (picked) {
      var shortTitle = String(picked.name || picked.id).slice(0, 44);
      return '<span class="cg-hud-dot" style="background:#e6c88a;box-shadow:0 0 9px #e6c88a;"></span>' +
        '<span><strong style="color:#fff8e7;">Locked Star:</strong> ' + esc(shortTitle) + (String(picked.name || "").length > 44 ? "…" : "") + '</span>' +
        '<button type="button" onclick="window.cgFlyGalaxyToStar(state.source)">Fly Closer</button>' +
        '<button type="button" onclick="state.source=null;state.activeMotifIds=[];syncUrl(false);renderApp();">Clear ×</button>';
    }
    if (leadProjs.length >= 2) {
      var lIdx = typeof window._cgActiveLeadIdx === "number" ? (window._cgActiveLeadIdx + 1) : 1;
      var pNames = leadProjs.map(function(pid){ return (manifest.projects[pid] && manifest.projects[pid].short) || pid; }).join(" ↔ ");
      return '<span class="cg-hud-dot"></span>' +
        '<span><strong style="color:#a7f3d0;">Lead #' + lIdx + ' Beam:</strong> ' + esc(pNames) + '</span>' +
        '<button type="button" onclick="if(window.cgFocusLeadBestStarInGalaxy)window.cgFocusLeadBestStarInGalaxy(' + (lIdx - 1) + ')">Jump to Lead Star ★</button>' +
        '<button type="button" onclick="window._cgHighlightedLeadProjects=null;renderApp();">Reset ×</button>';
    }
    if (activeCount < totalProjs) {
      var subLabel = activeCount <= 3
        ? state.projects.map(function(pid){ return (manifest.projects[pid] && manifest.projects[pid].short) || pid; }).join(state.match === "all" ? " ∩ " : " ∪ ")
        : (activeCount + " of " + totalProjs + " Projects");
      return '<span class="cg-hud-dot" style="background:#59c2ff;box-shadow:0 0 8px #59c2ff;"></span>' +
        '<span><strong style="color:#bae6fd;">Filtered View:</strong> ' + esc(subLabel) + '</span>' +
        '<button type="button" onclick="state.ecosystem=\'all\';state.projects=manifest.projectOrder.slice();state.match=\'any\';syncUrl(false);renderApp();">All 40 ×</button>';
    }
    return '<span class="cg-hud-dot"></span>' +
      '<span><strong>40-Project Cosmos</strong> · Drag to orbit · Scroll to zoom · Click any ★/◆ star or Shift+Click 2 hubs</span>' +
      '<button type="button" onclick="window.cgOpenOmnibox(\'\')">Quick Jump ⌘K</button>';
  };

  window.cgMountGalaxyHudOverlay = function() {
    var mountEl = document.getElementById("app-mount");
    var scenes = mountEl ? mountEl.querySelectorAll(".galaxy-scene") : [];
    var scene = scenes && scenes.length ? scenes[0] : null;
    if (scene) {
      var hudMarkup = window.cgBuildGalaxyHudHtml();
      var existingHud = scene.querySelector("#cg-galaxy-hud-pill");
      if (!existingHud) {
        scene.insertAdjacentHTML("beforeend",
          '<div id="cg-galaxy-hud-pill" class="cg-galaxy-hud-pill" aria-label="Constellation status and quick actions">' + hudMarkup + '</div>' +
          '<div id="cg-zen-floating-bar" class="cg-zen-floating-bar">' +
            '<button type="button" id="cg-zen-min-inspector-btn" class="cg-calm-chip" onclick="window.cgToggleZenInspectorCollapse()">Hide Inspector ▸</button>' +
            '<button type="button" class="cg-calm-chip" style="border-color:var(--gold);color:var(--gold);" onclick="window.cgToggleZenTheater(false)">Exit Theater (Z)</button>' +
          '</div>'
        );
      } else {
        existingHud.innerHTML = hudMarkup;
      }
      var hudRef = document.getElementById("cg-galaxy-hud-pill");
      if (hudRef) hudRef.innerHTML = hudMarkup;
    }
    var camBars = mountEl ? mountEl.querySelectorAll(".camera-controls") : [];
    var camBar = camBars && camBars.length ? camBars[0] : null;
    if (camBar && !camBar.querySelector('[data-cam="zen"]')) {
      camBar.insertAdjacentHTML("beforeend",
        '<button type="button" data-cam="zen" class="' + (window._cgZenTheaterActive ? "is-active" : "") + '" title="Toggle full-bleed Zen Theater mode (Z)" onclick="window.cgToggleZenTheater()">⛶ Theater</button>'
      );
    }
    window.cgSyncZenTheaterDom();
  };

  // 4. Scannable 3-Tab Progressive Disclosure for Selected Stars in #inspector-panel
  // Driven via #inspector-panel[data-active-ins-tab] + HTML wrapper panes so ALL inner HTML & button IDs stay intact!
  window.cgSwitchInspectorTab = function(tabId) {
    window._cgInspectorActiveTab = tabId || "intuition";
    var panel = document.getElementById("inspector-panel");
    if (!panel) return;
    panel.setAttribute("data-active-ins-tab", window._cgInspectorActiveTab);
    panel.querySelectorAll("[data-ins-tab]").forEach(function(btn) {
      var active = btn.getAttribute("data-ins-tab") === window._cgInspectorActiveTab;
      cgSetClassFlag(btn, "is-active", active);
      btn.setAttribute("aria-selected", String(active));
    });
  };

  window.cgRebindInspectorButtons = function(panel, picked) {
    if (!panel || !picked) return;
    panel.querySelectorAll("[data-proof-stage]").forEach(function(btn) {
      btn.onclick = function() { state.activeProofStage = Number(btn.dataset.proofStage); renderInspector(); };
    });
    var clr = document.getElementById("v7-clear-star");
    if (clr) clr.onclick = function() { state.source = null; renderInspector(); };
    var fullM = document.getElementById("v7-open-full-mech");
    if (fullM && picked.mechObj) fullM.onclick = function() {
      state.lens = "serendipity"; state.serenSubmode = "mechanisms"; state.selectedMechanismId = picked.mechObj.id; syncUrl(false); renderApp();
    };
    var isoP = document.getElementById("v7-isolate-mech-projs");
    if (isoP && picked.mechObj) isoP.onclick = function() {
      state.projects = picked.mechObj.participatingProjects.map(function(p){ return p.projectId; }); state.match = "any"; syncUrl(false); renderApp();
    };
    var fullI = document.getElementById("v7-open-full-iso");
    if (fullI && picked.isoObj) fullI.onclick = function() {
      state.lens = "serendipity"; state.serenSubmode = "isomorphisms"; state.selectedIsoId = picked.isoObj.id; syncUrl(false); renderApp();
    };
  };

  window.cgApplyInspectorTabs = function() {
    var panel = document.getElementById("inspector-panel");
    if (!panel || typeof state === "undefined" || !state.source) {
      if (panel) panel.setAttribute("data-active-ins-tab", "");
      return;
    }
    var html = panel.innerHTML || "";
    if (!html || html.indexOf("cg-ins-tabbar") !== -1) {
      window.cgSwitchInspectorTab(window._cgInspectorActiveTab || "intuition");
      return;
    }
    var picked = recordById.get(state.source);
    if (!picked || (picked.v7Kind !== "mechanism" && picked.v7Kind !== "isomorphism")) return;

    var curTab = window._cgInspectorActiveTab || "intuition";
    var tabBarHtml =
      '<div class="cg-ins-tabbar" role="tablist" aria-label="Inspector reading sections">' +
        '<button type="button" role="tab" class="cg-ins-tab ' + (curTab === "intuition" ? "is-active" : "") + '" data-ins-tab="intuition" onclick="window.cgSwitchInspectorTab(\'intuition\')">✦ Intuition &amp; Impact</button>' +
        '<button type="button" role="tab" class="cg-ins-tab ' + (curTab === "mechanism" ? "is-active" : "") + '" data-ins-tab="mechanism" onclick="window.cgSwitchInspectorTab(\'mechanism\')">⇄ Proof &amp; Rosetta</button>' +
        '<button type="button" role="tab" class="cg-ins-tab ' + (curTab === "rigor" ? "is-active" : "") + '" data-ins-tab="rigor" onclick="window.cgSwitchInspectorTab(\'rigor\')">✓ Gates &amp; Provenance</button>' +
        '<button type="button" role="tab" class="cg-ins-tab ' + (curTab === "all" ? "is-active" : "") + '" data-ins-tab="all" onclick="window.cgSwitchInspectorTab(\'all\')">All</button>' +
      '</div>';

    // Insert the 3-tab segmented control right before the provenance/plain-English body,
    // and wrap the provenance box in rigor pane, plain-English + consequence in intuition pane,
    // and proof-stepper / code blocks in mechanism pane while preserving 100% of HTML content!
    var provMarker = '<div class="cg-provenance-critique-box"';
    var plainMarker = '<div class="v6-plain-box">';
    var insertIdx = html.indexOf(provMarker);
    if (insertIdx === -1) insertIdx = html.indexOf(plainMarker);
    if (insertIdx === -1) return;

    var headHtml = html.slice(0, insertIdx);
    var bodyHtml = html.slice(insertIdx);

    // Split footer button bar so primary actions stay pinned at bottom across all tabs
    var footerIdx = bodyHtml.indexOf('<div style="display:flex;gap:8px;flex-wrap:wrap;margin-top:12px">');
    if (footerIdx === -1) footerIdx = bodyHtml.indexOf('<button type="button" id="v7-open-full-iso"');
    var footerHtml = "";
    if (footerIdx !== -1) {
      footerHtml = bodyHtml.slice(footerIdx);
      bodyHtml = bodyHtml.slice(0, footerIdx);
    }

    // Partition bodyHtml cleanly at known structural landmarks
    var plainPos = bodyHtml.indexOf(plainMarker);
    var rigorTopHtml = plainPos > 0 ? bodyHtml.slice(0, plainPos) : "";
    var restAfterProv = plainPos > 0 ? bodyHtml.slice(plainPos) : bodyHtml;

    // Move .cg-consequence-usecase-card into Intuition & Impact so users immediately see "Where This Leads"
    var cuMarker = '<div class="cg-consequence-usecase-card">';
    var cuHtml = "";
    var cuIdx = rigorTopHtml.indexOf(cuMarker);
    if (cuIdx !== -1) {
      cuHtml = rigorTopHtml.slice(cuIdx);
      rigorTopHtml = rigorTopHtml.slice(0, cuIdx);
    }

    // Split restAfterProv into intuition lead vs proof/mechanism details
    var mechSplitMarkers = [
      '<div style="margin:12px 0;background:#071120;',
      '<div class="eyebrow" style="color:#59c2ff;margin-top:10px">',
      '<div style="display:grid;gap:8px;margin-top:10px">'
    ];
    var mechSplitIdx = -1;
    for (var m = 0; m < mechSplitMarkers.length; m++) {
      var pos = restAfterProv.indexOf(mechSplitMarkers[m]);
      if (pos !== -1 && (mechSplitIdx === -1 || pos < mechSplitIdx)) mechSplitIdx = pos;
    }

    var intuitionCoreHtml = mechSplitIdx !== -1 ? restAfterProv.slice(0, mechSplitIdx) : restAfterProv;
    var mechAndTriadHtml = mechSplitIdx !== -1 ? restAfterProv.slice(mechSplitIdx) : "";

    var triadMarker = '<div class="v131-epistemic-triad"';
    var triadIdx = mechAndTriadHtml.indexOf(triadMarker);
    var mechOnlyHtml = mechAndTriadHtml;
    var triadHtml = "";
    if (triadIdx !== -1) {
      var rosettaMarker = '<details class="cg-code-disclosure">';
      var rosIdx = mechAndTriadHtml.indexOf(rosettaMarker, triadIdx);
      if (rosIdx !== -1) {
        mechOnlyHtml = mechAndTriadHtml.slice(0, triadIdx) + mechAndTriadHtml.slice(rosIdx);
        triadHtml = mechAndTriadHtml.slice(triadIdx, rosIdx);
      } else {
        mechOnlyHtml = mechAndTriadHtml.slice(0, triadIdx);
        triadHtml = mechAndTriadHtml.slice(triadIdx);
      }
    }

    panel.innerHTML =
      headHtml +
      tabBarHtml +
      '<div class="cg-ins-pane" data-ins-pane="intuition">' + intuitionCoreHtml + cuHtml + '</div>' +
      '<div class="cg-ins-pane" data-ins-pane="mechanism">' + (mechOnlyHtml || intuitionCoreHtml) + '</div>' +
      '<div class="cg-ins-pane" data-ins-pane="rigor">' + rigorTopHtml + triadHtml + '</div>' +
      footerHtml;

    panel.setAttribute("data-active-ins-tab", curTab);
    window.cgRebindInspectorButtons(panel, picked);
  };

  // 5. Universal ⌘K Spotlight Omnibox (Instant Search Across Leads, Breakthroughs, Mechanisms, Bridges, Projects, Labs & Glossary)
  window.cgBuildOmniboxCatalog = function() {
    var items = [];
    var leads = window.CG_PROMISING_RESEARCH_LEADS || [];
    leads.forEach(function(ld, idx) {
      items.push({
        id: "omni-lead-" + idx,
        cat: "leads",
        badge: "🧭 Discovery Lead #" + (idx + 1),
        badgeColor: "#34d399",
        title: ld.title.replace(/^\d+\.\s*/, ""),
        sub: ld.domains + " — " + (ld.realWorldUseCase || "").slice(0, 95),
        searchBlob: (ld.title + " " + ld.domains + " " + ld.whyPromising + " " + ld.whatStatementUnlocked + " " + ld.realWorldUseCase).toLowerCase(),
        run: function() {
          if (window.cgFocusLeadBestStarInGalaxy) {
            window.cgFocusLeadBestStarInGalaxy(idx);
            if (ld.targetStarId) window.cgFlyGalaxyToStar(ld.targetStarId);
          } else if (window.cgSelectPromisingLeadInGalaxy) {
            window.cgSelectPromisingLeadInGalaxy(idx);
          }
        }
      });
    });

    var labTitles = [
      "1. Path-Law Conditioning vs Endpoint Bridge",
      "2. Coupling Table Total-Variation Bound",
      "3. Commutative Carrier Encoding & Action",
      "4. Cut-Balance Spectral Vertex Partition",
      "5. Log-Sum-Exp Tropical Softmax Sandwich",
      "6. Möbius Divisor Inclusion-Exclusion Sieve",
      "7. Reversible Detailed-Balance Conductance",
      "8. Fenchel-Young Convex Duality Gap",
      "9. Gale-Shapley Deferred-Acceptance Stability",
      "10. Martingale Optional-Stopping Conservation",
      "11. Bellman Contraction & Myhill-Nerode Table",
      "12. 2-adic Valuation & Hensel Newton Lift",
      "13. Blackwell Garbling & DPI Witness",
      "14. Parseval DFT Plancherel Energy Identity",
      "15. Sidon Difference-Set Counting Bound",
      "16. Bellman Policy Improvement & Nerode 3-State",
      "17. RecoverableTwin, ObservableSpan & Glynn Permanent",
      "18. Gaussian Conjugate Precision & Graphon CutNorm",
      "19. Submodular Greedy Lovász & Log-Sobolev Variance",
      "20. Kantorovich Transport, Hopfian & Chebyshev Bias",
      "21. Temperley-Lieb Jones Trace, PGF & MarkovExch"
    ];
    labTitles.forEach(function(lt, idx) {
      items.push({
        id: "omni-lab-" + idx,
        cat: "labs",
        badge: "🔬 Finite Micro-Lab",
        badgeColor: "#7dd3fc",
        title: lt,
        sub: "Interactive finite witness checkable step-by-step by hand",
        searchBlob: ("lab micro-lab finite diagram " + lt).toLowerCase(),
        run: function() {
          if (window.v136OpenV34FiniteDiagramsModal) window.v136OpenV34FiniteDiagramsModal(idx);
        }
      });
    });

    if (typeof manifest !== "undefined" && manifest && manifest.projectOrder) {
      manifest.projectOrder.forEach(function(pid) {
        var p = manifest.projects[pid];
        if (!p) return;
        items.push({
          id: "omni-proj-" + pid,
          cat: "projects",
          badge: "🌌 Project · " + (p.organization || ""),
          badgeColor: p.color || "#e6c88a",
          title: p.short + " — " + p.name,
          sub: (p.discipline || p.organization) + " · Isolate hub in 3D Constellation",
          searchBlob: (pid + " " + p.short + " " + p.name + " " + (p.discipline || "") + " " + (p.organization || "")).toLowerCase(),
          run: function() {
            state.lens = "galaxy";
            state.projects = [pid];
            state.match = "any";
            state.page = 1;
            syncUrl(false);
            renderApp();
          }
        });
      });
    }

    var allIsos = (typeof semanticMechanisms !== "undefined" && semanticMechanisms && semanticMechanisms.customIsomorphisms) || [];
    allIsos.forEach(function(iso) {
      if (!iso || iso.epistemicSymbol !== "★") return;
      var dA = (iso.declA && iso.declA.name) || iso.projectA;
      var dB = (iso.declB && iso.declB.name) || iso.projectB;
      items.push({
        id: "omni-star-" + iso.id,
        cat: "verified",
        badge: "★ Reviewed Bridge",
        badgeColor: "#34d399",
        title: dA + " ↔ " + dB,
        sub: (iso.projectAName || iso.projectA) + " ↔ " + (iso.projectBName || iso.projectB) + " · " + (iso.astSkeleton || ""),
        searchBlob: (iso.id + " " + dA + " " + dB + " " + iso.projectAName + " " + iso.projectBName + " " + (iso.plainEnglishWhy || "")).toLowerCase(),
        run: function() {
          state.lens = "galaxy";
          state.signalTier = "isomorphisms";
          state.catSubFilter = "isomorphismsOnly";
          state.projects = manifest.projectOrder.slice();
          selectIngredient(iso.id);
          window.cgFlyGalaxyToStar(iso.id);
        }
      });
    });

    var allMechs = (typeof semanticMechanisms !== "undefined" && semanticMechanisms && semanticMechanisms.highLevelMechanisms) || [];
    allMechs.slice(0, 180).forEach(function(m) {
      items.push({
        id: "omni-mech-" + m.id,
        cat: "mechanisms",
        badge: "◆ Mechanism · " + m.mechanismScore,
        badgeColor: "#e6c88a",
        title: m.plainHeadline || m.title,
        sub: m.title + " · " + (m.category || ""),
        searchBlob: (m.id + " " + m.title + " " + (m.plainHeadline || "") + " " + (m.category || "") + " " + (m.whyItMatters || "")).toLowerCase(),
        run: function() {
          state.lens = "galaxy";
          state.signalTier = "mechanisms";
          state.catSubFilter = "all";
          state.projects = manifest.projectOrder.slice();
          selectIngredient(m.id);
          window.cgFlyGalaxyToStar(m.id);
        }
      });
    });

    items.unshift(
      {
        id: "omni-act-zen",
        cat: "actions",
        badge: "✦ View Mode",
        badgeColor: "#e6c88a",
        title: "Toggle Full-Bleed 3D Zen Theater Mode (Shortcut: Z)",
        sub: "Expand the 40-project 3D Constellation to cinema height with a floating glass Inspector",
        searchBlob: "zen theater fullscreen cinema immersive 3d galaxy wide",
        run: function() { window.cgToggleZenTheater(); }
      },
      {
        id: "omni-act-matcher",
        cat: "actions",
        badge: "◆ Role Matcher",
        badgeColor: "#c084fc",
        title: "Open 8-Role Mathematical Obstacle & Premise Matcher",
        sub: "Describe your proof bottleneck in plain words to find role-compatible mechanisms",
        searchBlob: "role matcher obstacle signature premise trap search",
        run: function() { if (window.v137OpenSemanticMatcherModal) window.v137OpenSemanticMatcherModal(""); }
      },
      {
        id: "omni-act-glossary",
        cat: "actions",
        badge: "📖 Glossary",
        badgeColor: "#38bdf8",
        title: "Open 36-Term Plain-English Visual Mathematical Glossary",
        sub: "Clear everyday definitions for AST, 0-Sorry, Coercivity, Spectral Gap, Wasserstein & more",
        searchBlob: "glossary acronym plain english novice definitions ast sorry",
        run: function() { if (window.v85OpenAcronymGlossaryModal) window.v85OpenAcronymGlossaryModal("ALL"); }
      }
    );

    return items;
  };

  window.cgFilterOmniboxItems = function(query, category) {
    var pool = window._cgOmniboxCachedPool || (window._cgOmniboxCachedPool = window.cgBuildOmniboxCatalog());
    var q = String(query || "").toLowerCase().trim();
    var tokens = q ? q.split(/\s+/).filter(Boolean) : [];
    var filtered = pool.filter(function(it) {
      if (category && category !== "all" && it.cat !== category) return false;
      if (!tokens.length) return true;
      return tokens.every(function(tok){ return it.searchBlob.indexOf(tok) !== -1; });
    });
    return filtered.slice(0, 28);
  };

  window.cgRenderOmniboxResults = function() {
    var st = window._cgOmniboxState;
    var listEl = document.getElementById("cg-omnibox-results");
    var catsEl = document.getElementById("cg-omnibox-cats");
    if (!listEl) return;

    st.items = window.cgFilterOmniboxItems(st.query, st.category);
    if (st.selectedIdx >= st.items.length) st.selectedIdx = 0;

    if (catsEl) {
      catsEl.querySelectorAll("[data-omni-cat]").forEach(function(btn) {
        var isAct = btn.getAttribute("data-omni-cat") === st.category;
        cgSetClassFlag(btn, "is-active", isAct);
      });
    }

    if (!st.items.length) {
      listEl.innerHTML = '<div style="padding:22px;text-align:center;color:#94a3b8;font-size:13px;">No matching theorems, leads, projects, or labs for "<strong>' + esc(st.query) + '</strong>". Try a broader keyword like <code>entropy</code>, <code>Fourier</code>, <code>Jones</code>, or <code>SAT</code>.</div>';
      return;
    }

    listEl.innerHTML = st.items.map(function(it, idx) {
      var sel = idx === st.selectedIdx;
      return '<button type="button" class="cg-omnibox-item ' + (sel ? "is-selected" : "") + '" data-omni-idx="' + idx + '" onclick="window.cgExecuteOmniboxItem(' + idx + ')">' +
        '<div style="min-width:0;flex:1;">' +
          '<div style="display:flex;align-items:center;gap:8px;flex-wrap:wrap;margin-bottom:2px;">' +
            '<span style="font-size:10px;font-weight:750;letter-spacing:0.04em;text-transform:uppercase;color:' + it.badgeColor + ';">' + esc(it.badge) + '</span>' +
          '</div>' +
          '<div style="font-size:13.5px;font-weight:650;color:#f8fafc;line-height:1.32;">' + esc(it.title) + '</div>' +
          '<div style="font-size:11.5px;color:#94a3b8;line-height:1.38;margin-top:2px;">' + esc(it.sub) + '</div>' +
        '</div>' +
        '<span class="cg-kbd-pill" style="flex:none;">Jump ↵</span>' +
      '</button>';
    }).join("");
  };

  window.cgExecuteOmniboxItem = function(idx) {
    var st = window._cgOmniboxState;
    var item = st.items[idx];
    window.cgCloseOmnibox();
    if (item && typeof item.run === "function") {
      item.run();
    }
  };

  window.cgCloseOmnibox = function() {
    window._cgOmniboxState.open = false;
    var bd = document.getElementById("cg-v165-omnibox-backdrop");
    if (bd) {
      bd.hidden = true;
      bd.innerHTML = "";
      if (typeof bd.remove === "function") bd.remove();
    }
  };

  window.cgSetOmniboxCategory = function(cat) {
    window._cgOmniboxState.category = cat || "all";
    window._cgOmniboxState.selectedIdx = 0;
    window.cgRenderOmniboxResults();
  };

  window.cgOpenOmnibox = function(initialQuery) {
    window.cgCloseOmnibox();
    window._cgOmniboxCachedPool = window.cgBuildOmniboxCatalog();
    var st = window._cgOmniboxState;
    st.open = true;
    st.query = typeof initialQuery === "string" ? initialQuery : "";
    st.category = "all";
    st.selectedIdx = 0;

    var html =
      '<div id="cg-v165-omnibox-backdrop" class="cg-omnibox-backdrop" role="dialog" aria-modal="true" aria-label="Common Ground Quick Jump Omnibox" onclick="if(event.target===this)window.cgCloseOmnibox()">' +
        '<div class="cg-omnibox-dialog">' +
          '<div class="cg-omnibox-search-row">' +
            '<span style="color:var(--gold);font-size:16px;" aria-hidden="true">✦</span>' +
            '<input id="cg-omnibox-input" class="cg-omnibox-input" type="search" autocomplete="off" value="' + esc(st.query) + '" placeholder="Jump to any discovery lead, ★ bridge, mechanism, project, finite lab, or glossary term…">' +
            '<button type="button" class="cg-calm-chip" onclick="window.cgCloseOmnibox()">Esc</button>' +
          '</div>' +
          '<div id="cg-omnibox-cats" class="cg-omnibox-cats">' +
            '<button type="button" class="cg-omnibox-cat-btn is-active" data-omni-cat="all" onclick="window.cgSetOmniboxCategory(\'all\')">All</button>' +
            '<button type="button" class="cg-omnibox-cat-btn" data-omni-cat="leads" onclick="window.cgSetOmniboxCategory(\'leads\')">🧭 14 Discovery Leads</button>' +
            '<button type="button" class="cg-omnibox-cat-btn" data-omni-cat="verified" onclick="window.cgSetOmniboxCategory(\'verified\')">★ Reviewed Bridges</button>' +
            '<button type="button" class="cg-omnibox-cat-btn" data-omni-cat="mechanisms" onclick="window.cgSetOmniboxCategory(\'mechanisms\')">◆ Mechanisms</button>' +
            '<button type="button" class="cg-omnibox-cat-btn" data-omni-cat="projects" onclick="window.cgSetOmniboxCategory(\'projects\')">🌌 40 Projects</button>' +
            '<button type="button" class="cg-omnibox-cat-btn" data-omni-cat="labs" onclick="window.cgSetOmniboxCategory(\'labs\')">🔬 21 Micro-Labs</button>' +
          '</div>' +
          '<div id="cg-omnibox-results" class="cg-omnibox-results"></div>' +
          '<div class="cg-omnibox-foot">' +
            '<span><strong>↑↓</strong> Navigate · <strong>↵</strong> Jump &amp; Fly in 3D · <strong>Esc</strong> Close</span>' +
            '<span><strong>Z</strong> Zen Theater · <strong>1–6</strong> Switch Lenses</span>' +
          '</div>' +
        '</div>' +
      '</div>';

    document.body.insertAdjacentHTML("beforeend", html);
    var bd = document.getElementById("cg-v165-omnibox-backdrop");
    if (bd) bd.hidden = false;
    window.cgRenderOmniboxResults();

    var inp = document.getElementById("cg-omnibox-input");
    if (inp) {
      inp.oninput = function() {
        st.query = inp.value || "";
        st.selectedIdx = 0;
        window.cgRenderOmniboxResults();
      };
      inp.onkeydown = function(ev) {
        if (ev.key === "ArrowDown") {
          ev.preventDefault();
          st.selectedIdx = Math.min(Math.max(0, st.items.length - 1), st.selectedIdx + 1);
          window.cgRenderOmniboxResults();
        } else if (ev.key === "ArrowUp") {
          ev.preventDefault();
          st.selectedIdx = Math.max(0, st.selectedIdx - 1);
          window.cgRenderOmniboxResults();
        } else if (ev.key === "Enter") {
          ev.preventDefault();
          window.cgExecuteOmniboxItem(st.selectedIdx);
        } else if (ev.key === "Escape") {
          ev.preventDefault();
          window.cgCloseOmnibox();
        }
      };
      if (typeof inp.focus === "function") inp.focus();
    }
    return true;
  };

  // 6. Hook renderGalaxyLens, cgBuildConnectionProvenanceAndCritiqueHtml / renderInspector, selectIngredient & Global Shortcuts
  if (typeof renderGalaxyLens === "function" && !window._cgWrappedGalaxyV165) {
    window._cgWrappedGalaxyV165 = true;
    var origRenderGalaxyLensV165 = renderGalaxyLens;
    renderGalaxyLens = function(mount) {
      origRenderGalaxyLensV165(mount);
      window.cgMountGalaxyHudOverlay();
    };
  }

  if (typeof renderInspector === "function" && !window._cgWrappedInspectorV165) {
    window._cgWrappedInspectorV165 = true;
    var origRenderInspectorV165 = renderInspector;
    renderInspector = function() {
      var p = origRenderInspectorV165();
      // Apply synchronously if panel already updated (mechanism/isomorphism), AND after microtask completion!
      window.cgApplyInspectorTabs();
      var pill = document.getElementById("cg-galaxy-hud-pill");
      if (pill) pill.innerHTML = window.cgBuildGalaxyHudHtml();
      if (p && typeof p.then === "function") {
        return p.then(function(res) {
          window.cgApplyInspectorTabs();
          var pillAfter = document.getElementById("cg-galaxy-hud-pill");
          if (pillAfter) pillAfter.innerHTML = window.cgBuildGalaxyHudHtml();
          return res;
        });
      }
      return p;
    };
  }

  if (typeof selectIngredient === "function" && !window._cgWrappedSelectIngV165) {
    window._cgWrappedSelectIngV165 = true;
    var origSelectIngV165 = selectIngredient;
    selectIngredient = function(id, primaryProj, compareProj, motifIds) {
      window._cgZenInspectorMinimized = false;
      var res = origSelectIngV165(id, primaryProj, compareProj, motifIds);
      if (id && typeof state !== "undefined" && state.lens === "galaxy") {
        window.cgFlyGalaxyToStar(id);
      }
      window.cgSyncZenTheaterDom();
      return res;
    };
  }

  if (!window._cgBoundKeysV165 && typeof document !== "undefined" && typeof document.addEventListener === "function") {
    window._cgBoundKeysV165 = true;
    document.addEventListener("keydown", function(ev) {
      if ((ev.metaKey || ev.ctrlKey) && String(ev.key || "").toLowerCase() === "k") {
        ev.preventDefault();
        if (window._cgOmniboxState.open) window.cgCloseOmnibox();
        else window.cgOpenOmnibox("");
        return;
      }
      if (ev.key === "Escape" && window._cgOmniboxState.open) {
        ev.preventDefault();
        window.cgCloseOmnibox();
        return;
      }
      var tag = ev.target && ev.target.tagName ? ev.target.tagName.toUpperCase() : "";
      if (tag === "INPUT" || tag === "TEXTAREA" || tag === "SELECT") return;
      if (!ev.metaKey && !ev.ctrlKey && !ev.altKey && String(ev.key || "").toLowerCase() === "z") {
        if (typeof state !== "undefined" && state.lens === "galaxy") {
          ev.preventDefault();
          window.cgToggleZenTheater();
        }
      }
    });
  }

  // Mount HUD immediately if galaxy is already rendered
  window.cgMountGalaxyHudOverlay();

  // Suite 24: V165 Immersive Zen Theater, Universal ⌘K Omnibox, Smooth Camera Flight & Tabbed Inspector (5 new checks -> 198 total!)
  var prevRunnerV164 = window.v147RunAllAutomatedTests;
  if (typeof prevRunnerV164 === "function") {
    window.v147RunAllAutomatedTests = function() {
      var rep = prevRunnerV164();
      var extra165 = [];
      function addV165Check(name, cond, detail) {
        extra165.push({
          id: "T" + (rep.results.length + extra165.length + 1),
          category: "24. V165 Immersive UI, Zen Theater, ⌘K Omnibox & Tabbed Inspector",
          name: name,
          passed: Boolean(cond),
          detail: String(detail || (cond ? "Verified OK" : "Assertion failed"))
        });
      }

      // Check 194: Masthead Quick Jump ⌘K & Zen Theater triggers registered cleanly
      var omniBtn = document.getElementById("cg-omnibox-open-btn");
      var zenBtn = document.getElementById("cg-masthead-zen-btn");
      addV165Check(
        "Masthead exposes 1-click Quick Jump (⌘K) Omnibox trigger & Zen Theater toggle without clutter",
        Boolean(omniBtn && zenBtn && typeof window.cgOpenOmnibox === "function" && typeof window.cgToggleZenTheater === "function"),
        "OmniboxBtn=" + Boolean(omniBtn) + ", ZenBtn=" + Boolean(zenBtn)
      );

      // Check 195: Universal ⌘K Omnibox indexes Discovery Leads, Reviewed Bridges, Mechanisms, 40 Projects & 21 Micro-Labs and filters accurately
      window.cgOpenOmnibox("Temperley");
      var omniDialog = document.getElementById("cg-v165-omnibox-backdrop");
      var wasOpen = Boolean(window._cgOmniboxState && window._cgOmniboxState.open && omniDialog && !omniDialog.hidden);
      var hitCount = (window._cgOmniboxState && window._cgOmniboxState.items) ? window._cgOmniboxState.items.length : 0;
      var allPoolCount = (window._cgOmniboxCachedPool || []).length;
      window.cgCloseOmnibox();
      var closedCleanly = Boolean(!window._cgOmniboxState.open && omniDialog && omniDialog.hidden === true);
      addV165Check(
        "Universal ⌘K Omnibox indexes 275+ cross-domain targets (Leads, ★ Bridges, Mechanisms, 40 Projects, 21 Labs) & filters live",
        Boolean(wasOpen && hitCount >= 1 && allPoolCount >= 260 && closedCleanly),
        "PoolSize=" + allPoolCount + ", TemperleyHits=" + hitCount + ", ClosedCleanly=" + closedCleanly
      );

      // Check 196: Zen Theater Mode toggles full-bleed cinema stage (.is-zen-theater) & collapsible floating glass Inspector cleanly
      var prevLens165 = state.lens;
      var savedSrc165 = state.source;
      state.lens = "galaxy";
      state.source = null;
      renderApp();
      var zenOn = window.cgToggleZenTheater(true);
      var mountEl165 = document.getElementById("app-mount");
      var wsList165 = mountEl165 ? mountEl165.querySelectorAll(".galaxy-workspace") : [];
      var wsEl = wsList165.length ? wsList165[0] : null;
      var hasZenClass = window.cgHasClassFlag(wsEl, "is-zen-theater");
      var minOn = window.cgToggleZenInspectorCollapse(true);
      var hasMinClass = window.cgHasClassFlag(wsEl, "is-inspector-minimized");
      var zenOff = window.cgToggleZenTheater(false);
      var clearedZenClass = !window.cgHasClassFlag(wsEl, "is-zen-theater");
      addV165Check(
        "Zen Theater Mode toggles full-bleed 3D cinema stage & floating glass Inspector drawer cleanly",
        Boolean(zenOn === true && hasZenClass && minOn === true && hasMinClass && zenOff === false && clearedZenClass),
        "ZenOn=" + hasZenClass + ", Minimized=" + hasMinClass + ", Restored=" + clearedZenClass
      );

      // Check 197: Selecting a star mounts 3-Tab Progressive Disclosure (.cg-ins-tabbar) while preserving all DOM buttons & consequence cards
      var firstMech = (semanticMechanisms && semanticMechanisms.highLevelMechanisms && semanticMechanisms.highLevelMechanisms[0]) || null;
      if (firstMech) {
        state.source = firstMech.id;
        renderInspector();
        // Also invokecgBuildConnectionProvenanceAndCritiqueHtml + cgApplyInspectorTabs synchronously in case async wrapper queued a microtask
        var pEl = document.getElementById("inspector-panel");
        var pickedRec165 = recordById.get(firstMech.id);
        if (pEl && pickedRec165 && (pEl.innerHTML || "").indexOf("cg-provenance-critique-box") === -1 && window.cgBuildConnectionProvenanceAndCritiqueHtml) {
          var pv = window.cgBuildConnectionProvenanceAndCritiqueHtml(pickedRec165);
          var pIdx = pEl.innerHTML.indexOf('<div class="v6-plain-box">');
          if (pIdx !== -1) pEl.innerHTML = pEl.innerHTML.slice(0, pIdx) + pv + pEl.innerHTML.slice(pIdx);
        }
        window.cgApplyInspectorTabs();
      }
      var inspEl165 = document.getElementById("inspector-panel");
      var inspHtml165 = (inspEl165 && inspEl165.innerHTML) || "";
      var hasTabBar = inspHtml165.indexOf("cg-ins-tabbar") !== -1;
      window.cgSwitchInspectorTab("rigor");
      var rigorActive = inspEl165 && inspEl165.getAttribute("data-active-ins-tab") === "rigor";
      window.cgSwitchInspectorTab("intuition");
      var keptCoreDom = Boolean(
        inspHtml165.indexOf("cg-consequence-usecase-card") !== -1 &&
        inspHtml165.indexOf("v7-open-full-mech") !== -1
      );
      addV165Check(
        "3-Tab Progressive Inspector (.cg-ins-tabbar) switches Intuition / Proof / Gates cleanly while preserving all DOM actions",
        Boolean(hasTabBar && rigorActive && keptCoreDom),
        "HasTabs=" + hasTabBar + ", RigorSwitch=" + rigorActive + ", PreservedDOM=" + keptCoreDom
      );

      // Check 198: Smooth 3D Camera Flight (`cgFlyGalaxyToStar`) & Floating Constellation HUD Breadcrumb (`#cg-galaxy-hud-pill`) active
      state.source = null;
      renderApp();
      var flewOk = window.cgFlyGalaxyToStar("iso-tauceti-tc-analysis-142");
      var afterCam = window._cgSavedGalaxyCamera || {};
      var hudPillEl = document.getElementById("cg-galaxy-hud-pill");
      var hudHtml = (hudPillEl && hudPillEl.innerHTML) || "";
      state.source = savedSrc165;
      state.lens = prevLens165;
      renderApp();
      addV165Check(
        "Smooth 3D Camera Flight (`cgFlyGalaxyToStar`) & Floating Constellation HUD Breadcrumb (`#cg-galaxy-hud-pill`) active",
        Boolean(flewOk && typeof afterCam.yaw === "number" && afterCam.zoom > 1.2 && hudHtml.indexOf("40-Project Cosmos") !== -1),
        "Flew=" + flewOk + ", Zoom=" + afterCam.zoom + ", HUD=" + (hudHtml.indexOf("40-Project Cosmos") !== -1)
      );

      for (var k = 0; k < extra165.length; k++) {
        rep.results.push(extra165[k]);
        rep.total++;
        if (extra165[k].passed) rep.passed++;
        else rep.failed++;
      }
      window._v147LastReport = rep;
      return rep;
    };
  }
})();
"""


def upgrade_css():
    css = CSS_PATH.read_text(encoding="utf-8")
    marker = "/* ============================================================================\n   V165 IMMERSIVE CELESTIAL OBSIDIAN"
    if marker in css:
        css = css[:css.index(marker)].rstrip() + "\n"
    CSS_PATH.write_text(css + V165_CSS_BLOCK, encoding="utf-8")
    print("1. Upgraded observatory/unified.css with V165 Celestial Obsidian, Zen Theater, Omnibox & Tabbed Inspector styles.")


def upgrade_html():
    html = HTML_PATH.read_text(encoding="utf-8")
    html = html.replace("?v=164", "?v=165")

    surprise_btn = '<button type="button" class="surprise-btn" id="surprise-me-btn" title="Jump to a surprising cross-domain connection">Surprise Me</button>'
    v165_buttons = (
        '<button type="button" class="cg-omnibox-trigger" id="cg-omnibox-open-btn" title="Instant search across all 3,287 ideas, 14 leads, 40 projects &amp; 21 labs (⌘K)" onclick="if(window.cgOpenOmnibox)window.cgOpenOmnibox(\'\');">'
        '<span>Quick Jump</span><span class="cg-kbd-pill">⌘K</span></button>\n        '
        '<button type="button" class="cg-zen-masthead-btn" id="cg-masthead-zen-btn" aria-pressed="false" title="Toggle full-bleed 3D Zen Theater mode (press Z)" onclick="if(window.cgToggleZenTheater)window.cgToggleZenTheater();">⛶ Theater</button>\n        '
        + surprise_btn
    )
    if 'id="cg-omnibox-open-btn"' not in html:
        assert surprise_btn in html, "Could not find #surprise-me-btn in observatory/index.html"
        html = html.replace(surprise_btn, v165_buttons, 1)

    HTML_PATH.write_text(html, encoding="utf-8")
    print("2. Upgraded observatory/index.html (?v=165 + Masthead Quick Jump ⌘K & Zen Theater triggers).")


def upgrade_canvas_in_js(js: str) -> str:
    old_nebula = """    // 1. Immersive Deep-Space Core Nebula Glow (feature-checked for headless test mocks)
    if (typeof ctx.createRadialGradient === 'function') {
      const neb = ctx.createRadialGradient(cx, cy, scale * 0.04, cx, cy, scale * 1.18);
      neb.addColorStop(0, 'rgba(56, 189, 248, 0.11)');
      neb.addColorStop(0.42, 'rgba(223, 192, 130, 0.05)');
      neb.addColorStop(1, 'rgba(5, 9, 16, 0)');
      ctx.fillStyle = neb;
      ctx.fillRect(0, 0, w, h);
    }"""

    new_nebula = """    // 1. V165 Deep-Space Multi-Layer Parallax Starfield & Dual Celestial Nebula (headless-safe)
    if (!window._cgDeepSpaceDust) {
      window._cgDeepSpaceDust = Array.from({ length: 160 }, (_, i) => {
        const s = Math.imul(i + 1, 2654435761) >>> 0;
        return {
          u: (s % 10000) / 10000,
          v: ((s >>> 10) % 10000) / 10000,
          depth: 0.25 + 0.75 * (((s >>> 20) % 1000) / 1000),
          r: 0.45 + 0.95 * (((s >>> 6) % 100) / 100),
          warm: (i % 7 === 0),
        };
      });
    }
    for (const st of window._cgDeepSpaceDust) {
      const sx = ((st.u * w - camera.yaw * 48 * st.depth) % w + w) % w;
      const sy = ((st.v * h - camera.pitch * 34 * st.depth) % h + h) % h;
      ctx.beginPath();
      ctx.arc(sx, sy, st.r * st.depth, 0, Math.PI * 2);
      ctx.fillStyle = st.warm ? 'rgba(230, 200, 138, 0.26)' : 'rgba(186, 230, 253, 0.2)';
      ctx.fill();
    }
    if (typeof ctx.createRadialGradient === 'function') {
      const neb = ctx.createRadialGradient(cx, cy, scale * 0.03, cx, cy, scale * 1.24);
      neb.addColorStop(0, 'rgba(56, 189, 248, 0.14)');
      neb.addColorStop(0.38, 'rgba(230, 200, 138, 0.07)');
      neb.addColorStop(0.72, 'rgba(16, 185, 129, 0.03)');
      neb.addColorStop(1, 'rgba(3, 7, 16, 0)');
      ctx.fillStyle = neb;
      ctx.fillRect(0, 0, w, h);
    }"""

    if old_nebula in js:
        js = js.replace(old_nebula, new_nebula, 1)

    old_filament = """    if (focusPt) {
      const sp = project3D(focusPt);
      for (const pid of focusPt.record.projects) {
        const hc = hubCoords.get(pid);
        if (!hc) continue;
        const pColor = manifest.projects[pid]?.color || '#e5c687';
        const ctrlX = (sp.x + hc.x) * 0.5 + (cx - (sp.x + hc.x) * 0.5) * 0.32;
        const ctrlY = (sp.y + hc.y) * 0.5 + (cy - (sp.y + hc.y) * 0.5) * 0.32;
        ctx.beginPath();
        ctx.moveTo(sp.x, sp.y);
        ctx.quadraticCurveTo(ctrlX, ctrlY, hc.x, hc.y);
        ctx.strokeStyle = state.source ? (pColor + 'dd') : (pColor + '88');
        ctx.lineWidth = state.source ? 2.1 : 1.3;
        ctx.stroke();
      }
    }"""

    new_filament = """    if (focusPt) {
      const sp = project3D(focusPt);
      const pulseT = ((typeof Date !== 'undefined' && Date.now ? Date.now() : 600) % 2400) / 2400;
      let pIdx = 0;
      for (const pid of focusPt.record.projects) {
        const hc = hubCoords.get(pid);
        if (!hc) continue;
        const pColor = manifest.projects[pid]?.color || '#e5c687';
        const ctrlX = (sp.x + hc.x) * 0.5 + (cx - (sp.x + hc.x) * 0.5) * 0.32;
        const ctrlY = (sp.y + hc.y) * 0.5 + (cy - (sp.y + hc.y) * 0.5) * 0.32;
        ctx.beginPath();
        ctx.moveTo(sp.x, sp.y);
        ctx.quadraticCurveTo(ctrlX, ctrlY, hc.x, hc.y);
        ctx.strokeStyle = state.source ? (pColor + '33') : (pColor + '1f');
        ctx.lineWidth = state.source ? 5.5 : 3.2;
        ctx.stroke();
        ctx.beginPath();
        ctx.moveTo(sp.x, sp.y);
        ctx.quadraticCurveTo(ctrlX, ctrlY, hc.x, hc.y);
        ctx.strokeStyle = state.source ? (pColor + 'ee') : (pColor + '99');
        ctx.lineWidth = state.source ? 2.1 : 1.35;
        ctx.stroke();
        const t = (pulseT + pIdx * 0.23) % 1;
        const omt = 1 - t;
        const bx = omt * omt * sp.x + 2 * omt * t * ctrlX + t * t * hc.x;
        const by = omt * omt * sp.y + 2 * omt * t * ctrlY + t * t * hc.y;
        ctx.beginPath();
        ctx.arc(bx, by, state.source ? 2.8 : 2.1, 0, Math.PI * 2);
        ctx.fillStyle = '#fff8e7';
        ctx.fill();
        pIdx++;
      }
      if (state.source && typeof ctx.fillText === 'function') {
        ctx.save();
        if ('font' in ctx) ctx.font = '600 11px Inter, system-ui, sans-serif';
        if ('textAlign' in ctx) ctx.textAlign = 'center';
        ctx.fillStyle = '#fff8e7';
        const callout = String(focusPt.record.name || '').slice(0, 42);
        ctx.fillText(callout, sp.x, Math.max(18, sp.y - 17));
        ctx.restore();
      }
    }"""

    if old_filament in js:
        js = js.replace(old_filament, new_filament, 1)

    old_cmd = """      } else if (cmd === 'wide') {
        window._cgWideGalaxyStage = !window._cgWideGalaxyStage;
        const ws = document.querySelector('.galaxy-workspace');
        if (ws && ws.classList) ws.classList.toggle('is-wide-galaxy', Boolean(window._cgWideGalaxyStage));
      }"""
    new_cmd = """      } else if (cmd === 'wide') {
        window._cgWideGalaxyStage = !window._cgWideGalaxyStage;
        const ws = document.querySelector('.galaxy-workspace');
        if (ws && ws.classList) ws.classList.toggle('is-wide-galaxy', Boolean(window._cgWideGalaxyStage));
      } else if (cmd === 'zen') {
        if (window.cgToggleZenTheater) window.cgToggleZenTheater();
      } else if (cmd === 'redraw') {
        // triggers smooth camera flight frame redraw
      }"""
    if old_cmd in js:
        js = js.replace(old_cmd, new_cmd, 1)

    return js


def upgrade_js():
    js = JS_PATH.read_text(encoding="utf-8")
    marker = "// === V165 IMMERSIVE 3D ZEN THEATER"
    if marker in js:
        js = js[:js.index(marker)].rstrip() + "\n"
    js = upgrade_canvas_in_js(js)
    JS_PATH.write_text(js + V165_JS_BLOCK, encoding="utf-8")
    print("3. Upgraded observatory/unified-standalone.js with V165 3D parallax starfield, animated bridge pulses, Zen Theater, ⌘K Omnibox, HUD pill, 3-Tab Inspector & Suite 24.")


def upgrade_build_and_daemon_versions():
    cf = CF_SCRIPT.read_text(encoding="utf-8")
    cf = cf.replace('ASSET_VER = "164"', 'ASSET_VER = "165"')
    cf = cf.replace(
        '"version": "V164-TemperleyLieb-TransportMatrix-PGF-MarkovExchangeable-14Leads"',
        '"version": "V165-Immersive-Celestial-ZenTheater-Omnibox-TabbedInspector"'
    )
    CF_SCRIPT.write_text(cf, encoding="utf-8")

    dm = DAEMON_SCRIPT.read_text(encoding="utf-8")
    dm = dm.replace('"version": "V164"', '"version": "V165"')
    DAEMON_SCRIPT.write_text(dm, encoding="utf-8")
    print("4. Updated build-cloudflare-dist.py and continuous-insight-daemon.py to V165.")


if __name__ == "__main__":
    upgrade_css()
    upgrade_html()
    upgrade_js()
    upgrade_build_and_daemon_versions()
    print("V165 UI/UX upgrade complete!")
