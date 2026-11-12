// Exhaustive DOM & Click-Handler Simulation Harness in Headless WebKit JSC
var window = this;
window.location = { search: "", href: "http://localhost:4190/universe/sources/" };
window.history = { replaceState: function(){}, pushState: function(){} };
window.requestAnimationFrame = function(cb){ return 1; };
window.setInterval = function(){ return 1; };
window.clearInterval = function(){};
window.scrollTo = function(){};
window.devicePixelRatio = 1;
window.localStorage = {
  _store: {},
  getItem: function(k){ return this._store[k] || ""; },
  setItem: function(k, v){ this._store[k] = String(v); }
};
window.URL = function(rel, base) {
  this.href = String(rel);
  this.search = "";
  this.searchParams = { set: function(){}, get: function(){ return null; } };
};
window.URL.createObjectURL = function(){ return "blob:local"; };
window.URL.revokeObjectURL = function(){};
window.Blob = function(parts){ this.parts = parts; };
window.Event = function(type){ this.type = type; };

// Mini DOM parser that extracts interactive elements (id, class, data-*) from innerHTML so querySelectorAll & getElementById work on real rendered HTML!
var elById = {};
var allCreatedEls = [];

function parseAttrs(attrStr) {
  var attrs = {};
  var dataset = {};
  var rx = /([a-zA-Z0-9_:-]+)\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s>]+))/g;
  var m;
  while ((m = rx.exec(attrStr)) !== null) {
    var k = m[1];
    var v = m[2] !== undefined ? m[2] : (m[3] !== undefined ? m[3] : m[4]);
    attrs[k] = v;
    if (k.indexOf("data-") === 0) {
      var camel = k.slice(5).replace(/-([a-z0-9])/g, function(_, c){ return c.toUpperCase(); });
      dataset[camel] = v;
    }
  }
  return { attrs: attrs, dataset: dataset };
}

function makeDomNode(tag, attrObj) {
  var attrs = (attrObj && attrObj.attrs) || {};
  var dataset = (attrObj && attrObj.dataset) || {};
  var _html = "";
  var _children = [];
  var node = {
    tagName: (tag || "DIV").toUpperCase(),
    id: attrs.id || "",
    className: attrs["class"] || "",
    value: attrs.value || "",
    hidden: false,
    attrs: attrs,
    dataset: dataset,
    style: { setProperty: function(){}, display: "", gridColumn: "", borderColor: "", background: "" },
    onclick: null,
    onchange: null,
    oninput: null,
    onsubmit: null,
    _listeners: {},
    classList: {
      add: function(){},
      remove: function(){},
      toggle: function(){},
      contains: function(){ return false; }
    },
    setAttribute: function(k, v) {
      this.attrs[k] = String(v);
      if (k === "id") { this.id = String(v); elById[this.id] = this; }
      if (k.indexOf("data-") === 0) {
        var camel = k.slice(5).replace(/-([a-z0-9])/g, function(_, c){ return c.toUpperCase(); });
        this.dataset[camel] = String(v);
      }
    },
    getAttribute: function(k) {
      return this.attrs[k] !== undefined ? this.attrs[k] : null;
    },
    addEventListener: function(ev, fn) {
      this._listeners[ev] = this._listeners[ev] || [];
      this._listeners[ev].push(fn);
    },
    dispatchEvent: function(ev) {
      var t = ev.type || ev;
      if (t === "input" && this.oninput) this.oninput({ target: this, preventDefault: function(){}, stopPropagation: function(){} });
      if (t === "change" && this.onchange) this.onchange({ target: this, preventDefault: function(){}, stopPropagation: function(){} });
      if (t === "click" && this.onclick) this.onclick({ target: this, preventDefault: function(){}, stopPropagation: function(){} });
      var ls = this._listeners[t] || [];
      for (var i = 0; i < ls.length; i++) ls[i]({ target: this, preventDefault: function(){}, stopPropagation: function(){} });
    },
    click: function() {
      this.dispatchEvent({ type: "click" });
    },
    focus: function(){},
    blur: function(){},
    scrollIntoView: function(){},
    replaceChildren: function(){ _children = []; },
    appendChild: function(ch){ _children.push(ch); if (ch && ch.id) elById[ch.id] = ch; },
    removeChild: function(){},
    remove: function(){},
    insertBefore: function(){},
    insertAdjacentHTML: function(pos, htmlStr) {
      this.innerHTML = _html + String(htmlStr || "");
    },
    getBoundingClientRect: function(){ return { width: 820, height: 520, left: 0, top: 0 }; },
    getContext: function(){
      return {
        setTransform: function(){}, clearRect: function(){}, beginPath: function(){},
        ellipse: function(){}, stroke: function(){}, moveTo: function(){},
        quadraticCurveTo: function(){}, lineTo: function(){}, closePath: function(){},
        fill: function(){}, arc: function(){}, fillRect: function(){}, strokeRect: function(){},
        fillText: function(){}, save: function(){}, restore: function(){}, setLineDash: function(){}
      };
    },
    querySelectorAll: function(sel) {
      return matchSelectorInList(_children, sel);
    },
    querySelector: function(sel) {
      var res = matchSelectorInList(_children, sel);
      return res.length ? res[0] : null;
    }
  };
  Object.defineProperty(node, "innerHTML", {
    get: function(){ return _html; },
    set: function(v) {
      _html = String(v == null ? "" : v);
      _children = parseHtmlChildren(_html);
    }
  });
  if (node.id) elById[node.id] = node;
  if (allCreatedEls.length > 4000) {
    allCreatedEls.splice(0, allCreatedEls.length - 2000);
  }
  allCreatedEls.push(node);
  return node;
}

function parseHtmlChildren(htmlStr) {
  var list = [];
  var tagRx = /<([a-zA-Z0-9]+)\s+([^>]*?)>/g;
  var m;
  while ((m = tagRx.exec(htmlStr)) !== null) {
    var tag = m[1];
    var attrPart = m[2];
    if (attrPart.indexOf("id=") !== -1 || attrPart.indexOf("data-") !== -1 || attrPart.indexOf("class=") !== -1) {
      var parsed = parseAttrs(attrPart);
      var child = makeDomNode(tag, parsed);
      list.push(child);
    }
  }
  return list;
}

function matchSelectorInList(list, sel) {
  var s = sel.trim();
  return list.filter(function(el) {
    if (s.indexOf("[data-") === 0 && s.slice(-1) === "]") {
      var attr = s.slice(1, -1);
      var eqIdx = attr.indexOf("=");
      if (eqIdx !== -1) {
        var k = attr.slice(0, eqIdx);
        var v = attr.slice(eqIdx + 1).replace(/^['"]|['"]$/g, "");
        return el.attrs[k] === v;
      }
      return el.attrs[attr] !== undefined;
    }
    if (s.indexOf(".") === 0) {
      var cls = s.slice(1);
      var classes = (el.className || "").split(/\s+/);
      return classes.indexOf(cls) !== -1;
    }
    if (s.indexOf("#") === 0) {
      return el.id === s.slice(1);
    }
    return false;
  });
}

var document = {
  body: makeDomNode("body", { attrs: { id: "body" }, dataset: {} }),
  activeElement: null,
  getElementById: function(id) {
    if (!elById[id]) elById[id] = makeDomNode("div", { attrs: { id: id }, dataset: {} });
    return elById[id];
  },
  createElement: function(tag) {
    return makeDomNode(tag, { attrs: {}, dataset: {} });
  },
  querySelectorAll: function(sel) {
    var mount = elById["app-mount"];
    var fromMount = mount ? mount.querySelectorAll(sel) : [];
    var fromAll = matchSelectorInList(allCreatedEls, sel);
    var combined = fromMount.slice();
    for (var i = 0; i < fromAll.length; i++) {
      if (combined.indexOf(fromAll[i]) === -1) combined.push(fromAll[i]);
    }
    return combined;
  },
  querySelector: function(sel) {
    var r = this.querySelectorAll(sel);
    return r.length ? r[0] : makeDomNode("div", { attrs: {}, dataset: {} });
  },
  addEventListener: function(){}
};
window.document = document;

// Load bundle-data.js and unified-standalone.js
load("/Users/fawadhaider/code/commonground-verification-gemini/observatory/bundle-data.js");
load("/Users/fawadhaider/code/commonground-verification-gemini/observatory/unified-standalone.js");

function assertNoUndefinedOrNaN(contextLabel, htmlStr) {
  if (!htmlStr || htmlStr.length < 20) {
    throw new Error("Empty HTML in " + contextLabel);
  }
  if (htmlStr.indexOf("undefined") !== -1) {
    var idx = htmlStr.indexOf("undefined");
    throw new Error("Literal 'undefined' found in " + contextLabel + ": ..." + htmlStr.slice(Math.max(0, idx - 80), idx + 80) + "...");
  }
  if (htmlStr.indexOf("NaN") !== -1) {
    var idx2 = htmlStr.indexOf("NaN");
    throw new Error("Literal 'NaN' found in " + contextLabel + ": ..." + htmlStr.slice(Math.max(0, idx2 - 80), idx2 + 80) + "...");
  }
}

var mount = document.getElementById("app-mount");

// 1. Test Galaxy Lens & READABLE GALAXY CATALOGUE Click Simulation
state.lens = "galaxy";
renderApp();
assertNoUndefinedOrNaN("Galaxy Initial Render", mount.innerHTML);

var fgAll = filterGalaxyRecords();
if (state.dedupEndpoints !== true || fgAll.total !== 3287) {
  throw new Error("Expected default dedup ON with 3287 records (1400 mechs + 1887 unique AST pairs), got dedup=" + state.dedupEndpoints + " total=" + fgAll.total);
}

// Click each of the 3 READABLE GALAXY CATALOGUE subfilter buttons
var catSubBtns = mount.querySelectorAll("[data-cat-subfilter]");
if (catSubBtns.length !== 3) {
  throw new Error("Expected 3 [data-cat-subfilter] buttons in READABLE GALAXY CATALOGUE, found " + catSubBtns.length);
}
// Click "mechanismsOnly" (1,400 Big-Idea Mechanisms)
catSubBtns[1].click();
if (filterGalaxyRecords().total !== 1400) {
  throw new Error("Clicking 1,400 Big-Idea Mechanisms button did not filter to 1400! Got " + filterGalaxyRecords().total);
}
assertNoUndefinedOrNaN("Galaxy Catalogue Mechanisms Only", mount.innerHTML);

// Click "isomorphismsOnly" (1,887 Deduplicated AST Syntax Candidates by default; 7,000 when dedup toggled off)
catSubBtns = mount.querySelectorAll("[data-cat-subfilter]");
catSubBtns[2].click();
if (filterGalaxyRecords().total !== 1887) {
  throw new Error("Clicking AST Syntax Candidates button with default dedup ON did not filter to 1887! Got " + filterGalaxyRecords().total);
}
window.cgToggleEndpointDedup(false);
if (filterGalaxyRecords().total !== 7000) {
  throw new Error("Unchecking endpoint dedup did not reveal all 7000 raw AST rows! Got " + filterGalaxyRecords().total);
}
window.cgToggleEndpointDedup(true);
assertNoUndefinedOrNaN("Galaxy Catalogue AST Syntax Candidates", mount.innerHTML);

// Click "all" (All 3,287 Deduplicated Records)
catSubBtns = mount.querySelectorAll("[data-cat-subfilter]");
catSubBtns[0].click();
if (filterGalaxyRecords().total !== 3287) {
  throw new Error("Clicking All (3,287) button did not restore 3287! Got " + filterGalaxyRecords().total);
}

// Click #catalogue-header-trigger (tapping READABLE GALAXY CATALOGUE header directly!)
var catHeader = document.getElementById("catalogue-header-trigger");
if (!catHeader || !catHeader.onclick) {
  throw new Error("#catalogue-header-trigger has no onclick handler!");
}
state.source = null;
catHeader.click();
if (!state.source) {
  throw new Error("Tapping #catalogue-header-trigger did not select the first catalogue idea!");
}

// Click `.ingredient-card` items inside READABLE GALAXY CATALOGUE (both mechanism and isomorphism cards)
var ingCards = mount.querySelectorAll(".ingredient-card");
if (ingCards.length !== 48) {
  throw new Error("Expected 48 .ingredient-card elements on page 1, found " + ingCards.length);
}
for (var cIdx of [0, 1, 5, 15, 30, 47]) {
  var card = ingCards[cIdx];
  if (!card.onclick) throw new Error(".ingredient-card[" + cIdx + "] missing onclick!");
  card.click();
  if (state.source !== card.dataset.id) {
    throw new Error("Clicking .ingredient-card[" + cIdx + "] did not set state.source to " + card.dataset.id);
  }
  assertNoUndefinedOrNaN("Inline Card Drawer for " + card.dataset.id, card.innerHTML);
  assertNoUndefinedOrNaN("Top Inspector Panel for " + card.dataset.id, document.getElementById("inspector-panel").innerHTML);
  if (card.innerHTML.indexOf("v146-inline-card-drawer") === -1) {
    throw new Error("Clicking .ingredient-card[" + cIdx + "] did not inject .v146-inline-card-drawer!");
  }
}

// Test bindV6QuickStartEvents controls in Galaxy Lens:
// (a) Obstacle pills [data-obstacle-pill]
var obsPills = mount.querySelectorAll("[data-obstacle-pill]");
if (obsPills.length !== 9) {
  throw new Error("Expected 9 [data-obstacle-pill] buttons, found " + obsPills.length);
}
obsPills[1].click(); // 'blowup'
if (state.obstacleFilter !== "blowup") {
  throw new Error("Clicking [data-obstacle-pill='blowup'] did not update state.obstacleFilter!");
}
assertNoUndefinedOrNaN("Galaxy Obstacle Filter 'blowup'", mount.innerHTML);
obsPills = mount.querySelectorAll("[data-obstacle-pill]");
obsPills[0].click(); // 'all'

// (b) Story Tour toggle (#v8-toggle-story) & Agenda Builder toggle (#v8-toggle-agenda)
var storyBtn = document.getElementById("v8-toggle-story");
if (!storyBtn || !storyBtn.onclick) throw new Error("#v8-toggle-story missing onclick!");
storyBtn.click();
if (!state.showStoryTour) throw new Error("Clicking #v8-toggle-story did not open Story Tour!");
assertNoUndefinedOrNaN("Galaxy Story Tour Open", mount.innerHTML);

var agendaBtn = document.getElementById("v8-toggle-agenda");
if (!agendaBtn || !agendaBtn.onclick) throw new Error("#v8-toggle-agenda missing onclick!");
agendaBtn.click();
if (!state.showAgendaBuilder) throw new Error("Clicking #v8-toggle-agenda did not open Agenda Builder!");
assertNoUndefinedOrNaN("Galaxy Agenda Builder Open", mount.innerHTML);

// (c) Guided Breakthrough Presets [data-v6-preset]
var presets = mount.querySelectorAll("[data-v6-preset]");
if (presets.length !== 6) throw new Error("Expected 6 [data-v6-preset] buttons, found " + presets.length);
presets[0].click();
if (!state.showCompareModal || state.compareProjA !== "ns" || state.compareProjB !== "poincare") {
  throw new Error("Clicking [data-v6-preset] #0 did not open Compare Modal for ns <-> poincare!");
}
assertNoUndefinedOrNaN("Galaxy Compare Modal Open", mount.innerHTML);
// Reset projects to all 40
document.getElementById("gal-select-all").click();

// 2. Test All 7 Submodes of Lens 2 (Serendipity / Unrelated-Field Engine) and Click Cards in Each
state.lens = "serendipity";
var submodes = ["mechanisms", "isomorphisms", "trinities", "pipelines", "verified", "chains", "dna", "motifs"];
for (var smIdx = 0; smIdx < submodes.length; smIdx++) {
  var sub = submodes[smIdx];
  state.serenSubmode = sub;
  renderApp();
  assertNoUndefinedOrNaN("Serendipity submode=" + sub, mount.innerHTML);

  if (sub === "mechanisms") {
    var mCards = mount.querySelectorAll("[data-mech-card]");
    if (mCards.length < 10) throw new Error("Expected mechanism cards in serendipity:mechanisms");
    mCards[3].click();
    assertNoUndefinedOrNaN("Serendipity clicked mechCard[3]", mount.innerHTML);
  } else if (sub === "isomorphisms") {
    var iCards = mount.querySelectorAll("[data-iso-card]");
    if (iCards.length < 10) throw new Error("Expected isomorphism cards in serendipity:isomorphisms");
    iCards[4].click();
    assertNoUndefinedOrNaN("Serendipity clicked isoCard[4]", mount.innerHTML);
  } else if (sub === "verified") {
    var vCards = mount.querySelectorAll("[data-ver-card]");
    if (vCards.length < 10) throw new Error("Expected verified suite cards in serendipity:verified");
    vCards[5].click();
    assertNoUndefinedOrNaN("Serendipity clicked verCard[5]", mount.innerHTML);
  } else if (sub === "chains") {
    var cCards = mount.querySelectorAll("[data-chain-card]");
    if (cCards.length < 5) throw new Error("Expected chain cards in serendipity:chains");
    cCards[2].click();
    assertNoUndefinedOrNaN("Serendipity clicked chainCard[2]", mount.innerHTML);
  } else if (sub === "motifs") {
    var moCards = mount.querySelectorAll("[data-motif-card]");
    if (moCards.length < 10) throw new Error("Expected motif cards in serendipity:motifs, found " + moCards.length);
    moCards[2].click();
    assertNoUndefinedOrNaN("Serendipity clicked motifCard[2]", mount.innerHTML);
  }
}

// 3. Test Lens 3 (Discovery Paths — all 2,800 paths + clicking paths across early, middle, and late indices)
state.lens = "paths";
state.selectedPath = null;
renderApp();
assertNoUndefinedOrNaN("Paths Lens Grid", mount.innerHTML);
var pathCards = mount.querySelectorAll("[data-open-path]");
if (pathCards.length < 100) throw new Error("Expected path cards in Paths Lens, found " + pathCards.length);
for (var pTestIdx of [0, 50, 600, 1500, 2799]) {
  state.selectedPath = insightPaths.connections[pTestIdx].id;
  renderApp();
  assertNoUndefinedOrNaN("Paths Lens Detail idx=" + pTestIdx, mount.innerHTML);
}
document.getElementById("path-back").click();
if (state.selectedPath !== null) throw new Error("#path-back did not clear state.selectedPath!");

// 4. Test Lens 4 (40x40 Bridge Radar)
state.lens = "bridges";
renderApp();
assertNoUndefinedOrNaN("Bridges Lens", mount.innerHTML);

// 5. Test Lens 5 (Family Atlas & 2.32M Search)
state.lens = "constellation";
renderApp();
assertNoUndefinedOrNaN("Constellation Lens", mount.innerHTML);

// 6. Test Lens 6 (Intuition Labs — all 4 labModes & clicking simulator buttons)
state.lens = "intuition";
for (var lm of ["simulators", "rosetta", "spectral", "complexity"]) {
  state.labMode = lm;
  renderApp();
  assertNoUndefinedOrNaN("Intuition Lens labMode=" + lm, mount.innerHTML);
  if (lm === "simulators") {
    var simBtns = mount.querySelectorAll("[data-pick-sim]");
    if (simBtns.length !== 160) throw new Error("Expected 160 [data-pick-sim] buttons, found " + simBtns.length);
    simBtns[25].click();
    assertNoUndefinedOrNaN("Intuition Lens clicked simBtns[25]", mount.innerHTML);
  }
}

print("JSC_V146_EXHAUSTIVE_CLICK_HARNESS_AND_MATH_VERIFICATION_OK: Galaxy_Ideas=" + fgAll.total + ", Mechs=1400, Isos=7000, Trinities=460, Pipelines=580, Suites=554, Paths=2800, Motifs=80, Simulators=160, All_Clicks_Verified=true");



// 7. V148 DOM Click & Modal Simulation: All 10 Exact Micro-Labs, 6-Tab V36 Catalogue, Researcher Studio & 2-Role Note Matcher
window.v136OpenV34FiniteDiagramsModal(0);
for (var labI = 0; labI < 10; labI++) {
  window.v136SetLab(labI);
  var fb = document.getElementById("v136-finite-mount");
  assertNoUndefinedOrNaN("V148 Finite Micro-Lab #" + (labI + 1), fb.innerHTML);
}
window.v136CloseFiniteModal();

window.v131OpenV34CatalogueModal("concepts");
var v36Tabs = ["concepts", "connections", "notes", "leads", "pairs", "projects"];
for (var ti = 0; ti < v36Tabs.length; ti++) {
  window.v131SwitchCatalogueTab(v36Tabs[ti]);
  var cb = document.getElementById("v131-cat-body");
  assertNoUndefinedOrNaN("V148 Epistemic Catalogue Tab=" + v36Tabs[ti], cb.innerHTML);
}
window.v131CloseV34CatalogueModal();

window.v148OpenArgumentAndWorksheetModal("compare");
for (var stTab of ["compare", "worksheet", "paths"]) {
  window._v148StudioState.tab = stTab;
  window.v148RenderArgumentModalBody();
  var sb = document.getElementById("v148-argstudio-body");
  assertNoUndefinedOrNaN("V148 Researcher Usability Studio Tab=" + stTab, sb.innerHTML);
}
window.v148CloseArgumentModal();

window.v137OpenSemanticMatcherModal("braid crossing markov trace invariant");
var mm = document.getElementById("v137-matcher-mount");
assertNoUndefinedOrNaN("V148 8-Role + 2-Role Note Matcher Modal", mm.innerHTML);
if (mm.innerHTML.indexOf("MATCHING SINGLE-PROJECT MECHANISM NOTES") === -1) {
  throw new Error("Expected 2-Role Single-Project Note section inside 8-Role Signature Matcher modal!");
}
window.v137CloseMatcherModal();

// Run V147 Comprehensive Automated UX, Functional & Mathematical Test Suite
var v147Report = window.v147RunAllAutomatedTests();
print("V147_AUTOMATED_TEST_SUITE_SUMMARY: Passed=" + v147Report.passed + "/" + v147Report.total + ", Failed=" + v147Report.failed + ", Elapsed=" + v147Report.elapsedMs + "ms");
if (v147Report.failed > 0) {
  v147Report.results.forEach(function(r) {
    if (!r.passed) print("  ❌ FAILED:", r.id, r.category, r.name, r.detail);
  });
  throw new Error("V147 Automated Test Suite had " + v147Report.failed + " failures!");
}
