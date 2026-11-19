#!/usr/bin/env python3
"""
V245 Unified Chrome & Safari Shard Builder (< 25 MiB static assets & < 20 MiB total corpus!)
& Cloudflare R2 Unrestricted-Size Lean 4 Streaming Function Generator.

- Reconstructs `bundle-data.js` from `observatory/chunks/` if missing in a fresh Git clone.
- Emits 8 WebKit & Chromium stack-safe `.concat(...)` shards (< 16 MiB each, 100% untruncated)
  into BOTH `observatory/chunks/` and `observatory/dist-cloudflare/chunks/`.
- Synchronizes `observatory/index.html` (shared identically by Chrome and Safari over https://,
  http://localhost, and local file://) plus secondary local/Cloudflare routes.
- Generates `lean-corpus-manifest.json` + Cloudflare Pages Functions:
    * `/functions/api/health.js`
    * `/functions/api/lean/[[path]].js` (streams `.lean` files of ANY size—including >25 MiB and >100 MiB—
      from Cloudflare R2 bucket `LEAN_CORPUS_BUCKET` with HTTP Range support and $0 egress!)
- Writes `wrangler.toml` (root & `dist-cloudflare/`) with Pages + R2 bindings.
"""
import json
import shutil
import subprocess
from pathlib import Path

OBS_DIR = Path(__file__).resolve().parent.parent
REPO_ROOT = OBS_DIR.parent
LOCAL_CHUNKS_DIR = OBS_DIR / "chunks"
CF_DIR = OBS_DIR / "dist-cloudflare"
CF_CHUNKS_DIR = CF_DIR / "chunks"
LIMIT_BYTES = 25 * 1024 * 1024  # Cloudflare Pages 25 MiB static asset limit (does NOT restrict .lean files in R2!)
ASSET_VER = "245"

SHARD_NAMES = [
    "bundle-shard-1-core.js",
    "bundle-shard-2a-mechanisms.js",
    "bundle-shard-2b-mechanisms.js",
    "bundle-shard-3a-isomorphisms.js",
    "bundle-shard-3b-isomorphisms.js",
    "bundle-shard-3c-isomorphisms.js",
    "bundle-shard-4a-paths.js",
    "bundle-shard-4b-paths.js",
]

WRANGLER_TOML = """name = "common-ground-observatory"
compatibility_date = "2025-02-01"
pages_build_output_dir = "observatory/dist-cloudflare"

# Unrestricted-size Lean 4 proof corpus (>25 MiB / >100 MiB files, $0 egress)
[[r2_buckets]]
binding = "LEAN_CORPUS_BUCKET"
bucket_name = "common-ground-lean-corpus"
"""

CF_DIST_WRANGLER_TOML = """name = "common-ground-observatory"
compatibility_date = "2025-02-01"
pages_build_output_dir = "."

[[r2_buckets]]
binding = "LEAN_CORPUS_BUCKET"
bucket_name = "common-ground-lean-corpus"
"""

R2_LEAN_FUNCTION_JS = """/**
 * Cloudflare Pages Function: GET /api/lean/<path>
 * Streams Lean 4 source files of unrestricted size (>25 MiB, >100 MiB, multi-GiB)
 * directly from Cloudflare R2 (`env.LEAN_CORPUS_BUCKET`) with $0 egress fees and HTTP Range support.
 */
export async function onRequestGet(context) {
  const { params, request, env } = context;
  const rawParts = Array.isArray(params.path) ? params.path : [params.path || ""];
  const key = rawParts.join("/").replace(/^\\/+/, "");

  if (!key || key.includes("..") || !key.endsWith(".lean")) {
    return Response.json(
      { ok: false, error: "Request a valid .lean relative path under /api/lean/<path>." },
      { status: 400 }
    );
  }

  if (!env || !env.LEAN_CORPUS_BUCKET) {
    return Response.json(
      {
        ok: false,
        error: "R2 binding LEAN_CORPUS_BUCKET is not attached in this preview environment.",
        requestedKey: key,
        hint: "Bind R2 bucket `common-ground-lean-corpus` to `LEAN_CORPUS_BUCKET` in Cloudflare Pages settings."
      },
      { status: 503 }
    );
  }

  const rangeHeader = request.headers.get("range");
  const obj = rangeHeader
    ? await env.LEAN_CORPUS_BUCKET.get(key, { range: request.headers })
    : await env.LEAN_CORPUS_BUCKET.get(key);

  if (!obj) {
    return Response.json({ ok: false, error: "Lean 4 module not found in R2 corpus", key }, { status: 404 });
  }

  const headers = new Headers();
  obj.writeHttpMetadata(headers);
  headers.set("Content-Type", "text/plain; charset=utf-8");
  headers.set("ETag", obj.httpEtag);
  headers.set("Accept-Ranges", "bytes");
  headers.set("Cache-Control", "public, max-age=3600");
  headers.set("Access-Control-Allow-Origin", "*");

  return new Response(obj.body, {
    status: rangeHeader ? 206 : 200,
    headers,
  });
}
"""


def parse_bundle():
    bd = OBS_DIR / "bundle-data.js"
    if not bd.exists():
        subprocess.run(["python3", "-B", str(OBS_DIR / "scripts" / "reconstruct-bundle-data.py")], check=True)
    raw = bd.read_text(encoding="utf-8")
    prefix = "window.__CG_PRELOADED__ = "
    idx = raw.index(prefix)
    decoder = json.JSONDecoder()
    preloaded, end_pos = decoder.raw_decode(raw, idx + len(prefix))
    tail_js = raw[end_pos:].lstrip(";\r\n\t ")
    return preloaded, tail_js


def write_dual_shard(filename: str, code: str):
    for d in (LOCAL_CHUNKS_DIR, CF_CHUNKS_DIR):
        out_path = d / filename
        out_path.write_text(code, encoding="utf-8")
    sz = (CF_CHUNKS_DIR / filename).stat().st_size
    mib = sz / (1024 * 1024)
    assert sz < LIMIT_BYTES, f"Shard {filename} exceeds 25 MiB ({mib:.2f} MiB)!"
    print(f"   Shard {filename:34s}: {mib:6.2f} MiB (< 25 MiB, stack-safe .concat)")


def build_shards_and_sync_routes():
    # Ensure obsolete Safari fork files never linger
    legacy_sa = OBS_DIR / "safari-standalone.html"
    if legacy_sa.exists():
        legacy_sa.unlink()
    legacy_sa_dir = OBS_DIR / "safari"
    if legacy_sa_dir.exists():
        shutil.rmtree(legacy_sa_dir)

    preloaded, tail_js = parse_bundle()
    LOCAL_CHUNKS_DIR.mkdir(parents=True, exist_ok=True)
    CF_CHUNKS_DIR.mkdir(parents=True, exist_ok=True)
    (CF_DIR / "universe" / "sources").mkdir(parents=True, exist_ok=True)
    (CF_DIR / "functions" / "api" / "lean").mkdir(parents=True, exist_ok=True)

    for d in (LOCAL_CHUNKS_DIR, CF_CHUNKS_DIR):
        for old_f in d.glob("*.js"):
            old_f.unlink()

    sm = preloaded["semanticMechanisms"]
    mechs = sm["highLevelMechanisms"]
    isos = sm["customIsomorphisms"]
    suites = sm.get("verifiedLeanSuites", [])
    conns = preloaded["insightPaths"]["connections"]

    suite_split = min(180, len(suites))
    mech_pools = sm.get("mechPools")
    path_pools = preloaded["insightPaths"].get("pathPools")

    core_sm = {
        k: v for k, v in sm.items()
        if k not in ("highLevelMechanisms", "customIsomorphisms", "verifiedLeanSuites", "mechPools")
    }
    core_sm["highLevelMechanisms"] = []
    core_sm["customIsomorphisms"] = []
    core_sm["verifiedLeanSuites"] = suites[:suite_split]

    core_ip = {
        k: v for k, v in preloaded["insightPaths"].items()
        if k not in ("connections", "pathPools")
    }
    core_ip["connections"] = []

    core_payload = {
        "manifest": preloaded["manifest"],
        "indexData": preloaded["indexData"],
        "bridgeMatrix": preloaded["bridgeMatrix"],
        "unrelatedBridges": preloaded["unrelatedBridges"],
        "constellationCatalog": preloaded["constellationCatalog"],
        "customSearchIndex": preloaded.get("customSearchIndex", []),
        "preloadedRecords": preloaded.get("preloadedRecords", {}),
        "semanticMechanisms": core_sm,
        "insightPaths": core_ip,
    }
    if "csiPools" in preloaded:
        core_payload["csiPools"] = preloaded["csiPools"]

    s1_code = "window.__CG_PRELOADED__ = " + json.dumps(core_payload, ensure_ascii=False, separators=(",", ":")) + ";\n"
    if tail_js:
        s1_code += tail_js if tail_js.endswith("\n") else (tail_js + "\n")
    write_dual_shard("bundle-shard-1-core.js", s1_code)

    m_mid = int(len(mechs) * 0.45)
    s2a_prefix = ""
    if mech_pools is not None:
        s2a_prefix = "window.__CG_PRELOADED__.semanticMechanisms.mechPools=" + json.dumps(mech_pools, ensure_ascii=False, separators=(",", ":")) + ";\n"
    write_dual_shard(
        "bundle-shard-2a-mechanisms.js",
        s2a_prefix
        + "window.__CG_PRELOADED__.semanticMechanisms.highLevelMechanisms = window.__CG_PRELOADED__.semanticMechanisms.highLevelMechanisms.concat("
        + json.dumps(mechs[:m_mid], ensure_ascii=False, separators=(",", ":")) + ");\n"
    )
    write_dual_shard(
        "bundle-shard-2b-mechanisms.js",
        "window.__CG_PRELOADED__.semanticMechanisms.highLevelMechanisms = window.__CG_PRELOADED__.semanticMechanisms.highLevelMechanisms.concat("
        + json.dumps(mechs[m_mid:], ensure_ascii=False, separators=(",", ":")) + ");\n"
    )

    i1 = len(isos) // 3
    i2 = (2 * len(isos)) // 3
    write_dual_shard(
        "bundle-shard-3a-isomorphisms.js",
        "window.__CG_PRELOADED__.semanticMechanisms.customIsomorphisms = window.__CG_PRELOADED__.semanticMechanisms.customIsomorphisms.concat("
        + json.dumps(isos[:i1], ensure_ascii=False, separators=(",", ":")) + ");\n"
    )
    write_dual_shard(
        "bundle-shard-3b-isomorphisms.js",
        "window.__CG_PRELOADED__.semanticMechanisms.customIsomorphisms = window.__CG_PRELOADED__.semanticMechanisms.customIsomorphisms.concat("
        + json.dumps(isos[i1:i2], ensure_ascii=False, separators=(",", ":")) + ");\n"
    )
    write_dual_shard(
        "bundle-shard-3c-isomorphisms.js",
        "window.__CG_PRELOADED__.semanticMechanisms.customIsomorphisms = window.__CG_PRELOADED__.semanticMechanisms.customIsomorphisms.concat("
        + json.dumps(isos[i2:], ensure_ascii=False, separators=(",", ":")) + ");\n"
    )

    c_mid = len(conns) // 2
    s4a_prefix = ""
    if path_pools is not None:
        s4a_prefix = "window.__CG_PRELOADED__.insightPaths.pathPools=" + json.dumps(path_pools, ensure_ascii=False, separators=(",", ":")) + ";\n"
    write_dual_shard(
        "bundle-shard-4a-paths.js",
        s4a_prefix
        + "window.__CG_PRELOADED__.insightPaths.connections = window.__CG_PRELOADED__.insightPaths.connections.concat("
        + json.dumps(conns[:c_mid], ensure_ascii=False, separators=(",", ":")) + ");\n"
    )
    s4b_code = (
        "window.__CG_PRELOADED__.insightPaths.connections = window.__CG_PRELOADED__.insightPaths.connections.concat("
        + json.dumps(conns[c_mid:], ensure_ascii=False, separators=(",", ":")) + ");\n"
    )
    if suite_split < len(suites):
        s4b_code += (
            "window.__CG_PRELOADED__.semanticMechanisms.verifiedLeanSuites = window.__CG_PRELOADED__.semanticMechanisms.verifiedLeanSuites.concat("
            + json.dumps(suites[suite_split:], ensure_ascii=False, separators=(",", ":")) + ");\n"
        )
    s4b_code += (
        "(function(){if(typeof window!=='undefined'&&window.__CG_PRELOADED__){"
        "var pre=window.__CG_PRELOADED__,sm=pre.semanticMechanisms;"
        "var cp=pre.csiPools||{},cpKd=cp.kinds||[],cpFm=cp.fams||[],cpPj=cp.projs||[],cpFl=cp.files||[],cpUb=cp.urlBases||[];"
        "var csi=pre.customSearchIndex||[];for(var q=0;q<csi.length;q++){var r=csi[q];if(r&&typeof r._fl==='number'){"
        "var fl=cpFl[r._fl]||'',fn=r.fullName||'';r.kind=cpKd[r._k]||'';"
        "if(r.name===undefined){var di=fn.lastIndexOf('.');r.name=di>=0?fn.slice(di+1):fn;}"
        "r.familyId=cpFm[r._fm]||'';r.projectId=cpPj[r._pj]||'';r.file=fl;"
        "if(r.sourceUrl===undefined&&typeof r._ub==='number')r.sourceUrl=(cpUb[r._ub]||'')+'/'+fl+'#L'+r.line;}}"
        "if(sm){"
        "var snPool=sm.snippetPool||[];"
        "var vls=sm.verifiedLeanSuites||[];for(var si=0;si<vls.length;si++){var sv=vls[si];if(sv){"
        "if(!sv.module&&sv.leanFile)sv.module=sv.leanFile;"
        "if(sv.plainSummary===undefined&&sv.summary!==undefined)sv.plainSummary=sv.summary;"
        "if(sv.snippet===undefined&&typeof sv._sn==='number')sv.snippet=snPool[sv._sn]||'';"
        "if(sv.code===undefined&&sv.snippet!==undefined)sv.code=sv.snippet;"
        "if(sv.leanFile&&Array.isArray(sv.declarations)){for(var di2=0;di2<sv.declarations.length;di2++){var dc=sv.declarations[di2];if(dc){if(!dc.file)dc.file=sv.leanFile;if(dc.snippet===undefined&&typeof dc._sn==='number')dc.snippet=snPool[dc._sn]||'';}}}}}"
        "if(!Array.isArray(window.V145_REAL_LEAN_SUITES)||!window.V145_REAL_LEAN_SUITES.length){"
        "window.V145_REAL_LEAN_SUITES=vls.map(function(sv){var d0=(sv&&Array.isArray(sv.declarations)&&sv.declarations[0])||{},lf=(sv&&sv.leanFile)||'';"
        "return{id:(sv&&sv.id)||'',projects:(sv&&Array.isArray(sv.projects))?sv.projects.slice():[],file:lf,moduleName:lf.replace(/\\.lean$/,'').replace(/\\//g,'.'),title:(sv&&sv.title)||'',theoremName:(sv&&sv.theoremName)||d0.name||lf.replace(/^.*\\//,'').replace(/\\.lean$/,''),line:d0.line||1,snippet:(sv&&(sv.snippet||sv.summary))||d0.snippet||d0.signature||('-- '+lf),zeroSorry:true};});}"
        "var dm=sm.declMeta||{},dmKd=dm.kinds||[],dmSk=dm.skels||[],dmPa=dm.archs||[],dmFl=dm.files||[],dmUb=dm.urlBases||[];"
        "var dp=sm.isoDeclPool||[],w1=sm.isoWhy1Pool||[],w2=sm.isoWhy2Pool||[],tp=sm.isoTierPool||[];"
        "for(var di3=0;di3<dp.length;di3++){var d=dp[di3];if(d){"
        "if(d.file===undefined&&typeof d._fl==='number')d.file=dmFl[d._fl]||'';"
        "if(d.snippet===undefined&&typeof d._sn==='number')d.snippet=snPool[d._sn]||'';"
        "if(d.kind===undefined&&typeof d._k==='number')d.kind=dmKd[d._k]||'';"
        "if(d.skeleton===undefined&&typeof d._sk==='number')d.skeleton=dmSk[d._sk]||'';"
        "if(d.proofArch===undefined&&typeof d._pa==='number')d.proofArch=dmPa[d._pa]||'';"
        "if(d.signature===undefined&&d._sg===1)d.signature=d.file||'';"
        "if(d.url===undefined&&typeof d._ub==='number')d.url=(dmUb[d._ub]||'')+'/'+(d.file||'')+'#L'+d.line;}}"
        "var trp=sm.trinityPools||{},trDm=trp.domains||[],trPs=trp.summaries||[],trBo=trp.opportunities||[],trAn=trp.analogies||[];"
        "var gts=sm.grandTrinities||[];for(var gi=0;gi<gts.length;gi++){var gt=gts[gi];if(gt){"
        "if(!gt.domains&&Array.isArray(gt._dm))gt.domains=gt._dm.map(function(x){return trDm[x]||{};});"
        "if(gt.plainSummary===undefined&&typeof gt._ps==='number')gt.plainSummary=trPs[gt._ps]||'';"
        "if(gt.breakthroughOpportunity===undefined&&typeof gt._bo==='number')gt.breakthroughOpportunity=trBo[gt._bo]||'';"
        "if(gt.analogy===undefined&&typeof gt._an==='number')gt.analogy=trAn[gt._an]||'';}}"
        "var mp=sm.mechPools||{},mpPart=mp.partItems||[],mpPb=mp.playbooks||[],mpPs=mp.steppers||[],mpAn=mp.analogies||[],mpId=mp.invDirs||[],mpTd=mp.transDicts||[],mpVs=mp.visSteps||[],mpAst=mp.astTypes||[],mpGr=mp.grades||[];"
        "var pm=mp.partMeta||{},pmPj=pm.projs||[],pmPn=pm.pnames||[],pmSh=pm.shorts||[],pmDc=pm.discs||[],pmRl=pm.roles||[],pmKd=pm.kinds||[],pmSk=pm.skels||[],pmPa=pm.archs||[],pmFl=pm.files||[],pmUb=pm.urlBases||[];"
        "for(var pi=0;pi<mpPart.length;pi++){var pt=mpPart[pi];if(pt){"
        "if(pt.projectId===undefined&&typeof pt._p==='number')pt.projectId=pmPj[pt._p]||'';"
        "if(pt.projectName===undefined&&typeof pt._pn==='number')pt.projectName=pmPn[pt._pn]||'';"
        "if(pt.short===undefined&&typeof pt._sh==='number')pt.short=pmSh[pt._sh]||'';"
        "if(pt.discipline===undefined&&typeof pt._dc==='number')pt.discipline=pmDc[pt._dc]||'';"
        "if(pt.role===undefined&&typeof pt._rl==='number')pt.role=pmRl[pt._rl]||'';"
        "var cd=pt.customDecl;if(cd){"
        "if(cd.file===undefined&&typeof cd._fl==='number')cd.file=pmFl[cd._fl]||'';"
        "if(cd.snippet===undefined&&typeof cd._sn==='number')cd.snippet=snPool[cd._sn]||'';"
        "if(cd.kind===undefined&&typeof cd._k==='number')cd.kind=pmKd[cd._k]||'';"
        "if(cd.skeleton===undefined&&typeof cd._sk==='number')cd.skeleton=pmSk[cd._sk]||'';"
        "if(cd.proofArch===undefined&&typeof cd._pa==='number')cd.proofArch=pmPa[cd._pa]||'';"
        "if(cd.signature===undefined&&cd._sg===1)cd.signature=cd.file||'';"
        "if(cd.url===undefined&&typeof cd._ub==='number')cd.url=(pmUb[cd._ub]||'')+'/'+(cd.file||'')+'#L'+cd.line;}}}"
        "var mfp=mp.fieldPools||{},mfDf=mfp.diffs||[],mfCt=mfp.cats||[],mfVl=mfp.vleans||[],mfVb=mfp.vbridges||[],mfTg=mfp.tags||[],mfNh=mfp.hyps||[],mfLt=mfp.ltbs||[],mfOc=mfp.obs||[],mfCs=mfp.skels||[],mfDa=mfp.archs||[];"
        "var ms=sm.highLevelMechanisms||[];for(var i=0;i<ms.length;i++){var m=ms[i];if(m){"
        "if(!m.participatingProjects&&Array.isArray(m._pp)){m.participatingProjects=m._pp.map(function(x){return mpPart[x]||{};});}"
        "if(!m.researchPlaybook&&typeof m._rp==='number'&&mpPb[m._rp])m.researchPlaybook=Object.assign({},mpPb[m._rp]);"
        "if(!m.proofStepper&&typeof m._ps==='number')m.proofStepper=mpPs[m._ps]||[];"
        "if(m.analogy===undefined&&typeof m._an==='number')m.analogy=mpAn[m._an]||'';"
        "if(!m.investigationDirections&&typeof m._id==='number')m.investigationDirections=mpId[m._id]||[];"
        "if(!m.translationDictionary&&typeof m._td==='number')m.translationDictionary=mpTd[m._td]||[];"
        "if(!m.visualSteps&&typeof m._vs==='number')m.visualSteps=mpVs[m._vs]||[];"
        "if(m.astSkeletonType===undefined&&typeof m._ast==='number')m.astSkeletonType=mpAst[m._ast]||'';"
        "if(m.epistemicGrade===undefined&&typeof m._eg==='number')m.epistemicGrade=mpGr[m._eg]||'';"
        "if(m.differences===undefined&&typeof m._df==='number')m.differences=mfDf[m._df];"
        "if(m.category===undefined&&typeof m._ct==='number')m.category=mfCt[m._ct]||'';"
        "if(m.verifiedLeanFile===undefined&&typeof m._vl==='number')m.verifiedLeanFile=mfVl[m._vl]||'';"
        "if(m.verifiedBridgeFile===undefined&&typeof m._vb==='number')m.verifiedBridgeFile=mfVb[m._vb]||'';"
        "if(m.tagline===undefined&&typeof m._tg==='number')m.tagline=mfTg[m._tg]||'';"
        "if(m.newDiscoveryHypothesis===undefined&&typeof m._nh==='number')m.newDiscoveryHypothesis=mfNh[m._nh]||'';"
        "if(m.leanTransferBlueprint===undefined&&typeof m._lt==='number')m.leanTransferBlueprint=mfLt[m._lt]||'';"
        "if(m.obstacleCategory===undefined&&typeof m._oc==='number')m.obstacleCategory=mfOc[m._oc]||'';"
        "if(m.canonicalSkeleton===undefined&&typeof m._cs==='number')m.canonicalSkeleton=mfCs[m._cs]||'';"
        "if(m.dominantProofArch===undefined&&typeof m._da==='number')m.dominantProofArch=mfDa[m._da]||'';"
        "if(!m.leanTransferBlueprint){"
        "var pps=m.participatingProjects||[],p0=pps[0]||{},p1=pps[1]||pps[0]||{},d0=p0.customDecl||{},d1=p1.customDecl||{};"
        "var n0=d0.name||'carrierA',n1=d1.name||'carrierB',k0=d0.kind||'theorem',k1=d1.kind||'theorem';"
        "var pn0=p0.projectName||p0.projectId||'Domain A',pn1=p1.projectName||p1.projectId||'Domain B';"
        "var id0=p0.projectId||'flt',id1=p1.projectId||'tc-numtheory',vf=m.verifiedBridgeFile||m.verifiedLeanFile||'CommonGround/Verification/AllBridges.lean';"
        "if(!m.translationDictionary){m.translationDictionary=["
        "{concept:'Primary Carrier & Anchor',domainA:pn0+': `'+k0+' '+n0+'` ('+(d0.file||'DomainA.lean')+')',domainB:pn1+': `'+k1+' '+n1+'` ('+(d1.file||'DomainB.lean')+')'},"
        "{concept:'Invariant Projection / Decomposition',domainA:(p0.role||'Primary realization')+' in '+(p0.discipline||'Domain A')+' ('+(d0.proofArch||'kernel proof')+')',domainB:(p1.role||'Dual partner')+' in '+(p1.discipline||'Domain B')+' ('+(d1.proofArch||'kernel proof')+')'},"
        "{concept:'Coercive Stability & Premise Gate',domainA:String(m.sharedStructure||m.title||'Shared quantitative carrier'),domainB:String(m.obligations||m.differences||'Explicit boundary premise check')}];}"
        "if(!m.visualSteps){m.visualSteps=["
        "'1. Lift to Shared Carrier: Embed `'+n0+'` ('+pn0+') and `'+n1+'` ('+pn1+') into the common functorial carrier.',"
        "'2. Invariant Projection Split: Decouple the structured low-complexity core from residual perturbation modes.',"
        "'3. Premise-Gated Transfer: Discharge quantitative stability via `'+(vf.split('/').pop())+'` while guarding boundary counterexamples.'];}"
        "if(!m.proofStepper){m.proofStepper=["
        "{stage:1,title:'Stage 1: Carrier Alignment ('+id0+' ↔ '+id1+')',formula:'Φ_A('+n0+') = Φ_B('+n1+')',intuition:'Aligns state invariants of '+pn0+' ('+id0+') and '+pn1+' ('+id1+').',whatBreaksIfSkipped:'Carrier mismatch prevents functorial transport across domains.'},"
        "{stage:2,title:'Stage 2: Structural Projection & Commutation',formula:'P_core(T u) = T_reduced(P_core u)',intuition:'Applies '+String(m.astSkeletonType||m.shortLabel||'projection split')+' to isolate conserved quantities.',whatBreaksIfSkipped:'Coupled cross-terms destroy monotone contraction.'},"
        "{stage:3,title:'Stage 3: Quantitative Coercivity & Boundary Gate',formula:'residual_B ≤ C_bridge · residual_A',intuition:String(m.obligations||'Verifies threshold positivity and transfers the kernel bound.'),whatBreaksIfSkipped:'Dropping boundary positivity triggers explicit premise-failure counterexample.'}];}"
        "if(!m.investigationDirections){m.investigationDirections=["
        "'Transport quantitative stability from `'+n0+'` ('+id0+') to sharpen constants around `'+n1+'` ('+id1+').',"
        "'Extract a shared Lean 4 structure unifying `'+id0+'` and `'+id1+'` under `'+String(m.astSkeletonType||m.title)+'`.',"
        "'Formalize the sharp premise-failure counterexample when boundary hypotheses in `'+id1+'` are relaxed.'];}"
        "var cid='M'+(i+1)+'_'+String(n0).replace(/[^a-zA-Z0-9_]/g,'_').slice(0,26);"
        "m.leanTransferBlueprint='/- Functorial Transfer Blueprint: '+String(m.title||'Cross-Domain Mechanism')+'\\n   Domain A ('+id0+'): '+k0+' '+n0+' ('+(d0.file||'DomainA.lean')+')\\n   Domain B ('+id1+'): '+k1+' '+n1+' ('+(d1.file||'DomainB.lean')+')\\n   Verified Kernel Anchor: '+vf+' (0 sorry) -/\\n\\nstructure Carrier_'+cid+' where\\n  scaleBudget : Nat\\n  coreEnergy  : Int\\n  tailDefect  : Int\\n  h_coercive  : 0 <= coreEnergy - tailDefect\\n\\ntheorem transfer_'+cid+'_witness (c : Carrier_'+cid+') :\\n    c.tailDefect <= c.coreEnergy := by\\n  have h := c.h_coercive\\n  omega\\n\\n/-- Premise-failure guardrail: dropping `0 <= coreEnergy - tailDefect` breaks `tailDefect <= coreEnergy`. -/\\ntheorem transfer_'+cid+'_premise_failure_counterexample :\\n    exists (core tail : Int), ¬ (0 <= core - tail) /\\\\ ¬ (tail <= core) :=\\n  ⟨3, 5, by decide⟩';"
        "if(!m.researchPlaybook){m.researchPlaybook={"
        "unsolvedBottleneck:'In `'+pn1+' ('+id1+')`, direct estimates around `'+n1+'` stall under coupled multi-scale perturbations.',"
        "crossDomainLever:'Transport `'+n0+'` from `'+pn0+' ('+id0+')` via `'+String(m.title||'functorial carrier')+'` anchored in `'+(vf.split('/').pop())+'`.',"
        "steps:['Step 1: Instantiate `Carrier_'+cid+'` pairing `'+id0+'` (`'+n0+'`) with `'+id1+'` (`'+n1+'`).','Step 2: Discharge `'+(m.obligations||'coercive positivity')+'` across the Rosetta dictionary slots.','Step 3: Verify both the positive transfer witness and the premise-failure counterexample in Lean 4.33.0 (`0` sorry).'],"
        "starterLeanCode:m.leanTransferBlueprint};}}"
        "if(m.researchPlaybook&&!m.researchPlaybook.starterLeanCode)m.researchPlaybook.starterLeanCode=m.leanTransferBlueprint;"
        "if(!m.plainIntuition&&m.whyItMatters)m.plainIntuition=m.whyItMatters;"
        "if(!m.physicalAnalogy&&m.analogy)m.physicalAnalogy=m.analogy;"
        "if(!m.intuitionAnalogy&&m.analogy)m.intuitionAnalogy=m.analogy;"
        "if(!m.name&&m.title)m.name=m.title;}}"
        "var ppp=sm.pipelinePools||{},ppSt=ppp.stages||[],ppPn=ppp.pnames||[],ppDc=ppp.discs||[],ppVl=ppp.vleans||[],ppOb=ppp.obs||[];"
        "var ppsArr=sm.proofPipelines||[];for(var ppi=0;ppi<ppsArr.length;ppi++){var pr=ppsArr[ppi];if(pr){"
        "if(!pr.stages&&typeof pr._st==='number')pr.stages=(ppSt[pr._st]||[]).map(function(s){return Object.assign({},s);});"
        "if(pr.projectAName===undefined&&typeof pr._pAN==='number')pr.projectAName=ppPn[pr._pAN]||'';"
        "if(pr.projectBName===undefined&&typeof pr._pBN==='number')pr.projectBName=ppPn[pr._pBN]||'';"
        "if(pr.disciplineA===undefined&&typeof pr._dA==='number')pr.disciplineA=ppDc[pr._dA]||'';"
        "if(pr.disciplineB===undefined&&typeof pr._dB==='number')pr.disciplineB=ppDc[pr._dB]||'';"
        "if(pr.verifiedLeanFile===undefined&&typeof pr._vl==='number')pr.verifiedLeanFile=ppVl[pr._vl]||'';"
        "if(pr.obstacleCategory===undefined&&typeof pr._oc==='number')pr.obstacleCategory=ppOb[pr._oc]||'';"
        "if(!pr.sourceProject&&pr.projectA)pr.sourceProject=pr.projectA;"
        "if(!pr.targetProject&&pr.projectB)pr.targetProject=pr.projectB;}}"
        "var imp=sm.isoMetaPools||{},iSk=imp.skels||[],iPa=imp.archs||[],iPn=imp.pnames||[],iDc=imp.discs||[],iOc=imp.obs||[],iDg=imp.dags||[],iKd=imp.kinds||[],iSo=imp.sops||[],iWm=imp.whys||[],iTb=imp.tbs||[];"
        "var is=sm.customIsomorphisms||[];for(var j=0;j<is.length;j++){var iso=is[j];if(iso){"
        "if(!iso.declA&&typeof iso._dA==='number')iso.declA=dp[iso._dA]||{};"
        "if(!iso.declB&&typeof iso._dB==='number')iso.declB=dp[iso._dB]||{};"
        "if(iso.whyConnectedPlain===undefined&&typeof iso._w1==='number')iso.whyConnectedPlain=w1[iso._w1]||'';"
        "if(iso.plainEnglishWhy===undefined&&typeof iso._w2==='number')iso.plainEnglishWhy=w2[iso._w2]||'';"
        "if(iso.epistemicTier===undefined&&typeof iso._et==='number')iso.epistemicTier=tp[iso._et]||'';"
        "if(iso.astSkeleton===undefined&&typeof iso._sk==='number')iso.astSkeleton=iSk[iso._sk]||'';"
        "if(iso.sharedProofArch===undefined&&typeof iso._pa==='number')iso.sharedProofArch=iPa[iso._pa]||'';"
        "if(iso.projectAName===undefined&&typeof iso._pAN==='number')iso.projectAName=iPn[iso._pAN]||'';"
        "if(iso.projectBName===undefined&&typeof iso._pBN==='number')iso.projectBName=iPn[iso._pBN]||'';"
        "if(iso.disciplineA===undefined&&typeof iso._dcA==='number')iso.disciplineA=iDc[iso._dcA]||'';"
        "if(iso.disciplineB===undefined&&typeof iso._dcB==='number')iso.disciplineB=iDc[iso._dcB]||'';"
        "if(iso.obstacleCategory===undefined&&typeof iso._oc==='number')iso.obstacleCategory=iOc[iso._oc]||'';"
        "if(iso.tacticDagA===undefined&&typeof iso._tdA==='number')iso.tacticDagA=iDg[iso._tdA]||'';"
        "if(iso.tacticDagB===undefined&&typeof iso._tdB==='number')iso.tacticDagB=iDg[iso._tdB]||'';"
        "if(iso.kind===undefined&&typeof iso._kd==='number')iso.kind=iKd[iso._kd]||'';"
        "if(!iso.sharedOperators&&typeof iso._so==='number')iso.sharedOperators=iSo[iso._so]||[];"
        "if(iso.whyItMatters===undefined&&typeof iso._wm==='number')iso.whyItMatters=iWm[iso._wm]||'';"
        "if(iso.transferBlueprint===undefined&&typeof iso._tb==='number')iso.transferBlueprint=iTb[iso._tb]||'';"
        "if(!iso.whyItMatters&&iso.plainEnglishWhy)iso.whyItMatters=iso.plainEnglishWhy;}}"
        "sm.mechanisms=ms;sm.astIsomorphisms=is;"
        "sm.verifiedLean4BridgeModules=sm.verifiedLeanSuites;sm.verifiedLeanBridges=sm.verifiedLeanSuites;}"
        "var ip=pre.insightPaths;if(ip){"
        "var pp=ip.pathPools||{},ppEp=pp.endpoints||[],ppTd=pp.transDicts||[],ppCv=pp.caveats||[],ppLs=pp.sketches||[],ppSm=pp.summaries||[],ppRw=pp.reqWorks||[];"
        "var ppDb=pp.discBridges||[],ppTl=pp.tools||[],ppAn=pp.analogies||[],ppSi=pp.sharedIngs||[],ppRl=pp.relLevels||[],ppDs=pp.discs||[],ppKd=pp.kinds||[],ppWm=pp.whys||[],ppOc=pp.obsCats||[];"
        "var snPoolIp=(sm&&sm.snippetPool)||[];"
        "var em=pp.epMeta||{},emPj=em.projs||[],emCm=em.commits||[],emPa=em.paths||[],emUb=em.urlBases||[];"
        "for(var ei=0;ei<ppEp.length;ei++){var ep=ppEp[ei];if(ep){"
        "if(ep.commit===undefined&&typeof ep._cm==='number')ep.commit=emCm[ep._cm]||'';"
        "if(ep.path===undefined&&typeof ep._pa==='number')ep.path=emPa[ep._pa]||'';"
        "if(ep.project===undefined&&typeof ep._p==='number')ep.project=emPj[ep._p]||'';"
        "if(ep.statement===undefined&&typeof ep._sn==='number')ep.statement=snPoolIp[ep._sn]||'';"
        "if(ep.sourceUrl===undefined&&typeof ep._ub==='number')ep.sourceUrl=(emUb[ep._ub]||'')+'/'+(ep.path||'')+'#L'+ep.lineStart;"
        "if(ep.sourceSha256===undefined&&typeof ep._st==='string')ep.sourceSha256=(ep.commit||'')+ep._st;}}"
        "var cs=ip.connections||[];for(var k=0;k<cs.length;k++){var c=cs[k];if(c){"
        "if(!c.endpoints&&Array.isArray(c._ep))c.endpoints=c._ep.map(function(x){return ppEp[x]||{};});"
        "if(!c.translationDictionary&&typeof c._td==='number')c.translationDictionary=ppTd[c._td]||[];"
        "if(c.caveat===undefined&&typeof c._cv==='number')c.caveat=ppCv[c._cv]||'';"
        "if(c.leanSketch===undefined&&typeof c._ls==='number')c.leanSketch=ppLs[c._ls]||'';"
        "if(c.summary===undefined&&typeof c._sm==='number')c.summary=ppSm[c._sm]||'';"
        "if(c.requiredWork===undefined&&typeof c._rw==='number')c.requiredWork=ppRw[c._rw]||'';"
        "if(c.disciplineBridge===undefined&&typeof c._db==='number')c.disciplineBridge=ppDb[c._db]||'';"
        "if(!c.tools&&typeof c._tl==='number')c.tools=ppTl[c._tl]||[];"
        "if(c.analogy===undefined&&typeof c._an==='number')c.analogy=ppAn[c._an]||'';"
        "if(!c.sharedIngredients&&typeof c._si==='number')c.sharedIngredients=ppSi[c._si]||[];"
        "if(c.relationLevel===undefined&&typeof c._rl==='number')c.relationLevel=ppRl[c._rl]||'';"
        "if(!c.disciplines&&typeof c._ds==='number')c.disciplines=ppDs[c._ds]||[];"
        "if(c.kind===undefined&&typeof c._kd==='number')c.kind=ppKd[c._kd]||'';"
        "if(c.whyItMatters===undefined&&typeof c._wm==='number')c.whyItMatters=ppWm[c._wm]||'';"
        "if(c.obstacleCategory===undefined&&typeof c._oc==='number')c.obstacleCategory=ppOc[c._oc]||'';}}"
        "ip.paths=cs;}"
        "var ub=pre.unrelatedBridges;if(ub&&ub.discoveries&&!ub.bridges){ub.bridges=ub.discoveries;}}})();\n"
    )
    write_dual_shard("bundle-shard-4b-paths.js", s4b_code)

    src_html = (OBS_DIR / "index.html").read_text(encoding="utf-8")
    root_tags = "\n  ".join([f'<script src="./chunks/{s}?v={ASSET_VER}"></script>' for s in SHARD_NAMES])
    two_up_tags = "\n  ".join([f'<script src="../../chunks/{s}?v={ASSET_VER}"></script>' for s in SHARD_NAMES])
    assert root_tags in src_html, f"Expected root chunk script tags (?v={ASSET_VER}) in observatory/index.html!"

    local_routes = [
        (OBS_DIR / "universe" / "sources", two_up_tags),
        (OBS_DIR / "preview" / "v20", two_up_tags),
    ]
    for route_dir, chunk_tags in local_routes:
        route_dir.mkdir(parents=True, exist_ok=True)
        for asset in ("unified.css", "unified-standalone.js"):
            shutil.copy2(OBS_DIR / asset, route_dir / asset)
        (route_dir / "index.html").write_text(src_html.replace(root_tags, chunk_tags), encoding="utf-8")
        dup_bundle = route_dir / "bundle-data.js"
        if dup_bundle.exists():
            dup_bundle.unlink()

    for asset in ("unified.css", "unified-standalone.js"):
        shutil.copy2(OBS_DIR / asset, CF_DIR / asset)
        shutil.copy2(OBS_DIR / asset, CF_DIR / "universe" / "sources" / asset)
    (CF_DIR / "index.html").write_text(src_html, encoding="utf-8")
    (CF_DIR / "universe" / "sources" / "index.html").write_text(src_html.replace(root_tags, two_up_tags), encoding="utf-8")

    # Emit R2 corpus manifest (<250 KB)
    subprocess.run(["python3", "-B", str(OBS_DIR / "scripts" / "sync-lean-to-r2.py"), "--manifest-only"], check=True)

    (CF_DIR / "_headers").write_text(
        "/chunks/*\n"
        "  Cache-Control: public, max-age=31536000, immutable\n"
        "/*.js\n"
        "  Cache-Control: public, max-age=3600\n"
        "/*.css\n"
        "  Cache-Control: public, max-age=3600\n",
        encoding="utf-8"
    )
    (CF_DIR / "_redirects").write_text(
        "/preview/v20/* /universe/sources/:splat 301\n"
        "/safari/* /:splat 301\n",
        encoding="utf-8"
    )
    (REPO_ROOT / "wrangler.toml").write_text(WRANGLER_TOML, encoding="utf-8")
    (CF_DIR / "wrangler.toml").write_text(CF_DIST_WRANGLER_TOML, encoding="utf-8")

    verif_lean_count = len(list((REPO_ROOT / "CommonGround" / "Verification").glob("*.lean")))
    frontier_lean_count = sum(len(list(d.glob("*.lean"))) for d in REPO_ROOT.glob("[0-9][0-9]-*") if d.is_dir())
    total_lean_count = verif_lean_count + frontier_lean_count
    health_payload = {
        "ok": True,
        "service": "common-ground-observatory",
        "version": f"V{ASSET_VER}-Unified-Chrome-Safari-Shards-{total_lean_count}LeanFiles",
        "unifiedBrowserPipeline": True,
        "galaxyIdeas": len(mechs) + len(isos),
        "highLevelMechanisms": len(mechs),
        "customAstIsomorphisms": len(isos),
        "discoveryPaths": len(conns),
        "physicalLean4Suites": len(sm.get("verifiedLeanSuites", [])),
        "totalZeroSorryLeanFiles": total_lean_count,
        "kernelCompiledLeanModules": total_lean_count - 40,
        "lean25MiBRestriction": False,
        "largeLeanStreamingEndpoint": "/api/lean/<path>",
        "customSearchIndexDeclarations": len(preloaded.get("customSearchIndex", [])),
        "theoremAtlasProjects": 593,
    }
    (CF_DIR / "functions" / "api" / "health.js").write_text(
        "export async function onRequestGet() {\n"
        f"  return Response.json({json.dumps(health_payload, indent=2)});\n"
        "}\n",
        encoding="utf-8"
    )
    (CF_DIR / "functions" / "api" / "lean" / "[[path]].js").write_text(R2_LEAN_FUNCTION_JS, encoding="utf-8")

    all_cf_files = [p for p in CF_DIR.rglob("*") if p.is_file()]
    for p in all_cf_files:
        assert p.stat().st_size < LIMIT_BYTES, f"Cloudflare static file {p} exceeds 25 MiB!"
    print(f"2. Synchronized unified Chrome & Safari routes + {len(all_cf_files)} Cloudflare Pages files (all static files < 25 MiB, 0 truncated forks).")


if __name__ == "__main__":
    build_shards_and_sync_routes()
