// Cloudflare Pages Function: GET /api/health
export async function onRequestGet(context) {
  return new Response(
    JSON.stringify({
      status: "ok",
      service: "Common Ground Mathematical Observatory",
      version: "V148",
      leanKernel: "leanprover/lean4:v4.33.0",
      counts: {
        projects: 40,
        theoremAtlasV36Projects: 593,
        theoremAtlasV36Concepts: 24,
        theoremAtlasV36Connections: 31,
        theoremAtlasV36MechanismNotes: 17,
        theoremAtlasV36SourceLeads: 155,
        theoremAtlasV36CoreConsequences: 22,
        highLevelMechanisms: 1400,
        customAstIsomorphisms: 7000,
        totalGalaxyIdeas: 8400,
        grandTrinities: 460,
        proofPipelines: 580,
        physicalLean4Suites: 554,
        exactFiniteMicroLabs: 10,
        discoveryPaths: 2800,
        simulators: 160
      },
      cloudflareCompliance: {
        maxFileLimitMiB: 25,
        shardedAssetsCount: 8,
        allShardsUnder25MiB: true
      }
    }),
    {
      headers: {
        "Content-Type": "application/json;charset=utf-8",
        "Cache-Control": "public, max-age=60"
      }
    }
  );
}
