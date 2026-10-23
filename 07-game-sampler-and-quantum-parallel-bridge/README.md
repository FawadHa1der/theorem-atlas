# Discovery 07: Game Question-Law Sampler Representation & Parallel Repetition Bridge

## Overview & Verification Status
- **V34 Record Owner:** [`sampler_representation`](http://127.0.0.1:4200/preview/v34/?v=1&a=sampler_representation&s=joint-law) (`CommonGround.OpenAIGame.joint_eq_sampler`)
- **V34 Proof Status:** Native Lean 4.32.0 verified (`Mathlib 81a5d257` + byte-exact `CSLib` pairing slice), zero `sorryAx`, standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **Source Files in This Folder:**
  1. [`OpenAIGame.lean`](./OpenAIGame.lean) — Verified V34 Lean 4 source proving `joint_eq_sampler`, `sampler_fallback_independent`, `conditional_unique_on_support`, and `groupedMass_eq_map` (SHA-256: `c1f3db9f4f10d70b9dc007c78200faac01ef395d9210da8a4bb97f6077688d38`).
  2. [`ParallelGameSamplerExtension.lean`](./ParallelGameSamplerExtension.lean) — **Novel Breakthrough Formalization** proving expected game payoff fallback invariance and commutativity of two-stage sampler representation with parallel repetition ($G_1 \otimes G_2$).

## 1. The V34 Discovery: Why Zero-Marginal Rows Need an Explicit Adapter
In OpenAI's `QuantumParallelRepetition.Game X Y A B`, the conditional distribution `G.conditionalYGivenX x y` is defined by division by `G.marginalX x`, so on unreachable questions where `G.marginalX x = 0`, the raw conditional sum over `Y` is `0` (`source_conditional_zero_sum`) rather than `1`. By contrast, CSLib's monadic `PMF` bind (`pairLaw : PMF X → (X → PMF Y) → PMF (X × Y)`) requires a **total** conditional family `X → PMF Y` normalized at *every* `x : X`.
- **The Adapter (`joint_eq_sampler`):** By supplying an explicit typed `fallback : X → PMF Y` used only when `G.marginalX x = 0`, `conditionalPMF G fallback` becomes a valid total kernel `X → PMF Y` whose two-stage `pairLaw` equals `jointPMF G` for *every* choice of `fallback` (`sampler_fallback_independent`).
- **Support Uniqueness (`conditional_unique_on_support`):** Any kernel `k : X → PMF Y` realizing `jointPMF G` must equal `conditionalPMF G fallback` on every positive-marginal question `G.marginalX x > 0`.

## 2. New Breakthrough in `ParallelGameSamplerExtension.lean`
In [`ParallelGameSamplerExtension.lean`](./ParallelGameSamplerExtension.lean), we extend this representation bridge to game payoffs and parallel repetition:
- **Expected Game Value Fallback Invariance (`expectedGamePayoff_eq_joint`):** Proves that for any referee payoff `win : X → Y → ℝ`, two-stage conditional evaluation yields the exact joint game expectation regardless of the fallback on zero-marginal rows.
- **Parallel Product Commutativity (`parallelProduct_sampler_eq_jointProduct`):** Proves that for two independent games $G_1, G_2$, the tensor product of their two-stage marginal-then-completed-conditional laws equals the product joint law $G_1 \otimes G_2$.
