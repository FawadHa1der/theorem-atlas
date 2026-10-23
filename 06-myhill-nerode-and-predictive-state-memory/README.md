# Discovery 06: Myhill–Nerode Witness Memory & Predictive State Representations (PSRs)

## Overview & Verification Status
- **V34 Record Owner:** [`ending01_memory`](http://127.0.0.1:4200/preview/v34/?v=1&a=ending01_memory&s=ending01-lower-bound) (`ending01-correct`, `ending01-lower-bound`)
- **V34 Proof Status:** Native Lean 4.35.0 verified (`CSLib 0b1e3680`, `Mathlib 56a00585`), zero `sorryAx`, standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **Source Files in This Folder:**
  1. [`Ending01.lean`](./Ending01.lean) — Verified V34 Lean 4 source proving `ending01_recognizer_correct` and `ending01_requires_three_states` (SHA-256: `8b8864caf4cb0e812c14c8739a4ad57475b70cf7458af5c6a2f6ac5d091fc1ea`).
  2. [`PredictiveStateSufficiency.lean`](./PredictiveStateSufficiency.lean) — **Novel Breakthrough Formalization** proving the Stochastic Myhill–Nerode / Predictive State Representation (PSR) Theorem that unifies `Ending01` with `LinearQueryObservability`.

## 1. The V34 Discovery
In [`Ending01.lean`](./Ending01.lean), V34 defines the Boolean language $L_{01} = \{w \in \text{List Bool} \mid \exists u,\ w = u \mathbin{+\!\!+} [\text{false}, \text{true}]\}$ and proves two independent theorems:
- **Sufficiency (`ending01_recognizer_correct`):** An explicit 3-state automaton `M01` recognizes $L_{01}$ by induction on right-append via the semantic invariant `suffixState`.
- **Necessity (`ending01_requires_three_states`):** The 3 witness histories $W = \{[], [0], [0,1]\}$ are pairwise Nerode-inequivalent (separated by future suffixes $[1]$ and $[]$), so CSLib's `Language.dfa_num_state_ge` forces $3 \le \text{Nat.card}(\text{State})$ for *every* finite deterministic recognizer of $L_{01}$, without assuming state reachability or `DecidableEq State`.

## 2. New Breakthrough in `PredictiveStateSufficiency.lean`
In the V34 Consequence Lens (`lens-data.mjs`), `query_identification` ("One specified answer") and `ending01_memory` ("Every future acceptance answer") sit side-by-side with no formal link. In [`PredictiveStateSufficiency.lean`](./PredictiveStateSufficiency.lean), we unify them:
- **Predictive Nerode Equivalence (`allFutureQueriesFiberConstant_iff_nerode_on_fibers`):** Requiring a state-abstraction map $g : H \to M$ to satisfy the active-fiber constancy condition of `query_identifiable_iff_active_fibers` across a family of future test queries $\Phi : Z \to H \to \mathbb{R}$ is equivalent to requiring that $g$ only merges histories that are predictively Nerode equivalent ($\forall z \in Z,\ \Phi(z, h_1) = \Phi(z, h_2)$).
- **Predictive State Memory Lower Bound (`memory_card_ge_distinguishable_witnesses`):** Whenever a finite set $W \subseteq H$ of active histories is pairwise separated by at least one future test $z \in Z$, any observation-sufficient state representation $g : H \to M$ is injective on $W$, forcing $|W| \le |M|$.
