# Discovery 09: The Consequence-Oriented Meta-Mathematical Atlas & Quantifier-Order Taxonomy

## Overview & Architecture
- **V34 Source Modules:** [`lens-data.mjs`](http://127.0.0.1:4200/preview/v34/lens-data.mjs), [`consequence-map.mjs`](http://127.0.0.1:4200/preview/v34/consequence-map.mjs), [`universe-registry.mjs`](http://127.0.0.1:4200/preview/v34/universe-registry.mjs), and [`capture-reader.mjs`](http://127.0.0.1:4200/preview/v34/studies/l2-averaging/capture-reader.mjs)
- **Machine-Readable Graph in This Folder:** [`consequence_atlas_graph.json`](./consequence_atlas_graph.json)

## 1. Why the Consequence Lens Is a Breakthrough in Formal Mathematics
Traditional formal libraries (such as Mathlib, AFP, or Coq's Mathematical Components) organize theorems by **algebraic/topological hierarchy** and **declaration name**. However, when a mathematician, economist, or AI theorem-proving agent attacks a research problem, the question is rarely *"What lemmas exist in `Mathlib.Analysis.Convex.Caratheodory`?"*—it is *"What mathematical guarantee lets me compress a representation while keeping my target invariant unchanged?"*

Common Ground V34 introduces a three-axis **Consequence Taxonomy** (`What must stay unchanged?` in [`lens-data.mjs`](http://127.0.0.1:4200/preview/v34/lens-data.mjs)):

| Consequence Class | V34 Exemplar Owner | What Is Fixed First | What Can Vary After | Quantifier Signature | Sharp Boundary / Counterexample |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **1. One Specified Answer** | `query_identification/query-iff` | Observation $g$, reference $Q$, source $P$, payoff $f$ | Any observation-compatible law $S$ | $\forall f, (\forall S \in \mathcal{C}(P), \langle S, f\rangle = \langle P, f\rangle) \iff \text{ActiveFiberConst}(f)$ | Preserving one payoff does not identify $P$ (`fin3-mean-boundary`). |
| **2. Every Affine Answer** | `observable_span/observable-universal-query-compression` | Finite distribution $p$ and $k$ observables $f_1,\dots,f_k$ | Arbitrary affine coefficients $(c, a)$ and query $q = c + \sum_j a_j f_j$ | $\exists (s,w)\text{ with }\|s\|\le k+1,\ \forall (c,a,q),\ \langle w_s, q\rangle = \langle p, q\rangle$ | Closure membership alone does not grant finite exact support (`convex-boundary`: $0 \in \overline{\text{conv}}(0,\infty) \setminus \text{conv}(0,\infty)$). |
| **3. Every Prior's Best Binary Score** | `all_prior_recovery/all-prior-iff` | Laws $p,q$ and shared forward channel $K$ | Prior $t \in [0,1]$ and attaining deterministic test $\text{test}_t : \beta \to \text{Bool}$ | $(\exists R,\ P R = p \land Q R = q) \iff (\forall t \in [0,1], V_t(P,Q)=V_t(p,q)) \iff (\forall b, V_{t_b}(P,Q)=V_{t_b}(p,q))$ | Preserving distance at a single prior ($t=1/2$) fails to ensure common recovery (`decision-no-converse`). |
| **4. Minimum-Divergence Law Selection** | `canonical_reconstruction/unique` | Observation $g$, reference $Q$, observed totals $gP$ | Any compatible nonnegative array $S$ | $\forall S \in \mathcal{C}(P),\ D(R, Q) \le D(S, Q) \text{ with } = \iff S = R$ | Uniqueness of the KL minimizer $R$ does not make $\mathcal{C}(P)$ a singleton. |
| **5. Whole Joint Law** | `sampler_representation/joint-law` | Finite game question weights $G$ | Arbitrary fallback kernel `fallback : X → PMF Y` on zero-marginal rows | $\forall \text{fallback},\ \text{jointPMF}(G) = \text{pairLaw}(\text{marginal}, \text{cond}(\text{fallback}))$ | Conditional distributions are non-unique on zero-marginal rows (`conditionalPMF_of_zero`). |
| **6. Every Future Acceptance Answer** | `ending01_memory/ending01-lower-bound` | Language $L_{01}$ and witness histories $\{\varepsilon, 0, 01\}$ | Any finite recognizer $M$ and separating future suffix $z$ | $\forall M,\ L(M)=L_{01} \implies 3 \le |\text{State}(M)|$ | Suffix `01` fails to separate the witnesses; separating suffixes vary by pair (`[1]` vs. `[]`). |

## 2. How Our 8 Extension Modules Transform the Atlas Graph
In [`consequence_atlas_graph.json`](./consequence_atlas_graph.json), we document how the 8 new Lean 4 modules in Folders `01`–`08` convert V34's conceptual comparisons into **compiled mathematical bridges**:
1. `UnifiedSufficiencyBridge.lean` connects **Consequence Class 3** (`all_prior_recovery`) with **Consequence Class 4** (`information_recovery` / `canonical_reconstruction`).
2. `CoresetBellmanCompression.lean` connects **Consequence Class 2** (`observable_span`) with **Bellman Error Control** (`bellman_residual`).
3. `PredictiveStateSufficiency.lean` connects **Consequence Class 1** (`query_identification`) with **Consequence Class 6** (`ending01_memory`).
4. `LagrangianVolumeStability.lean` connects **Matrix Volume Rate** (`determinant_rate`) with **Euler $L^2$ Averaging** (`l2_averaging`).
