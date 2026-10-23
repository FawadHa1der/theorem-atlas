# Discovery 02: Connes–Carathéodory Convex Support & Universal Affine Query Compression

## Overview & Verification Status
- **V34 Record Owners:** [`finite_convex_representation`](http://127.0.0.1:4200/preview/v34/?v=1&a=finite_convex_representation&s=convex-support), [`moment_matching`](http://127.0.0.1:4200/preview/v34/?v=1&a=moment_matching&s=moment-support), and [`observable_span`](http://127.0.0.1:4200/preview/v34/?v=1&a=observable_span&s=observable-universal-query-compression)
- **V34 Proof Status:** Native Lean 4.32.0 verified (`Mathlib 81a5d257`), zero `sorryAx`, standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **Source Files in This Folder:**
  1. [`FiniteConvexAndMoments.lean`](./FiniteConvexAndMoments.lean) — Verified V34 Lean 4 source for Carathéodory support compression (`exists_small_support_of_mem_convexHull`) and finite observable moment-matching (`exists_small_positive_support_matching_observables`).
  2. [`ObservableSpan.lean`](./ObservableSpan.lean) — Verified V34 Lean 4 source for `sum_affine_query`, `affine_query_eq_of_matching`, and `exists_small_support_preserving_all_affine_queries`.
  3. [`ApproximateAffineCoreset.lean`](./ApproximateAffineCoreset.lean) — **Novel Breakthrough Formalization** proving the $(\varepsilon, \eta)$-Approximate Universal Affine Query Compression Bound (`approx_affine_query_bound`).

## 1. The V34 Discovery: Quantifier Order in Universal Query Compression
The central proof path of the V34 Universe connects three layers:
1. **Convex Geometry (`exists_small_support_of_mem_convexHull`):** Any point $x \in \text{convexHull}\,\mathbb{R}(\text{range}(\text{orbit}))$ in a finite-dimensional real normed space $V$ admits a nonnegative normalized representation on at most $\dim_{\mathbb{R}}(V) + 1$ original indices. When composed with the transported helper from OpenAI's [`ConnesRigidity.lean`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L18914-L18932), every point $y \in \overline{\text{convexHull}}\,\mathbb{R}(\text{range}(\text{orbit}))$ admits an $\varepsilon$-approximating mixture supported on at most $\dim_{\mathbb{R}}(V) + 1$ points.
2. **Moment Matching (`exists_small_positive_support_matching_observables`):** Viewing $k$ real observables $f_1, \dots, f_k : I \to \mathbb{R}$ as an orbit in $\mathbb{R}^k$, any finite probability distribution $p : I \to \mathbb{R}$ admits a sparse support $s \subseteq \{i \mid p_i > 0\}$ of cardinality $|s| \le k + 1$ and weights $w_i \ge 0$ ($\sum_{i\in s} w_i = 1$) matching all $k$ expectations.
3. **Universal Affine Compression (`exists_small_support_preserving_all_affine_queries`):** Because `s` and `w` are constructed **before** quantifying over queries, that single $(k+1)$-point representative simultaneously preserves every affine query $q(i) = c + \sum_{j=1}^k a_j f_j(i)$.

## 2. New Breakthrough in `ApproximateAffineCoreset.lean`
In real-world cubature, randomized coresets, and kernel herding, moments are matched up to tolerance $\varepsilon_j$ and target payoff functions $q$ are only approximately affine ($\|q - (c + \sum_j a_j f_j)\|_\infty \le \eta$). In [`ApproximateAffineCoreset.lean`](./ApproximateAffineCoreset.lean), we prove:
- **Exact Error Decomposition (`query_diff_decomposition`):** Decomposes compressed query error into mass drift, coefficient-weighted moment drift, and supportwise feature approximation residuals.
- **Universal $(\varepsilon, \eta)$-Coreset Bound (`approx_affine_query_bound`):**
  $$\left|\sum_{i \in s} w_i q(i) - \sum_{i \in t} p_i q(i)\right| \le 2 M \eta + \sum_{j=1}^k |a_j|\,\varepsilon_j.$$
