# Discovery 03: Information Recovery, KL Pythagorean Geometry & The Unified Sufficiency Bridge

## Overview & Verification Status
- **V34 Record Owners:** [`information_recovery`](http://127.0.0.1:4200/preview/v34/?v=1&a=information_recovery&s=entropy), [`canonical_reconstruction`](http://127.0.0.1:4200/preview/v34/?v=1&a=canonical_reconstruction&s=unique), [`query_identification`](http://127.0.0.1:4200/preview/v34/?v=1&a=query_identification&s=query-iff), and [`indicator_observation`](http://127.0.0.1:4200/preview/v34/?v=1&a=indicator_observation&s=indicator-compatible)
- **V34 Proof Status:** Native Lean 4.32.0 verified (`Mathlib 81a5d257`), zero `sorryAx`, standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **Source Files in This Folder:**
  1. [`InformationRecoveryTrilogy.lean`](./InformationRecoveryTrilogy.lean) — Verified V34 Lean 4 source proving `native_entropy_eq_iff_fiberLikelihoodConstant` and `native_entropy_eq_iff_recovered`.
  2. [`UnifiedSufficiencyBridge.lean`](./UnifiedSufficiencyBridge.lean) — **Novel Breakthrough Formalization** bridging the deterministic grouped-observation KL recovery criterion (`FiberLikelihoodConstant`) with the stochastic channel critical-prior criterion (`ChannelCriticalBalance`) from Discovery 01.

## 1. The V34 Information Trilogy
Across `Recovery.lean`, `ObservationClass.lean`, and `LinearQueryObservability.lean`, V34 establishes three distinct guarantees for a deterministic observation map $g : \iota \to \kappa$:
1. **Query Identifiability (`query_identifiable_iff_active_fibers`):** Every compatible law $S$ gives the same weighted answer $\sum_i S_i f_i = \sum_i P_i f_i$ if and only if the payoff $f$ is constant on each active $Q$-positive fiber of $g$.
2. **Minimum-Divergence Selection (`recovered_entropy_minimum` & `recovered_entropy_eq_iff`):** The $Q$-relative canonical reconstruction $R(i) = \frac{gP(g(i))}{gQ(g(i))} Q(i)$ uniquely minimizes the unnormalized relative entropy $D(S, Q)$ over the compatible class, and for normalized laws satisfies the exact Pythagorean decomposition $D(S, Q) = D(S, R) + D(R, Q)$ (`observation_class_pythagorean`).
3. **Divergence Preservation (`native_entropy_eq_iff_recovered`):** $D(P, Q) = D(gP, gQ)$ if and only if $R = P$, which holds if and only if $P/Q$ is constant within each active observed fiber (`FiberLikelihoodConstant`).

## 2. New Breakthrough in `UnifiedSufficiencyBridge.lean`
Why did `all_prior_recovery` use the sum-mixture decoder $R_{\text{mix}}(b,a) = \frac{(p_a+q_a)K(a,b)}{P_b+Q_b}$ while `canonical_reconstruction` used the reference decoder $R_{\text{ref}}(b,a) = \frac{q_a K(a,b)}{Q_b}$?
In [`UnifiedSufficiencyBridge.lean`](./UnifiedSufficiencyBridge.lean), we prove:
- **Equivalence of Pairwise Fiber Proportionality and Channel Critical Balance (`channelCriticalBalance_of_pairwise` & `pairwise_of_channelCriticalBalance`):** For any stochastic channel $K$, the critical-prior balance identity $p_{a} K(a,b) Q_b = q_{a} K(a,b) P_b$ holds for all $a$ if and only if the pairwise channel-weighted likelihood ratios agree: $(p_{a_1} K(a_1,b))(q_{a_2} K(a_2,b)) = (q_{a_1} K(a_1,b))(p_{a_2} K(a_2,b))$.
- **Coincidence of Mixture and Canonical Reference Decoders (`mixturePosterior_eq_referencePosterior_iff_criticalBalance`):** On every active output $b$, the sum-mixture decoder $R_{\text{mix}}$ and the $Q$-relative decoder $R_{\text{ref}}$ coincide if and only if `ChannelCriticalBalance` holds! Using $R_{\text{mix}}$ in `RecoveryConverseFull.lean` cleverly avoids division by $Q_b = 0$ when $P_b > 0$ and $Q_b = 0$, while reducing to $R_{\text{ref}}$ whenever $Q_b > 0$ and sufficiency holds.
