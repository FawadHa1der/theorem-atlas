# Discovery 01: Finite Critical-Prior Blackwell Sufficiency & Quantitative Le Cam Slack

## Overview & Verification Status
- **V34 Record Owners:** [`all_prior_recovery`](http://127.0.0.1:4200/preview/v34/?v=1&a=all_prior_recovery&s=all-prior-iff) and [`decision_preservation`](http://127.0.0.1:4200/preview/v34/?v=1&a=decision_preservation&s=decision-no-converse)
- **V34 Proof Status:** Native Lean 4.35.0 verified (`CSLib 0b1e3680`, `Mathlib 56a00585`), zero `sorryAx`, standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **Source Files in This Folder:**
  1. [`RecoveryConverseFull.lean`](./RecoveryConverseFull.lean) — Exact verified V34 Lean 4 source proving `weighted_tie_of_value_eq`, `exists_common_recovery_of_critical_values`, `exists_common_recovery_of_all_prior_values`, and `all_prior_values_iff_common_recovery` (SHA-256: `7065d191f609b9d4bc5e34235fa9ffdb05b75aa091d8012df6d9f66e860892ca`).
  2. [`QuantitativeCriticalSlack.lean`](./QuantitativeCriticalSlack.lean) — **Novel Breakthrough Formalization** extending the exact critical-prior converse to the quantitative approximate sufficiency (Le Cam deficiency) regime and proving the exact equivalence with the $(\varepsilon, \delta)$-Differential Privacy Hockey-Stick Divergence.

## 1. The V34 Discovery: Why Critical Priors Suffice
Given two finite probability mass functions $p, q : \text{PMF }\alpha$ and a shared stochastic channel $K : \alpha \to \text{PMF }\beta$ with observed laws $P = p.\text{bind } K$ and $Q = q.\text{bind } K$, the optimal Bayes binary-decision score at prior $t \in [0,1]$ is:
$$V_t(p,q) = \sum_{a \in \alpha} \max\big(t\,p(a),\, (1-t)\,q(a)\big).$$
In [`decision_preservation`](http://127.0.0.1:4200/preview/v34/?v=1&a=decision_preservation&s=decision-no-converse), the counterexample $p = (2/5, 1/10, 1/2)$, $q = (1/10, 1/20, 17/20)$ with observation $g : \text{Fin } 3 \to \text{Fin } 2$ merging $\{0,1\} \mapsto 0$ preserves total variation distance ($d_{\text{TV}} = 7/20$, corresponding to $t = 1/2$) while admitting **no common recovery kernel** $R$, because opposing likelihood ratios on $\{0,1\}$ cancel at $t = 1/2$ but are exposed at the critical prior $t_0 = Q_0 / (P_0 + Q_0) = (3/20) / (13/20) = 3/13$.

In [`RecoveryConverseFull.lean`](./RecoveryConverseFull.lean), `exists_common_recovery_of_critical_values` proves that checking $V_{t_b}(P,Q) = V_{t_b}(p,q)$ at the **finite set of output-dependent critical priors** $t_b = Q_b / (P_b + Q_b)$ (for all $b \in \beta$ with $P_b + Q_b > 0$) is both **necessary and sufficient** for the explicit sum-mixture posterior
$$R(b, a) = \frac{(p(a) + q(a))\,K(a,b)}{P_b + Q_b}$$
to simultaneously recover both distributions ($P.\text{bind } R = p \land Q.\text{bind } R = q$).

## 2. New Breakthrough in `QuantitativeCriticalSlack.lean`
In [`QuantitativeCriticalSlack.lean`](./QuantitativeCriticalSlack.lean), we replace the exact equality premise $V_{t_b}(P,Q) = V_{t_b}(p,q)$ with a quantitative slack $\Delta_t(b) \le \delta_t$:
- **Exact Proportionality-Slack Identity (`weighted_abs_tie_defect_eq_twice_localSlack`):** At any tied output $t P_b = (1-t) Q_b$, the one-sided Jensen slacks are equal and sum to the exact $L^1$ proportionality defect:
  $$\sum_{a \in \alpha} |t\,p_a - (1-t)\,q_a|\,K(a,b) = 2\,\Delta_t(b).$$
- **Fiberwise Mixture Reconstruction Bound (`fiber_joint_l1_defect_eq_twice_critical_slack`):** For the explicit recovery kernel `mixtureRecoverReal`, the joint reconstruction error on fiber $b$ satisfies:
  $$\sum_{a \in \alpha} \big|P_b\,R(b,a) - p_a\,K(a,b)\big| = 2\,\Delta_{t_b}(b) \le 2\big(V_{t_b}(p,q) - V_{t_b}(P,Q)\big).$$
- **Hockey-Stick Divergence Equivalence (`weightedValue_eq_hockeyStick`):** For any $t \in (0,1]$ and $\gamma = (1-t)/t$,
  $$V_t(p,q) = (1-t)\sum_{a} q_a + t \sum_{a} \max\big(p_a - \gamma q_a, 0\big),$$
  establishing that critical-prior Bayes preservation is equivalent to preserving the $(\varepsilon, \delta)$-Differential Privacy tradeoff curve at the $|\beta|$ critical slopes $\gamma_b = P_b / Q_b$.
