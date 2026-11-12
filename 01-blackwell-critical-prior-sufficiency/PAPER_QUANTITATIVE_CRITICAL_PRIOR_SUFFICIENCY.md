# Quantitative Critical-Prior Sufficiency: Finite-Grid Le Cam Deficiency Bounds, Canonical Mixture Posteriors, and Hockey-Stick Differential Privacy

## Abstract

Blackwell's equivalence theorem for statistical dichotomies states that a stochastic channel $K : \alpha \to \text{PMF }\beta$ is sufficient for a pair of probability distributions $(p, q)$ on a finite state space $\alpha$—meaning there exists a single prior-independent recovery kernel $R : \beta \to \text{PMF }\alpha$ such that $(p.\text{bind } K).\text{bind } R = p$ and $(q.\text{bind } K).\text{bind } R = q$—if and only if the optimal Bayes binary-decision score $V_t(p, q) = \sum_{a \in \alpha} \max(t p_a, (1-t) q_a)$ is preserved across the entire continuum of priors $t \in [0, 1]$. In the Common Ground V34 development ([`RecoveryConverseFull.lean`](./RecoveryConverseFull.lean)), this universal quantifier over $t \in [0,1]$ was reduced in the exact zero-loss case to checking at most $|\beta|$ output-determined **critical priors** $t_b = Q_b / (P_b + Q_b)$ (where $P = p.\text{bind } K$ and $Q = q.\text{bind } K$).

This paper develops and formally proves in Lean 4 the **quantitative, approximate-sufficiency generalization** of this reduction ([`QuantitativeCriticalSlack.lean`](./QuantitativeCriticalSlack.lean), [`AdversarialTightnessAndMarginalBound.lean`](./AdversarialTightnessAndMarginalBound.lean), and [`UnifiedSufficiencyBridge.lean`](../03-information-recovery-kl-pythagorean/UnifiedSufficiencyBridge.lean)). First, it proves that at every active output $b \in \beta$, the fiberwise $L^1$ joint reconstruction defect under the explicit sum-mixture posterior $R_{\text{mix}}(b, a) = \frac{(p_a + q_a) K(a,b)}{P_b + Q_b}$ equals **exactly twice the local Jensen slack** $2\Delta_{t_b}(b)$ at the critical prior $t_b$, simultaneously for both $p$ and $q$. Second, summing over all outputs $b \in \beta$ yields an explicit, finite-check **Le Cam Deficiency Bound**:
$$\max\big(\|P.\text{bind } R_{\text{mix}} - p\|_1,\ \|Q.\text{bind } R_{\text{mix}} - q\|_1\big) \le 2 \sum_{b : P_b + Q_b > 0} \Delta_{t_b}(b) \le 2 \sum_{b : P_b + Q_b > 0} \big(V_{t_b}(p, q) - V_{t_b}(P, Q)\big).$$
Third, adversarial stress-testing and formal tightness proofs establish that the constant factor $2$ is attained with exact equality on every deterministic observation map $g : \alpha \to \beta$, that any fixed finite prior grid $T \subset (0,1)$ can be adversarially evaded while the output-adaptive critical priors $t_b$ always detect non-sufficiency, and that $R_{\text{mix}}$ uniquely avoids the $Q_b = 0$ singularity of the canonical $Q$-relative KL reconstruction $R_{\text{ref}}(b,a) = \frac{q_a K(a,b)}{Q_b}$. Finally, the paper proves the algebraic equivalence between $V_t(p,q)$ and the $(\varepsilon, \delta)$-Differential Privacy **Hockey-Stick Divergence** $H_\gamma(p \parallel q)$ at $\gamma = (1-t)/t$.

## 1. Preliminaries and the V34 Exact Critical-Prior Theorem

Let $\alpha$ and $\beta$ be finite types (`[Fintype α]`, `[Fintype β]`), let $p, q : \alpha \to \mathbb{R}_{\ge 0}$ be normalized probability mass functions ($\sum_a p_a = \sum_a q_a = 1$), and let $K : \alpha \to \beta \to \mathbb{R}_{\ge 0}$ be a row-normalized stochastic channel ($\forall a \in \alpha, \sum_{b \in \beta} K(a,b) = 1$). Denote the pushforward (observed) distributions on $\beta$ by:
$$P_b := \sum_{a \in \alpha} p_a K(a,b), \qquad Q_b := \sum_{a \in \alpha} q_a K(a,b).$$
For any real prior weight $t \in [0, 1]$, the optimal Bayes binary-decision value (`weightedValue` in [`RecoveryConverseFull.lean`](./RecoveryConverseFull.lean)) is:
$$V_t(p, q) := \sum_{a \in \alpha} \max\big(t\,p_a,\ (1-t)\,q_a\big), \qquad V_t(P, Q) := \sum_{b \in \beta} \max\big(t\,P_b,\ (1-t)\,Q_b\big).$$
By `optimal_test_value`, $V_t(p, q)$ is the maximum over all deterministic tests $\text{test} : \alpha \to \text{Bool}$ of the prior-weighted success probability $\sum_a (\text{if test}(a)\text{ then } t p_a \text{ else } (1-t) q_a)$, attained by the likelihood-ratio test $\text{decide}((1-t) q_a \le t p_a)$.

At the equal prior $t = 1/2$, `equal_prior_max_sum` establishes $V_{1/2}(p, q) = \frac{1}{2} + \frac{1}{2} d_{\text{TV}}(p, q)$, where $d_{\text{TV}}(p, q) = \frac{1}{2} \sum_a |p_a - q_a|$. A foundational insight of the V34 Atlas ([`decision_preservation`](http://127.0.0.1:4200/preview/v34/?v=1&a=decision_preservation&s=decision-no-converse)) is that **preserving total variation distance $d_{\text{TV}}(P, Q) = d_{\text{TV}}(p, q)$ does not imply the existence of a common recovery kernel $R$**. Specifically, when two atoms $a_1, a_2$ merged into the same output $b_0$ both satisfy $p(a_i) > q(a_i)$ (so both favor $p$ at $t = 1/2$) while having unequal likelihood ratios $p(a_1)/q(a_1) \ne p(a_2)/q(a_2)$, the equal-prior test experiences zero loss, hiding the lost within-fiber distinction.

To expose any such hidden distinction, [`RecoveryConverseFull.lean`](./RecoveryConverseFull.lean) defines for each output $b \in \beta$ with $P_b + Q_b > 0$ the **critical prior**:
$$t_b := \frac{Q_b}{P_b + Q_b} \in [0, 1],$$
which is the unique prior weight at which the observed posterior at output $b$ is in exact tie:
$$t_b P_b = \frac{Q_b P_b}{P_b + Q_b} = (1 - t_b) Q_b.$$

## 2. Quantitative Critical-Prior Slack and Fiberwise $L^1$ Reconstruction

In [`QuantitativeCriticalSlack.lean`](./QuantitativeCriticalSlack.lean), we replace the qualitative equality assumption $V_{t_b}(P, Q) = V_{t_b}(p, q)$ with a quantitative analysis of the **local Jensen slack** at each output $b \in \beta$:
$$\Delta_t(b) := \left(\sum_{a \in \alpha} \max\big(t\,p_a,\ (1-t)\,q_a\big)\,K(a,b)\right) - \max\big(t\,P_b,\ (1-t)\,Q_b\big).$$

### Theorem 2.1 (Nonnegativity and Global Defect Decomposition)
*Formalized as `local_jensen_slack_nonneg` and `sum_local_slack_eq_global_defect` in [`QuantitativeCriticalSlack.lean`](./QuantitativeCriticalSlack.lean).*
For every $t \in \mathbb{R}$ and every output $b \in \beta$:
1. $\Delta_t(b) \ge 0$, and
2. $\sum_{b \in \beta} \Delta_t(b) = V_t(p, q) - V_t(P, Q) =: \delta_t$.
In particular, for every individual output $b \in \beta$, $0 \le \Delta_t(b) \le \delta_t$.

### Theorem 2.2 (Exact Proportionality-Slack Identity at a Tied Output)
*Formalized as `weighted_abs_tie_defect_eq_twice_localSlack` in [`QuantitativeCriticalSlack.lean`](./QuantitativeCriticalSlack.lean).*
Suppose output $b \in \beta$ is tied at prior $t$, meaning $t P_b = (1-t) Q_b$. Then the two one-sided coordinate slack sums are both equal to $\Delta_t(b)$:
$$\sum_{a \in \alpha} \big(\max(t p_a, (1-t) q_a) - t p_a\big)\,K(a,b) = \Delta_t(b) = \sum_{a \in \alpha} \big(\max(t p_a, (1-t) q_a) - (1-t) q_a\big)\,K(a,b),$$
and their sum equals the exact $L^1$ proportionality defect on fiber $b$:
$$\sum_{a \in \alpha} \big|t\,p_a - (1-t)\,q_a\big|\,K(a,b) = 2\,\Delta_t(b).$$

**Proof Mechanism:** For any reals $u, v \in \mathbb{R}$, the lemma `max_sub_add_max_sub_eq_abs` proves $(\max(u,v) - u) + (\max(u,v) - v) = |u - v|$ by case analysis on $u \le v$. Multiplying by $K(a,b) \ge 0$ and summing over $a \in \alpha$ using $\max(t P_b, (1-t) Q_b) = t P_b = (1-t) Q_b$ yields the identity. $\square$

### Theorem 2.3 (Exact Fiberwise $L^1$ Error of the Sum-Mixture Decoder)
*Formalized as `fiber_joint_l1_defect_eq_twice_critical_slack` in [`QuantitativeCriticalSlack.lean`](./QuantitativeCriticalSlack.lean).*
Define the explicit sum-mixture recovery kernel (`mixtureRecoverReal`):
$$R_{\text{mix}}(b, a) := \begin{cases} \dfrac{(p_a + q_a)\,K(a,b)}{P_b + Q_b} & \text{if } P_b + Q_b > 0, \\[8pt] p_a & \text{if } P_b + Q_b = 0. \end{cases}$$
Then for every active output $b \in \beta$ with $P_b + Q_b > 0$, the joint reconstruction $L^1$ defect on fiber $b$ satisfies:
$$\sum_{a \in \alpha} \big|P_b\,R_{\text{mix}}(b, a) - p_a\,K(a,b)\big| = \sum_{a \in \alpha} \big|Q_b\,R_{\text{mix}}(b, a) - q_a\,K(a,b)\big| = 2\,\Delta_{t_b}(b) \le 2\,\delta_{t_b}.$$

**Proof Mechanism:** By the algebraic identity `mixture_joint_discrepancy_identity`, for $P_b + Q_b \ne 0$:
$$P_b \cdot \frac{(p_a + q_a) K(a,b)}{P_b + Q_b} - p_a K(a,b) = \frac{P_b q_a - Q_b p_a}{P_b + Q_b} K(a,b) = (1 - t_b) q_a K(a,b) - t_b p_a K(a,b),$$
and symmetrically $Q_b R_{\text{mix}}(b,a) - q_a K(a,b) = t_b p_a K(a,b) - (1-t_b) q_a K(a,b)$. Taking absolute values and applying Theorem 2.2 at $t = t_b$ completes the proof. $\square$

## 3. Global Marginal $L^1$ Bound, Tightness, and Adversarial Stress Testing

In [`AdversarialTightnessAndMarginalBound.lean`](./AdversarialTightnessAndMarginalBound.lean), Theorem 2.3 is lifted from individual fibers to the global reconstructed marginals $(P.\text{bind } R_{\text{mix}})_a = \sum_{b \in \beta} P_b R_{\text{mix}}(b,a)$ and $(Q.\text{bind } R_{\text{mix}})_a = \sum_{b \in \beta} Q_b R_{\text{mix}}(b,a)$.

### Theorem 3.1 (Global Marginal $L^1$ Bound & Deterministic Tightness)
*Formalized as `marginal_l1_error_le_sum_fiber_joint_defect` and `deterministic_observation_marginal_l1_exact_tightness` in [`AdversarialTightnessAndMarginalBound.lean`](./AdversarialTightnessAndMarginalBound.lean).*
1. For any row-normalized stochastic channel $K$, the marginal $L^1$ reconstruction errors satisfy:
   $$\max\big(\|P.\text{bind } R_{\text{mix}} - p\|_1,\ \|Q.\text{bind } R_{\text{mix}} - q\|_1\big) \le 2 \sum_{b : P_b + Q_b > 0} \Delta_{t_b}(b) \le 2 \sum_{b : P_b + Q_b > 0} \delta_{t_b}.$$
2. **Exact Tightness on Deterministic Observations:** When $K(a,b) = \mathbf{1}_{g(a)=b}$ is induced by a deterministic observation map $g : \alpha \to \beta$, only the single fiber $b = g(a)$ contributes to the reconstructed mass at atom $a$. Consequently, there is zero cross-fiber cancellation, and the upper bound holds with **exact equality**:
   $$\|P.\text{bind } R_{\text{mix}} - p\|_1 = \|Q.\text{bind } R_{\text{mix}} - q\|_1 = 2 \sum_{b : P_b + Q_b > 0} \Delta_{t_b}(b).$$

### Summary of Exact-Rational Adversarial Validation ([`validate_adversarial.py`](./validate_adversarial.py))

All theorems were subjected to an automated exact-rational (`fractions.Fraction`) test suite across 500+ randomized channels and four targeted adversarial stress fixtures ([`ADVERSARIAL_VALIDATION_RESULTS.json`](./ADVERSARIAL_VALIDATION_RESULTS.json)):

| Adversarial Stress Test | Channel & Priors $(p, q, K)$ | Fixed-Grid Defect ($\delta_{1/2}$, etc.) | Critical Priors $t_b$ & Local Slack $\Delta_{t_b}(b)$ | Marginal Error $\|P R_{\text{mix}} - p\|_1$ vs. Bound $2\sum \Delta_{t_b}(b)$ | Key Validation Finding |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **1. Equal-Prior TV Evasion** (`test_01`) | $p=(2/5, 1/10, 1/2)$, $q=(1/10, 1/20, 17/20)$, $g=(0,0,1)$ | $\delta_{1/2} = 0$ ($d_{\text{TV}} = 7/20$ preserved) | $t_0 = 3/13 \implies \Delta_{t_0}(0) = 1/65$; $t_1 = 17/27 \implies \Delta_{t_1}(1) = 0$ | $\|P R_{\text{mix}} - p\|_1 = 2/65 = 2 \sum \Delta_{t_b}(b)$ (**Ratio = 1.000**) | Confirms exact attainment of the factor $2$ and exposes the hidden 4:1 vs. 2:1 likelihood-ratio mismatch at $t_0 = 3/13$. |
| **2. Recoverable Twin** (`test_02`) | $p=(2/5, 1/10, 1/2)$, $q_R=(3/25, 3/100, 17/20)$, $g=(0,0,1)$ | $\delta_t = 0\ \forall t \in [0,1]$ | $t_0 = 3/13 \implies \Delta = 0$; $t_1 = 17/27 \implies \Delta = 0$ | $\|P R_{\text{mix}} - p\|_1 = 0$, and $R_{\text{mix}} = R_{\text{ref}}$ | Verifies `UnifiedSufficiencyBridge`: when critical balance holds, `mixtureRecover` and `nativeReferenceRecover` are identical. |
| **3. Multi-Grid Evasion** (`test_03`) | $p=(8/15, 1/5, 4/15, 0)$, $q=(1/30, 1/30, 14/15, 0)$, $g=(0,0,1,1)$ | $\delta_{1/4} = \delta_{1/2} = \delta_{3/4} = 0$ (evades 3-point grid!) | $t_0 = 1/12 \implies \Delta_{t_0}(0) = 1/72$; $t_1 = 7/9 \implies \Delta_{t_1}(1) = 0$ | $\|P R_{\text{mix}} - p\|_1 = 1/36 = 2 \sum \Delta_{t_b}(b)$ (**Ratio = 1.000**) | Proves `two_atom_fiber_evasion_and_critical_determinant`: any fixed grid $T$ is evaded if merged ratios lie on one side of $(1-t)/t$, but $t_0 = 1/12$ bisects ratios $16$ and $6$ at slope $11$. |
| **4. Singular $Q_b = 0$ Boundary** (`test_04`) | $p=(1/2, 0, 1/2)$, $q=(0, 0, 1)$, $g=(0,0,1)$ | $\delta_t = 0\ \forall t \in [0,1]$ | $t_0 = 0 \implies \Delta_0(0) = 0$; $t_1 = 2/3 \implies \Delta_{2/3}(1) = 0$ | $\|P R_{\text{mix}} - p\|_1 = 0$, whereas $\|P R_{\text{ref}} - p\|_1 = 2/3$ | Demonstrates why $R_{\text{mix}}$ strictly dominates $R_{\text{ref}}$ on non-absolutely-continuous pairs ($P_0 = 1/2 > 0, Q_0 = 0$). |
| **5. 500 Random Channels** (`test_05`) | $\text{Fin } n \to \text{Fin } m$ ($n \in [2,6], m \in [2,5]$), sparse & dense | Tested across all critical priors | $\Delta_{t_b}(b) \ge 0$ verified on $100\%$ of fibers | $0$ violations across $500$ exact-rational trials | Confirms 100% soundness of all 5 theorems in `QuantitativeCriticalSlack.lean` and `AdversarialTightnessAndMarginalBound.lean`. |

## 4. Equivalence with $(\varepsilon, \delta)$-Differential Privacy Hockey-Stick Divergence

In differential privacy and hypothesis-testing privacy ($f$-DP), a randomized mechanism satisfies $(\varepsilon, \delta)$-DP on neighboring inputs with output distributions $p, q$ if and only if the **Hockey-Stick Divergence**
$$H_{e^\varepsilon}(p \parallel q) := \sum_{a \in \alpha} \max\big(p_a - e^\varepsilon q_a,\ 0\big) \le \delta.$$
Theorem `weightedValue_eq_hockeyStick` in [`QuantitativeCriticalSlack.lean`](./QuantitativeCriticalSlack.lean) proves that for any $t \in (0, 1]$ and threshold $\gamma = (1-t)/t = e^\varepsilon$ (so $t = \frac{1}{1 + e^\varepsilon}$):
$$V_t(p, q) = (1 - t)\sum_{a \in \alpha} q_a + t \cdot H_{(1-t)/t}(p \parallel q).$$
Consequently, for normalized probability distributions ($\sum_a q_a = \sum_b Q_b = 1$), the Bayes score defect $\delta_t = V_t(p, q) - V_t(P, Q)$ is strictly proportional to the Hockey-Stick privacy amplification gap:
$$V_t(p, q) - V_t(P, Q) = t \cdot \Big(H_{(1-t)/t}(p \parallel q) - H_{(1-t)/t}(P \parallel Q)\Big).$$
By Theorems 2.3 and 3.1, a post-processing channel $K$ preserves the entire $(\varepsilon, \delta)$-DP tradeoff curve $H_{e^\varepsilon}(P \parallel Q) = H_{e^\varepsilon}(p \parallel q)$ across all $\varepsilon \in \mathbb{R}$ if and only if it preserves the Hockey-Stick divergence at the **finite set of $|\beta|$ critical privacy parameters** $\varepsilon_b := \ln(P_b / Q_b)$!

## References

- [Common Ground V34 / V36 Candidate Atlas](http://127.0.0.1:4200/preview/v34/)
- [All-Prior Recovery Converse Lean Source (`RecoveryConverseFull.lean`)](http://127.0.0.1:4200/preview/v34/studies/all-prior/evidence/converse/package/src/RecoveryConverseFull.lean)
- [`QuantitativeCriticalSlack.lean`](./QuantitativeCriticalSlack.lean)
- [`AdversarialTightnessAndMarginalBound.lean`](./AdversarialTightnessAndMarginalBound.lean)
- [`UnifiedSufficiencyBridge.lean`](../03-information-recovery-kl-pythagorean/UnifiedSufficiencyBridge.lean)
- [`validate_adversarial.py`](./validate_adversarial.py)
- [`ADVERSARIAL_VALIDATION_RESULTS.json`](./ADVERSARIAL_VALIDATION_RESULTS.json)
- [`demo/index.html`](./demo/index.html)
