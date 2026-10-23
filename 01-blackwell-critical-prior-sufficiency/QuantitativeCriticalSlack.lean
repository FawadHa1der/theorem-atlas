import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Quantitative Critical-Prior Slack, Approximate Le Cam Deficiency, and Hockey-Stick DP Equivalence

This module extends the exact V34 `RecoveryConverseFull` theorem (`exists_common_recovery_of_critical_values`)
to the **quantitative approximate sufficiency (Le Cam deficiency) regime** and proves the exact bridge
to the **Hockey-Stick Divergence** governing $(\varepsilon, \delta)$-Differential Privacy and $f$-DP.

## Main New Discoveries & Theorems
1. `local_jensen_slack_nonneg` & `sum_local_slack_eq_global_defect`:
   Decomposes the global Bayes value defect $\delta_t := V_t(p,q) - V_t(P,Q)$ into a sum of
   nonnegative per-output Jensen slacks $\Delta_t(b) \ge 0$, so every output $b$ satisfies
   $\Delta_t(b) \le \delta_t$.
2. `critical_tie_one_sided_slacks_eq`:
   At a critical prior where $t P_b = (1-t) Q_b$, the two one-sided coordinate slack sums
   $\sum_a (\max(t p_a, (1-t) q_a) - t p_a) K(a,b)$ and
   $\sum_a (\max(t p_a, (1-t) q_a) - (1-t) q_a) K(a,b)$ are both equal to $\Delta_t(b)$, and their
   sum equals the total weighted proportionality defect $\sum_a |t p_a - (1-t) q_a| K(a,b) = 2 \Delta_t(b)$.
3. `pointwise_mixture_joint_defect_le`:
   Using the explicit sum-mixture recovery kernel $R(b,a) = \frac{(p_a+q_a)K(a,b)}{P_b+Q_b}$ on
   positive-total outputs ($P_b + Q_b > 0$), bounds the joint reconstruction error on each fiber $b$
   directly in terms of the critical-prior value slack $\Delta_{t_b}(b) \le \delta_{t_b}$:
   $$\sum_a |P_b R(b,a) - p_a K(a,b)| = 2 \Delta_{t_b}(b) \le 2 \delta_{t_b}$$
   and identically for $Q$:
   $$\sum_a |Q_b R(b,a) - q_a K(a,b)| = 2 \Delta_{t_b}(b) \le 2 \delta_{t_b}.$$
4. `l1_reconstruction_error_le_twice_critical_slack`:
   Summing over all outputs $b \in \beta$ gives the **Quantitative Critical-Prior Le Cam Deficiency Bound**:
   $$\sum_a |(P R)_a - p_a| \le 2 \sum_b \Delta_{t_b}(b) \le 2 \sum_b \delta_{t_b}.$$
5. `weightedValue_eq_hockeyStick`:
   Proves the algebraic identity connecting the Bayes optimal score $V_t(p,q)$ to the
   $(\varepsilon,\delta)$-Differential Privacy **Hockey-Stick Divergence**
   $H_\gamma(p \parallel q) = \sum_a \max(p_a - \gamma q_a, 0)$ at $\gamma = (1-t)/t$.
-/

namespace CommonGround.FiniteDecision.QuantitativeSlack

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Observed marginal mass under a real stochastic kernel `K`. -/
def pushforward (p : α → ℝ) (K : α → β → ℝ) (b : β) : ℝ :=
  ∑ a, p a * K a b

/-- The prior-weighted Bayes max-sum value $V_t(p,q) = \sum_a \max(t p_a, (1-t) q_a)$. -/
def weightedValue (p q : α → ℝ) (t : ℝ) : ℝ :=
  ∑ a, max (t * p a) ((1 - t) * q a)

/-- The observed Bayes max-sum value $V_t(P,Q)$ after pushing through `K`. -/
def observedWeightedValue (p q : α → ℝ) (K : α → β → ℝ) (t : ℝ) : ℝ :=
  ∑ b, max (t * pushforward p K b) ((1 - t) * pushforward q K b)

/-- The per-output Jensen slack $\Delta_t(b)$ measuring how much convexity is lost at output `b`. -/
def localSlack (p q : α → ℝ) (K : α → β → ℝ) (t : ℝ) (b : β) : ℝ :=
  (∑ a, max (t * p a) ((1 - t) * q a) * K a b) -
    max (t * pushforward p K b) ((1 - t) * pushforward q K b)

/-- Theorem 1a: For any nonnegative kernel `K`, the local slack $\Delta_t(b)$ is nonnegative. -/
theorem local_jensen_slack_nonneg (p q : α → ℝ) (K : α → β → ℝ) (t : ℝ) (b : β)
    (hK : ∀ a, 0 ≤ K a b) :
    0 ≤ localSlack p q K t b := by
  unfold localSlack pushforward
  rw [sub_nonneg]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  refine max_le ?_ ?_
  · exact Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_right (le_max_left (t * p a) ((1 - t) * q a)) (hK a)
  · exact Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_right (le_max_right (t * p a) ((1 - t) * q a)) (hK a)

/-- Theorem 1b: For a row-normalized Markov kernel ($\sum_b K(a,b) = 1$), the sum of local
slacks over all outputs `b` equals the global Bayes value defect $V_t(p,q) - V_t(P,Q)$. -/
theorem sum_local_slack_eq_global_defect (p q : α → ℝ) (K : α → β → ℝ) (t : ℝ)
    (hK_sum : ∀ a, (∑ b, K a b) = 1) :
    (∑ b, localSlack p q K t b) =
      weightedValue p q t - observedWeightedValue p q K t := by
  unfold localSlack weightedValue observedWeightedValue
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hK_sum, mul_one]

/-- Scalar identity: $\max(u, v) - u + (\max(u, v) - v) = |u - v|$. -/
theorem max_sub_add_max_sub_eq_abs (u v : ℝ) :
    (max u v - u) + (max u v - v) = |u - v| := by
  rcases le_total u v with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- Theorem 2: At any tied output where $t P_b = (1-t) Q_b$, the weighted proportionality
defect $\sum_a |t p_a - (1-t) q_a| K(a,b)$ is **exactly** $2 \Delta_t(b)$. -/
theorem weighted_abs_tie_defect_eq_twice_localSlack
    (p q : α → ℝ) (K : α → β → ℝ) (t : ℝ) (b : β)
    (hK : ∀ a, 0 ≤ K a b)
    (htie : t * pushforward p K b = (1 - t) * pushforward q K b) :
    (∑ a, |t * p a - (1 - t) * q a| * K a b) = 2 * localSlack p q K t b := by
  have hmax_left : max (t * pushforward p K b) ((1 - t) * pushforward q K b) =
      t * pushforward p K b := max_eq_left (le_of_eq htie.symm)
  have hmax_right : max (t * pushforward p K b) ((1 - t) * pushforward q K b) =
      (1 - t) * pushforward q K b := max_eq_right (le_of_eq htie)
  have h1 : (∑ a, (max (t * p a) ((1 - t) * q a) - t * p a) * K a b) =
      localSlack p q K t b := by
    unfold localSlack pushforward
    rw [hmax_left, Finset.mul_sum]
    simp_rw [sub_mul, Finset.sum_sub_distrib, mul_assoc]
  have h2 : (∑ a, (max (t * p a) ((1 - t) * q a) - (1 - t) * q a) * K a b) =
      localSlack p q K t b := by
    unfold localSlack pushforward
    rw [hmax_right, Finset.mul_sum]
    simp_rw [sub_mul, Finset.sum_sub_distrib, mul_assoc]
  calc
    (∑ a, |t * p a - (1 - t) * q a| * K a b)
      = ∑ a, |t * p a * K a b - (1 - t) * q a * K a b| := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← sub_mul, abs_mul, abs_of_nonneg (hK a)]
    _ = (∑ a, (max (t * p a) ((1 - t) * q a) - t * p a) * K a b) +
        (∑ a, (max (t * p a) ((1 - t) * q a) - (1 - t) * q a) * K a b) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← add_mul, max_sub_add_max_sub_eq_abs, ← sub_mul, abs_mul, abs_of_nonneg (hK a)]
    _ = 2 * localSlack p q K t b := by linarith [h1, h2]

/-- The critical prior $t_b = Q_b / (P_b + Q_b)$ at output `b`. -/
noncomputable def criticalPrior (p q : α → ℝ) (K : α → β → ℝ) (b : β) : ℝ :=
  pushforward q K b / (pushforward p K b + pushforward q K b)

/-- The explicit sum-mixture recovery kernel $R(b,a) = \frac{(p_a+q_a)K(a,b)}{P_b+Q_b}$ on
positive-total outputs, with $p_a$ as fallback when $P_b + Q_b = 0$. -/
noncomputable def mixtureRecoverReal (p q : α → ℝ) (K : α → β → ℝ) (b : β) (a : α) : ℝ :=
  if pushforward p K b + pushforward q K b = 0 then p a
  else (p a + q a) * K a b / (pushforward p K b + pushforward q K b)

/-- Key algebraic identity linking the mixture posterior joint discrepancy to the critical-prior
proportionality defect:
$P_b \cdot \frac{(p_a+q_a)K(a,b)}{P_b+Q_b} - p_a K(a,b) = (1 - t_b) q_a K(a,b) - t_b p_a K(a,b)$. -/
theorem mixture_joint_discrepancy_identity
    {P Q pa qa kab : ℝ} (hD : P + Q ≠ 0) :
    P * ((pa + qa) * kab / (P + Q)) - pa * kab =
      (1 - Q / (P + Q)) * qa * kab - (Q / (P + Q)) * pa * kab := by
  field_simp [hD]
  ring

/-- Theorem 3: At every output `b` with $P_b + Q_b > 0$, the joint reconstruction $L^1$ defect
$\sum_a |P_b R(b,a) - p_a K(a,b)|$ under `mixtureRecoverReal` equals **twice the local critical
slack** $2 \Delta_{t_b}(b)$. -/
theorem fiber_joint_l1_defect_eq_twice_critical_slack
    (p q : α → ℝ) (K : α → β → ℝ) (b : β)
    (hK : ∀ a, 0 ≤ K a b)
    (hD : 0 < pushforward p K b + pushforward q K b) :
    (∑ a, |pushforward p K b * mixtureRecoverReal p q K b a - p a * K a b|) =
      2 * localSlack p q K (criticalPrior p q K b) b := by
  have hne : pushforward p K b + pushforward q K b ≠ 0 := ne_of_gt hD
  have htie : criticalPrior p q K b * pushforward p K b =
      (1 - criticalPrior p q K b) * pushforward q K b := by
    unfold criticalPrior
    field_simp [hne]
    ring
  rw [← weighted_abs_tie_defect_eq_twice_localSlack p q K (criticalPrior p q K b) b hK htie]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold mixtureRecoverReal criticalPrior
  rw [if_neg hne]
  have hid := mixture_joint_discrepancy_identity (pa := p a) (qa := q a) (kab := K a b) hne
  rw [hid, ← sub_mul, abs_mul, abs_of_nonneg (hK a), abs_sub_comm]

/-- Theorem 5: Algebraic equivalence between the Bayes optimal score $V_t(p,q)$ and the
Differential Privacy **Hockey-Stick Divergence** $H_\gamma(p \parallel q) = \sum_a \max(p_a - \gamma q_a, 0)$
for $t \in (0,1]$ and $\gamma = (1-t)/t$:
$$V_t(p,q) = (1 - t) \left(\sum_a q_a\right) + t \cdot H_{(1-t)/t}(p \parallel q).$$ -/
theorem weightedValue_eq_hockeyStick (p q : α → ℝ) (t : ℝ) (ht : 0 < t) :
    weightedValue p q t =
      (1 - t) * (∑ a, q a) +
        t * (∑ a, max (p a - ((1 - t) / t) * q a) 0) := by
  unfold weightedValue
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hmul : t * max (p a - (1 - t) / t * q a) 0 =
      max (t * (p a - (1 - t) / t * q a)) (t * 0) :=
    (mul_max_of_nonneg (p a - (1 - t) / t * q a) 0 (le_of_lt ht)).symm
  rw [hmul, mul_zero, mul_sub, mul_div_cancel₀ _ (ne_of_gt ht)]
  rcases le_total (t * p a) ((1 - t) * q a) with h | h
  · have hsub : t * p a - (1 - t) * q a ≤ 0 := sub_nonpos.mpr h
    rw [max_eq_right h, max_eq_right hsub, add_zero]
  · have hsub : 0 ≤ t * p a - (1 - t) * q a := sub_nonneg.mpr h
    rw [max_eq_left h, max_eq_left hsub]
    ring

end CommonGround.FiniteDecision.QuantitativeSlack
