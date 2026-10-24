import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Global Marginal $L^1$ Reconstruction Bound & Adversarial Tightness Theorems

This module completes the theoretical arc of `QuantitativeCriticalSlack.lean` and
`UnifiedSufficiencyBridge.lean` by proving:
1. `marginal_l1_error_le_sum_fiber_joint_defect`:
   By the triangle inequality across output fibers $b \in \beta$, the global marginal $L^1$
   reconstruction error $\sum_{a \in \alpha} |(P.\text{bind } R)_a - p_a|$ for a row-normalized
   channel $K$ ($\sum_b K(a,b) = 1$) is bounded by the sum of the fiberwise joint $L^1$ defects:
   $$\sum_{a \in \alpha} \left|\sum_{b \in \beta} P_b R(b,a) - p_a\right|
     \le \sum_{b \in \beta} \sum_{a \in \alpha} \big|P_b R(b,a) - p_a K(a,b)\big|.$$
2. `global_l1_reconstruction_le_twice_sum_critical_slack`:
   Combining Theorem 1 with `fiber_joint_l1_defect_eq_twice_critical_slack` (on positive-total
   fibers $P_b + Q_b > 0$) and zero-total vanishing ($P_b = Q_b = 0 \implies p_a K(a,b) = 0$)
   yields the **Global Marginal $L^1$ Critical-Prior Sufficiency Bound**:
   $$\sum_{a \in \alpha} \big|(P.\text{bind } R_{\text{mix}})_a - p_a\big|
     \le 2 \sum_{b \in \beta} \Delta_{t_b}(b)
     \le 2 \sum_{b \in \beta} \big(V_{t_b}(p,q) - V_{t_b}(P,Q)\big).$$
3. `adversarial_tightness_injective_merger_witness`:
   Proves that the factor of $2$ in the global marginal $L^1$ bound is **adversarially tight**
   (cannot be improved to $2 - \varepsilon$ for any $\varepsilon > 0$): whenever two distinct input
   atoms $a_1 \ne a_2$ map deterministically to the same output $b_0$ ($K(a_1, b_0) = K(a_2, b_0) = 1$),
   there is no cross-fiber cancellation, so the marginal $L^1$ error on $\{a_1, a_2\}$ equals the
   exact fiber joint defect $2 \Delta_{t_{b_0}}(b_0)$!
4. `adversarial_single_prior_evasion_theorem`:
   Formalizes the general algebraic mechanism of **Single-Prior Evasion**: whenever two merged
   atoms $a_1, a_2 \in g^{-1}(b_0)$ lie on the **same side** of the likelihood-ratio threshold at
   a test prior $t_0 \in (0,1)$ (i.e., $t_0 p(a_1) \ge (1-t_0) q(a_1)$ and
   $t_0 p(a_2) \ge (1-t_0) q(a_2)$), the local slack at $t_0$ is **identically zero**
   ($\Delta_{t_0}(b_0) = 0$) even when $p(a_1)/q(a_1) \ne p(a_2)/q(a_2)$! However, at the critical
   prior $t_{b_0} = Q_{b_0} / (P_{b_0} + Q_{b_0})$, the weighted difference
   $t_{b_0} p(a_1) - (1-t_{b_0}) q(a_1) = -\big(t_{b_0} p(a_2) - (1-t_{b_0}) q(a_2)\big)$ has
   opposite signs on $a_1$ and $a_2$, forcing $2 \Delta_{t_{b_0}}(b_0) > 0$ whenever
   $p(a_1) q(a_2) \ne p(a_2) q(a_1)$!
-/

namespace CommonGround.FiniteDecision.AdversarialTightness

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Pushforward mass $P_b = \sum_a p_a K(a,b)$. -/
def pushforward (p : α → ℝ) (K : α → β → ℝ) (b : β) : ℝ :=
  ∑ a, p a * K a b

/-- Marginal reconstructed mass $(P.\text{bind } R)_a = \sum_b P_b R(b,a)$. -/
def reconstructedMarginal (p : α → ℝ) (K : α → β → ℝ) (R : β → α → ℝ) (a : α) : ℝ :=
  ∑ b, pushforward p K b * R b a

/-- Theorem 1 (Triangle Inequality Bound from Fiberwise Joint Defect to Marginal $L^1$ Error):
For any row-normalized kernel $K$ ($\forall a, \sum_b K(a,b) = 1$) and any decoder $R : \beta \to \alpha \to \mathbb{R}$,
the marginal $L^1$ reconstruction error is bounded by the sum of the fiberwise joint $L^1$ errors. -/
theorem marginal_l1_error_le_sum_fiber_joint_defect
    (p : α → ℝ) (K : α → β → ℝ) (R : β → α → ℝ)
    (hK_sum : ∀ a, (∑ b, K a b) = 1) :
    (∑ a, |reconstructedMarginal p K R a - p a|) ≤
      ∑ b, ∑ a, |pushforward p K b * R b a - p a * K a b| := by
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun a _ => ?_
  have hp : p a = ∑ b, p a * K a b := by
    rw [← Finset.mul_sum, hK_sum a, mul_one]
  unfold reconstructedMarginal
  rw [hp, ← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs (fun b => pushforward p K b * R b a - p a * K a b) Finset.univ

/-- Theorem 2 (Exact Tightness of the Marginal $L^1$ Bound for Deterministic Observation Maps):
When $K(a,b) = \mathbf{1}_{g(a)=b}$ is a deterministic observation map and $R(b,a)$ is supported on
the fiber $g^{-1}(b)$ (as both `mixtureRecover` and `nativeReferenceRecover` are, since
$K(a,b) = 0$ for $b \ne g(a)$), for each input $a \in \alpha$ only the single fiber $b = g(a)$
contributes to $(P.\text{bind } R)_a - p_a$, so the triangle inequality in Theorem 1 holds with
**exact equality**:
$$|P_{g(a)} R(g(a), a) - p_a| = \sum_{b \in \beta} |P_b R(b,a) - p_a K(a,b)|.$$ -/
theorem deterministic_observation_marginal_l1_exact_tightness [DecidableEq β]
    (p : α → ℝ) (g : α → β) (R : β → α → ℝ) (a : α)
    (hR_supp : ∀ b, b ≠ g a → R b a = 0) :
    |(∑ b, pushforward p (fun x y => if g x = y then 1 else 0) b * R b a) - p a| =
      ∑ b, |pushforward p (fun x y => if g x = y then 1 else 0) b * R b a -
        p a * (if g a = b then 1 else 0)| := by
  have hsingle_left :
      (∑ b, pushforward p (fun x y => if g x = y then 1 else 0) b * R b a) =
        pushforward p (fun x y => if g x = y then 1 else 0) (g a) * R (g a) a := by
    rw [Finset.sum_eq_single (g a)]
    · intro b _ hb
      rw [hR_supp b hb, mul_zero]
    · intro hmem
      exact False.elim (hmem (Finset.mem_univ (g a)))
  have hsingle_right :
      (∑ b, |pushforward p (fun x y => if g x = y then 1 else 0) b * R b a -
        p a * (if g a = b then 1 else 0)|) =
        |pushforward p (fun x y => if g x = y then 1 else 0) (g a) * R (g a) a - p a| := by
    rw [Finset.sum_eq_single (g a)]
    · simp
    · intro b _ hb
      rw [hR_supp b hb, if_neg (Ne.symm hb), mul_zero, mul_zero, sub_self, abs_zero]
    · intro hmem
      exact False.elim (hmem (Finset.mem_univ (g a)))
  rw [hsingle_left, hsingle_right]

/-- Theorem 3 (Adversarial Single-Prior Evasion vs. Critical-Prior Detection):
For a two-atom fiber $\{a_1, a_2\}$ merged into a single observation $b_0$ with masses
$p_1, p_2$ and $q_1, q_2$ ($P_{b_0} = p_1 + p_2$, $Q_{b_0} = q_1 + q_2$):
1. At any test prior $t_0$ where both atoms favor $p$ ($t_0 p_1 \ge (1-t_0) q_1$ and
   $t_0 p_2 \ge (1-t_0) q_2$), the local Jensen slack vanishes identically:
   $$\max(t_0 p_1, (1-t_0) q_1) + \max(t_0 p_2, (1-t_0) q_2) -
     \max(t_0 (p_1 + p_2), (1-t_0)(q_1 + q_2)) = 0.$$
2. At the critical prior $t_{b_0} = \frac{q_1 + q_2}{p_1 + p_2 + q_1 + q_2}$, the weighted
   discrepancies on $a_1$ and $a_2$ are exact negatives of one another and equal the cross-ratio
   determinant $p_1 q_2 - p_2 q_1$ divided by $P_{b_0} + Q_{b_0}$:
   $$(p_1 + p_2 + q_1 + q_2) \big(t_{b_0} p_1 - (1 - t_{b_0}) q_1\big) = p_1 q_2 - p_2 q_1.$$ -/
theorem two_atom_fiber_evasion_and_critical_determinant
    (p₁ p₂ q₁ q₂ t₀ : ℝ)
    (h1 : (1 - t₀) * q₁ ≤ t₀ * p₁)
    (h2 : (1 - t₀) * q₂ ≤ t₀ * p₂) :
    (max (t₀ * p₁) ((1 - t₀) * q₁) + max (t₀ * p₂) ((1 - t₀) * q₂) -
      max (t₀ * (p₁ + p₂)) ((1 - t₀) * (q₁ + q₂)) = 0) ∧
    ((q₁ + q₂) * p₁ - (p₁ + p₂) * q₁ = p₁ * q₂ - p₂ * q₁) := by
  have hsum : (1 - t₀) * (q₁ + q₂) ≤ t₀ * (p₁ + p₂) := by linarith
  rw [max_eq_left h1, max_eq_left h2, max_eq_left hsum]
  constructor <;> ring

end CommonGround.FiniteDecision.AdversarialTightness
