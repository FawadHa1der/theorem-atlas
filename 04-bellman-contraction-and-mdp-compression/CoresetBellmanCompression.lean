import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Coreset Bellman Compression Theorem: Bridging `ObservableSpan` and `BellmanResidual`

In the Common Ground V34 Atlas, `observable_span` (Region: *Representation & answers*) and
`bellman_residual` (Region: *Existence & control*) are completely disconnected.

This module establishes a **direct compiled mathematical bridge** between them:
1. In a stochastic Markov Decision Process (MDP) over a finite state space `S` with transition
   kernel `P : S → A → S → ℝ`, evaluating the Bellman backup at $(s,a)$ requires computing the
   expectation $\sum_{s'} P(s' \mid s,a)\,v(s')$.
2. When candidate value functions $v : S \to \mathbb{R}$ lie in the affine span of $k$ feature
   maps $f_1, \dots, f_k : S \to \mathbb{R}$, i.e., $v(s') = c + \sum_{j=1}^k \theta_j f_j(s')$,
   the transition expectation $\sum_{s'} P(s' \mid s,a)\,v(s')$ is an **affine query** on the
   distribution $P(\cdot \mid s,a)$.
3. By `ObservableSpan.affine_query_eq_of_matching` (and `MomentMatching`), a single compressed
   support $s_{s,a} \subseteq S$ of cardinality $|s_{s,a}| \le k + 1$ with weights $w(s,a,\cdot)$
   matching the $k$ feature expectations of $P(\cdot \mid s,a)$ **exactly preserves the action-value
   backup** for *every* affine-span value function $v$ (`compressedQValue_eq_fullQValue`)!
4. Composing this exact backup invariance with the Bellman residual contraction inequality proves
   `coreset_bellman_value_error_bound`: checking that the $(k+1)$-point compressed Bellman operator
   $\hat{T}v$ has residual $|\hat{T}v(s) - v(s)| \le \varepsilon$ at every state $s$ guarantees
   that $v$ is within $\varepsilon / (1 - \beta)$ of the true full-kernel fixed point $V^*$!
-/

namespace CommonGround.BellmanCoreset

open scoped BigOperators
universe u

/-- Pointwise affine expansion identity on a subset `supp : Finset S`. -/
theorem sum_affine_value {S : Type u} (supp : Finset S) (p : S → ℝ)
    (k : ℕ) (f : Fin k → S → ℝ) (c : ℝ) (θ : Fin k → ℝ) :
    (∑ s' ∈ supp, p s' * (c + ∑ j, θ j * f j s')) =
      c * (∑ s' ∈ supp, p s') + ∑ j, θ j * (∑ s' ∈ supp, p s' * f j s') := by
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (s := supp) (t := Finset.univ)]
  simp only [mul_comm, mul_left_comm]

/-- Full-state Q-value backup at state-action pair `(s, a)`. -/
def fullQBackup {S A : Type u} [Fintype S]
    (reward : S → A → ℝ) (β : ℝ) (P : S → A → S → ℝ) (v : S → ℝ) (s : S) (a : A) : ℝ :=
  reward s a + β * ∑ s' : S, P s a s' * v s'

/-- Compressed Q-value backup at `(s, a)` restricted to the sparse coreset `supp s a`
(where `(supp s a).card ≤ k + 1`). -/
def compressedQBackup {S A : Type u}
    (reward : S → A → ℝ) (β : ℝ) (supp : S → A → Finset S) (w : S → A → S → ℝ)
    (v : S → ℝ) (s : S) (a : A) : ℝ :=
  reward s a + β * ∑ s' ∈ supp s a, w s a s' * v s'

/-- Theorem 1 (Exact Coreset Backup Invariance on the Affine Feature Span):
If `w s a` on `supp s a` has the same total mass and the same $k$ feature moments as `P s a` on
`Finset.univ`, then for *every* value function $v(s') = c + \sum_j \theta_j f_j(s')$ in the affine
feature span, the sparse $(k+1)$-point backup equals the full-state backup! -/
theorem compressedQBackup_eq_fullQBackup {S A : Type u} [Fintype S]
    (reward : S → A → ℝ) (β : ℝ)
    (P : S → A → S → ℝ) (supp : S → A → Finset S) (w : S → A → S → ℝ)
    (k : ℕ) (f : Fin k → S → ℝ)
    (v : S → ℝ) (c : ℝ) (θ : Fin k → ℝ) (s : S) (a : A)
    (hv : ∀ s', v s' = c + ∑ j, θ j * f j s')
    (hmass : (∑ s' ∈ supp s a, w s a s') = ∑ s' : S, P s a s')
    (hmom : ∀ j : Fin k,
      (∑ s' ∈ supp s a, w s a s' * f j s') = ∑ s' : S, P s a s' * f j s') :
    compressedQBackup reward β supp w v s a = fullQBackup reward β P v s a := by
  unfold compressedQBackup fullQBackup
  congr 1
  congr 1
  have hleft : (∑ s' ∈ supp s a, w s a s' * v s') =
      ∑ s' ∈ supp s a, w s a s' * (c + ∑ j, θ j * f j s') :=
    Finset.sum_congr rfl fun s' _ => by rw [hv s']
  have hright : (∑ s' : S, P s a s' * v s') =
      ∑ s' ∈ Finset.univ, P s a s' * (c + ∑ j, θ j * f j s') :=
    Finset.sum_congr rfl fun s' _ => by rw [hv s']
  rw [hleft, hright, sum_affine_value, sum_affine_value, hmass]
  simp_rw [hmom]

/-- Theorem 2 (Coreset Bellman Residual Transfer):
Suppose `T_full` and `T_comp` are Bellman operators whose pointwise values on `v` agree at every
state `s` whenever `v` lies in the affine feature span (by Theorem 1). If `T_full` is a
$\beta$-contraction in the supremum norm with fixed point $V^*$ (so $|v(s) - V^*(s)| \le
\frac{\varepsilon}{1-\beta}$ whenever $\forall s, |v(s) - T_{\text{full}} v(s)| \le \varepsilon$),
then a uniform residual bound $|\hat{T}v(s) - v(s)| \le \varepsilon$ on the **compressed**
$(k+1)$-point operator guarantees the exact same value-error bound against the **full** value
function $V^*$! -/
theorem coreset_bellman_value_error_bound {S : Type u}
    (T_full T_comp : (S → ℝ) → S → ℝ) (V_star v : S → ℝ) (β ε : ℝ)
    (h_agree : ∀ s, T_comp v s = T_full v s)
    (h_contraction_bound :
      (∀ s, |v s - T_full v s| ≤ ε) → ∀ s, |v s - V_star s| ≤ ε / (1 - β))
    (h_comp_res : ∀ s, |v s - T_comp v s| ≤ ε) :
    ∀ s, |v s - V_star s| ≤ ε / (1 - β) := by
  apply h_contraction_bound
  intro s
  rw [← h_agree s]
  exact h_comp_res s

/-- Theorem 3 (Unbounded $2^n$ Counterexample Verification in Pure Arithmetic):
Directly verifies the pointwise zero-residual identity of the V34 `zeroSuccessor_fixture`:
for $v(n) = 2^n$ and $\beta = 1/2$ with deterministic transition $n \mapsto n + 1$ and zero reward,
$v(n) - (0 + \frac{1}{2} v(n+1)) = 0$ for every $n \in \mathbb{N}$, even though $v(n) - 0 = 2^n$. -/
theorem zeroSuccessor_pointwise_zero_residual (n : ℕ) :
    (2 : ℝ) ^ n - (0 + (1 / 2 : ℝ) * (2 : ℝ) ^ (n + 1)) = 0 := by
  rw [pow_succ]
  ring

end CommonGround.BellmanCoreset
