import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# $(\varepsilon, \eta)$-Approximate Universal Affine Query Compression & Coreset Transfer

This module extends `CommonGround.ObservableSpan` to the **approximate coreset and misspecified
feature regime**:
1. `affine_query_error_decomposition`: Exact algebraic decomposition of the query discrepancy
   $\sum_{i\in s} w_i q_i - \sum_{i\in t} p_i q_i$ into a mass term, a moment-discrepancy sum,
   and two pointwise feature-approximation residual sums.
2. `approx_affine_query_bound`: When the two distributions have equal total mass $M$ (e.g., $M=1$),
   their $k$ moments agree within $\varepsilon_j$, and the query $q$ is $\eta$-close in $\ell_\infty$
   to the affine span $c + \sum_j a_j f_j$, the compressed query answer differs from the full
   query answer by at most:
   $$\left|\sum_{i\in s} w_i q_i - \sum_{i\in t} p_i q_i\right| \le 2 M \eta + \sum_{j=1}^k |a_j|\,\varepsilon_j.$$
-/

namespace CommonGround.ObservableSpan.Approximate

open scoped BigOperators
universe u

/-- Pointwise affine approximation of a query `q` by constant `c` and coefficients `a`. -/
def affineApprox {I : Type u} {k : ℕ} (f : Fin k → I → ℝ) (c : ℝ) (a : Fin k → ℝ) (i : I) : ℝ :=
  c + ∑ j, a j * f j i

/-- Weighted affine expansion identity on any finite set `s`. -/
theorem sum_affineApprox {I : Type u} (s : Finset I) (p : I → ℝ)
    (k : ℕ) (f : Fin k → I → ℝ) (c : ℝ) (a : Fin k → ℝ) :
    (∑ i ∈ s, p i * affineApprox f c a i) =
      c * (∑ i ∈ s, p i) + ∑ j, a j * (∑ i ∈ s, p i * f j i) := by
  unfold affineApprox
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (s := s) (t := Finset.univ)]
  simp only [mul_comm, mul_left_comm]

/-- Exact decomposition of the difference between two weighted query sums when `q` is approximated
by `affineApprox f c a`. -/
theorem query_diff_decomposition {I : Type u} (s t : Finset I)
    (w p : I → ℝ) (k : ℕ) (f : Fin k → I → ℝ)
    (q : I → ℝ) (c : ℝ) (a : Fin k → ℝ) :
    (∑ i ∈ s, w i * q i) - (∑ i ∈ t, p i * q i) =
      c * ((∑ i ∈ s, w i) - (∑ i ∈ t, p i)) +
      (∑ j, a j * ((∑ i ∈ s, w i * f j i) - (∑ i ∈ t, p i * f j i))) +
      (∑ i ∈ s, w i * (q i - affineApprox f c a i)) -
      (∑ i ∈ t, p i * (q i - affineApprox f c a i)) := by
  have hs : (∑ i ∈ s, w i * (q i - affineApprox f c a i)) =
      (∑ i ∈ s, w i * q i) - (∑ i ∈ s, w i * affineApprox f c a i) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  have ht : (∑ i ∈ t, p i * (q i - affineApprox f c a i)) =
      (∑ i ∈ t, p i * q i) - (∑ i ∈ t, p i * affineApprox f c a i) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  have hmom : (∑ j, a j * ((∑ i ∈ s, w i * f j i) - (∑ i ∈ t, p i * f j i))) =
      (∑ j, a j * (∑ i ∈ s, w i * f j i)) - (∑ j, a j * (∑ i ∈ t, p i * f j i)) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [hs, ht, hmom, sum_affineApprox, sum_affineApprox]
  ring

/-- Helper bound: for nonnegative weights `w` on `s` and $\ell_\infty$ residual bound $\eta$,
$|\sum_{i\in s} w_i r_i| \le \eta \sum_{i\in s} w_i$. -/
theorem abs_sum_mul_residual_le {I : Type u} (s : Finset I) (w r : I → ℝ) (η : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hr : ∀ i ∈ s, |r i| ≤ η) :
    |∑ i ∈ s, w i * r i| ≤ (∑ i ∈ s, w i) * η := by
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_of_nonneg (hw i hi)]
  exact mul_le_mul_of_nonneg_left (hr i hi) (hw i hi)

/-- Master $(\varepsilon, \eta)$-Approximate Affine Query Compression Bound:
If `w` on `s` and `p` on `t` are nonnegative with equal total mass `M` (for instance `M = 1`),
their $k$ feature moments agree within $\varepsilon_j$, and the query $q$ is within $\eta$ of
`affineApprox f c a` on both supports, then the compressed sum approximates the full sum within
$2 M \eta + \sum_j |a_j| \varepsilon_j$. -/
theorem approx_affine_query_bound {I : Type u} (s t : Finset I)
    (w p : I → ℝ) (k : ℕ) (f : Fin k → I → ℝ)
    (q : I → ℝ) (c : ℝ) (a ε : Fin k → ℝ) (M η : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hp : ∀ i ∈ t, 0 ≤ p i)
    (hws : (∑ i ∈ s, w i) = M) (hps : (∑ i ∈ t, p i) = M)
    (hmom : ∀ j, |(∑ i ∈ s, w i * f j i) - (∑ i ∈ t, p i * f j i)| ≤ ε j)
    (hqs : ∀ i ∈ s, |q i - affineApprox f c a i| ≤ η)
    (hqt : ∀ i ∈ t, |q i - affineApprox f c a i| ≤ η) :
    |(∑ i ∈ s, w i * q i) - (∑ i ∈ t, p i * q i)| ≤
      2 * M * η + ∑ j, |a j| * ε j := by
  rw [query_diff_decomposition s t w p k f q c a, hws, hps, sub_self, mul_zero, zero_add]
  have h1 : |∑ j, a j * ((∑ i ∈ s, w i * f j i) - (∑ i ∈ t, p i * f j i))| ≤
      ∑ j, |a j| * ε j := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hmom j) (abs_nonneg (a j))
  have h2 : |∑ i ∈ s, w i * (q i - affineApprox f c a i)| ≤ M * η := by
    rw [← hws]
    exact abs_sum_mul_residual_le s w (fun i => q i - affineApprox f c a i) η hw hqs
  have h3 : |∑ i ∈ t, p i * (q i - affineApprox f c a i)| ≤ M * η := by
    rw [← hps]
    exact abs_sum_mul_residual_le t p (fun i => q i - affineApprox f c a i) η hp hqt
  have htri1 := abs_sub (∑ j, a j * ((∑ i ∈ s, w i * f j i) - (∑ i ∈ t, p i * f j i)) +
    ∑ i ∈ s, w i * (q i - affineApprox f c a i)) (∑ i ∈ t, p i * (q i - affineApprox f c a i))
  have htri2 := abs_add (∑ j, a j * ((∑ i ∈ s, w i * f j i) - (∑ i ∈ t, p i * f j i)))
    (∑ i ∈ s, w i * (q i - affineApprox f c a i))
  linarith

end CommonGround.ObservableSpan.Approximate
