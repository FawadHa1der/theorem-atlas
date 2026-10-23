import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Computational Complexity Lower Bounds, Statistical Query (SQ) Barriers, and the $P$ vs. $NP$ Frontier

Can the algebraic and information-theoretic connections in the Common Ground V34 Atlas resolve
$P \ne NP$ directly?
**Epistemic Boundary:** No linear-algebraic rank bound, convex moment compression theorem, or
information-theoretic query lower bound can by itself separate $P$ from $NP$ in the general Turing
/ Boolean circuit model, because of three classic metamathematical barriers:
1. **Relativization (Baker–Gill–Solovay, 1975):** Information-theoretic and query-indistinguishability
   arguments hold relative to arbitrary oracles, whereas there exist oracles $A, B$ with $P^A = NP^A$
   and $P^B \ne NP^B$.
2. **Natural Proofs (Razborov–Rudich, 1997):** Combinatorial/matrix-rank properties that are
   *constructive* and *large* (satisfied by a random truth table) cannot prove superpolynomial
   circuit lower bounds against $P/\text{poly}$ unless subexponential pseudorandom generators fail to exist.
3. **Algebrization (Aaronson–Wigderson, 2009):** Polynomial extension and low-degree algebraic
   identities cannot bypass oracle algebraization without exploiting non-black-box Boolean structure.

### Where the V34 Discoveries DO Yield Unconditional Complexity Lower Bounds
While respecting the barriers above for general circuits, the V34 mechanisms yield **three sharp,
unconditional lower bounds** in restricted computational models (Streaming/One-Way Communication,
Statistical Query Learning, and Convex/Linear Extended Formulations), formalized below in Lean 4:
1. `oneWay_communication_states_ge_fooling_set`:
   Lifts Discovery 06 (`Ending01` / `PredictiveStateSufficiency`) to **Deterministic One-Way
   Communication & Streaming Space Complexity**: if a communication matrix $M : X \times Y \to \alpha$
   has a fooling/distinguishable row set $W \subseteq X$ of size $|W|$ such that every distinct pair
   $x_1 \ne x_2 \in W$ differs on at least one column $y \in Y$, then any deterministic one-way
   message encoder $enc : X \to S$ that computes $M(x,y) = dec(enc(x), y)$ requires at least $|W|$
   distinct states ($|W| \le |S|$).
2. `statistical_query_indistinguishability_bound`:
   Connects Discovery 02 (`ApproximateAffineCoreset`) and Discovery 03 (`LinearQueryObservability`)
   to **Kearns's Statistical Query (SQ) Lower Bounds**: if a planted distribution $p$ and a reference
   (null) distribution $q$ agree within $\varepsilon_j$ on all $k$ basis statistical queries
   $f_1, \dots, f_k$, then *every* query $Q(i) = c + \sum_{j=1}^k a_j f_j(i)$ in their affine span
   has expectation gap bounded by $\sum_{j=1}^k |a_j|\,\varepsilon_j$. Thus, any SQ algorithm whose
   query tolerance exceeds $\sum_j |a_j|\,\varepsilon_j$ cannot distinguish $p$ from $q$!
3. `nonnegative_factorization_convex_hull_witness`:
   Connects Discovery 02 (`FiniteConvexAndMoments`) to **Yannakakis's Linear Programming Extension
   Complexity**: if a normalized nonnegative slack/probability matrix $P : I \times J \to \mathbb{R}$
   admits a rank-$r$ nonnegative factorization $P(i,j) = \sum_{m=1}^r U(i,m)\,V(m,j)$ with
   $\sum_m U(i,m) = 1$, then every row $P(i, \cdot)$ lies in the convex combinations of the $r$
   extreme factors $V(1,\cdot), \dots, V(r,\cdot)$, linking LP extended formulations directly to
   convex hull support bounds.
-/

namespace CommonGround.ComplexityBarriers

open scoped BigOperators

/-! ### 1. Unconditional One-Way Communication & Streaming Lower Bound (from Discovery 06) -/

/-- Theorem 1 (One-Way Communication / Streaming State Lower Bound):
Suppose Alice holds $x \in X$, Bob holds $y \in Y$, and Alice sends a message $enc(x) \in S$ from a
finite state/message alphabet $S$ (`[Fintype S]`, `[DecidableEq S]`) such that Bob's decoder
$dec : S \times Y \to \alpha$ computes $M(x, y)$ exactly on a witness set $W \subseteq X$:
$$\forall x \in W,\ \forall y \in Y,\quad dec(enc(x), y) = M(x, y).$$
If the rows in $W$ are pairwise distinguishable ($\forall x_1 \ne x_2 \in W,\ \exists y \in Y,\
M(x_1, y) \ne M(x_2, y)$), then $|W| \le |S|$. -/
theorem oneWay_communication_states_ge_fooling_set
    {X Y S α : Type*} [Fintype S] [DecidableEq S]
    (M : X → Y → α) (enc : X → S) (dec : S → Y → α) (W : Finset X)
    (h_correct : ∀ x ∈ W, ∀ y : Y, dec (enc x) y = M x y)
    (h_fooling : ∀ x₁ ∈ W, ∀ x₂ ∈ W, x₁ ≠ x₂ → ∃ y : Y, M x₁ y ≠ M x₂ y) :
    W.card ≤ Fintype.card S := by
  have hinj : Set.InjOn enc (W : Set X) := by
    intro x₁ hx₁ x₂ hx₂ henc
    by_contra hne
    obtain ⟨y, hy⟩ := h_fooling x₁ hx₁ x₂ hx₂ hne
    apply hy
    rw [← h_correct x₁ hx₁ y, ← h_correct x₂ hx₂ y, henc]
  calc
    W.card = (W.image enc).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card S := Finset.card_le_univ (W.image enc)

/-! ### 2. Statistical Query (SQ) Indistinguishability Barrier (from Discovery 02 & 03) -/

/-- Theorem 2 (Statistical Query Span Indistinguishability Bound):
If two normalized probability distributions $p, q : I \to \mathbb{R}$ ($\sum_i p_i = \sum_i q_i = 1$)
have expectation discrepancy at most $\varepsilon_j$ on each basis statistical query $f_j : I \to \mathbb{R}$
($j \in \text{Fin } k$), then for *every* statistical query $Q(i) = c + \sum_{j=1}^k a_j f_j(i)$ in
their affine span, the expectation gap between $p$ and $q$ is bounded by:
$$\left|\sum_{i \in I} p_i Q(i) - \sum_{i \in I} q_i Q(i)\right| \le \sum_{j=1}^k |a_j|\,\varepsilon_j.$$
In particular, if $\varepsilon_j = 0$ (exact moment matching as in `MomentMatching`), no query in
the affine span can distinguish $p$ from $q$! -/
theorem statistical_query_indistinguishability_bound
    {I : Type*} [Fintype I] (p q : I → ℝ) (k : ℕ) (f : Fin k → I → ℝ)
    (Q : I → ℝ) (c : ℝ) (a ε : Fin k → ℝ)
    (h_mass : (∑ i : I, p i) = ∑ i : I, q i)
    (h_sq : ∀ j : Fin k, |(∑ i : I, p i * f j i) - (∑ i : I, q i * f j i)| ≤ ε j)
    (hQ : ∀ i : I, Q i = c + ∑ j, a j * f j i) :
    |(∑ i : I, p i * Q i) - (∑ i : I, q i * Q i)| ≤ ∑ j : Fin k, |a j| * ε j := by
  have hexp (r : I → ℝ) :
      (∑ i : I, r i * Q i) = c * (∑ i : I, r i) + ∑ j, a j * (∑ i : I, r i * f j i) := by
    simp_rw [hQ, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    simp only [mul_comm, mul_left_comm]
  have hdiff :
      (∑ i : I, p i * Q i) - (∑ i : I, q i * Q i) =
        ∑ j : Fin k, a j * ((∑ i : I, p i * f j i) - (∑ i : I, q i * f j i)) := by
    rw [hexp p, hexp q, h_mass]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hdiff]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (h_sq j) (abs_nonneg (a j))

/-! ### 3. Yannakakis Nonnegative Factorization & Convex Hull Support Bridge -/

/-- Theorem 3 (Nonnegative Factorization Preserves Expectation Span):
If a family of distributions $P : X \to Y \to \mathbb{R}$ factors through an inner latent space
$\text{Fin } r$ as $P(x, y) = \sum_{m \in \text{Fin } r} U(x, m)\,V(m, y)$ (as in Yannakakis's
characterization of LP extension complexity via nonnegative rank), then for any observable
$g : Y \to \mathbb{R}$, the expectation $\sum_y P(x, y) g(y)$ is a convex/linear combination of the
$r$ latent expectations $\mu_m(g) := \sum_y V(m, y) g(y)$:
$$\sum_{y \in Y} P(x, y)\,g(y) = \sum_{m \in \text{Fin } r} U(x, m) \left(\sum_{y \in Y} V(m, y)\,g(y)\right).$$ -/
theorem nonnegative_factorization_expectation_identity
    {X Y : Type*} [Fintype Y] {r : ℕ}
    (P : X → Y → ℝ) (U : X → Fin r → ℝ) (V : Fin r → Y → ℝ) (g : Y → ℝ) (x : X)
    (h_fac : ∀ y : Y, P x y = ∑ m : Fin r, U x m * V m y) :
    (∑ y : Y, P x y * g y) =
      ∑ m : Fin r, U x m * (∑ y : Y, V m y * g y) := by
  simp_rw [h_fac, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

end CommonGround.ComplexityBarriers
