import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Stochastic Myhill–Nerode & Predictive State Representations (PSRs)
## Uniting `Ending01` (Automata Nerode Memory) and `LinearQueryObservability` (Active-Fiber Query Identifiability)

In the Common Ground V34 Consequence Lens (`lens-data.mjs`), `query_identification` ("One specified
answer") and `ending01_memory` ("Every future acceptance answer") are contrasted as editorial peers
with "no cross-model implication".

This module proves that they are two projections of a single **Predictive State Sufficiency Theorem**:
1. Let `H` be a type of histories, `M` a type of memory states, `g : H → M` a state-abstraction map,
   and `Φ : Z → H → ℝ` a family of future test payoffs indexed by future suffixes/tests `z : Z`
   (for deterministic automata, $\Phi(z, h) = \mathbf{1}_L(h \mathbin{+\!\!+} z)$; for stochastic
   processes / PSRs, $\Phi(z, h) = \mathbb{P}(\text{future } z \mid \text{history } h)$).
2. Two histories $h_1, h_2 \in H$ are **Predictively Nerode Equivalent** (`PredictiveNerodeEquiv Φ h₁ h₂`)
   iff $\forall z : Z,\ \Phi(z, h_1) = \Phi(z, h_2)$.
3. `active_fiber_constancy_iff_nerode_merge`: Every future test query $\Phi(z, \cdot)$ is constant
   on the active $Q$-supported fibers of $g$ (the exact condition of
   `LinearQueryObservability.query_identifiable_iff_active_fibers` applied across all $z \in Z$)
   if and only if `g` only merges Predictively Nerode Equivalent histories!
4. `memory_card_ge_distinguishable_witnesses`: If a finite set `W : Finset H` of active histories
   is pairwise separated by at least one future test $z \in Z$ ($\neg \text{PredictiveNerodeEquiv }\Phi\ h_1\ h_2$),
   then any state map `g : H → M` that satisfies active-fiber query identifiability for the family `Φ`
   must be injective on `W`, forcing `W.card ≤ Fintype.card M`!
-/

namespace CommonGround.PredictiveStateSufficiency

open scoped BigOperators

variable {H M Z : Type*}

/-- Two histories `h₁` and `h₂` are predictively Nerode equivalent with respect to the future-test
family `Φ : Z → H → ℝ` iff they yield identical expected payoffs for every future test `z : Z`. -/
def PredictiveNerodeEquiv (Φ : Z → H → ℝ) (h₁ h₂ : H) : Prop :=
  ∀ z : Z, Φ z h₁ = Φ z h₂

theorem predictiveNerodeEquiv_refl (Φ : Z → H → ℝ) (h : H) :
    PredictiveNerodeEquiv Φ h h :=
  fun _ => rfl

theorem predictiveNerodeEquiv_symm {Φ : Z → H → ℝ} {h₁ h₂ : H}
    (h : PredictiveNerodeEquiv Φ h₁ h₂) :
    PredictiveNerodeEquiv Φ h₂ h₁ :=
  fun z => (h z).symm

theorem predictiveNerodeEquiv_trans {Φ : Z → H → ℝ} {h₁ h₂ h₃ : H}
    (h12 : PredictiveNerodeEquiv Φ h₁ h₂) (h23 : PredictiveNerodeEquiv Φ h₂ h₃) :
    PredictiveNerodeEquiv Φ h₁ h₃ :=
  fun z => (h12 z).trans (h23 z)

/-- The active-fiber constancy condition from `LinearQueryObservability`, simultaneous across all
future tests `z : Z` on an active support predicate `Active : H → Prop`. -/
def AllFutureQueriesFiberConstant (g : H → M) (Active : H → Prop) (Φ : Z → H → ℝ) : Prop :=
  ∀ z : Z, ∀ h₁ h₂ : H, Active h₁ → Active h₂ → g h₁ = g h₂ → Φ z h₁ = Φ z h₂

/-- Theorem 1 (Bridge Between Query Identifiability and Nerode Congruence):
`AllFutureQueriesFiberConstant g Active Φ` holds if and only if every pair of active histories
mapped to the same memory state ($g(h_1) = g(h_2)$) is `PredictiveNerodeEquiv Φ h₁ h₂`. -/
theorem allFutureQueriesFiberConstant_iff_nerode_on_fibers
    (g : H → M) (Active : H → Prop) (Φ : Z → H → ℝ) :
    AllFutureQueriesFiberConstant g Active Φ ↔
      (∀ h₁ h₂ : H, Active h₁ → Active h₂ → g h₁ = g h₂ → PredictiveNerodeEquiv Φ h₁ h₂) := by
  constructor
  · intro hfib h₁ h₂ ha₁ ha₂ hg z
    exact hfib z h₁ h₂ ha₁ ha₂ hg
  · intro hner z h₁ h₂ ha₁ ha₂ hg
    exact hner h₁ h₂ ha₁ ha₂ hg z

/-- Theorem 2 (Injectivity of Sufficient Memory on Pairwise Distinguishable Witnesses):
If `g : H → M` satisfies `AllFutureQueriesFiberConstant g Active Φ`, and `W : Finset H` is a finite
set of active witness histories that are pairwise future-distinguishable
($\forall h_1 \ne h_2 \in W,\ \neg \text{PredictiveNerodeEquiv }\Phi\ h_1\ h_2$), then `g` is
injective on `W`. -/
theorem injOn_witnesses_of_allFutureQueriesFiberConstant
    (g : H → M) (Active : H → Prop) (Φ : Z → H → ℝ) (W : Finset H)
    (hfib : AllFutureQueriesFiberConstant g Active Φ)
    (hact : ∀ h ∈ W, Active h)
    (hsep : ∀ h₁ ∈ W, ∀ h₂ ∈ W, h₁ ≠ h₂ → ¬ PredictiveNerodeEquiv Φ h₁ h₂) :
    Set.InjOn g (W : Set H) := by
  intro h₁ hh₁ h₂ hh₂ hg
  by_contra hne
  apply hsep h₁ hh₁ h₂ hh₂ hne
  intro z
  exact hfib z h₁ h₂ (hact h₁ hh₁) (hact h₂ hh₂) hg

/-- Theorem 3 (Stochastic Myhill–Nerode / Predictive State Lower Bound):
Under the hypotheses of Theorem 2, any finite memory state space `M` (`[Fintype M]`, `[DecidableEq M]`)
that preserves all future test queries across active fibers must have at least `W.card` states:
$$|W| \le |M|.$$
When `Φ` is specialized to Boolean language acceptance $\mathbf{1}_{L_{01}}(h \mathbin{+\!\!+} z)$
and $W = \{[], [0], [0,1]\}$ with $|W| = 3$, this recovers `ending01_requires_three_states`! -/
theorem memory_card_ge_distinguishable_witnesses
    [Fintype M] [DecidableEq M]
    (g : H → M) (Active : H → Prop) (Φ : Z → H → ℝ) (W : Finset H)
    (hfib : AllFutureQueriesFiberConstant g Active Φ)
    (hact : ∀ h ∈ W, Active h)
    (hsep : ∀ h₁ ∈ W, ∀ h₂ ∈ W, h₁ ≠ h₂ → ¬ PredictiveNerodeEquiv Φ h₁ h₂) :
    W.card ≤ Fintype.card M := by
  have hinj := injOn_witnesses_of_allFutureQueriesFiberConstant g Active Φ W hfib hact hsep
  calc
    W.card = (W.image g).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card M := Finset.card_le_univ (W.image g)

end CommonGround.PredictiveStateSufficiency
