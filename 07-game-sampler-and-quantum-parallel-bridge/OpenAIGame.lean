import QuantumParallelRepetition
import FiniteSampler

namespace CommonGround.OpenAIGame
open scoped BigOperators
open QuantumParallelRepetition
noncomputable section

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem joint_normalized (G : Game X Y A B) :
    ∑ z : X × Y, G.questionWeight z.1 z.2 = 1 := by
  simpa only [Fintype.sum_prod_type] using G.weight_normalized

def jointPMF (G : Game X Y A B) : PMF (X × Y) :=
  realPMF (fun z => G.questionWeight z.1 z.2)
    (fun z => G.weight_nonneg z.1 z.2) (joint_normalized G)

def marginalPMF (G : Game X Y A B) : PMF X :=
  realPMF G.marginalX G.marginalX_nonneg G.marginalX_normalized

def conditionalPMF (G : Game X Y A B) (fallback : X → PMF Y) : X → PMF Y :=
  completeConditional G.marginalX G.conditionalYGivenX G.conditionalYGivenX_nonneg
    (fun x hx => G.conditionalYGivenX_sum x
      (lt_of_le_of_ne (G.marginalX_nonneg x) (Ne.symm hx))) fallback

/-- The actual native game question-weight law equals a two-stage PMF sampling law.
The pairing endpoint is the byte-exact CSLib compatibility slice checked in this 4.32 host. -/
theorem joint_eq_sampler (G : Game X Y A B) (fallback : X → PMF Y) :
    jointPMF G = pairLaw (marginalPMF G) (conditionalPMF G fallback) := by
  exact finiteJoint_eq_bind (fun z => G.questionWeight z.1 z.2)
    G.marginalX G.conditionalYGivenX (fun z => G.weight_nonneg z.1 z.2)
    G.marginalX_nonneg G.conditionalYGivenX_nonneg (joint_normalized G)
    G.marginalX_normalized
    (fun x hx => G.conditionalYGivenX_sum x
      (lt_of_le_of_ne (G.marginalX_nonneg x) (Ne.symm hx)))
    G.marginalX_mul_conditionalYGivenX fallback

theorem sampler_fallback_independent (G : Game X Y A B) (f g : X → PMF Y) :
    pairLaw (marginalPMF G) (conditionalPMF G f) =
      pairLaw (marginalPMF G) (conditionalPMF G g) :=
  (joint_eq_sampler G f).symm.trans (joint_eq_sampler G g)

theorem conditionalPMF_of_zero (G : Game X Y A B) (fallback : X → PMF Y)
    (x : X) (hx : G.marginalX x = 0) : conditionalPMF G fallback x = fallback x := by
  simp only [conditionalPMF, completeConditional, dif_pos hx]

theorem conditionalPMF_apply_of_pos (G : Game X Y A B) (fallback : X → PMF Y)
    (x : X) (hx : 0 < G.marginalX x) (y : Y) :
    conditionalPMF G fallback x y = ENNReal.ofReal (G.conditionalYGivenX x y) := by
  simp only [conditionalPMF, completeConditional, dif_neg (ne_of_gt hx), realPMF_apply]

theorem source_conditional_zero_sum (G : Game X Y A B)
    (x : X) (hx : G.marginalX x = 0) : (∑ y, G.conditionalYGivenX x y) = 0 := by
  simp [Game.conditionalYGivenX, hx]

theorem conditional_unique_on_support (G : Game X Y A B) (fallback : X → PMF Y)
    (k : X → PMF Y) (h : jointPMF G = pairLaw (marginalPMF G) k)
    (x : X) (hx : 0 < G.marginalX x) : k x = conditionalPMF G fallback x := by
  apply (pairLaw_eq_iff (marginalPMF G) k (conditionalPMF G fallback)).mp
    (h.symm.trans (joint_eq_sampler G fallback)) x
  exact ne_of_gt (ENNReal.ofReal_pos.mpr hx)

/-- The actual OpenAI grouped-mass operation is the mass function of a PMF pushforward. -/
theorem groupedMass_eq_map {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (g : ι → κ) (w : ι → ℝ) (hn : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (j : κ) :
    ENNReal.ofReal (ClassicalInformation.groupedMass g w j) =
      ((realPMF w hn hs).map g) j :=
  (realPMF_map_apply w hn hs g j).symm

end
end CommonGround.OpenAIGame
