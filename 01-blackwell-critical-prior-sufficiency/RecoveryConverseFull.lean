module

public import Cslib.Probability.StatisticalDistance

public section

namespace CommonGround.FiniteDecision

universe u

/-- The weighted value of a deterministic binary test. True chooses the first law.
For a prior t in [0,1], this is its probability of a correct decision. -/
noncomputable def success {α : Type u} [Fintype α]
    (p q : PMF α) (t : ℝ) (test : α → Bool) : ℝ :=
  ∑ a, if test a then t * (p a).toReal else (1 - t) * (q a).toReal

/-- The finite max-sum is an attained optimum over deterministic binary tests.
The algebra holds for any real weight; the prior interpretation uses 0 ≤ t ≤ 1. -/
theorem optimal_test_value {α : Type u} [Fintype α]
    (p q : PMF α) (t : ℝ) :
    (∀ test : α → Bool, success p q t test ≤
      ∑ a, max (t * (p a).toReal) ((1 - t) * (q a).toReal)) ∧
    ∃ test : α → Bool, success p q t test =
      ∑ a, max (t * (p a).toReal) ((1 - t) * (q a).toReal) := by
  classical
  constructor
  · intro test
    unfold success
    apply Finset.sum_le_sum
    intro a _
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  · refine ⟨fun a => decide ((1 - t) * (q a).toReal ≤ t * (p a).toReal), ?_⟩
    unfold success
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : (1 - t) * (q a).toReal ≤ t * (p a).toReal
    · simp [h]
    · have h' : t * (p a).toReal ≤ (1 - t) * (q a).toReal :=
        le_of_lt (lt_of_not_ge h)
      simp [h, max_eq_right h']

end CommonGround.FiniteDecision

-- All-prior recovery development. The accepted prefix above is byte-identical.
namespace CommonGround.FiniteDecision

universe u v

private theorem sum_toReal {α : Type u} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_one, ← p.tsum_coe, tsum_fintype,
    ENNReal.toReal_sum fun a _ => p.apply_ne_top a]

private theorem bind_apply_toReal {α : Type u} {β : Type v} [Fintype α]
    (p : PMF α) (kernel : α → PMF β) (b : β) :
    ((p.bind kernel) b).toReal =
      ∑ a, (p a).toReal * (kernel a b).toReal := by
  rw [PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum fun a _ =>
      ENNReal.mul_ne_top (p.apply_ne_top a) ((kernel a).apply_ne_top b)]
  simp only [ENNReal.toReal_mul]

/-- A shared stochastic kernel cannot increase the finite weighted max-sum.
This algebra permits every real t; interpret it as a prior only for 0 ≤ t ≤ 1. -/
theorem max_sum_bind_le {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (p q : PMF α) (kernel : α → PMF β) (t : ℝ) :
    (∑ b, max (t * ((p.bind kernel) b).toReal)
      ((1 - t) * ((q.bind kernel) b).toReal)) ≤
    ∑ a, max (t * (p a).toReal) ((1 - t) * (q a).toReal) := by
  simp_rw [bind_apply_toReal, Finset.mul_sum]
  calc
    _ ≤ ∑ b, ∑ a, max (t * (p a).toReal) ((1 - t) * (q a).toReal) *
        (kernel a b).toReal := by
      refine Finset.sum_le_sum fun b _ => ?_
      refine max_le ?_ ?_
      · simpa only [mul_assoc] using
          (Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
            mul_le_mul_of_nonneg_right
              (le_max_left (t * (p a).toReal) ((1 - t) * (q a).toReal))
              (ENNReal.toReal_nonneg (a := kernel a b)))
      · simpa only [mul_assoc] using
          (Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
            mul_le_mul_of_nonneg_right
              (le_max_right (t * (p a).toReal) ((1 - t) * (q a).toReal))
              (ENNReal.toReal_nonneg (a := kernel a b)))
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, sum_toReal, mul_one]

/-- One shared recovery kernel preserves the attained binary-decision value at
 every real weight, hence at every prior in [0,1]. The attaining test may vary with t.
 Recovery concerns both laws, not identification of the hidden sample. -/
theorem optimal_test_value_bind_of_common_recovery
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (p q : PMF α) (kernel : α → PMF β) (recover : β → PMF α)
    (hp : (p.bind kernel).bind recover = p)
    (hq : (q.bind kernel).bind recover = q) :
    ∀ t : ℝ,
      (∀ test : β → Bool, success (p.bind kernel) (q.bind kernel) t test ≤
        ∑ a, max (t * (p a).toReal) ((1 - t) * (q a).toReal)) ∧
      ∃ test : β → Bool, success (p.bind kernel) (q.bind kernel) t test =
        ∑ a, max (t * (p a).toReal) ((1 - t) * (q a).toReal) := by
  intro t
  have hback := max_sum_bind_le (p.bind kernel) (q.bind kernel) recover t
  rw [hp, hq] at hback
  have heq := le_antisymm (max_sum_bind_le p q kernel t) hback
  simpa only [heq] using optimal_test_value (p.bind kernel) (q.bind kernel) t

end CommonGround.FiniteDecision

namespace CommonGround.FiniteDecision

universe u v

/-- The finite weighted optimum used in the accepted source. -/
noncomputable def weightedValue {α : Type u} [Fintype α]
    (p q : PMF α) (t : ℝ) : ℝ :=
  ∑ a, max (t * (p a).toReal) ((1 - t) * (q a).toReal)

private theorem local_value_le
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (p q : PMF α) (kernel : α → PMF β) (t : ℝ) (b : β) :
    max (t * ((p.bind kernel) b).toReal) ((1 - t) * ((q.bind kernel) b).toReal) ≤
      ∑ a, max (t * (p a).toReal) ((1 - t) * (q a).toReal) * (kernel a b).toReal := by
  simpa only [bind_apply_toReal, Finset.mul_sum, mul_assoc] using
    (max_le
      (Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
        mul_le_mul_of_nonneg_right
          (le_max_left (t * (p a).toReal) ((1 - t) * (q a).toReal))
          (ENNReal.toReal_nonneg (a := kernel a b)))
      (Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
        mul_le_mul_of_nonneg_right
          (le_max_right (t * (p a).toReal) ((1 - t) * (q a).toReal))
          (ENNReal.toReal_nonneg (a := kernel a b))))

private theorem total_local_value
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (p q : PMF α) (kernel : α → PMF β) (t : ℝ) :
    (∑ b, ∑ a, max (t * (p a).toReal) ((1 - t) * (q a).toReal) *
      (kernel a b).toReal) = weightedValue p q t := by
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_toReal, mul_one, weightedValue]

private theorem weighted_bind_sum
    {α : Type u} {β : Type v} [Fintype α]
    (p : PMF α) (kernel : α → PMF β) (t : ℝ) (b : β) :
    (∑ a, t * (p a).toReal * (kernel a b).toReal) =
      t * ((p.bind kernel) b).toReal := by
  simp only [bind_apply_toReal, Finset.mul_sum, mul_assoc]

/-- Global value preservation and one tied observed output force every incoming
weighted pair to tie. All real weights are allowed. -/
theorem weighted_tie_of_value_eq
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (p q : PMF α) (kernel : α → PMF β) (t : ℝ) (b : β)
    (hvalue : weightedValue (p.bind kernel) (q.bind kernel) t =
      weightedValue p q t)
    (htie : t * ((p.bind kernel) b).toReal =
      (1 - t) * ((q.bind kernel) b).toReal) :
    ∀ a : α, t * (p a).toReal * (kernel a b).toReal =
      (1 - t) * (q a).toReal * (kernel a b).toReal := by
  intro a
  have hrow := (Finset.sum_eq_sum_iff_of_le
    (fun c (_ : c ∈ Finset.univ) => local_value_le p q kernel t c)).mp
    (hvalue.trans (total_local_value p q kernel t).symm) b (Finset.mem_univ b)
  have hleft := (Finset.sum_eq_sum_iff_of_le
    (fun x (_ : x ∈ Finset.univ) => mul_le_mul_of_nonneg_right
      (le_max_left (t * (p x).toReal) ((1 - t) * (q x).toReal))
      (ENNReal.toReal_nonneg (a := kernel x b)))).mp
    ((weighted_bind_sum p kernel t b).trans
      ((max_eq_left (le_of_eq htie.symm)).symm.trans hrow)) a (Finset.mem_univ a)
  exact hleft.trans ((Finset.sum_eq_sum_iff_of_le
    (fun x (_ : x ∈ Finset.univ) => mul_le_mul_of_nonneg_right
      (le_max_right (t * (p x).toReal) ((1 - t) * (q x).toReal))
      (ENNReal.toReal_nonneg (a := kernel x b)))).mp
    ((weighted_bind_sum q kernel (1 - t) b).trans
      ((max_eq_right (le_of_eq htie)).symm.trans hrow)) a (Finset.mem_univ a)).symm

/-- The output-dependent prior which ties the two observed weighted masses. -/
noncomputable def criticalPrior {α : Type u} {β : Type v}
    (p q : PMF α) (kernel : α → PMF β) (b : β) : ℝ :=
  ((q.bind kernel) b).toReal /
    (((p.bind kernel) b).toReal + ((q.bind kernel) b).toReal)

private theorem mixture_total
    {α : Type u} {β : Type v} [Fintype α]
    (p q : PMF α) (kernel : α → PMF β) (b : β) :
    (∑' a, (p a + q a) * kernel a b) = (p.bind kernel) b + (q.bind kernel) b := by
  simp only [PMF.bind_apply, tsum_fintype, add_mul, Finset.sum_add_distrib]

private theorem mixture_total_toReal
    {α : Type u} {β : Type v} [Fintype α]
    (p q : PMF α) (kernel : α → PMF β) (b : β) :
    (∑' a, (p a + q a) * kernel a b).toReal =
      ((p.bind kernel) b).toReal + ((q.bind kernel) b).toReal := by
  rw [mixture_total, ENNReal.toReal_add ((p.bind kernel).apply_ne_top b)
    ((q.bind kernel).apply_ne_top b)]

private theorem mixture_total_ne_top
    {α : Type u} {β : Type v} [Fintype α]
    (p q : PMF α) (kernel : α → PMF β) (b : β) :
    (∑' a, (p a + q a) * kernel a b) ≠ ⊤ := by
  simpa only [mixture_total] using ENNReal.add_ne_top.mpr
    ⟨(p.bind kernel).apply_ne_top b, (q.bind kernel).apply_ne_top b⟩

open scoped Classical in
/-- A native normalized mixture posterior with p as the zero-output fallback. -/
private noncomputable def mixtureRecover
    {α : Type u} {β : Type v} [Fintype α]
    (p q : PMF α) (kernel : α → PMF β) : β → PMF α :=
  fun b => if hzero : (∑' a, (p a + q a) * kernel a b) = 0 then p else
    PMF.normalize (fun a => (p a + q a) * kernel a b) hzero
      (mixture_total_ne_top p q kernel b)

private theorem critical_ratio_tie {P Q : ℝ} (hD : P + Q ≠ 0) :
    Q / (P + Q) * P = (1 - Q / (P + Q)) * Q := by
  field_simp [hD]
  simp only [add_sub_cancel_right]

private theorem critical_balance
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (p q : PMF α) (kernel : α → PMF β) (b : β)
    (hD : 0 < ((p.bind kernel) b).toReal + ((q.bind kernel) b).toReal)
    (hvalue : weightedValue (p.bind kernel) (q.bind kernel) (criticalPrior p q kernel b) =
      weightedValue p q (criticalPrior p q kernel b)) (a : α) :
    (p a).toReal * (kernel a b).toReal * ((q.bind kernel) b).toReal =
      (q a).toReal * (kernel a b).toReal * ((p.bind kernel) b).toReal := by
  have ht := weighted_tie_of_value_eq p q kernel (criticalPrior p q kernel b) b
    hvalue (critical_ratio_tie (ne_of_gt hD)) a
  dsimp only [criticalPrior] at ht
  field_simp [ne_of_gt hD] at ht
  simpa only [add_sub_cancel_right, mul_comm, mul_left_comm, mul_assoc] using ht

private theorem mixture_apply
    {α : Type u} {β : Type v} [Fintype α]
    (p q : PMF α) (kernel : α → PMF β) (b : β)
    (hD : 0 < ((p.bind kernel) b).toReal + ((q.bind kernel) b).toReal) (a : α) :
    (mixtureRecover p q kernel b a).toReal =
      ((p a).toReal + (q a).toReal) * (kernel a b).toReal /
        (((p.bind kernel) b).toReal + ((q.bind kernel) b).toReal) := by
  have hne : (∑' x, (p x + q x) * kernel x b) ≠ 0 :=
    fun hz => (ne_of_gt hD) ((mixture_total_toReal p q kernel b).symm.trans
      (congrArg ENNReal.toReal hz))
  simp only [mixtureRecover, dite_eq_right hne, PMF.normalize_apply,
    ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_add (p.apply_ne_top a) (q.apply_ne_top a),
    mixture_total_toReal, div_eq_mul_inv]

private theorem real_joint {P Q x y k : ℝ} (hD : P + Q ≠ 0)
    (hbal : x * k * Q = y * k * P) :
    P * ((x + y) * k / (P + Q)) = x * k ∧
      Q * ((x + y) * k / (P + Q)) = y * k := by
  constructor <;> rw [← mul_div_assoc, div_eq_iff hD] <;> nlinarith [hbal]

private theorem bind_joint_zero
    {α : Type u} {β : Type v} [Fintype α]
    (p : PMF α) (kernel : α → PMF β) (b : β)
    (hb : ((p.bind kernel) b).toReal = 0) (a : α) :
    (p a).toReal * (kernel a b).toReal = 0 := by
  exact congr_fun ((Fintype.sum_eq_zero_iff_of_nonneg fun x =>
    mul_nonneg (ENNReal.toReal_nonneg (a := p x))
      (ENNReal.toReal_nonneg (a := kernel x b))).mp
    ((bind_apply_toReal p kernel b).symm.trans hb)) a

private theorem mixture_joint
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (p q : PMF α) (kernel : α → PMF β)
    (hvalue : ∀ b : β,
      0 < ((p.bind kernel) b).toReal + ((q.bind kernel) b).toReal →
      weightedValue (p.bind kernel) (q.bind kernel) (criticalPrior p q kernel b) =
        weightedValue p q (criticalPrior p q kernel b)) (a : α) (b : β) :
    ((p.bind kernel) b).toReal * (mixtureRecover p q kernel b a).toReal =
        (p a).toReal * (kernel a b).toReal ∧
      ((q.bind kernel) b).toReal * (mixtureRecover p q kernel b a).toReal =
        (q a).toReal * (kernel a b).toReal := by
  by_cases hD : 0 < ((p.bind kernel) b).toReal + ((q.bind kernel) b).toReal
  · simpa only [mixture_apply p q kernel b hD a] using
      real_joint (ne_of_gt hD) (critical_balance p q kernel b hD (hvalue b hD) a)
  · have hp : ((p.bind kernel) b).toReal = 0 := by
      linarith [ENNReal.toReal_nonneg (a := (p.bind kernel) b),
        ENNReal.toReal_nonneg (a := (q.bind kernel) b)]
    have hq : ((q.bind kernel) b).toReal = 0 := by
      linarith [ENNReal.toReal_nonneg (a := (q.bind kernel) b)]
    simp only [hp, hq, zero_mul, bind_joint_zero p kernel b hp a,
      bind_joint_zero q kernel b hq a, and_self]

private theorem reconstruct_of_joint
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (p : PMF α) (kernel : α → PMF β) (recover : β → PMF α)
    (hjoint : ∀ a b, ((p.bind kernel) b).toReal * (recover b a).toReal =
      (p a).toReal * (kernel a b).toReal) :
    (p.bind kernel).bind recover = p := by
  ext a : 1
  apply (ENNReal.toReal_eq_toReal_iff'
    (((p.bind kernel).bind recover).apply_ne_top a) (p.apply_ne_top a)).mp
  simpa only [hjoint, ← Finset.mul_sum, sum_toReal, mul_one] using
    bind_apply_toReal (p.bind kernel) recover a

/-- Equality at the output-dependent critical priors suffices for one stochastic
recovery of both laws. Zero-output rows use p as a normalized fallback. -/
theorem exists_common_recovery_of_critical_values
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (p q : PMF α) (kernel : α → PMF β)
    (hvalue : ∀ b : β,
      0 < ((p.bind kernel) b).toReal + ((q.bind kernel) b).toReal →
      weightedValue (p.bind kernel) (q.bind kernel) (criticalPrior p q kernel b) =
        weightedValue p q (criticalPrior p q kernel b)) :
    ∃ recover : β → PMF α,
      (p.bind kernel).bind recover = p ∧
      (q.bind kernel).bind recover = q := by
  exact ⟨mixtureRecover p q kernel,
    reconstruct_of_joint p kernel (mixtureRecover p q kernel)
      (fun a b => (mixture_joint p q kernel hvalue a b).1),
    reconstruct_of_joint q kernel (mixtureRecover p q kernel)
      (fun a b => (mixture_joint p q kernel hvalue a b).2)⟩

/-- Preserving the binary decision value for every probability prior supplies
one stochastic recovery kernel for both finite laws. -/
theorem exists_common_recovery_of_all_prior_values
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (p q : PMF α) (kernel : α → PMF β)
    (hvalue : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      weightedValue (p.bind kernel) (q.bind kernel) t = weightedValue p q t) :
    ∃ recover : β → PMF α,
      (p.bind kernel).bind recover = p ∧
      (q.bind kernel).bind recover = q := by
  refine exists_common_recovery_of_critical_values p q kernel
    (fun b hD => hvalue (criticalPrior p q kernel b) ?_ ?_)
  · exact div_nonneg (ENNReal.toReal_nonneg (a := (q.bind kernel) _)) (le_of_lt hD)
  · exact (div_le_one hD).2
      (le_add_of_nonneg_left (ENNReal.toReal_nonneg (a := (p.bind kernel) _)))

/-- All-prior value preservation is equivalent to a common stochastic recovery.
The reverse implication follows by contraction in both directions. -/
theorem all_prior_values_iff_common_recovery
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (p q : PMF α) (kernel : α → PMF β) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      weightedValue (p.bind kernel) (q.bind kernel) t = weightedValue p q t) ↔
    ∃ recover : β → PMF α,
      (p.bind kernel).bind recover = p ∧
      (q.bind kernel).bind recover = q := by
  refine ⟨exists_common_recovery_of_all_prior_values p q kernel, ?_⟩
  rintro ⟨recover, hp, hq⟩ t _ _
  apply le_antisymm (max_sum_bind_le p q kernel t)
  simpa only [hp, hq] using
    max_sum_bind_le (p.bind kernel) (q.bind kernel) recover t

end CommonGround.FiniteDecision
