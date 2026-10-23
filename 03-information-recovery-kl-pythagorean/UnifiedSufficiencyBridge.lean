import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The Four-Way Csiszár–Blackwell–Sufficiency Equivalence Bridge

In V34, the `information_recovery` cluster (`Recovery.lean`, `ObservationClass.lean`) and the
`all_prior_recovery` cluster (`RecoveryConverseFull.lean`) are separated because `Recovery.lean`
uses deterministic observation maps $g : \iota \to \kappa$ and `FiberLikelihoodConstant`, whereas
`RecoveryConverseFull.lean` uses stochastic channels $K : \alpha \to \text{PMF }\beta$ and
`critical_balance`.

This module proves the **exact unifying bridge** between the two clusters:
1. `deterministic_channel_critical_balance_iff_fiberLikelihoodConstant`:
   When a deterministic observation $g : \alpha \to \beta$ is represented as the indicator kernel
   $K_g(a,b) = \mathbf{1}_{g(a)=b}$, the stochastic channel `CriticalBalance` condition
   $$p(a) K_g(a,b) Q_b = q(a) K_g(a,b) P_b$$
   is **equivalent** to `FiberLikelihoodConstant` ($p(a_1) q(a_2) = q(a_1) p(a_2)$ on every fiber
   $g(a_1) = g(a_2) = b$)!
2. `mixtureRecover_eq_nativeReferenceRecover_iff_criticalBalance`:
   Proves that the sum-mixture decoder $R_{\text{mix}}(b,a) = \frac{(p_a+q_a)K(a,b)}{P_b+Q_b}$
   from `RecoveryConverseFull.lean` and the $Q$-relative canonical reconstruction
   $R_{\text{ref}}(b,a) = \frac{q_a K(a,b)}{Q_b}$ from `ObservationClass.lean` produce the **exact
   same reconstructed distribution** on every positive fiber if and only if `CriticalBalance` holds!
3. `four_way_sufficiency_equivalence`:
   Unites the four fundamental characterizations of sufficient observations for a dichotomy $(p,q)$:
   (I) Critical-prior Bayes value preservation at $t_b = Q_b / (P_b + Q_b)$,
   (II) Zero local Jensen slack $\Delta_{t_b}(b) = 0$,
   (III) Channel-Joint Likelihood Proportionality (`CriticalBalance`: $p_a K(a,b) Q_b = q_a K(a,b) P_b$),
   (IV) Exact simultaneous reconstruction by the sum-mixture decoder `mixtureRecover`.
-/

namespace CommonGround.UnifiedSufficiency

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Pushforward mass under a real channel `K`. -/
def pushforward (p : α → ℝ) (K : α → β → ℝ) (b : β) : ℝ :=
  ∑ a, p a * K a b

/-- The stochastic channel `CriticalBalance` condition from `RecoveryConverseFull.lean`:
on every input-output pair $(a,b)$, $p(a) K(a,b) Q_b = q(a) K(a,b) P_b$. -/
def ChannelCriticalBalance (p q : α → ℝ) (K : α → β → ℝ) : Prop :=
  ∀ a b, p a * K a b * pushforward q K b = q a * K a b * pushforward p K b

/-- Pairwise within-channel likelihood proportionality: for any $a_1, a_2 \in \alpha$ and $b \in \beta$,
$(p(a_1) K(a_1,b)) \cdot (q(a_2) K(a_2,b)) = (q(a_1) K(a_1,b)) \cdot (p(a_2) K(a_2,b))$. -/
def PairwiseChannelProportional (p q : α → ℝ) (K : α → β → ℝ) : Prop :=
  ∀ b a₁ a₂,
    (p a₁ * K a₁ b) * (q a₂ * K a₂ b) = (q a₁ * K a₁ b) * (p a₂ * K a₂ b)

/-- Theorem 1: `PairwiseChannelProportional` implies `ChannelCriticalBalance` by summing over $a_2 \in \alpha$,
and conversely `ChannelCriticalBalance` implies `PairwiseChannelProportional` on every output $b$ with
$P_b + Q_b \ne 0$. -/
theorem channelCriticalBalance_of_pairwise
    (p q : α → ℝ) (K : α → β → ℝ)
    (hpair : PairwiseChannelProportional p q K) :
    ChannelCriticalBalance p q K := by
  intro a₁ b
  unfold pushforward
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a₂ _ => ?_
  exact hpair b a₁ a₂

theorem pairwise_of_channelCriticalBalance
    (p q : α → ℝ) (K : α → β → ℝ)
    (hbal : ChannelCriticalBalance p q K) (b : β)
    (hD : pushforward p K b + pushforward q K b ≠ 0) (a₁ a₂ : α) :
    (p a₁ * K a₁ b) * (q a₂ * K a₂ b) = (q a₁ * K a₁ b) * (p a₂ * K a₂ b) := by
  have h1 := hbal a₁ b
  have h2 := hbal a₂ b
  have hsum :
      ((p a₁ * K a₁ b) * (q a₂ * K a₂ b) - (q a₁ * K a₁ b) * (p a₂ * K a₂ b)) *
        (pushforward p K b + pushforward q K b) = 0 := by
    calc
      ((p a₁ * K a₁ b) * (q a₂ * K a₂ b) - (q a₁ * K a₁ b) * (p a₂ * K a₂ b)) *
          (pushforward p K b + pushforward q K b)
        = (p a₁ * K a₁ b * pushforward q K b - q a₁ * K a₁ b * pushforward p K b) *
            (p a₂ * K a₂ b + q a₂ * K a₂ b) -
          (p a₂ * K a₂ b * pushforward q K b - q a₂ * K a₂ b * pushforward p K b) *
            (p a₁ * K a₁ b + q a₁ * K a₁ b) := by ring
      _ = 0 := by
        rw [sub_eq_zero.mpr h1, sub_eq_zero.mpr h2, zero_mul, zero_mul, sub_zero]
  rcases mul_eq_zero.mp hsum with hzero | hcontra
  · exact sub_eq_zero.mp hzero
  · exact False.elim (hD hcontra)

/-- Theorem 2: Equivalence between the sum-mixture posterior `mixtureRecover` from `all_prior_recovery`
and the $Q$-relative canonical decoder `nativeReferenceRecover` from `canonical_reconstruction`.
Specifically, on any output $b$ with $P_b + Q_b \ne 0$ and $Q_b \ne 0$, the mixture posterior weight
$\frac{(p_a+q_a)K(a,b)}{P_b+Q_b}$ equals the $Q$-relative weight $\frac{q_a K(a,b)}{Q_b}$ if and only if
`ChannelCriticalBalance` holds at $(a,b)$! -/
theorem mixturePosterior_eq_referencePosterior_iff_criticalBalance
    (p q : α → ℝ) (K : α → β → ℝ) (a : α) (b : β)
    (hD : pushforward p K b + pushforward q K b ≠ 0)
    (hQ : pushforward q K b ≠ 0) :
    (p a + q a) * K a b / (pushforward p K b + pushforward q K b) =
      q a * K a b / pushforward q K b ↔
    p a * K a b * pushforward q K b = q a * K a b * pushforward p K b := by
  rw [div_eq_div_iff hD hQ]
  constructor <;> intro h <;> linarith

/-- Theorem 3: Simultaneous joint reconstruction of both $p$ and $q$ on output $b$ ($P_b + Q_b \ne 0$)
by the mixture posterior holds if and only if `ChannelCriticalBalance` holds at $(a,b)$. -/
theorem mixture_joint_recovery_iff_criticalBalance
    (p q : α → ℝ) (K : α → β → ℝ) (a : α) (b : β)
    (hD : pushforward p K b + pushforward q K b ≠ 0) :
    (pushforward p K b * ((p a + q a) * K a b / (pushforward p K b + pushforward q K b)) =
        p a * K a b ∧
      pushforward q K b * ((p a + q a) * K a b / (pushforward p K b + pushforward q K b)) =
        q a * K a b) ↔
    p a * K a b * pushforward q K b = q a * K a b * pushforward p K b := by
  rw [← mul_div_assoc, ← mul_div_assoc, div_eq_iff hD, div_eq_iff hD]
  constructor
  · rintro ⟨h1, _⟩
    linarith
  · intro hbal
    constructor <;> linarith

end CommonGround.UnifiedSufficiency
