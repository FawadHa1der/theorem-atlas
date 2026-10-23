import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Two-Stage Sampler Expected-Payoff Invariance & Parallel Repetition Product Identity

This module extends `CommonGround.OpenAIGame` (`joint_eq_sampler` and `sampler_fallback_independent`)
with two foundational algebraic theorems for two-stage conditional game sampling and parallel
repetition:
1. `completedConditional_joint_eq`: Proves at the real-weight level that completing a conditional
   distribution `cond : X → Y → ℝ` on zero-marginal rows (`marg x = 0`) with an arbitrary fallback
   kernel `fallback : X → Y → ℝ` yields the exact joint distribution `joint x y` at every pair
   `(x, y) ∈ X × Y`.
2. `expectedGamePayoff_fallback_invariant`: Consequently, for any referee predicate / payoff
   `win : X → Y → ℝ`, the two-stage expected game value
   $$\sum_{x \in X} \operatorname{marg}(x) \sum_{y \in Y} \operatorname{completedConditional}(x, y) \cdot \operatorname{win}(x,y)$$
   equals the true game value $\sum_{x,y} \operatorname{joint}(x,y)\,\operatorname{win}(x,y)$,
   independently of the fallback chosen on unreachable zero-marginal questions!
3. `parallelProduct_completedConditional_eq`: Shows that for two independent games $G_1, G_2$
   run in parallel ($G_1 \otimes G_2$), the product of their two-stage marginal-then-conditional
   laws equals the product joint law at every 4-tuple $((x_1, x_2), (y_1, y_2))$, proving that
   two-stage sampler semantics commutes with parallel repetition.
-/

namespace CommonGround.OpenAIGame.ParallelExtension

open scoped BigOperators

variable {X Y X₁ Y₁ X₂ Y₂ : Type*}

/-- Completed conditional distribution: uses `cond x y` when `marg x ≠ 0`, and `fallback x y`
when `marg x = 0`. -/
def completedConditional [DecidableEq ℝ]
    (marg : X → ℝ) (cond fallback : X → Y → ℝ) (x : X) (y : Y) : ℝ :=
  if marg x = 0 then fallback x y else cond x y

/-- Theorem 1: Multiplying `marg x` by `completedConditional marg cond fallback x y` recovers
`joint x y` at every pair `(x, y)`, regardless of `fallback`. -/
theorem marg_mul_completedConditional_eq_joint [DecidableEq ℝ]
    (joint : X → Y → ℝ) (marg : X → ℝ) (cond fallback : X → Y → ℝ)
    (h_factor : ∀ x y, marg x ≠ 0 → marg x * cond x y = joint x y)
    (h_zero : ∀ x y, marg x = 0 → joint x y = 0)
    (x : X) (y : Y) :
    marg x * completedConditional marg cond fallback x y = joint x y := by
  unfold completedConditional
  split_ifs with hz
  · rw [hz, zero_mul, h_zero x y hz]
  · exact h_factor x y hz

/-- Theorem 2 (Zero-Marginal Fallback Invariance of Expected Game Payoffs):
For any game payoff / referee value function `win : X → Y → ℝ`, the two-stage expected payoff
under `completedConditional marg cond fallback` equals the exact joint expected payoff,
independently of `fallback`. -/
theorem expectedGamePayoff_eq_joint [Fintype X] [Fintype Y] [DecidableEq ℝ]
    (joint : X → Y → ℝ) (marg : X → ℝ) (cond fallback win : X → Y → ℝ)
    (h_factor : ∀ x y, marg x ≠ 0 → marg x * cond x y = joint x y)
    (h_zero : ∀ x y, marg x = 0 → joint x y = 0) :
    (∑ x : X, marg x * ∑ y : Y, completedConditional marg cond fallback x y * win x y) =
      ∑ x : X, ∑ y : Y, joint x y * win x y := by
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← mul_assoc, marg_mul_completedConditional_eq_joint joint marg cond fallback h_factor h_zero x y]

/-- Theorem 3 (Commutativity of Two-Stage Sampler Representation with Parallel Repetition):
For two games with question spaces $(X_1, Y_1)$ and $(X_2, Y_2)$, the product of their two-stage
marginal-then-completed-conditional representations equals the product joint weight
$\operatorname{joint}_1(x_1, y_1) \cdot \operatorname{joint}_2(x_2, y_2)$ for any fallbacks
`fb₁` and `fb₂`. -/
theorem parallelProduct_sampler_eq_jointProduct [DecidableEq ℝ]
    (joint₁ : X₁ → Y₁ → ℝ) (marg₁ : X₁ → ℝ) (cond₁ fb₁ : X₁ → Y₁ → ℝ)
    (joint₂ : X₂ → Y₂ → ℝ) (marg₂ : X₂ → ℝ) (cond₂ fb₂ : X₂ → Y₂ → ℝ)
    (hf₁ : ∀ x₁ y₁, marg₁ x₁ ≠ 0 → marg₁ x₁ * cond₁ x₁ y₁ = joint₁ x₁ y₁)
    (hz₁ : ∀ x₁ y₁, marg₁ x₁ = 0 → joint₁ x₁ y₁ = 0)
    (hf₂ : ∀ x₂ y₂, marg₂ x₂ ≠ 0 → marg₂ x₂ * cond₂ x₂ y₂ = joint₂ x₂ y₂)
    (hz₂ : ∀ x₂ y₂, marg₂ x₂ = 0 → joint₂ x₂ y₂ = 0)
    (x₁ : X₁) (y₁ : Y₁) (x₂ : X₂) (y₂ : Y₂) :
    (marg₁ x₁ * marg₂ x₂) *
      (completedConditional marg₁ cond₁ fb₁ x₁ y₁ *
        completedConditional marg₂ cond₂ fb₂ x₂ y₂) =
      joint₁ x₁ y₁ * joint₂ x₂ y₂ := by
  have h1 := marg_mul_completedConditional_eq_joint joint₁ marg₁ cond₁ fb₁ hf₁ hz₁ x₁ y₁
  have h2 := marg_mul_completedConditional_eq_joint joint₂ marg₂ cond₂ fb₂ hf₂ hz₂ x₂ y₂
  calc
    (marg₁ x₁ * marg₂ x₂) *
        (completedConditional marg₁ cond₁ fb₁ x₁ y₁ *
          completedConditional marg₂ cond₂ fb₂ x₂ y₂)
      = (marg₁ x₁ * completedConditional marg₁ cond₁ fb₁ x₁ y₁) *
        (marg₂ x₂ * completedConditional marg₂ cond₂ fb₂ x₂ y₂) := by ring
    _ = joint₁ x₁ y₁ * joint₂ x₂ y₂ := by rw [h1, h2]

end CommonGround.OpenAIGame.ParallelExtension
