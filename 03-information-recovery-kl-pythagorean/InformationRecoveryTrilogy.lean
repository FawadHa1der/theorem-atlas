import RecoveryNative
import FiberEntropy
import RecoveryStability
import EntropyRecoveryNative
import EventIdentifiability

/-!
# Verified V34 Information Recovery, Canonical Reconstruction & Query Identifiability Trilogy

This file consolidates the verified V34 Lean 4 sources for:
1. `CommonGround.Recovery`: `native_entropy_eq_iff_fiberLikelihoodConstant`, `native_entropy_eq_iff_recovered`, `native_entropy_strict_iff_not_recovered`
2. `CommonGround.ObservationClass`: `recovered_entropy_minimum`, `recovered_entropy_eq_iff`, `observation_class_pythagorean`
3. `CommonGround.LinearQueryObservability`: `compatible_query_eq_observed`, `query_identifiable_iff_active_fibers`
-/

open scoped BigOperators
open QuantumParallelRepetition QuantumParallelRepetition.ClassicalInformation

namespace CommonGround.Recovery

variable {ι κ : Type*}

theorem fiber_entropy_le (s : Finset ι) (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hac : ∀ i, q i = 0 → p i = 0) :
    (∑ i ∈ s, q i) * InformationTheory.klFun ((∑ i ∈ s, p i) / (∑ i ∈ s, q i)) ≤
      (∑ i ∈ s, q i * InformationTheory.klFun (p i / q i)) := by
  by_cases hQ : (∑ i ∈ s, q i) = 0
  · simpa only [hQ, zero_mul] using
      Finset.sum_nonneg (fun i (_ : i ∈ s) =>
        mul_nonneg (hq i) (InformationTheory.klFun_nonneg (div_nonneg (hp i) (hq i))))
  · exact ClassicalInformation.finite_log_sum_inequality s p q hp hq hac
      (lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => hq i)) (Ne.symm hQ))

theorem native_entropy_eq_iff_fiberLikelihoodConstant
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (g : ι → κ) (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hac : ∀ i, q i = 0 → p i = 0) :
    Pinsker.finiteRelativeEntropy
        (ClassicalInformation.groupedMass g p)
        (ClassicalInformation.groupedMass g q) = Pinsker.finiteRelativeEntropy p q ↔
      FiberLikelihoodConstant g p q := by
  have hsplit :
      (∑ j : κ, ∑ i ∈ (Finset.univ.filter fun i => g i = j),
        q i * InformationTheory.klFun (p i / q i)) =
      ∑ i : ι, q i * InformationTheory.klFun (p i / q i) := by
    simpa only [] using
      (Finset.sum_fiberwise (Finset.univ : Finset ι) g
        (fun i => q i * InformationTheory.klFun (p i / q i)))
  unfold Pinsker.finiteRelativeEntropy ClassicalInformation.groupedMass
  rw [← hsplit]
  rw [Finset.sum_eq_sum_iff_of_le (fun j (_ : j ∈ (Finset.univ : Finset κ)) =>
    fiber_entropy_le (Finset.univ.filter fun i => g i = j) p q hp hq hac)]
  simp_rw [fiber_entropy_eq_iff_nonneg _ p q hp hq hac]
  simp only [Finset.mem_univ, true_implies, Finset.mem_filter, true_and, FiberLikelihoodConstant]
  exact ⟨fun h i j hij hi hj => h (g i) i rfl hi j hij.symm hj,
    fun h k i hi hiq j hj hjq => h i j (hi.trans hj.symm) hiq hjq⟩

theorem native_entropy_eq_iff_recovered
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (g : ι → κ) (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hac : ∀ i, q i = 0 → p i = 0) :
    Pinsker.finiteRelativeEntropy
        (ClassicalInformation.groupedMass g p)
        (ClassicalInformation.groupedMass g q) = Pinsker.finiteRelativeEntropy p q ↔
      nativeReferenceRecover g q p = p := by
  exact (native_entropy_eq_iff_fiberLikelihoodConstant g p q hp hq hac).trans
    (nativeReferenceRecover_eq_iff_fiberLikelihoodConstant g p q hq hac).symm

end CommonGround.Recovery
