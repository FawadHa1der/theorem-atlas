import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Verified V34 Finite Convex Support & Moment-Matching Theorems

This file combines the verified V34 Lean 4 sources for:
1. `CommonGround.FiniteConvexApproximation.exists_small_support_of_mem_convexHull`
2. `CommonGround.FiniteConvexApproximation.exists_small_support_approx_of_mem_closedConvexHull`
3. `CommonGround.MomentMatching.exists_small_positive_support_matching_observables`
-/

namespace CommonGround.FiniteConvexApproximation
open scoped BigOperators
universe u v

/-- An ordinary convex-hull point has a representation on at most dim(V)+1
orbit indices. No finiteness assumption is imposed on the original index type. -/
theorem exists_small_support_of_mem_convexHull
    {I : Type u} {V : Type v}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (orbit : I → V) {x : V} (hx : x ∈ convexHull ℝ (Set.range orbit)) :
    ∃ (s : Finset I) (w : I → ℝ),
      s.card ≤ Module.finrank ℝ V + 1 ∧
      (∀ i ∈ s, 0 ≤ w i) ∧
      (∑ i ∈ s, w i) = 1 ∧
      (∑ i ∈ s, w i • orbit i) = x := by
  classical
  obtain ⟨J, hJ, z, a, hz, haff, hpos, hsum, heq⟩ := eq_pos_convex_span_of_mem_convexHull hx
  let j : J → I := fun k => Classical.choose (hz (Set.mem_range_self k))
  have hj : ∀ k, orbit (j k) = z k := fun k => Classical.choose_spec (hz (Set.mem_range_self k))
  have hinj : Function.Injective j :=
    fun k l h => haff.injective ((hj k).symm.trans ((congrArg orbit h).trans (hj l)))
  refine ⟨Finset.univ.image j, Function.extend j a (fun _ => 0), ?_, ?_, ?_, ?_⟩
  · exact (Finset.card_image_le.trans_eq Finset.card_univ).trans
      (haff.card_le_finrank_succ.trans
        (Nat.add_le_add_right (Submodule.finrank_le (vectorSpan ℝ (Set.range z))) 1))
  · rintro i hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
    simpa only [hinj.extend_apply] using (hpos k).le
  · simpa only [Finset.sum_image hinj.injOn, hinj.extend_apply] using hsum
  · simpa only [Finset.sum_image hinj.injOn, hinj.extend_apply, hj] using heq

end CommonGround.FiniteConvexApproximation

namespace CommonGround.MomentMatching
open scoped BigOperators
universe u

/-- A finite menu of real expectations has a representative using at most
`k + 1` original positive-support indices. This does not reconstruct the law. -/
theorem exists_small_positive_support_matching_observables
    {I : Type u} [Fintype I] (k : ℕ) (p : I → ℝ) (f : Fin k → I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∃ (s : Finset I) (w : I → ℝ),
      s.card ≤ k + 1 ∧
      (∀ i ∈ s, 0 < p i) ∧
      (∀ i ∈ s, 0 ≤ w i) ∧
      (∑ i ∈ s, w i) = 1 ∧
      (∀ j : Fin k, (∑ i ∈ s, w i * f j i) = ∑ i, p i * f j i) := by
  classical
  have hpzero : ∀ i, ¬ 0 < p i → p i = 0 :=
    fun i hi => le_antisymm (le_of_not_gt hi) (hp i)
  let J := {i : I // 0 < p i}
  have hsumJ : (∑ i : J, p i) = 1 :=
    (Finset.sum_congr_set {i | 0 < p i} p (fun i => p i)
      (fun _ _ => rfl) hpzero).symm.trans hsum
  let orbit : J → Fin k → ℝ := fun i j => f j i
  have hx : (∑ i : J, p i • orbit i) ∈ convexHull ℝ (Set.range orbit) :=
    mem_convexHull_of_exists_fintype (fun i : J => p i) orbit
      (fun i => (i.property).le) hsumJ (fun i => Set.mem_range_self i) rfl
  obtain ⟨s, w, hcard, hw, hwsum, heq⟩ :=
    FiniteConvexApproximation.exists_small_support_of_mem_convexHull orbit hx
  have heqj (j : Fin k) : (∑ i ∈ s, w i * f j i) = ∑ i : J, p i * f j i := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, orbit] using
      congrArg (fun z : Fin k → ℝ => z j) heq
  have hmom (j : Fin k) : (∑ i ∈ s, w i * f j i) = ∑ i, p i * f j i :=
    (heqj j).trans (Finset.sum_congr_set {i | 0 < p i}
      (fun i => p i * f j i) (fun i => p i * f j i) (fun _ _ => rfl)
      (fun i hi => by rw [hpzero i hi, zero_mul])).symm
  refine ⟨s.image Subtype.val, Function.extend Subtype.val w (fun _ => 0),
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Module.finrank_pi, Fintype.card_fin] using
      (Finset.card_image_le (s := s) (f := Subtype.val)).trans hcard
  · simpa only [Finset.forall_mem_image] using (fun (i : J) (_ : i ∈ s) => i.property)
  · simpa only [Finset.forall_mem_image, Subtype.val_injective.extend_apply] using hw
  · simpa only [Finset.sum_image Subtype.val_injective.injOn,
      Subtype.val_injective.extend_apply] using hwsum
  · simpa only [Finset.sum_image Subtype.val_injective.injOn,
      Subtype.val_injective.extend_apply] using hmom

end CommonGround.MomentMatching
