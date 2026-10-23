import MomentMatching
import Boundary
import Mathlib.Tactic.Ring

/- Finite-sum identities for explicit coefficient witnesses.
   No converse, probability adapter, or browser certificate. -/
namespace CommonGround.ObservableSpan

open scoped BigOperators
universe u

theorem sum_affine_query {I : Type u} (s : Finset I) (p : I → ℝ)
    (k : ℕ) (f : Fin k → I → ℝ) (c : ℝ) (a : Fin k → ℝ) :
    (∑ i ∈ s, p i * (c + ∑ j, a j * f j i)) =
      c * (∑ i ∈ s, p i) + ∑ j, a j * (∑ i ∈ s, p i * f j i) := by
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (s := s) (t := Finset.univ)]
  simp only [mul_comm, mul_left_comm]

theorem affine_query_eq_of_matching {I : Type u} (s t : Finset I)
    (p r : I → ℝ) (k : ℕ) (f : Fin k → I → ℝ)
    (q : I → ℝ) (c : ℝ) (a : Fin k → ℝ)
    (hqs : ∀ i ∈ s, q i = c + ∑ j, a j * f j i)
    (hqt : ∀ i ∈ t, q i = c + ∑ j, a j * f j i)
    (hmass : (∑ i ∈ s, p i) = ∑ i ∈ t, r i)
    (hmom : ∀ j, (∑ i ∈ s, p i * f j i) = ∑ i ∈ t, r i * f j i) :
    (∑ i ∈ s, p i * q i) = ∑ i ∈ t, r i * q i := by
  have hleft : (∑ i ∈ s, p i * q i) = ∑ i ∈ s, p i * (c + ∑ j, a j * f j i) :=
    Finset.sum_congr rfl (fun i hi => congrArg (fun x => p i * x) (hqs i hi))
  have hright : (∑ i ∈ t, r i * q i) = ∑ i ∈ t, r i * (c + ∑ j, a j * f j i) :=
    Finset.sum_congr rfl (fun i hi => congrArg (fun x => r i * x) (hqt i hi))
  rw [hleft, hright, sum_affine_query, sum_affine_query, hmass]
  simp_rw [hmom]

/-- One sparse representative, chosen before the query, preserves every
explicit affine query. Values of `w` outside `s` remain unconstrained. -/
theorem exists_small_support_preserving_all_affine_queries
    {I : Type u} [Fintype I] (k : ℕ) (p : I → ℝ) (f : Fin k → I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∃ (s : Finset I) (w : I → ℝ),
      s.card ≤ k + 1 ∧
      (∀ i ∈ s, 0 < p i) ∧
      (∀ i ∈ s, 0 ≤ w i) ∧
      (∑ i ∈ s, w i) = 1 ∧
      (∀ j : Fin k, (∑ i ∈ s, w i * f j i) = ∑ i, p i * f j i) ∧
      (∀ (c : ℝ) (a : Fin k → ℝ) (q : I → ℝ),
        (∀ i, q i = c + ∑ j, a j * f j i) →
        (∑ i ∈ s, w i * q i) = ∑ i, p i * q i) := by
  obtain ⟨s, w, hcard, hpos, hw, hnorm, hmom⟩ :=
    MomentMatching.exists_small_positive_support_matching_observables k p f hp hsum
  refine ⟨s, w, hcard, hpos, hw, hnorm, hmom, ?_⟩
  intro c a q hq
  exact affine_query_eq_of_matching s Finset.univ w p k f q c a
    (fun i _ => hq i) (fun i _ => hq i) (hnorm.trans hsum.symm) hmom

theorem middleEventMass_eq_two_mean_sub_secondMoment (r : Fin 3 → ℝ) :
    MomentBoundary.middleEventMass r =
      2 * MomentBoundary.mean r - MomentBoundary.secondMoment r := by
  norm_num [MomentBoundary.middleEventMass, MomentBoundary.mean,
    MomentBoundary.secondMoment, MomentBoundary.observable, Fin.sum_univ_three]
  ring

end CommonGround.ObservableSpan
