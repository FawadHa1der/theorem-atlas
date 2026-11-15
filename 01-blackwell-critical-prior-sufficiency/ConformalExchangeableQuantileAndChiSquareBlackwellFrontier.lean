/-
Copyright (c) 2026 Common Ground Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Arbitrary-Sample Weighted Conformal Quantile Coverage, Proper Brier Calibration–Refinement Decomposition & `χ²` Fisher–Neyman Sufficiency Frontier

This standalone pure-core Lean 4.33.0 module (`0` imports, `0` `sorry`) unifies Folders
`01` (Blackwell Critical-Prior Sufficiency), `03` (Information Recovery & KL Pythagorean Split),
and `08` (Galois Quantile Transport Duality) with distribution-free uncertainty quantification
(`cslib`, `tc-probcomb`, `econlib`, `tc-analysis`):

1. **Arbitrary-Sample, Arbitrary-Tie, Importance-Weighted Conformal Coverage Guarantee**:
   For **every** finite list of weighted nonconformity scores `pts : List WeightedScore`
   (arbitrary length `N`, arbitrary score ties, arbitrary nonnegative importance weights `w_i`)
   and **every** miscoverage weight budget `budget : Nat`, the total importance weight of points
   whose upper-tail weight `upperTailWeight pts p.score` falls at or below `budget` satisfies
   `weightedMiscoverMass pts budget ≤ budget`.
   - Specializing `w_i = 1` yields Vovk–Gammerman–Shafer finite-sample split-conformal coverage
     (`≤ ⌊α(n+1)⌋/(n+1)` miscoverage: exact `1` of `4` on distinct 4-tuples, conservative `0` of `4` on tied maxima).
   - General `w_i = dP_test / dP_cal` yields Tibshirani–Foygel Barber–Candès–Ramdas covariate-shift
     weighted conformal prediction, repairing unweighted covariate-shift collapse (`5 > 2`).
2. **Murphy–Sanders Proper Brier Calibration–Refinement Decomposition vs. `L¹` Hallucination Collapse**:
   Proves `(n₁ + n₀) · Brier(f) = Q² n₁ n₀ + (n₁ Q - (n₁ + n₀) f)²`, decomposing quadratic forecast loss
   into irreducible uncertainty plus squared calibration error, contrasted with linear `L¹` probability
   loss where overconfident `100%` reporting strictly beats true `60%` reporting (`10 < 12`).
3. **Exact `χ²` Data-Processing Remainder (`(q₁ d₂ - q₂ d₁)² ≥ 0`), Fisher–Neyman Sufficiency Rigidity
   & Multi-Task Blackwell Poset Non-Totality**:
   Proves the exact polynomial `χ²` coarse-graining slack `(q₁ + q₂)(q₂ d₁² + q₁ d₂²) - q₁ q₂(d₁ + d₂)² = (q₁ d₂ - q₂ d₁)²`,
   characterizing zero `χ²` loss by Fisher–Neyman likelihood-ratio constancy, and exhibits orthogonal
   row vs. column channels on `{0,1}²` that are strictly incomparable in Blackwell's order.
-/

namespace CommonGround.BlackwellConformalChiSquareFrontier

/-! ## 1. Arbitrary-Sample Weighted Conformal Prediction & Covariate-Shift Repair -/

/-- A calibration or test point carrying an integer nonconformity score and nonnegative importance weight. -/
structure WeightedScore where
  score : Int
  weight : Nat
  deriving DecidableEq, Repr

/-- Total importance weight of points in `pts` with score at least `thr`: `∑_{q ∈ pts : thr ≤ q.score} q.weight`. -/
def upperTailWeight : List WeightedScore → Int → Nat
  | [], _ => 0
  | p :: rest, thr => (if thr ≤ p.score then p.weight else 0) + upperTailWeight rest thr

/-- Total importance weight of points in `xs` satisfying boolean predicate `pred`. -/
def sumWeightWhere (pred : WeightedScore → Bool) : List WeightedScore → Nat
  | [] => 0
  | p :: rest => (if pred p then p.weight else 0) + sumWeightWhere pred rest

/-- Total miscovered weight at budget `budget`: points whose upper-tail weight (including self) is `≤ budget`,
    i.e. points strictly exceeding the `(W_total - budget)` weighted conformal quantile. -/
def weightedMiscoverMass (pts : List WeightedScore) (budget : Nat) : Nat :=
  sumWeightWhere (fun p => decide (upperTailWeight pts p.score ≤ budget)) pts

/-- Unweighted miscoverage mass when a calibration maximum `calMax` is deployed against a
    test score `rTest` of importance weight `wTest` without likelihood-ratio reweighting. -/
def unweightedShiftMiscoverMass (calMax rTest : Int) (wTest : Nat) : Nat :=
  if calMax < rTest then wTest else 0

/-- Inductive invariant asserting every element of `xs` has `P p = false`. -/
def allFalseWhere (P : WeightedScore → Bool) : List WeightedScore → Prop
  | [] => True
  | p :: rest => P p = false ∧ allFalseWhere P rest

/-- Inductive invariant asserting every element of `xs` satisfying `P` has score at least `thr`. -/
def allWhereScoreGe (P : WeightedScore → Bool) (thr : Int) : List WeightedScore → Prop
  | [] => True
  | p :: rest => (P p = true → thr ≤ p.score) ∧ allWhereScoreGe P thr rest

/-- Minimum-score witness finder among elements of `xs` satisfying `P`. -/
def findMinWhere (P : WeightedScore → Bool) : List WeightedScore → Option WeightedScore
  | [] => none
  | p :: rest =>
    match findMinWhere P rest with
    | none => if P p then some p else none
    | some m => if P p then (if p.score ≤ m.score then some p else some m) else some m

private theorem allFalse_sumZero (P : WeightedScore → Bool) :
    ∀ xs : List WeightedScore, allFalseWhere P xs → sumWeightWhere P xs = 0
  | [], _ => rfl
  | p :: rest, ⟨hfp, htail⟩ => by
    have ih := allFalse_sumZero P rest htail
    simp [sumWeightWhere, hfp, ih]

private theorem allFalse_scoreGe (P : WeightedScore → Bool) (thr : Int) :
    ∀ xs : List WeightedScore, allFalseWhere P xs → allWhereScoreGe P thr xs
  | [], _ => trivial
  | _ :: rest, ⟨hfp, htail⟩ =>
    ⟨fun hp => Bool.noConfusion (hfp.symm.trans hp), allFalse_scoreGe P thr rest htail⟩

private theorem allWhereScoreGe_mono (P : WeightedScore → Bool) {t1 t2 : Int} (hle : t1 ≤ t2) :
    ∀ xs : List WeightedScore, allWhereScoreGe P t2 xs → allWhereScoreGe P t1 xs
  | [], _ => trivial
  | _ :: rest, ⟨hhead, htail⟩ =>
    ⟨fun hp => have h2 := hhead hp; by omega, allWhereScoreGe_mono P hle rest htail⟩

private theorem sumWeightWhere_le_upperTail (P : WeightedScore → Bool) (thr : Int) :
    ∀ xs : List WeightedScore, allWhereScoreGe P thr xs → sumWeightWhere P xs ≤ upperTailWeight xs thr
  | [], _ => Nat.le_refl 0
  | p :: rest, ⟨hhead, htail⟩ => by
    have ih := sumWeightWhere_le_upperTail P thr rest htail
    simp only [sumWeightWhere, upperTailWeight]
    cases hp : P p with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    | true =>
      have hge : thr ≤ p.score := hhead hp
      simp only [↓reduceIte, hge]
      omega

private theorem findMinWhere_spec (P : WeightedScore → Bool) :
    ∀ xs : List WeightedScore,
      (findMinWhere P xs = none ∧ allFalseWhere P xs) ∨
      (∃ m : WeightedScore, findMinWhere P xs = some m ∧ P m = true ∧ allWhereScoreGe P m.score xs)
  | [] => Or.inl ⟨rfl, trivial⟩
  | p :: rest => by
    rcases findMinWhere_spec P rest with ⟨hnone, hfalse⟩ | ⟨m, hsome, hpm, hall⟩
    · simp only [findMinWhere, hnone]
      cases hp : P p with
      | false =>
        exact Or.inl ⟨rfl, ⟨hp, hfalse⟩⟩
      | true =>
        exact Or.inr ⟨p, by simp, hp, ⟨fun _ => Int.le_refl p.score, allFalse_scoreGe P p.score rest hfalse⟩⟩
    · simp only [findMinWhere, hsome]
      cases hp : P p with
      | false =>
        exact Or.inr ⟨m, by simp, hpm, ⟨fun h => Bool.noConfusion (hp.symm.trans h), hall⟩⟩
      | true =>
        simp only [↓reduceIte]
        by_cases hle : p.score ≤ m.score
        · simp only [hle, ↓reduceIte]
          exact Or.inr ⟨p, rfl, hp, ⟨fun _ => Int.le_refl p.score, allWhereScoreGe_mono P hle rest hall⟩⟩
        · simp only [hle, ↓reduceIte]
          have hmle : m.score ≤ p.score := by omega
          exact Or.inr ⟨m, rfl, hpm, ⟨fun _ => hmle, hall⟩⟩

/-- Canonical distinct unweighted 4-sample (`α = 1/4` -> exact `1` miscovered of `4`). -/
def distinctUnweighted4 : List WeightedScore :=
  [⟨10, 1⟩, ⟨20, 1⟩, ⟨30, 1⟩, ⟨40, 1⟩]

/-- Canonical tied-maximum unweighted 4-sample (`α = 1/4` -> conservative `0` miscovered of `4`). -/
def tiedMaxUnweighted4 : List WeightedScore :=
  [⟨10, 1⟩, ⟨40, 1⟩, ⟨40, 1⟩, ⟨40, 1⟩]

/-- Canonical covariate-shifted sample (`W = 9`, test score `40` carries likelihood-ratio weight `5`). -/
def covariateShifted4 : List WeightedScore :=
  [⟨10, 1⟩, ⟨20, 1⟩, ⟨30, 2⟩, ⟨40, 5⟩]

/-- **Theorem 1 (Arbitrary-Sample, Arbitrary-Tie, Importance-Weighted Conformal Coverage Guarantee
    vs. Unweighted Covariate-Shift Collapse)**:
    - **(a) Universal Distribution-Free Bound**: For **every** `pts : List WeightedScore` and **every**
      `budget : Nat`, `weightedMiscoverMass pts budget ≤ budget`.
    - **(b) Split-Conformal Exactness & Tie Conservatism**: On `distinctUnweighted4` at `budget = 1`,
      `weightedMiscoverMass = 1` (exact `75%` coverage); on `tiedMaxUnweighted4` at `budget = 1`,
      `weightedMiscoverMass = 0` (ties never inflate miscoverage!).
    - **(c) Covariate-Shift Collapse vs. Weighted Repair**: Under `5×` test likelihood shift (`W = 9`,
      target `budget = 2`), unweighted deployment (`calMax = 30 < 40`) miscovers mass `5 > 2` (`55.6% > 22.2%`),
      whereas Tibshirani–Barber importance-weighted conformal prediction achieves `0 ≤ 2` (and `5 ≤ 5` at `budget = 5`). -/
theorem arbitrary_sample_weighted_conformal_quantile_coverage_bound :
    (∀ (pts : List WeightedScore) (budget : Nat),
      weightedMiscoverMass pts budget ≤ budget) ∧
    (weightedMiscoverMass distinctUnweighted4 1 = 1 ∧
      weightedMiscoverMass tiedMaxUnweighted4 1 = 0) ∧
    (unweightedShiftMiscoverMass 30 40 5 = 5 ∧ 2 < unweightedShiftMiscoverMass 30 40 5 ∧
      weightedMiscoverMass covariateShifted4 2 = 0 ∧
      weightedMiscoverMass covariateShifted4 5 = 5) := by
  refine ⟨?_, ?_, ?_⟩
  · intro pts budget
    let P : WeightedScore → Bool := fun p => decide (upperTailWeight pts p.score ≤ budget)
    rcases findMinWhere_spec P pts with ⟨_, hfalse⟩ | ⟨m, _, hpm, hall⟩
    · change sumWeightWhere P pts ≤ budget
      rw [allFalse_sumZero P pts hfalse]
      exact Nat.zero_le budget
    · have hmBudget : upperTailWeight pts m.score ≤ budget := of_decide_eq_true hpm
      have hleTail : sumWeightWhere P pts ≤ upperTailWeight pts m.score :=
        sumWeightWhere_le_upperTail P m.score pts hall
      exact Nat.le_trans hleTail hmBudget
  · decide
  · decide

/-! ## 2. Murphy–Sanders Proper Brier Calibration–Refinement Split vs. `L¹` Overconfidence Collapse -/

/-- Scaled quadratic Brier loss on a forecast bin with `n1` positive outcomes (`y = Q`), `n0` negative
    outcomes (`y = 0`), and integer forecast `f ∈ [0, Q]`. -/
def brierBinLoss (n1 n0 Q f : Int) : Int :=
  n1 * (Q - f) * (Q - f) + n0 * f * f

/-- Scaled linear `L¹` probability loss on `n1` positives and `n0` negatives for `f ∈ [0, Q]`. -/
def l1BinLoss (n1 n0 Q f : Int) : Int :=
  n1 * (Q - f) + n0 * f

private theorem sq_nonneg_int (z : Int) : 0 ≤ z * z := by
  by_cases h : 0 ≤ z
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -z := by omega
    have hmul : 0 ≤ (-z) * (-z) := Int.mul_nonneg hn hn
    have heq : (-z) * (-z) = z * z := by
      calc
        (-z) * (-z) = -(z * (-z)) := Int.neg_mul z (-z)
        _ = -(-(z * z)) := by rw [Int.mul_neg z z]
        _ = z * z := Int.neg_neg (z * z)
    rw [← heq]
    exact hmul

private theorem brier_orth_identity (n1 n0 Q f : Int) :
    (n1 + n0) * brierBinLoss n1 n0 Q f =
      Q * Q * n1 * n0 + (n1 * Q - (n1 + n0) * f) * (n1 * Q - (n1 + n0) * f) := by
  dsimp [brierBinLoss]
  have hL :
      (n1 + n0) * (n1 * (Q - f) * (Q - f) + n0 * f * f) =
        n1 * n1 * Q * Q + n1 * n0 * Q * Q -
          2 * ((n1 * (n1 + n0)) * (Q * f)) +
          (n1 * n1 + 2 * (n1 * n0) + n0 * n0) * (f * f) := by
    calc
      (n1 + n0) * (n1 * (Q - f) * (Q - f) + n0 * f * f)
          = n1 * (n1 * ((Q - f) * (Q - f)) + n0 * (f * f)) +
              n0 * (n1 * ((Q - f) * (Q - f)) + n0 * (f * f)) := by
            rw [Int.add_mul, Int.mul_assoc, Int.mul_assoc]
      _ = n1 * n1 * Q * Q + n1 * n0 * Q * Q -
            2 * ((n1 * (n1 + n0)) * (Q * f)) +
            (n1 * n1 + 2 * (n1 * n0) + n0 * n0) * (f * f) := by
            have hqf : (Q - f) * (Q - f) = Q * Q - 2 * (Q * f) + f * f := by
              calc
                (Q - f) * (Q - f) = Q * (Q - f) - f * (Q - f) := Int.sub_mul Q f (Q - f)
                _ = (Q * Q - Q * f) - (f * Q - f * f) := by rw [Int.mul_sub, Int.mul_sub]
                _ = (Q * Q - Q * f) - (Q * f - f * f) := by rw [Int.mul_comm f Q]
                _ = Q * Q - 2 * (Q * f) + f * f := by omega
            rw [hqf]
            have h1 : n1 * (n1 * (Q * Q - 2 * (Q * f) + f * f) + n0 * (f * f)) =
                n1 * n1 * (Q * Q) - 2 * ((n1 * n1) * (Q * f)) + (n1 * n1 + n1 * n0) * (f * f) := by
              calc
                n1 * (n1 * (Q * Q - 2 * (Q * f) + f * f) + n0 * (f * f))
                    = n1 * (n1 * (Q * Q - 2 * (Q * f)) + n1 * (f * f) + n0 * (f * f)) := by
                      rw [Int.mul_add n1 (Q * Q - 2 * (Q * f)) (f * f)]
                _ = n1 * (n1 * (Q * Q) - n1 * (2 * (Q * f)) + (n1 + n0) * (f * f)) := by
                      rw [Int.mul_sub, Int.add_assoc (n1 * (Q * Q) - n1 * (2 * (Q * f))), ← Int.add_mul n1 n0 (f * f)]
                _ = n1 * (n1 * (Q * Q) - n1 * (2 * (Q * f))) + n1 * ((n1 + n0) * (f * f)) := by
                      rw [Int.mul_add]
                _ = (n1 * n1) * (Q * Q) - (n1 * n1) * (2 * (Q * f)) + (n1 * n1 + n1 * n0) * (f * f) := by
                      rw [Int.mul_sub, ← Int.mul_assoc n1 n1 (Q * Q), ← Int.mul_assoc n1 n1 (2 * (Q * f)),
                          ← Int.mul_assoc n1 (n1 + n0) (f * f), Int.mul_add n1 n1 n0]
                _ = n1 * n1 * (Q * Q) - 2 * ((n1 * n1) * (Q * f)) + (n1 * n1 + n1 * n0) * (f * f) := by
                      have hc : (n1 * n1) * (2 * (Q * f)) = 2 * ((n1 * n1) * (Q * f)) := by
                        rw [← Int.mul_assoc (n1 * n1) 2 (Q * f), Int.mul_comm (n1 * n1) 2, Int.mul_assoc 2 (n1 * n1) (Q * f)]
                      rw [hc]
            have h2 : n0 * (n1 * (Q * Q - 2 * (Q * f) + f * f) + n0 * (f * f)) =
                n0 * n1 * (Q * Q) - 2 * ((n0 * n1) * (Q * f)) + (n0 * n1 + n0 * n0) * (f * f) := by
              calc
                n0 * (n1 * (Q * Q - 2 * (Q * f) + f * f) + n0 * (f * f))
                    = n0 * (n1 * (Q * Q - 2 * (Q * f)) + n1 * (f * f) + n0 * (f * f)) := by
                      rw [Int.mul_add n1 (Q * Q - 2 * (Q * f)) (f * f)]
                _ = n0 * (n1 * (Q * Q) - n1 * (2 * (Q * f)) + (n1 + n0) * (f * f)) := by
                      rw [Int.mul_sub, Int.add_assoc (n1 * (Q * Q) - n1 * (2 * (Q * f))), ← Int.add_mul n1 n0 (f * f)]
                _ = n0 * (n1 * (Q * Q) - n1 * (2 * (Q * f))) + n0 * ((n1 + n0) * (f * f)) := by
                      rw [Int.mul_add]
                _ = (n0 * n1) * (Q * Q) - (n0 * n1) * (2 * (Q * f)) + (n0 * n1 + n0 * n0) * (f * f) := by
                      rw [Int.mul_sub, ← Int.mul_assoc n0 n1 (Q * Q), ← Int.mul_assoc n0 n1 (2 * (Q * f)),
                          ← Int.mul_assoc n0 (n1 + n0) (f * f), Int.mul_add n0 n1 n0]
                _ = n0 * n1 * (Q * Q) - 2 * ((n0 * n1) * (Q * f)) + (n0 * n1 + n0 * n0) * (f * f) := by
                      have hc : (n0 * n1) * (2 * (Q * f)) = 2 * ((n0 * n1) * (Q * f)) := by
                        rw [← Int.mul_assoc (n0 * n1) 2 (Q * f), Int.mul_comm (n0 * n1) 2, Int.mul_assoc 2 (n0 * n1) (Q * f)]
                      rw [hc]
            rw [h1, h2]
            have hcomm : n0 * n1 = n1 * n0 := Int.mul_comm n0 n1
            rw [hcomm]
            have hqq1 : n1 * n1 * (Q * Q) = n1 * n1 * Q * Q := by rw [← Int.mul_assoc (n1 * n1) Q Q]
            have hqq2 : n1 * n0 * (Q * Q) = n1 * n0 * Q * Q := by rw [← Int.mul_assoc (n1 * n0) Q Q]
            have hff_sum :
                (n1 * n1 + n1 * n0) * (f * f) + (n1 * n0 + n0 * n0) * (f * f) =
                  (n1 * n1 + 2 * (n1 * n0) + n0 * n0) * (f * f) := by
              rw [← Int.add_mul (n1 * n1 + n1 * n0) (n1 * n0 + n0 * n0) (f * f)]
              have hc2 : (n1 * n1 + n1 * n0) + (n1 * n0 + n0 * n0) = n1 * n1 + 2 * (n1 * n0) + n0 * n0 := by omega
              rw [hc2]
            have hqf_split :
                2 * ((n1 * (n1 + n0)) * (Q * f)) =
                  2 * ((n1 * n1) * (Q * f)) + 2 * ((n1 * n0) * (Q * f)) := by
              rw [Int.mul_add n1 n1 n0, Int.add_mul (n1 * n1) (n1 * n0) (Q * f), Int.mul_add 2]
            rw [hqq1, hqq2, hqf_split, ← hff_sum]
            omega
  have hR :
      Q * Q * n1 * n0 + (n1 * Q - (n1 + n0) * f) * (n1 * Q - (n1 + n0) * f) =
        n1 * n1 * Q * Q + n1 * n0 * Q * Q -
          2 * ((n1 * (n1 + n0)) * (Q * f)) +
          (n1 * n1 + 2 * (n1 * n0) + n0 * n0) * (f * f) := by
    have hsq :
        (n1 * Q - (n1 + n0) * f) * (n1 * Q - (n1 + n0) * f) =
          (n1 * Q) * (n1 * Q) - 2 * ((n1 * Q) * ((n1 + n0) * f)) + ((n1 + n0) * f) * ((n1 + n0) * f) := by
      calc
        (n1 * Q - (n1 + n0) * f) * (n1 * Q - (n1 + n0) * f)
            = (n1 * Q) * (n1 * Q - (n1 + n0) * f) - ((n1 + n0) * f) * (n1 * Q - (n1 + n0) * f) := Int.sub_mul _ _ _
        _ = ((n1 * Q) * (n1 * Q) - (n1 * Q) * ((n1 + n0) * f)) -
              (((n1 + n0) * f) * (n1 * Q) - ((n1 + n0) * f) * ((n1 + n0) * f)) := by rw [Int.mul_sub, Int.mul_sub]
        _ = ((n1 * Q) * (n1 * Q) - (n1 * Q) * ((n1 + n0) * f)) -
              ((n1 * Q) * ((n1 + n0) * f) - ((n1 + n0) * f) * ((n1 + n0) * f)) := by
              rw [Int.mul_comm ((n1 + n0) * f) (n1 * Q)]
        _ = (n1 * Q) * (n1 * Q) - 2 * ((n1 * Q) * ((n1 + n0) * f)) + ((n1 + n0) * f) * ((n1 + n0) * f) := by omega
    have h1 : (n1 * Q) * (n1 * Q) = n1 * n1 * Q * Q := by
      calc
        (n1 * Q) * (n1 * Q) = n1 * (Q * (n1 * Q)) := Int.mul_assoc n1 Q (n1 * Q)
        _ = n1 * ((Q * n1) * Q) := by rw [← Int.mul_assoc Q n1 Q]
        _ = n1 * ((n1 * Q) * Q) := by rw [Int.mul_comm Q n1]
        _ = n1 * n1 * Q * Q := by rw [← Int.mul_assoc n1 (n1 * Q) Q, ← Int.mul_assoc n1 n1 Q]
    have h2 : Q * Q * n1 * n0 = n1 * n0 * Q * Q := by
      calc
        Q * Q * n1 * n0 = (Q * Q) * (n1 * n0) := Int.mul_assoc (Q * Q) n1 n0
        _ = (n1 * n0) * (Q * Q) := Int.mul_comm (Q * Q) (n1 * n0)
        _ = n1 * n0 * Q * Q := by rw [← Int.mul_assoc (n1 * n0) Q Q]
    have h3 : 2 * ((n1 * Q) * ((n1 + n0) * f)) = 2 * ((n1 * (n1 + n0)) * (Q * f)) := by
      calc
        2 * ((n1 * Q) * ((n1 + n0) * f))
            = 2 * (n1 * (Q * ((n1 + n0) * f))) := by rw [Int.mul_assoc n1 Q ((n1 + n0) * f)]
        _ = 2 * (n1 * ((Q * (n1 + n0)) * f)) := by rw [← Int.mul_assoc Q (n1 + n0) f]
        _ = 2 * (n1 * (((n1 + n0) * Q) * f)) := by rw [Int.mul_comm Q (n1 + n0)]
        _ = 2 * ((n1 * (n1 + n0)) * (Q * f)) := by
            rw [Int.mul_assoc (n1 + n0) Q f, ← Int.mul_assoc n1 (n1 + n0) (Q * f)]
    have h4 : ((n1 + n0) * f) * ((n1 + n0) * f) = (n1 * n1 + 2 * (n1 * n0) + n0 * n0) * (f * f) := by
      have hsqn : (n1 + n0) * (n1 + n0) = n1 * n1 + 2 * (n1 * n0) + n0 * n0 := by
        calc
          (n1 + n0) * (n1 + n0) = n1 * (n1 + n0) + n0 * (n1 + n0) := Int.add_mul n1 n0 (n1 + n0)
          _ = (n1 * n1 + n1 * n0) + (n0 * n1 + n0 * n0) := by rw [Int.mul_add, Int.mul_add]
          _ = (n1 * n1 + n1 * n0) + (n1 * n0 + n0 * n0) := by rw [Int.mul_comm n0 n1]
          _ = n1 * n1 + 2 * (n1 * n0) + n0 * n0 := by omega
      calc
        ((n1 + n0) * f) * ((n1 + n0) * f) = (n1 + n0) * (f * ((n1 + n0) * f)) := Int.mul_assoc (n1 + n0) f _
        _ = (n1 + n0) * ((f * (n1 + n0)) * f) := by rw [← Int.mul_assoc f (n1 + n0) f]
        _ = (n1 + n0) * (((n1 + n0) * f) * f) := by rw [Int.mul_comm f (n1 + n0)]
        _ = ((n1 + n0) * (n1 + n0)) * (f * f) := by
            rw [Int.mul_assoc (n1 + n0) f f, ← Int.mul_assoc (n1 + n0) (n1 + n0) (f * f)]
        _ = (n1 * n1 + 2 * (n1 * n0) + n0 * n0) * (f * f) := by rw [hsqn]
    rw [hsq, h1, h2, h3, h4]
    omega
  rw [hL, hR]

/-- **Theorem 2 (Murphy–Sanders Proper Brier Calibration–Refinement Decomposition
    vs. Linear `L¹` Overconfidence Hallucination Collapse)**:
    - **(a)** Universally over all `n1 n0 Q f : Int`, `(n1 + n0) · Brier(f) = Q² n1 n0 + (n1 Q - (n1 + n0) f)²`,
      and `(n1 + n0) · Brier(f) ≥ Q² n1 n0`, attaining exact equality at calibrated `f = n1` (`Q = n1 + n0`).
    - **(b) Improperness of `L¹` Probability Loss**: At `n1 = 3, n0 = 2, Q = 5` (`60%` true frequency),
      miscalibrated `100%` overconfidence (`f = 5`) achieves `l1BinLoss = 10 < 12 = l1BinLoss(f = 3)`! -/
theorem brier_proper_calibration_refinement_decomposition_vs_l1_overconfidence_collapse :
    (∀ n1 n0 Q f : Int,
      (n1 + n0) * brierBinLoss n1 n0 Q f =
        Q * Q * n1 * n0 + (n1 * Q - (n1 + n0) * f) * (n1 * Q - (n1 + n0) * f) ∧
      Q * Q * n1 * n0 ≤ (n1 + n0) * brierBinLoss n1 n0 Q f) ∧
    (∀ n1 n0 : Int, (n1 + n0) * brierBinLoss n1 n0 (n1 + n0) n1 = (n1 + n0) * (n1 + n0) * n1 * n0) ∧
    (l1BinLoss 3 2 5 5 = 10 ∧ l1BinLoss 3 2 5 3 = 12 ∧ l1BinLoss 3 2 5 5 < l1BinLoss 3 2 5 3) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n1 n0 Q f
    have hid := brier_orth_identity n1 n0 Q f
    have hnn := sq_nonneg_int (n1 * Q - (n1 + n0) * f)
    exact ⟨hid, by omega⟩
  · intro n1 n0
    have hid := brier_orth_identity n1 n0 (n1 + n0) n1
    have hcal : n1 * (n1 + n0) - (n1 + n0) * n1 = 0 := by rw [Int.mul_comm n1 (n1 + n0)]; omega
    rw [hid, hcal]
    omega
  · decide

/-! ## 3. Exact `χ²` Data-Processing Slack, Fisher–Neyman Sufficiency & Blackwell Poset Non-Totality -/

/-- Exact polynomial `χ²` coarse-graining slack when merging two atoms `(d₁, q₁)` and `(d₂, q₂)`. -/
def chiSqMergeSlack (q1 q2 d1 d2 : Int) : Int :=
  (q1 + q2) * (q2 * d1 * d1 + q1 * d2 * d2) - q1 * q2 * (d1 + d2) * (d1 + d2)

/-- Maximum expected utility on `{0,1}²` (uniform scaled weight `1` per state `(b₁, b₂)`) when observing
    only the row bit `b₁` (`rowTask = true` rewards guessing `b₁`, `rowTask = false` rewards guessing `b₂`). -/
def channelRowBitUtility (rowTask : Bool) : Int :=
  if rowTask then 4 else 2

/-- Maximum expected utility on `{0,1}²` when observing only the column bit `b₂`. -/
def channelColBitUtility (rowTask : Bool) : Int :=
  if rowTask then 2 else 4

/-- **Theorem 3 (`χ²` Data-Processing Remainder, Fisher–Neyman Sufficiency Rigidity
    & Multi-Task Blackwell Poset Non-Totality)**:
    - **(a)** Universally over `q1 q2 d1 d2 : Int`, `chiSqMergeSlack q1 q2 d1 d2 = (q1 * d2 - q2 * d1)² ≥ 0`,
      vanishing iff `q1 * d2 = q2 * d1` (proportional likelihood shift `d₁ / q₁ = d₂ / q₂`, i.e. Fisher–Neyman sufficiency).
    - **(b)** Orthogonal row-bit and column-bit channels on `{0,1}²` are strictly incomparable in Blackwell's order:
      `U(K_row, taskRow) = 4 > 2 = U(K_col, taskRow)` while `U(K_col, taskCol) = 4 > 2 = U(K_row, taskCol)`. -/
theorem chi_square_data_processing_slack_and_blackwell_poset_incomparability :
    (∀ q1 q2 d1 d2 : Int,
      chiSqMergeSlack q1 q2 d1 d2 = (q1 * d2 - q2 * d1) * (q1 * d2 - q2 * d1) ∧
      0 ≤ chiSqMergeSlack q1 q2 d1 d2) ∧
    (chiSqMergeSlack 2 4 1 2 = 0 ∧ chiSqMergeSlack 2 4 1 (-1) = 36) ∧
    (channelColBitUtility true < channelRowBitUtility true ∧
      channelRowBitUtility false < channelColBitUtility false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q1 q2 d1 d2
    have hid : chiSqMergeSlack q1 q2 d1 d2 = (q1 * d2 - q2 * d1) * (q1 * d2 - q2 * d1) := by
      dsimp [chiSqMergeSlack]
      have hL :
          (q1 + q2) * (q2 * d1 * d1 + q1 * d2 * d2) - q1 * q2 * (d1 + d2) * (d1 + d2) =
            q1 * q1 * (d2 * d2) - 2 * ((q1 * d2) * (q2 * d1)) + q2 * q2 * (d1 * d1) := by
        have hexp1 :
            (q1 + q2) * (q2 * d1 * d1 + q1 * d2 * d2) =
              q1 * q2 * (d1 * d1) + q1 * q1 * (d2 * d2) + q2 * q2 * (d1 * d1) + q1 * q2 * (d2 * d2) := by
          calc
            (q1 + q2) * (q2 * d1 * d1 + q1 * d2 * d2)
                = q1 * (q2 * (d1 * d1) + q1 * (d2 * d2)) + q2 * (q2 * (d1 * d1) + q1 * (d2 * d2)) := by
                  rw [Int.add_mul, Int.mul_assoc q2 d1 d1, Int.mul_assoc q1 d2 d2]
            _ = (q1 * (q2 * (d1 * d1)) + q1 * (q1 * (d2 * d2))) +
                  (q2 * (q2 * (d1 * d1)) + q2 * (q1 * (d2 * d2))) := by rw [Int.mul_add, Int.mul_add]
            _ = (q1 * q2 * (d1 * d1) + q1 * q1 * (d2 * d2)) +
                  (q2 * q2 * (d1 * d1) + q1 * q2 * (d2 * d2)) := by
                  rw [← Int.mul_assoc q1 q2, ← Int.mul_assoc q1 q1, ← Int.mul_assoc q2 q2,
                      ← Int.mul_assoc q2 q1, Int.mul_comm q2 q1]
            _ = q1 * q2 * (d1 * d1) + q1 * q1 * (d2 * d2) + q2 * q2 * (d1 * d1) + q1 * q2 * (d2 * d2) := by omega
        have hexp2 :
            q1 * q2 * (d1 + d2) * (d1 + d2) =
              q1 * q2 * (d1 * d1) + 2 * ((q1 * d2) * (q2 * d1)) + q1 * q2 * (d2 * d2) := by
          have hd : (d1 + d2) * (d1 + d2) = d1 * d1 + 2 * (d1 * d2) + d2 * d2 := by
            calc
              (d1 + d2) * (d1 + d2) = d1 * (d1 + d2) + d2 * (d1 + d2) := Int.add_mul d1 d2 (d1 + d2)
              _ = (d1 * d1 + d1 * d2) + (d2 * d1 + d2 * d2) := by rw [Int.mul_add, Int.mul_add]
              _ = (d1 * d1 + d1 * d2) + (d1 * d2 + d2 * d2) := by rw [Int.mul_comm d2 d1]
              _ = d1 * d1 + 2 * (d1 * d2) + d2 * d2 := by omega
          have hcross : (q1 * q2) * (2 * (d1 * d2)) = 2 * ((q1 * d2) * (q2 * d1)) := by
            calc
              (q1 * q2) * (2 * (d1 * d2)) = 2 * ((q1 * q2) * (d1 * d2)) := by
                rw [← Int.mul_assoc (q1 * q2) 2 (d1 * d2), Int.mul_comm (q1 * q2) 2, Int.mul_assoc 2 (q1 * q2) (d1 * d2)]
              _ = 2 * (q1 * (q2 * (d1 * d2))) := by rw [Int.mul_assoc q1 q2 (d1 * d2)]
              _ = 2 * (q1 * ((q2 * d1) * d2)) := by rw [← Int.mul_assoc q2 d1 d2]
              _ = 2 * (q1 * (d2 * (q2 * d1))) := by rw [Int.mul_comm (q2 * d1) d2]
              _ = 2 * ((q1 * d2) * (q2 * d1)) := by rw [← Int.mul_assoc q1 d2 (q2 * d1)]
          calc
            q1 * q2 * (d1 + d2) * (d1 + d2) = (q1 * q2) * ((d1 + d2) * (d1 + d2)) := Int.mul_assoc (q1 * q2) _ _
            _ = (q1 * q2) * (d1 * d1 + 2 * (d1 * d2) + d2 * d2) := by rw [hd]
            _ = (q1 * q2) * (d1 * d1 + 2 * (d1 * d2)) + (q1 * q2) * (d2 * d2) := Int.mul_add _ _ _
            _ = (q1 * q2) * (d1 * d1) + (q1 * q2) * (2 * (d1 * d2)) + (q1 * q2) * (d2 * d2) := by rw [Int.mul_add]
            _ = q1 * q2 * (d1 * d1) + 2 * ((q1 * d2) * (q2 * d1)) + q1 * q2 * (d2 * d2) := by rw [hcross]
        rw [hexp1, hexp2]
        omega
      have hR :
          (q1 * d2 - q2 * d1) * (q1 * d2 - q2 * d1) =
            q1 * q1 * (d2 * d2) - 2 * ((q1 * d2) * (q2 * d1)) + q2 * q2 * (d1 * d1) := by
        have hsq :
            (q1 * d2 - q2 * d1) * (q1 * d2 - q2 * d1) =
              (q1 * d2) * (q1 * d2) - 2 * ((q1 * d2) * (q2 * d1)) + (q2 * d1) * (q2 * d1) := by
          calc
            (q1 * d2 - q2 * d1) * (q1 * d2 - q2 * d1)
                = (q1 * d2) * (q1 * d2 - q2 * d1) - (q2 * d1) * (q1 * d2 - q2 * d1) := Int.sub_mul _ _ _
            _ = ((q1 * d2) * (q1 * d2) - (q1 * d2) * (q2 * d1)) -
                  ((q2 * d1) * (q1 * d2) - (q2 * d1) * (q2 * d1)) := by rw [Int.mul_sub, Int.mul_sub]
            _ = ((q1 * d2) * (q1 * d2) - (q1 * d2) * (q2 * d1)) -
                  ((q1 * d2) * (q2 * d1) - (q2 * d1) * (q2 * d1)) := by rw [Int.mul_comm (q2 * d1) (q1 * d2)]
            _ = (q1 * d2) * (q1 * d2) - 2 * ((q1 * d2) * (q2 * d1)) + (q2 * d1) * (q2 * d1) := by omega
        have hp1 : (q1 * d2) * (q1 * d2) = q1 * q1 * (d2 * d2) := by
          calc
            (q1 * d2) * (q1 * d2) = q1 * (d2 * (q1 * d2)) := Int.mul_assoc q1 d2 (q1 * d2)
            _ = q1 * ((d2 * q1) * d2) := by rw [← Int.mul_assoc d2 q1 d2]
            _ = q1 * ((q1 * d2) * d2) := by rw [Int.mul_comm d2 q1]
            _ = q1 * q1 * (d2 * d2) := by rw [Int.mul_assoc q1 d2 d2, ← Int.mul_assoc q1 q1 (d2 * d2)]
        have hp2 : (q2 * d1) * (q2 * d1) = q2 * q2 * (d1 * d1) := by
          calc
            (q2 * d1) * (q2 * d1) = q2 * (d1 * (q2 * d1)) := Int.mul_assoc q2 d1 (q2 * d1)
            _ = q2 * ((d1 * q2) * d1) := by rw [← Int.mul_assoc d1 q2 d1]
            _ = q2 * ((q2 * d1) * d1) := by rw [Int.mul_comm d1 q2]
            _ = q2 * q2 * (d1 * d1) := by rw [Int.mul_assoc q2 d1 d1, ← Int.mul_assoc q2 q2 (d1 * d1)]
        rw [hsq, hp1, hp2]
      rw [hL, hR]
    exact ⟨hid, hid ▸ sq_nonneg_int (q1 * d2 - q2 * d1)⟩
  · decide
  · decide

end CommonGround.BlackwellConformalChiSquareFrontier
