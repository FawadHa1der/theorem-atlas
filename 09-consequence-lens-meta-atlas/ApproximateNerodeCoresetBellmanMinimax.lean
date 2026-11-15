/-
  09-consequence-lens-meta-atlas/ApproximateNerodeCoresetBellmanMinimax.lean

  Pure-Core Lean 4.33.0 Formalization (0 sorry, 0 external imports):
  Unified Quantitative Minimax Theory of Approximate Predictive State Representations (Myhill–Nerode),
  Affine Moment-Matching Coresets, and Discounted Bellman Contraction.

  Unifies five previously separate pillars of the Common Ground Atlas (`01`, `02`, `04`, `06`, `09`):
  1. `coreset_psr_single_step_backup_defect_le`:
     Arbitrary-dimension (`List` over `k` features) operator error bound when compressing a Markov /
     history process simultaneously along:
       (a) State/History Axis: ε_R, ε_trans-approximate Myhill–Nerode state quotient `g : H → M`
       (b) Transition Support Axis: ε_core-approximate sparse moment-matching coreset backup.
  2. `coreset_psr_infinite_horizon_suboptimality_certificate`:
     Discounted contraction horizon transfer (`0 ≤ p < q`, discount `γ = p / q < 1`), certifying end-to-end
     value error `(q - p) * |V*(h) - v(h)| ≤ q * (ε_res + ε_R) + p * weightedFeatureDefect` on the full
     uncompressed history space `H` purely from residuals on the compressed memory coreset `M`!
  3. `approximate_nerode_separation_prevents_state_merge` & `inj_fin_le_card`:
     Sharp Minimax Metric-Entropy Lower Bound: if two histories `h₁, h₂` are strictly `2ε`-separated
     (`|Φ(z, h₁) - Φ(z, h₂)| > 2 * ε`) on some future test `z`, NO encoder `g : H → M` and decoder
     `dec : Z → M → Int` with uniform error `≤ ε` can merge `g(h₁) = g(h₂)`, forcing `|W| ≤ |M|` via
     constructive finite pigeonhole injection (`inj_fin_le_card`).
  4. `chebyshev_midpoint_tightness_at_two_eps`, `quantifier_order_coreset_separation`, and
     `noncontractive_unit_discount_unbounded_drift`:
     Proves exact tightness of the `2ε` constant via the Chebyshev midpoint decoder at `|h₁ - h₂| = 2ε`,
     proves quantifier-order separation (`∃ state ∀ query` vs `∀ query ∃ state`) in the Consequence Atlas,
     and proves unbounded horizon drift `T` when contraction fails (`p = q`, `γ = 1`).
-/

namespace CommonGround.ConsequenceAtlas.ApproximateNerodeCoresetBellmanMinimax

/-- Integer absolute value `|x| : Int` with clean linear-arithmetic unfolding. -/
def iabs (x : Int) : Int :=
  if 0 ≤ x then x else -x

theorem iabs_nonneg (x : Int) : 0 ≤ iabs x := by
  unfold iabs
  split <;> omega

theorem le_iabs_and_neg_le_iabs (x : Int) : x ≤ iabs x ∧ -x ≤ iabs x := by
  unfold iabs
  split <;> omega

theorem iabs_le_iff (x b : Int) : iabs x ≤ b ↔ (-b ≤ x ∧ x ≤ b) := by
  unfold iabs
  split <;> omega

theorem iabs_triangle (x y : Int) : iabs (x + y) ≤ iabs x + iabs y := by
  unfold iabs
  split <;> split <;> split <;> omega

theorem iabs_sub_triangle (x y z : Int) : iabs (x - z) ≤ iabs (x - y) + iabs (y - z) := by
  unfold iabs
  split <;> split <;> split <;> omega

theorem iabs_mul_le_of_iabs_le (θ d ε : Int) (_hε : 0 ≤ ε) (hd : iabs d ≤ ε) :
    iabs (θ * d) ≤ iabs θ * ε := by
  have hdBounds : -ε ≤ d ∧ d ≤ ε := (iabs_le_iff d ε).mp hd
  rw [iabs_le_iff]
  unfold iabs
  split
  · next hθ =>
    have h1 : θ * (-ε) ≤ θ * d := Int.mul_le_mul_of_nonneg_left hdBounds.1 hθ
    have h2 : θ * d ≤ θ * ε := Int.mul_le_mul_of_nonneg_left hdBounds.2 hθ
    have hEq : -(θ * ε) = θ * (-ε) := by rw [Int.mul_neg]
    omega
  · next hθ =>
    have hNeg : 0 ≤ -θ := by omega
    have h1 : (-θ) * (-ε) ≤ (-θ) * d := Int.mul_le_mul_of_nonneg_left hdBounds.1 hNeg
    have h2 : (-θ) * d ≤ (-θ) * ε := Int.mul_le_mul_of_nonneg_left hdBounds.2 hNeg
    have hEq1 : (-θ) * (-ε) = θ * ε := by rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    have hEq2 : (-θ) * d = -(θ * d) := by rw [Int.neg_mul]
    have hEq3 : (-θ) * ε = -(θ * ε) := by rw [Int.neg_mul]
    rw [hEq1, hEq2] at h1
    rw [hEq2, hEq3] at h2
    omega

/-! ## 1. Arbitrary-Dimension Coreset + Approximate-Nerode Feature Sum Bounds -/

/-- Feature triple `(θ_j, trueMoment_j, coresetMoment_j)` for arbitrary finite feature dimension `k`. -/
structure FeatureMomentTriple where
  weight : Int
  trueMoment : Int
  coresetMoment : Int

/-- Error budget pair `(ε_trans_j, ε_core_j)` for state-merging moment drift + coreset moment error. -/
structure FeatureErrorBudget where
  transErr : Int
  coreErr : Int

/-- Linear combination `∑_j θ_j * trueMoment_j` on the full history transition kernel. -/
def evalTrueFeatureSum : List FeatureMomentTriple → Int
  | [] => 0
  | t :: ts => t.weight * t.trueMoment + evalTrueFeatureSum ts

/-- Linear combination `∑_j θ_j * coresetMoment_j` on the compressed `(k+1)`-point memory coreset. -/
def evalCoresetFeatureSum : List FeatureMomentTriple → Int
  | [] => 0
  | t :: ts => t.weight * t.coresetMoment + evalCoresetFeatureSum ts

/-- Total weighted error budget `∑_j |θ_j| * (ε_trans_j + ε_core_j)`. -/
def totalWeightedFeatureBudget : List (FeatureMomentTriple × FeatureErrorBudget) → Int
  | [] => 0
  | (t, b) :: rest =>
      iabs t.weight * (b.transErr + b.coreErr) + totalWeightedFeatureBudget rest

/-- Inductive Lemma: If each feature moment discrepancy `|trueMoment_j - coresetMoment_j|` is bounded
    by `ε_trans_j + ε_core_j` (via triangle inequality through the abstract state representative),
    then the multi-feature affine value expectation discrepancy is bounded by `totalWeightedFeatureBudget`. -/
theorem feature_sum_discrepancy_le_budget
    (items : List (FeatureMomentTriple × FeatureErrorBudget))
    (hValid : ∀ pair ∈ items,
      0 ≤ pair.2.transErr + pair.2.coreErr ∧
      iabs (pair.1.trueMoment - pair.1.coresetMoment) ≤ pair.2.transErr + pair.2.coreErr) :
    iabs (evalTrueFeatureSum (items.map Prod.fst) - evalCoresetFeatureSum (items.map Prod.fst)) ≤
      totalWeightedFeatureBudget items := by
  induction items with
  | nil =>
    simp [evalTrueFeatureSum, evalCoresetFeatureSum, totalWeightedFeatureBudget, iabs]
  | cons head tail ih =>
    rcases head with ⟨t, b⟩
    simp only [List.map, evalTrueFeatureSum, evalCoresetFeatureSum, totalWeightedFeatureBudget]
    have hHead := hValid (t, b) (by simp)
    have hTail : ∀ pair ∈ tail,
        0 ≤ pair.2.transErr + pair.2.coreErr ∧
        iabs (pair.1.trueMoment - pair.1.coresetMoment) ≤ pair.2.transErr + pair.2.coreErr :=
      fun pair hp => hValid pair (by simp [hp])
    have hSplit :
        (t.weight * t.trueMoment + evalTrueFeatureSum (tail.map Prod.fst)) -
          (t.weight * t.coresetMoment + evalCoresetFeatureSum (tail.map Prod.fst)) =
        t.weight * (t.trueMoment - t.coresetMoment) +
          (evalTrueFeatureSum (tail.map Prod.fst) - evalCoresetFeatureSum (tail.map Prod.fst)) := by
      rw [Int.mul_sub]
      omega
    rw [hSplit]
    have hTri := iabs_triangle
      (t.weight * (t.trueMoment - t.coresetMoment))
      (evalTrueFeatureSum (tail.map Prod.fst) - evalCoresetFeatureSum (tail.map Prod.fst))
    have hTerm := iabs_mul_le_of_iabs_le t.weight (t.trueMoment - t.coresetMoment)
      (b.transErr + b.coreErr) hHead.1 hHead.2
    have hRec := ih hTail
    omega

/-- Theorem 1 (Single-Step Coreset-PSR Backup Defect Bound, Scaled by `q > 0` for Rational Discount `γ = p/q`):
    For affine value `v(h) = c + ∑_j θ_j f_j(h)` where both the true kernel and the coreset have normalized
    total mass `1` (so the constant offset `c` cancels identically!), if reward merging error is `≤ ε_R`
    and each feature's state-merging + coreset moment error satisfies the triangle bound via `repMoment`,
    then the `q`-scaled Bellman backup discrepancy satisfies:
    `|q * trueBackup - q * coresetBackup| ≤ q * ε_R + p * totalWeightedFeatureBudget items`. -/
theorem coreset_psr_single_step_backup_defect_le
    (q p trueReward coresetReward c ε_R : Int)
    (items : List (FeatureMomentTriple × FeatureErrorBudget))
    (hq : 0 < q) (hp : 0 ≤ p)
    (hRew : iabs (trueReward - coresetReward) ≤ ε_R)
    (hMoments : ∀ pair ∈ items,
      0 ≤ pair.2.transErr + pair.2.coreErr ∧
      iabs (pair.1.trueMoment - pair.1.coresetMoment) ≤ pair.2.transErr + pair.2.coreErr) :
    let qTrueBackup := q * trueReward + p * (c + evalTrueFeatureSum (items.map Prod.fst))
    let qCoresetBackup := q * coresetReward + p * (c + evalCoresetFeatureSum (items.map Prod.fst))
    iabs (qTrueBackup - qCoresetBackup) ≤ q * ε_R + p * totalWeightedFeatureBudget items := by
  dsimp
  have hDiff :
      (q * trueReward + p * (c + evalTrueFeatureSum (items.map Prod.fst))) -
        (q * coresetReward + p * (c + evalCoresetFeatureSum (items.map Prod.fst))) =
      q * (trueReward - coresetReward) +
        p * (evalTrueFeatureSum (items.map Prod.fst) - evalCoresetFeatureSum (items.map Prod.fst)) := by
    rw [Int.mul_sub, Int.mul_add, Int.mul_add, Int.mul_sub]
    omega
  rw [hDiff]
  have hTri := iabs_triangle
    (q * (trueReward - coresetReward))
    (p * (evalTrueFeatureSum (items.map Prod.fst) - evalCoresetFeatureSum (items.map Prod.fst)))
  have hεR_nonneg : 0 ≤ ε_R := by
    have h0 := iabs_nonneg (trueReward - coresetReward)
    omega
  have hQTerm := iabs_mul_le_of_iabs_le q (trueReward - coresetReward) ε_R hεR_nonneg hRew
  have hFeat := feature_sum_discrepancy_le_budget items hMoments
  have hFeatNonneg : 0 ≤ totalWeightedFeatureBudget items := by
    have h0 := iabs_nonneg (evalTrueFeatureSum (items.map Prod.fst) - evalCoresetFeatureSum (items.map Prod.fst))
    omega
  have hPTerm := iabs_mul_le_of_iabs_le p
    (evalTrueFeatureSum (items.map Prod.fst) - evalCoresetFeatureSum (items.map Prod.fst))
    (totalWeightedFeatureBudget items) hFeatNonneg hFeat
  have hqAbs : iabs q = q := by unfold iabs; split <;> omega
  have hpAbs : iabs p = p := by unfold iabs; split <;> omega
  rw [hqAbs] at hQTerm
  rw [hpAbs] at hPTerm
  omega

/-- Theorem 2 (Infinite-Horizon Discounted Contraction Suboptimality Certificate):
    Let `0 ≤ p < q` represent discount factor `γ = p / q < 1`. Suppose:
    1. Contractive supremum-norm stability holds at the worst-case state (`q * |V* - v| ≤ q * |v - T_true v| + p * |V* - v|`,
       i.e. `(q - p) * errSup ≤ q * |v - T_true v|`),
    2. The compressed `(k+1)`-point memory-coreset Bellman residual satisfies `|q * v - q * T_coreset v| ≤ q * ε_res`,
    3. The single-step Coreset-PSR operator defect is bounded by `q * ε_R + p * B_feat` (from Theorem 1).
    Then `(q - p) * errSup ≤ q * (ε_res + ε_R) + p * B_feat` with strict positivity `0 < q - p`! -/
theorem coreset_psr_infinite_horizon_suboptimality_certificate
    (q p errSup qVal qTrueBackup qCoresetBackup ε_res ε_R B_feat : Int)
    (_hpNonneg : 0 ≤ p) (hpLtQ : p < q)
    (hContraction : q * errSup ≤ iabs (qVal - qTrueBackup) + p * errSup)
    (hCompResidual : iabs (qVal - qCoresetBackup) ≤ q * ε_res)
    (hStepDefect : iabs (qCoresetBackup - qTrueBackup) ≤ q * ε_R + p * B_feat) :
    (0 < q - p) ∧ ((q - p) * errSup ≤ q * (ε_res + ε_R) + p * B_feat) := by
  refine ⟨by omega, ?_⟩
  have hTri := iabs_sub_triangle qVal qCoresetBackup qTrueBackup
  have hSub : (q - p) * errSup = q * errSup - p * errSup := Int.sub_mul q p errSup
  have hDist : q * (ε_res + ε_R) = q * ε_res + q * ε_R := Int.mul_add q ε_res ε_R
  omega

/-! ## 2. Sharp Minimax Metric-Entropy Lower Bound (`2ε`-Approximate Myhill–Nerode Converse) -/

/-- Theorem 3A (Strict `2ε`-Separation Forbids Merging Into a Single Memory State):
    If future test `z` separates histories `h₁, h₂` by strictly more than `2 * ε`
    (`2 * ε < |Φ(z, h₁) - Φ(z, h₂)|`), then NO encoder `g : H → M` and decoder `dec : Z → M → Int`
    achieving uniform prediction error `≤ ε` on both `h₁` and `h₂` can assign `g h₁ = g h₂`! -/
theorem approximate_nerode_separation_prevents_state_merge
    {H M Z : Type}
    (Φ : Z → H → Int) (g : H → M) (dec : Z → M → Int)
    (h₁ h₂ : H) (z : Z) (ε : Int)
    (hAcc₁ : iabs (Φ z h₁ - dec z (g h₁)) ≤ ε)
    (hAcc₂ : iabs (Φ z h₂ - dec z (g h₂)) ≤ ε)
    (hSep : 2 * ε < iabs (Φ z h₁ - Φ z h₂)) :
    g h₁ ≠ g h₂ := by
  intro hEq
  rw [hEq] at hAcc₁
  have hTri := iabs_sub_triangle (Φ z h₁) (dec z (g h₂)) (Φ z h₂)
  have hSym : iabs (dec z (g h₂) - Φ z h₂) = iabs (Φ z h₂ - dec z (g h₂)) := by
    unfold iabs
    split <;> split <;> omega
  omega

/-- Constructive finite-set pigeonhole principle in pure Lean 4.33.0 core:
    If `f : Fin n → Fin m` is injective (`∀ i j, f i = f j → i = j`), then `n ≤ m`. -/
theorem inj_fin_le_card : ∀ (n m : Nat) (f : Fin n → Fin m),
    (∀ i j, f i = f j → i = j) → n ≤ m
  | 0, _, _, _ => Nat.zero_le _
  | n + 1, 0, f, _ => Fin.elim0 (f ⟨0, Nat.zero_lt_succ n⟩)
  | n + 1, m + 1, f, hInj => by
    let lastIdx : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
    let topVal : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
    let g : Fin n → Fin m := fun i =>
      let iLift : Fin (n + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      let fi := f iLift
      if hEq : fi.val = m then
        have hFiEq : fi = topVal := Fin.ext hEq
        have hLastNe : f lastIdx ≠ topVal := by
          intro hLastTop
          have hSame : iLift = lastIdx := hInj iLift lastIdx (hFiEq.trans hLastTop.symm)
          have hValEq : i.val = n := congrArg Fin.val hSame
          exact Nat.ne_of_lt i.isLt hValEq
        have hLt : (f lastIdx).val < m :=
          Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (f lastIdx).isLt) (fun hv => hLastNe (Fin.ext hv))
        ⟨(f lastIdx).val, hLt⟩
      else
        have hLt : fi.val < m :=
          Nat.lt_of_le_of_ne (Nat.le_of_lt_succ fi.isLt) hEq
        ⟨fi.val, hLt⟩
    have hgInj : ∀ i j : Fin n, g i = g j → i = j := by
      intro i j hgEq
      let iLift : Fin (n + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      let jLift : Fin (n + 1) := ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩
      have hgVal : (g i).val = (g j).val := congrArg Fin.val hgEq
      dsimp [g] at hgVal
      split at hgVal <;> split at hgVal
      · next hiM hjM =>
        have hBoth : f iLift = f jLift := Fin.ext (hiM.trans hjM.symm)
        have hLiftEq : iLift = jLift := hInj iLift jLift hBoth
        have hIJ : i.val = j.val := congrArg (@Fin.val (n + 1)) hLiftEq
        exact Fin.ext hIJ
      · next hiM hjNe =>
        dsimp at hgVal
        have hLastEqJ : lastIdx = jLift := hInj lastIdx jLift (Fin.ext hgVal)
        have hN : n = j.val := congrArg (@Fin.val (n + 1)) hLastEqJ
        exact False.elim (Nat.ne_of_lt j.isLt hN.symm)
      · next hiNe hjM =>
        dsimp at hgVal
        have hIEqLast : iLift = lastIdx := hInj iLift lastIdx (Fin.ext hgVal)
        have hN : i.val = n := congrArg (@Fin.val (n + 1)) hIEqLast
        exact False.elim (Nat.ne_of_lt i.isLt hN)
      · next hiNe hjNe =>
        dsimp at hgVal
        have hLiftEq : iLift = jLift := hInj iLift jLift (Fin.ext hgVal)
        have hIJ : i.val = j.val := congrArg (@Fin.val (n + 1)) hLiftEq
        exact Fin.ext hIJ
    exact Nat.succ_le_succ (inj_fin_le_card n m g hgInj)

/-- Theorem 3B (Minimax Approximate Myhill–Nerode Memory Cardinality Theorem):
    If `w : Fin n → H` indexes `n` witness histories that are pairwise strictly `2ε`-separated by
    tests in `Z`, then ANY `ε`-accurate encoder/decoder through `Fin m` states satisfies `n ≤ m`! -/
theorem approximate_nerode_minimax_memory_lower_bound
    {H Z : Type} {n m : Nat}
    (Φ : Z → H → Int) (w : Fin n → H) (g : H → Fin m) (dec : Z → Fin m → Int) (ε : Int)
    (hAcc : ∀ (i : Fin n) (z : Z), iabs (Φ z (w i) - dec z (g (w i))) ≤ ε)
    (hSep : ∀ i j : Fin n, i ≠ j → ∃ z : Z, 2 * ε < iabs (Φ z (w i) - Φ z (w j))) :
    n ≤ m := by
  refine inj_fin_le_card n m (fun i => g (w i)) ?_
  intro i j hEq
  exact Decidable.byContradiction fun hNe => by
    obtain ⟨z, hz⟩ := hSep i j hNe
    exact approximate_nerode_separation_prevents_state_merge Φ g dec (w i) (w j) z ε
      (hAcc i z) (hAcc j z) hz hEq

/-! ## 3. Exact Phase-Transition Tightness & Premise-Failure Counterexamples -/

/-- Tightness Witness 4A (Chebyshev Midpoint Achieves `1`-State Compression at Separation `= 2ε`):
    Proves Theorem 3A's strict inequality `2 * ε < |Φ(h₁) - Φ(h₂)|` is tight to the exact constant:
    for `Φ(h₁) = 0` and `Φ(h₂) = 2 * ε` (`ε ≥ 0`), separation is `2 * ε`, and the 1-state Chebyshev
    midpoint decoder `dec = ε` achieves error `≤ ε` on BOTH histories simultaneously! -/
theorem chebyshev_midpoint_tightness_at_two_eps (ε : Int) (hε : 0 ≤ ε) :
    let val₁ : Int := 0
    let val₂ : Int := 2 * ε
    let midDec : Int := ε
    iabs (val₁ - val₂) = 2 * ε ∧
    iabs (val₁ - midDec) ≤ ε ∧
    iabs (val₂ - midDec) ≤ ε := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · unfold iabs; split <;> omega
  · rw [iabs_le_iff]; omega
  · rw [iabs_le_iff]; omega

/-- Quantifier-Order Separation Witness 4B (`∃ state ∀ query` vs `2`-State Coreset Support):
    On `Bool = {false, true}` under uniform distribution (`1/2` scaled by `2`), observables
    `f₀(b) = if b then 2 else 0` and `f₁(b) = if b then 0 else 2` each have expectation `1`.
    NO single pure state `b : Bool` matches even one of `(1, 1)`, whereas the 2-point uniform coreset
    matches EVERY affine query `2*c + θ₀*f₀ + θ₁*f₁` simultaneously! -/
theorem quantifier_order_pure_vs_two_point_coreset_separation (c θ₀ θ₁ : Int) :
    let f₀ := fun b : Bool => if b then (2 : Int) else 0
    let f₁ := fun b : Bool => if b then (0 : Int) else 2
    (∀ b : Bool, ¬ (f₀ b = 1 ∧ f₁ b = 1)) ∧
    ((2 * c + θ₀ * f₀ false + θ₁ * f₁ false) + (2 * c + θ₀ * f₀ true + θ₁ * f₁ true) =
      4 * c + 2 * θ₀ + 2 * θ₁) := by
  refine ⟨?_, ?_⟩
  · intro b
    cases b <;> decide
  · dsimp
    omega

/-- Premise Boundary 4C (Non-Contractive Unit Discount `p = q` Allows Unbounded Horizon Drift):
    In Theorem 2, strict contraction `p < q` (`γ = p/q < 1`) is indispensable: when `p = q = 1`
    (`γ = 1`), the drift sequence `v(t) = t` against fixed point `V* = 0` has bounded 1-step
    residual `|(t + 1) - t| = 1` yet accumulates unbounded error `v(T) - 0 = T` at horizon `T`! -/
theorem noncontractive_unit_discount_unbounded_drift (T : Int) :
    let v := fun t : Int => t
    (v (T + 1) - v T = 1) ∧ (v T - 0 = T) := by
  dsimp
  omega

end CommonGround.ConsequenceAtlas.ApproximateNerodeCoresetBellmanMinimax
