/-
Copyright (c) 2026 Common Ground Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Csiszár Perspective Data Processing, Hellinger–TV–$\chi^2$ Sandwich, Freedman Variance Gain & Optional Stopping Frontier

Pure-core Lean 4.33.0 module (`0` imports, `0` `sorry`) in Folder `03`
(`03-information-recovery-kl-pythagorean`) unifying:
1. **Exact Denominator-Free Csiszár $\chi^2$ Perspective Identity & Sufficiency Zero-Slack**
   (`perspective_convex_subadditivity_and_sufficiency_zero_slack_vs_quasiprobability_failure`):
   For all integers `p1, p2, q1, q2` with `0 < q1` and `0 < q2`,
   `q1 * q2 * (p1 + p2)^2 + (q1 * p2 - q2 * p1)^2 = (q1 + q2) * (q2 * p1^2 + q1 * p2^2)`,
   certifying monotonic data processing AND zero information loss iff `q1 * p2 = q2 * p1`
   (`FiberLikelihoodConstant`), vs. signed quasi-probability reversal at `q1 = 2, q2 = -1`.
2. **Hellinger–TV–$\chi^2$ Sandwich vs. Parametric Reverse-Pinsker Unbounded Blowup**
   (`hellinger_tv_chisquare_sandwich_vs_reverse_pinsker_unbounded_ratio`):
   Termwise Hellinger-to-$\chi^2$ domination `b^2 * (a - b)^2 ≤ (a^2 - b^2)^2` for `a, b ≥ 0`
   and 2-state Le Cam Cauchy–Schwarz `(|a0^2 - b0^2| + |a1^2 - b1^2|)^2 ≤ ((a0 - b0)^2 + (a1 - b1)^2) * ((a0 + b0)^2 + (a1 + b1)^2)`,
   paired with the infinite parametric family `P_M = (M, 0), Q_M = (1, M - 1)` (`M ≥ 2`) where
   `χ²_num = M * (M - 1)^2` while `TV_num^2 = (M - 1)^2`, forcing `χ² / TV² = M → ∞`!
3. **Hoeffding Range Parabola & Freedman Variance-Adaptive Gain vs. Heavy-Tail 4th-Moment Spike**
   (`hoeffding_range_bound_and_freedman_variance_gain_vs_heavy_tail_kurtosis`):
   Proves `(c - x) * (c + x) ≥ 0` on `[-c, c]` and the exact zero-mean asymmetric variance identity
   `(a + b)^2 - 4 * a * b = (a - b)^2 ≥ 0` (`2,500` Hoeffding range proxy vs. `99` true Freedman
   variance at `a = 1, b = 99` — `25.25×` gain!), vs. unbounded-range kurtosis blowup `2 * M^2` at fixed variance `2`.
4. **Doob–Wald Optional Stopping Conservation vs. Unbounded Doubling Martingale Paradox**
   (`optional_stopping_two_step_conservation_vs_unbounded_doubling_paradox`):
   Proves exact martingale expectation conservation `𝔼[X_τ] = 4 * x0` across ALL `8` adaptive
   stopping policies on a 2-step heteroskedastic martingale tree, and proves by induction on `T : Nat`
   that the truncated doubling martingale satisfies `(2^T - 1) * 1 + 1 * (-(2^T - 1)) = 0` for all `T`,
   whereas dropping bounded horizon / uniform integrability claims `+1 ≠ 0`.
-/

namespace CommonGround.InformationRecovery.CsiszarMartingaleFreedmanFrontier

def sqInt (z : Int) : Int := z * z

theorem sqInt_nonneg (z : Int) : 0 ≤ sqInt z := by
  unfold sqInt
  by_cases h : 0 ≤ z
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -z := by omega
    have hm : 0 ≤ (-z) * (-z) := Int.mul_nonneg hn hn
    grind

theorem sqInt_eq_zero_iff (z : Int) : sqInt z = 0 ↔ z = 0 := by
  unfold sqInt
  constructor
  · intro hz
    by_cases h0 : z = 0
    · exact h0
    · by_cases hp : 0 < z
      · have hpos : 0 < z * z := Int.mul_pos hp hp
        omega
      · have hn : 0 < -z := by omega
        have hpos : 0 < (-z) * (-z) := Int.mul_pos hn hn
        have heq : (-z) * (-z) = z * z := by grind
        omega
  · intro hz
    subst hz
    rfl

def absInt (z : Int) : Int := if 0 ≤ z then z else -z

theorem sq_absInt (z : Int) : sqInt (absInt z) = sqInt z := by
  unfold absInt sqInt
  split <;> grind

theorem absInt_sq_sub (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    absInt (sqInt a - sqInt b) = absInt (a - b) * (a + b) := by
  have hp : 0 ≤ a + b := by omega
  have hf : sqInt a - sqInt b = (a - b) * (a + b) := by unfold sqInt; grind
  rw [hf]
  unfold absInt
  by_cases h : 0 ≤ a - b
  · have hprod : 0 ≤ (a - b) * (a + b) := Int.mul_nonneg h hp
    rw [if_pos hprod, if_pos h]
  · rw [if_neg h]
    by_cases hprod : 0 ≤ (a - b) * (a + b)
    · have hn : 0 ≤ b - a := by omega
      have hprod2 : 0 ≤ (b - a) * (a + b) := Int.mul_nonneg hn hp
      have heq : (b - a) * (a + b) = -((a - b) * (a + b)) := by grind
      have heq2 : -(a - b) * (a + b) = -((a - b) * (a + b)) := by grind
      rw [if_pos hprod]
      omega
    · rw [if_neg hprod]
      grind

/-! ## 1. Denominator-Free Csiszár Perspective Identity & Sufficiency Zero-Slack vs. Signed Quasi-Probability -/

/-- Exact polynomial perspective identity underlying Csiszár $f$-divergence data processing:
    `q₁ q₂ (p₁ + p₂)² + (q₁ p₂ - q₂ p₁)² = (q₁ + q₂) (q₂ p₁² + q₁ p₂²)`. -/
theorem perspective_quadratic_exact_identity (p1 p2 q1 q2 : Int) :
    q1 * q2 * sqInt (p1 + p2) + sqInt (q1 * p2 - q2 * p1) =
      (q1 + q2) * (q2 * sqInt p1 + q1 * sqInt p2) := by
  unfold sqInt
  grind

/-- Csiszár $\chi^2$ Data Processing & Sufficiency Characterization vs. Signed Quasi-Probability Failure:
    1. When `0 < q1` and `0 < q2`, coarse-graining `(p1, p2) ↦ p1 + p2` satisfies
       `q1 * q2 * (p1 + p2)^2 ≤ (q1 + q2) * (q2 * p1^2 + q1 * p2^2)`,
    2. Equality holds if and only if the fiber likelihood ratio is constant (`q1 * p2 = q2 * p1`),
    3. Signed quasi-probability counterexample (`q1 = 2, q2 = -1`, `q1 + q2 = 1 > 0` yet `q1 * q2 = -2 < 0`):
       for `p1 = 1, p2 = 0`, `(p1 + p2)^2 / (q1 + q2) = 1 > 1/2 = p1^2/q1 + p2^2/q2`
       (i.e. `2 * (p1 + p2)^2 = 2 > 1 = (q1 + q2) * (p1^2 * 1 + 0)`). -/
theorem perspective_convex_subadditivity_and_sufficiency_zero_slack_vs_quasiprobability_failure :
    (∀ p1 p2 q1 q2 : Int, 0 < q1 → 0 < q2 →
      q1 * q2 * sqInt (p1 + p2) ≤ (q1 + q2) * (q2 * sqInt p1 + q1 * sqInt p2)) ∧
    (∀ p1 p2 q1 q2 : Int,
      q1 * q2 * sqInt (p1 + p2) = (q1 + q2) * (q2 * sqInt p1 + q1 * sqInt p2) ↔
        q1 * p2 = q2 * p1) ∧
    (let p1 : Int := 1; let p2 : Int := 0; let q1 : Int := 2; let q2 : Int := -1
     0 < q1 + q2 ∧ q1 * q2 < 0 ∧
     2 * sqInt (p1 + p2) > (q1 + q2) * (1 * sqInt p1 - 2 * sqInt p2)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p1 p2 q1 q2 _ _
    have hid := perspective_quadratic_exact_identity p1 p2 q1 q2
    have hsq := sqInt_nonneg (q1 * p2 - q2 * p1)
    omega
  · intro p1 p2 q1 q2
    have hid := perspective_quadratic_exact_identity p1 p2 q1 q2
    have hiff := sqInt_eq_zero_iff (q1 * p2 - q2 * p1)
    constructor
    · intro heq
      have hz : sqInt (q1 * p2 - q2 * p1) = 0 := by omega
      have hsub : q1 * p2 - q2 * p1 = 0 := hiff.mp hz
      omega
    · intro hprop
      have hsub : q1 * p2 - q2 * p1 = 0 := by omega
      have hz : sqInt (q1 * p2 - q2 * p1) = 0 := hiff.mpr hsub
      omega
  · decide

/-! ## 2. Hellinger–TV–$\chi^2$ Sandwich vs. Parametric Reverse-Pinsker Unbounded Blowup -/

/-- Squared Hellinger – Total Variation – Pearson $\chi^2$ Sandwich vs. Parametric Reverse-Pinsker Failure:
    1. Termwise Hellinger-to-$\chi^2$ bound: for all `a, b ≥ 0` (`p = a², q = b²`),
       `b² (a - b)² ≤ (a² - b²)²` (since `(a² - b²)² - b²(a - b)² = (a - b)² (a² + 2ab) ≥ 0`),
    2. 2-state Le Cam Hellinger–TV Cauchy–Schwarz bound: for all `a0, b0, a1, b1 ≥ 0`,
       `(|a0² - b0²| + |a1² - b1²|)² ≤ ((a0 - b0)² + (a1 - b1)²) · ((a0 + b0)² + (a1 + b1)²)`,
    3. Parametric Reverse-Pinsker / Reverse-$\chi^2$ Failure: on two-point distributions of total mass `M ≥ 2`,
       `P_M = (M, 0)` and `Q_M = (1, M - 1)` have half-L1 distance `TV_num = M - 1` (`TV_num² = (M - 1)²`),
       whereas the scaled Pearson $\chi^2$ numerator `(M - 1)² (M - 1) + (-(M - 1))² · 1` equals
       `M · (M - 1)² = M · TV_num²`, blowing up at rate `M → ∞` as `q_min = 1/M → 0`! -/
theorem hellinger_tv_chisquare_sandwich_vs_reverse_pinsker_unbounded_ratio :
    (∀ a b : Int, 0 ≤ a → 0 ≤ b →
      sqInt b * sqInt (a - b) ≤ sqInt (sqInt a - sqInt b)) ∧
    (∀ a0 b0 a1 b1 : Int, 0 ≤ a0 → 0 ≤ b0 → 0 ≤ a1 → 0 ≤ b1 →
      sqInt (absInt (sqInt a0 - sqInt b0) + absInt (sqInt a1 - sqInt b1)) ≤
        (sqInt (a0 - b0) + sqInt (a1 - b1)) * (sqInt (a0 + b0) + sqInt (a1 + b1))) ∧
    (∀ M : Int, 2 ≤ M →
      let tvNum := M - 1
      let chi2Scaled := sqInt (M - 1) * (M - 1) + sqInt (0 - (M - 1)) * 1
      chi2Scaled = M * sqInt tvNum ∧ 0 < sqInt tvNum) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b ha hb
    have hdiff :
        sqInt (sqInt a - sqInt b) - sqInt b * sqInt (a - b) =
          sqInt (a - b) * (sqInt a + 2 * (a * b)) := by
      unfold sqInt
      grind
    have hs1 : 0 ≤ sqInt (a - b) := sqInt_nonneg (a - b)
    have hs2 : 0 ≤ sqInt a := sqInt_nonneg a
    have hab : 0 ≤ a * b := Int.mul_nonneg ha hb
    have hsum : 0 ≤ sqInt a + 2 * (a * b) := by omega
    have hprod : 0 ≤ sqInt (a - b) * (sqInt a + 2 * (a * b)) := Int.mul_nonneg hs1 hsum
    omega
  · intro a0 b0 a1 b1 ha0 hb0 ha1 hb1
    rw [absInt_sq_sub a0 b0 ha0 hb0, absInt_sq_sub a1 b1 ha1 hb1]
    have hlag :
        (sqInt (absInt (a0 - b0)) + sqInt (absInt (a1 - b1))) *
            (sqInt (a0 + b0) + sqInt (a1 + b1)) -
          sqInt (absInt (a0 - b0) * (a0 + b0) + absInt (a1 - b1) * (a1 + b1)) =
        sqInt (absInt (a0 - b0) * (a1 + b1) - absInt (a1 - b1) * (a0 + b0)) := by
      unfold sqInt
      grind
    have hcsNonneg := sqInt_nonneg (absInt (a0 - b0) * (a1 + b1) - absInt (a1 - b1) * (a0 + b0))
    rw [sq_absInt (a0 - b0), sq_absInt (a1 - b1)] at hlag
    omega
  · intro M hM
    dsimp only
    constructor
    · unfold sqInt
      grind
    · unfold sqInt
      have hpos : 0 < M - 1 := by omega
      exact Int.mul_pos hpos hpos

/-! ## 3. Hoeffding Range Parabola & Freedman Variance Gain vs. Heavy-Tail 4th-Moment Spike -/

/-- Freedman / Bernstein Variance Gain over Azuma–Hoeffding vs. Unbounded Heavy-Tail Kurtosis:
    1. Bounded-range parabola: for `-c ≤ x ≤ c`, `x² ≤ c²` (`c² - x² = (c - x)(c + x) ≥ 0`),
    2. Asymmetric zero-mean increment (`P(X = b) = a/(a+b), P(X = -a) = b/(a+b)`):
       true variance `𝔼[X²] = a b` satisfies `4 a b + (a - b)² = (a + b)²`, so the Hoeffding
       worst-case range proxy `(a + b)² / 4` exceeds true variance `a b` by `(a - b)² / 4`!
       At `a = 1, b = 99` (`1%` rare spike), `4 · Var = 396 < 10,000 = R²` (`25.25×` tighter!),
    3. Heavy-tail symmetric spike counterexample: the 3-point symmetric law taking `±M` with weight `1`
       each and `0` with weight `M² - 2` (`M ≥ 2`, total weight `M²`) has fixed unit-order variance
       `(1 · M² + 1 · M²) = 2 · M²` (`𝔼[X²] = 2`), YET its 4th moment `(1 · M⁴ + 1 · M⁴) = 2 M² · M²`
       gives `𝔼[X⁴] = 2 M² → ∞`, violating Bernstein boundedness! -/
theorem hoeffding_range_bound_and_freedman_variance_gain_vs_heavy_tail_kurtosis :
    (∀ x c : Int, -c ≤ x → x ≤ c → sqInt x ≤ sqInt c) ∧
    (∀ a b : Int,
      a * sqInt b + b * sqInt (-a) = (a + b) * (a * b) ∧
      sqInt (a + b) - 4 * (a * b) = sqInt (a - b)) ∧
    (4 * (1 * 99) = 396 ∧ sqInt (1 + 99) = 10000 ∧ 25 * 396 < 10000) ∧
    (∀ M : Int, 2 ≤ M →
      let totalW := sqInt M
      let mom2 := sqInt M + sqInt (-M)
      let mom4 := sqInt (sqInt M) + sqInt (sqInt (-M))
      mom2 = 2 * totalW ∧ mom4 = (2 * sqInt M) * totalW) := by
  refine ⟨?_, ?_, by decide, ?_⟩
  · intro x c hlow hhigh
    have h1 : 0 ≤ c - x := by omega
    have h2 : 0 ≤ c + x := by omega
    have hprod : 0 ≤ (c - x) * (c + x) := Int.mul_nonneg h1 h2
    have hid : sqInt c - sqInt x = (c - x) * (c + x) := by
      unfold sqInt
      grind
    omega
  · intro a b
    unfold sqInt
    constructor <;> grind
  · intro M _
    dsimp only
    unfold sqInt
    constructor <;> grind

/-! ## 4. Doob–Wald Optional Stopping Conservation vs. Unbounded Doubling Martingale Paradox -/

/-- Stopped value sum across all `4` equiprobable coin paths `(ξ₁, ξ₂) ∈ {±1}²` of a 2-step
    heteroskedastic martingale starting at `x0` with step-1 amplitude `d1` and path-dependent
    step-2 amplitudes `d2Up` (after `+d1`) and `d2Down` (after `-d1`), under an arbitrary
    adapted stopping policy `(stop0, stopUp, stopDown) : Bool × Bool × Bool`. -/
def twoStepMartingaleStoppedSum (x0 d1 d2Up d2Down : Int)
    (stop0 stopUp stopDown : Bool) : Int :=
  if stop0 then
    4 * x0
  else
    let sumUp :=
      if stopUp then 2 * (x0 + d1)
      else (x0 + d1 + d2Up) + (x0 + d1 - d2Up)
    let sumDown :=
      if stopDown then 2 * (x0 - d1)
      else (x0 - d1 + d2Down) + (x0 - d1 - d2Down)
    sumUp + sumDown

/-- Stopped quadratic variation `∑_{ω} ((X_τ(ω) - x0)²)` vs. expected stopped increment energy
    `∑_{ω} ∑_{t ≤ τ(ω)} (ΔX_t(ω))²` across all `4` paths. -/
def twoStepStoppedEnergy (d1 d2Up d2Down : Int) (stop0 stopUp stopDown : Bool) : Int :=
  if stop0 then 0
  else
    let eUp :=
      if stopUp then 2 * sqInt d1
      else sqInt (d1 + d2Up) + sqInt (d1 - d2Up)
    let eDown :=
      if stopDown then 2 * sqInt (-d1)
      else sqInt (-d1 + d2Down) + sqInt (-d1 - d2Down)
    eUp + eDown

def twoStepPredictableQuadVar (d1 d2Up d2Down : Int) (stop0 stopUp stopDown : Bool) : Int :=
  if stop0 then 0
  else
    4 * sqInt d1 +
      (if stopUp then 0 else 2 * sqInt d2Up) +
      (if stopDown then 0 else 2 * sqInt d2Down)

def pow2Int : Nat → Int
  | 0 => 1
  | T + 1 => 2 * pow2Int T

/-- Weighted path sum `(2^T - 1) · (+1) + 1 · (-(2^T - 1))` of the doubling martingale
    truncated at any finite horizon `T : Nat`:
    `2^T - 1` paths win `+1` before/by step `T`, and the `1` all-losses path loses `-(2^T - 1)`. -/
def doublingTruncatedExpectationNum (T : Nat) : Int :=
  (pow2Int T - 1) * 1 + 1 * (-(pow2Int T - 1))

theorem pow2Int_pos (T : Nat) : 1 ≤ pow2Int T := by
  induction T with
  | zero => decide
  | succ k ih =>
    unfold pow2Int
    omega

/-- Doob–Wald Optional Stopping Conservation vs. Unbounded Doubling Martingale Paradox:
    1. For EVERY initial state `x0`, heteroskedastic step amplitudes `d1, d2Up, d2Down`, and
       adapted stopping rule `(stop0, stopUp, stopDown)`, `twoStepMartingaleStoppedSum = 4 * x0`
       AND `twoStepStoppedEnergy = twoStepPredictableQuadVar` (optional quadratic variation identity!),
    2. For EVERY finite truncation horizon `T : Nat`, the doubling martingale has exact zero
       expected net gain (`doublingTruncatedExpectationNum T = 0`), while the worst-case loss on the
       surviving tail path `-(2^T - 1)` diverges unboundedly (`pow2Int (T + 1) - 1 > pow2Int T - 1`),
       explaining why `𝔼[G_τ] = +1 ≠ 0 = 𝔼[G_0]` violates Optional Stopping when uniform integrability fails! -/
theorem optional_stopping_two_step_conservation_vs_unbounded_doubling_paradox :
    (∀ x0 d1 d2Up d2Down : Int, ∀ s0 sU sD : Bool,
      twoStepMartingaleStoppedSum x0 d1 d2Up d2Down s0 sU sD = 4 * x0 ∧
      twoStepStoppedEnergy d1 d2Up d2Down s0 sU sD =
        twoStepPredictableQuadVar d1 d2Up d2Down s0 sU sD) ∧
    (∀ T : Nat,
      doublingTruncatedExpectationNum T = 0 ∧
      pow2Int T - 1 < pow2Int (T + 1) - 1) ∧
    ((1 : Int) ≠ 0) := by
  refine ⟨?_, ?_, by decide⟩
  · intro x0 d1 d2Up d2Down s0 sU sD
    cases s0 <;> cases sU <;> cases sD <;>
      simp [twoStepMartingaleStoppedSum, twoStepStoppedEnergy, twoStepPredictableQuadVar, sqInt] <;>
      grind
  · intro T
    constructor
    · unfold doublingTruncatedExpectationNum
      omega
    · have hp := pow2Int_pos T
      have hstep : pow2Int (T + 1) = 2 * pow2Int T := rfl
      omega

end CommonGround.InformationRecovery.CsiszarMartingaleFreedmanFrontier
