/-!
# Cramér–Rao Score Information Bound, Exponential-Family Efficiency, and
# Helmert–Kingman–Aldous `S_n`-Equicorrelation Spectral Rigidity

This standalone, pure-core Lean 4.33.0 frontier module (`0` imports, `0` sorrys) unifies
Folder `01` (Blackwell sufficiency), Folder `02` (moment compression), and Folder `03`
(`InformationRecoveryTrilogy` & `DeFinettiExchangeableSufficiencyAndSpectralPoincareGap`)
by proving two universal, denominator-free integer identities and their sharp premise boundaries:

1. **Weighted Integer Cauchy–Schwarz & Universal Discrete Cramér–Rao Lower Bound**:
   - `weighted_cauchy_schwarz_range_int`: for arbitrary `N : Nat` and non-negative weights `0 ≤ P(x)`,
     `(∑_{x<N} P(x) u(x) v(x))² ≤ (∑_{x<N} P(x) u(x)²) · (∑_{x<N} P(x) v(x)²)`
     proved via non-negative weighted discriminant `∑_{x<N} P(x) (A u(x) - B v(x))² ≥ 0`.
   - `cramer_rao_discrete_score_variance_lower_bound`: for any zero-mean score perturbation
     `∑_{x<N} P(x) s(x) = 0` (`S_P = ∑ P(x)`, `μ_P = ∑ P(x) T(x)`),
     `(S_P · ∑_{x<N} P(x) T(x) s(x))² ≤ VarScaled(P, S_P, μ_P, T) · FisherInfo(P, s)`.
   - `cramer_rao_exponential_family_score_attainment`: proves exact equality (`LHS = RHS`)
     whenever `S_P · T(x) - μ_P = k · s(x)` (Darmois–Koopman–Pitman natural-statistic efficiency).
   - `moving_support_super_efficiency_counterexample`: proves on `N = 2` (`P = [1, 0]`, `Q = [0, 1]`,
     `T = [0, 1]`, discrete `Uniform[0, θ]` boundary shift) that moving support yields zero variance
     under `P` while `E_Q[T] - E_P[T] = 1 ≠ 0`!

2. **Helmert–Kingman–Aldous `S_n`-Equicorrelation Spectral Decomposition & Exchangeability Rigidity**:
   - `lagrange_pairwise_diff_sq_identity`: for arbitrary `n : Nat` and `u : Nat → Int`,
     `∑_{j<n} ∑_{i<j} (u_i - u_j)² = n · (∑_{i<n} u_i²) - (∑_{i<n} u_i)²`.
   - `helmert_equicorrelation_quadratic_identity`: decomposes every `S_n`-invariant bilinear
     quadratic form `Q_n(a, b; u) = a ∑_{i<n} u_i² + 2b ∑_{i<j<n} u_i u_j` into orthogonal
     irreducible `Triv_1 ⊕ Std_{n-1}` eigenspaces:
     `n · Q_n(a, b; u) = (a + (n - 1) b) · (∑_{i<n} u_i)² + (a - b) · ∑_{i<j<n} (u_i - u_j)²`.
   - `equicorrelation_psd_and_aldous_kingman_floor`: proves exact PSD sufficiency (`0 ≤ a - b` and
     `0 ≤ a + (n - 1)b`), the Aldous–Kingman negative-correlation floor `0 ≤ a + (n - 1)b` for
     `1 ≤ n`, and tight attainment (`= 0`) by finite without-replacement urn draws `(a, b) = (n - 1, -1)`.
   - `infinite_exchangeable_nonneg_correlation_rigidity`: proves that any infinitely extendable
     `FullyExchangeable` pair (`0 ≤ a + (n - 1)b` for all `n ≥ 1`, with `0 ≤ a`) satisfies **`0 ≤ b`**,
     ruling out negative pairwise correlations in infinite exchangeable processes!
-/

namespace CommonGround.Frontier.CramerRaoAndHelmertExchangeableRigidity

/-! ## Elementary Range Summation & Integer Order Infrastructure -/

def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

theorem sumRange_add (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih =>
    simp only [sumRange, ih]
    omega

theorem sumRange_sub (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i - g i) = sumRange n f - sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih =>
    simp only [sumRange, ih]
    omega

theorem sumRange_const_mul (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih =>
    simp only [sumRange, ih, Int.mul_add]

theorem sumRange_const (n : Nat) (c : Int) :
    sumRange n (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih =>
    simp only [sumRange, ih, Int.natCast_add, Int.add_mul]
    omega

theorem sumRange_congr (n : Nat) (f g : Nat → Int)
    (hfg : ∀ i : Nat, i < n → f i = g i) :
    sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have hm : sumRange m f = sumRange m g :=
      ih (fun i hi => hfg i (Nat.lt_succ_of_lt hi))
    have hl : f m = g m := hfg m (Nat.lt_succ_self m)
    simp only [sumRange, hm, hl]

theorem sq_nonneg_int (z : Int) : 0 ≤ z * z := by
  by_cases hz : 0 ≤ z
  · exact Int.mul_nonneg hz hz
  · have hneg : 0 ≤ -z := by omega
    have hp : 0 ≤ (-z) * (-z) := Int.mul_nonneg hneg hneg
    have heq : (-z) * (-z) = z * z := by simp [Int.neg_mul, Int.mul_neg]
    omega

theorem sumRange_nonneg (n : Nat) (f : Nat → Int)
    (hf : ∀ i : Nat, i < n → 0 ≤ f i) :
    0 ≤ sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih =>
    have hp := ih (fun i hi => hf i (Nat.lt_succ_of_lt hi))
    have hl := hf m (Nat.lt_succ_self m)
    simp only [sumRange]
    omega

theorem cancel_pos_mul_left {a x y : Int} (ha : 0 < a) (h : a * x ≤ a * y) :
    x ≤ y := by
  by_cases hxy : x ≤ y
  · exact hxy
  · have hgt : 0 < x - y := by omega
    have hprod : 0 < a * (x - y) := Int.mul_pos ha hgt
    have hexp : a * (x - y) = a * x - a * y := Int.mul_sub a x y
    omega

theorem zero_of_weighted_sq_sum_eq_zero (n : Nat) (P v : Nat → Int)
    (hP : ∀ x : Nat, x < n → 0 ≤ P x)
    (hzero : sumRange n (fun x => P x * (v x * v x)) = 0) :
    ∀ x : Nat, x < n → P x * (v x * v x) = 0 := by
  induction n with
  | zero =>
    intro x hx
    exact False.elim (Nat.not_lt_zero x hx)
  | succ m ih =>
    simp only [sumRange] at hzero
    have hprev_nn : 0 ≤ sumRange m (fun x => P x * (v x * v x)) :=
      sumRange_nonneg m _ (fun x hx => Int.mul_nonneg (hP x (Nat.lt_succ_of_lt hx)) (sq_nonneg_int (v x)))
    have hlast_nn : 0 ≤ P m * (v m * v m) :=
      Int.mul_nonneg (hP m (Nat.lt_succ_self m)) (sq_nonneg_int (v m))
    have hprev_z : sumRange m (fun x => P x * (v x * v x)) = 0 := by omega
    have hlast_z : P m * (v m * v m) = 0 := by omega
    intro x hx
    by_cases hxm : x = m
    · subst hxm
      exact hlast_z
    · have hlt : x < m := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hx) hxm
      exact ih (fun y hy => hP y (Nat.lt_succ_of_lt hy)) hprev_z x hlt

theorem prod_zero_of_mul_sq_zero {p u v : Int} (hp : 0 ≤ p) (hz : p * (v * v) = 0) :
    p * (u * v) = 0 := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · have hp_pos : 0 < p := by omega
    by_cases hv0 : v = 0
    · simp [hv0]
    · have hpos : 0 < p * (v * v) := by
        by_cases hvp : 0 < v
        · exact Int.mul_pos hp_pos (Int.mul_pos hvp hvp)
        · have hvn : 0 < -v := by omega
          have heq : (-v) * (-v) = v * v := by simp [Int.neg_mul, Int.mul_neg]
          have hv2 : 0 < v * v := by
            rw [← heq]
            exact Int.mul_pos hvn hvn
          exact Int.mul_pos hp_pos hv2
      omega

/-! ## Part 1: Weighted Integer Cauchy–Schwarz & Discrete Cramér–Rao Information Bound -/

theorem mul_pair_rearrange (a b x y : Int) :
    (a * x) * (b * y) = (a * b) * (x * y) := by
  rw [Int.mul_assoc a x (b * y), Int.mul_left_comm x b y, ← Int.mul_assoc a b (x * y)]

theorem weighted_discriminant_term (p A B ux vx : Int) :
    p * ((A * ux - B * vx) * (A * ux - B * vx)) =
      (A * A) * (p * (ux * ux)) - (2 * A * B) * (p * (ux * vx)) + (B * B) * (p * (vx * vx)) := by
  have h1 : (A * ux - B * vx) * (A * ux - B * vx) =
      (A * A) * (ux * ux) - (2 * A * B) * (ux * vx) + (B * B) * (vx * vx) := by
    simp only [Int.sub_mul, Int.mul_sub]
    rw [mul_pair_rearrange A A ux ux,
        mul_pair_rearrange A B ux vx,
        mul_pair_rearrange B A vx ux,
        mul_pair_rearrange B B vx vx]
    have hc1 : B * A = A * B := Int.mul_comm B A
    have hc2 : vx * ux = ux * vx := Int.mul_comm vx ux
    rw [hc1, hc2]
    have htwo : 2 * A * B * (ux * vx) = (A * B) * (ux * vx) + (A * B) * (ux * vx) := by
      have h2 : 2 * A * B = A * B + A * B := by
        rw [Int.mul_assoc 2 A B]
        omega
      rw [h2, Int.add_mul]
    omega
  rw [h1, Int.mul_add, Int.mul_sub]
  rw [← Int.mul_assoc p (A * A) (ux * ux), Int.mul_comm p (A * A), Int.mul_assoc (A * A) p (ux * ux)]
  rw [← Int.mul_assoc p (2 * A * B) (ux * vx), Int.mul_comm p (2 * A * B), Int.mul_assoc (2 * A * B) p (ux * vx)]
  rw [← Int.mul_assoc p (B * B) (vx * vx), Int.mul_comm p (B * B), Int.mul_assoc (B * B) p (vx * vx)]

/-- **Universal Weighted Integer Buniakovsky–Cauchy–Schwarz Inequality**:
For any `N : Nat` and non-negative weights `0 ≤ P(x)`,
`(∑_{x<N} P(x) u(x) v(x))² ≤ (∑_{x<N} P(x) u(x)²) · (∑_{x<N} P(x) v(x)²)`. -/
theorem weighted_cauchy_schwarz_range_int
    (N : Nat) (P u v : Nat → Int)
    (hP : ∀ x : Nat, x < N → 0 ≤ P x) :
    sumRange N (fun x => P x * (u x * v x)) * sumRange N (fun x => P x * (u x * v x)) ≤
      sumRange N (fun x => P x * (u x * u x)) * sumRange N (fun x => P x * (v x * v x)) := by
  let U := sumRange N (fun x => P x * (u x * u x))
  let A := sumRange N (fun x => P x * (v x * v x))
  let B := sumRange N (fun x => P x * (u x * v x))
  have hA_nn : 0 ≤ A :=
    sumRange_nonneg N _ (fun x hx => Int.mul_nonneg (hP x hx) (sq_nonneg_int (v x)))
  by_cases hA0 : A = 0
  · have hterm0 := zero_of_weighted_sq_sum_eq_zero N P v hP hA0
    have hB0 : B = 0 := by
      have hcg : sumRange N (fun x => P x * (u x * v x)) = sumRange N (fun _ => 0) := by
        apply sumRange_congr
        intro x hx
        exact prod_zero_of_mul_sq_zero (hP x hx) (hterm0 x hx)
      dsimp [B]
      rw [hcg, sumRange_const]
      omega
    change B * B ≤ U * A
    rw [hA0, hB0]
    omega
  · have hA_pos : 0 < A := by omega
    have hdisc_nn : 0 ≤ sumRange N (fun x => P x * ((A * u x - B * v x) * (A * u x - B * v x))) :=
      sumRange_nonneg N _ (fun x hx => Int.mul_nonneg (hP x hx) (sq_nonneg_int _))
    have hexp :
        sumRange N (fun x => P x * ((A * u x - B * v x) * (A * u x - B * v x))) =
          (A * A) * U - (2 * A * B) * B + (B * B) * A := by
      have hcg :
          sumRange N (fun x => P x * ((A * u x - B * v x) * (A * u x - B * v x))) =
            sumRange N (fun x =>
              (A * A) * (P x * (u x * u x)) - (2 * A * B) * (P x * (u x * v x)) +
                (B * B) * (P x * (v x * v x))) := by
        apply sumRange_congr
        intro x _
        exact weighted_discriminant_term (P x) A B (u x) (v x)
      rw [hcg, sumRange_add, sumRange_sub, sumRange_const_mul, sumRange_const_mul, sumRange_const_mul]
    rw [hexp] at hdisc_nn
    have h2 : (2 * A * B) * B = 2 * (A * (B * B)) := by
      have htwo : 2 * A * B = 2 * (A * B) := Int.mul_assoc 2 A B
      rw [htwo, Int.mul_assoc 2 (A * B) B, Int.mul_assoc A B B]
    have hba : (B * B) * A = A * (B * B) := Int.mul_comm (B * B) A
    have hau : (A * A) * U = A * (U * A) := by
      rw [Int.mul_assoc A A U, Int.mul_comm A U]
    rw [h2, hba, hau] at hdisc_nn
    have hmul : A * (B * B) ≤ A * (U * A) := by omega
    exact cancel_pos_mul_left hA_pos hmul

/-- Zero-mean score centering: when `∑_{x<N} P(x) s(x) = 0`, subtracting any constant `μ_P`
from `S_P · T(x)` leaves the score inner product invariant. -/
theorem centered_score_inner_eq
    (N : Nat) (P T s : Nat → Int) (S_P μ_P : Int)
    (hZeroMean : sumRange N (fun x => P x * s x) = 0) :
    sumRange N (fun x => P x * ((S_P * T x - μ_P) * s x)) =
      S_P * sumRange N (fun x => P x * (T x * s x)) := by
  have hcg :
      sumRange N (fun x => P x * ((S_P * T x - μ_P) * s x)) =
        sumRange N (fun x => S_P * (P x * (T x * s x)) - μ_P * (P x * s x)) := by
    apply sumRange_congr
    intro x _
    simp only [Int.sub_mul, Int.mul_sub]
    have h1 : P x * (S_P * T x * s x) = S_P * (P x * (T x * s x)) := by
      rw [Int.mul_assoc S_P (T x) (s x), ← Int.mul_assoc (P x) S_P _,
          Int.mul_comm (P x) S_P, Int.mul_assoc S_P (P x) _]
    have h2 : P x * (μ_P * s x) = μ_P * (P x * s x) := by
      rw [← Int.mul_assoc (P x) μ_P (s x), Int.mul_comm (P x) μ_P, Int.mul_assoc μ_P (P x) (s x)]
    rw [h1, h2]
  rw [hcg, sumRange_sub, sumRange_const_mul, sumRange_const_mul, hZeroMean]
  omega

/-- **Universal Discrete Cramér–Rao Information Lower Bound**:
For any non-negative distribution weights `0 ≤ P(x)`, any zero-mean score `∑_{x<N} P(x) s(x) = 0`,
and any estimator `T : Nat → Int` with scaling constants `S_P, μ_P : Int`,
`(S_P · ∑_{x<N} P(x) T(x) s(x))² ≤ (∑_{x<N} P(x) (S_P · T(x) - μ_P)²) · (∑_{x<N} P(x) s(x)²)`. -/
theorem cramer_rao_discrete_score_variance_lower_bound
    (N : Nat) (P T s : Nat → Int) (S_P μ_P : Int)
    (hP : ∀ x : Nat, x < N → 0 ≤ P x)
    (hZeroMean : sumRange N (fun x => P x * s x) = 0) :
    (S_P * sumRange N (fun x => P x * (T x * s x))) *
        (S_P * sumRange N (fun x => P x * (T x * s x))) ≤
      sumRange N (fun x => P x * ((S_P * T x - μ_P) * (S_P * T x - μ_P))) *
        sumRange N (fun x => P x * (s x * s x)) := by
  have hcs := weighted_cauchy_schwarz_range_int N P (fun x => S_P * T x - μ_P) s hP
  rw [centered_score_inner_eq N P T s S_P μ_P hZeroMean] at hcs
  exact hcs

/-- **Darmois–Koopman–Pitman Exponential-Family Attainment**:
When the centered statistic `S_P · T(x) - μ_P` is proportional to the score `k · s(x)` on `{0, …, N-1}`,
the Cramér–Rao inequality holds with **exact equality**! -/
theorem cramer_rao_exponential_family_score_attainment
    (N : Nat) (P T s : Nat → Int) (S_P μ_P k : Int)
    (hProp : ∀ x : Nat, x < N → S_P * T x - μ_P = k * s x) :
    sumRange N (fun x => P x * ((S_P * T x - μ_P) * s x)) *
        sumRange N (fun x => P x * ((S_P * T x - μ_P) * s x)) =
      sumRange N (fun x => P x * ((S_P * T x - μ_P) * (S_P * T x - μ_P))) *
        sumRange N (fun x => P x * (s x * s x)) := by
  have hL :
      sumRange N (fun x => P x * ((S_P * T x - μ_P) * s x)) =
        k * sumRange N (fun x => P x * (s x * s x)) := by
    rw [← sumRange_const_mul]
    apply sumRange_congr
    intro x hx
    rw [hProp x hx, Int.mul_assoc k (s x) (s x), ← Int.mul_assoc (P x) k (s x * s x),
        Int.mul_comm (P x) k, Int.mul_assoc k (P x) (s x * s x)]
  have hR :
      sumRange N (fun x => P x * ((S_P * T x - μ_P) * (S_P * T x - μ_P))) =
        (k * k) * sumRange N (fun x => P x * (s x * s x)) := by
    rw [← sumRange_const_mul]
    apply sumRange_congr
    intro x hx
    rw [hProp x hx, mul_pair_rearrange k k (s x) (s x),
        ← Int.mul_assoc (P x) (k * k) (s x * s x),
        Int.mul_comm (P x) (k * k),
        Int.mul_assoc (k * k) (P x) (s x * s x)]
  rw [hL, hR]
  let I := sumRange N (fun x => P x * (s x * s x))
  change (k * I) * (k * I) = ((k * k) * I) * I
  rw [mul_pair_rearrange k k I I, ← Int.mul_assoc (k * k) I I]

/-- **Moving-Support Premise-Failure Counterexample (`supp(Q) ⊈ supp(P)`)**:
When `P = (1, 0)` and `Q = (0, 1)` have disjoint/moving support on `{0, 1}` with `T = (0, 1)`,
`T` has **zero** variance under `P` (`VarScaled = 0`), yet its expectation jumps by `1 ≠ 0`
between `P` and `Q` — breaking Cramér–Rao when regularity/support domination fails! -/
theorem moving_support_super_efficiency_counterexample :
    let P : Nat → Int := fun x => if x == 0 then 1 else 0
    let Q : Nat → Int := fun x => if x == 1 then 1 else 0
    let T : Nat → Int := fun x => if x == 1 then 1 else 0
    sumRange 2 (fun x => P x * (T x * T x)) = 0 ∧
    sumRange 2 (fun x => Q x * T x) - sumRange 2 (fun x => P x * T x) = 1 := by
  decide

/-! ## Part 2: Helmert–Kingman–Aldous `S_n`-Equicorrelation Spectral Rigidity -/

/-- `S_n`-invariant equicorrelation quadratic form
`Q_n(a, b; u) = a ∑_{i<n} u_i² + 2 b ∑_{i<j<n} u_i u_j`. -/
def equicorrQuadForm : Nat → Int → Int → (Nat → Int) → Int
  | 0, _, _, _ => 0
  | m + 1, a, b, u => equicorrQuadForm m a b u + a * (u m * u m) + 2 * b * sumRange m u * u m

/-- Pairwise squared difference sum `∑_{j<n} ∑_{i<j} (u_i - u_j)²`. -/
def pairwiseDiffSqSum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | m + 1, u => pairwiseDiffSqSum m u + sumRange m (fun i => (u i - u m) * (u i - u m))

/-- Exact closed form `Q_n(a, b; u) = (a - b) ∑_{i<n} u_i² + b (∑_{i<n} u_i)²`. -/
theorem equicorrQuadForm_eq_diag_plus_sum_sq (n : Nat) (a b : Int) (u : Nat → Int) :
    equicorrQuadForm n a b u =
      (a - b) * sumRange n (fun i => u i * u i) + b * (sumRange n u * sumRange n u) := by
  induction n with
  | zero =>
    simp [equicorrQuadForm, sumRange]
  | succ m ih =>
    simp only [equicorrQuadForm, sumRange, ih]
    let Sm := sumRange m u
    let Dm := sumRange m (fun i => u i * u i)
    change ((a - b) * Dm + b * (Sm * Sm)) + a * (u m * u m) + 2 * b * Sm * u m =
      (a - b) * (Dm + u m * u m) + b * ((Sm + u m) * (Sm + u m))
    have hsq : (Sm + u m) * (Sm + u m) = Sm * Sm + 2 * Sm * u m + u m * u m := by
      simp only [Int.add_mul, Int.mul_add]
      have hc : u m * Sm = Sm * u m := Int.mul_comm (u m) Sm
      have h2 : 2 * Sm * u m = Sm * u m + Sm * u m := by
        have ht : 2 * Sm = Sm + Sm := by omega
        rw [ht, Int.add_mul]
      omega
    rw [hsq, Int.mul_add, Int.mul_add, Int.mul_add]
    have h2b : 2 * b * Sm * u m = b * (2 * Sm * u m) := by
      simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    have hab : (a - b) * (u m * u m) + b * (u m * u m) = a * (u m * u m) := by
      rw [← Int.add_mul]
      have hs : (a - b) + b = a := by omega
      rw [hs]
    omega

/-- **Lagrange Pairwise Squared-Difference Identity**:
`∑_{j<n} ∑_{i<j} (u_i - u_j)² = n · (∑_{i<n} u_i²) - (∑_{i<n} u_i)²`. -/
theorem lagrange_pairwise_diff_sq_identity (n : Nat) (u : Nat → Int) :
    pairwiseDiffSqSum n u =
      (n : Int) * sumRange n (fun i => u i * u i) - sumRange n u * sumRange n u := by
  induction n with
  | zero =>
    simp [pairwiseDiffSqSum, sumRange]
  | succ m ih =>
    simp only [pairwiseDiffSqSum, sumRange, ih]
    have hstep :
        sumRange m (fun i => (u i - u m) * (u i - u m)) =
          sumRange m (fun i => u i * u i) - 2 * u m * sumRange m u + (m : Int) * (u m * u m) := by
      have hcg :
          sumRange m (fun i => (u i - u m) * (u i - u m)) =
            sumRange m (fun i => (u i * u i - 2 * u m * u i) + u m * u m) := by
        apply sumRange_congr
        intro i _
        simp only [Int.sub_mul, Int.mul_sub]
        have hc : u m * u i = u i * u m := Int.mul_comm (u m) (u i)
        have h2 : 2 * u m * u i = u m * u i + u m * u i := by
          have ht : 2 * u m = u m + u m := by omega
          rw [ht, Int.add_mul]
        omega
      rw [hcg, sumRange_add, sumRange_sub, sumRange_const_mul, sumRange_const]
    rw [hstep]
    let Sm := sumRange m u
    let Dm := sumRange m (fun i => u i * u i)
    change ((m : Int) * Dm - Sm * Sm) + (Dm - 2 * u m * Sm + (m : Int) * (u m * u m)) =
      ((m + 1 : Nat) : Int) * (Dm + u m * u m) - (Sm + u m) * (Sm + u m)
    have hcast : ((m + 1 : Nat) : Int) = (m : Int) + 1 := by simp [Int.natCast_add]
    have hsq : (Sm + u m) * (Sm + u m) = Sm * Sm + 2 * u m * Sm + u m * u m := by
      simp only [Int.add_mul, Int.mul_add]
      have hc : Sm * u m = u m * Sm := Int.mul_comm Sm (u m)
      have h2 : 2 * u m * Sm = u m * Sm + u m * Sm := by
        have ht : 2 * u m = u m + u m := by omega
        rw [ht, Int.add_mul]
      omega
    rw [hcast, hsq, Int.add_mul, Int.one_mul, Int.mul_add]
    omega

theorem pairwiseDiffSqSum_nonneg (n : Nat) (u : Nat → Int) :
    0 ≤ pairwiseDiffSqSum n u := by
  induction n with
  | zero => simp [pairwiseDiffSqSum]
  | succ m ih =>
    simp only [pairwiseDiffSqSum]
    have hs := sumRange_nonneg m _ (fun i _ => sq_nonneg_int (u i - u m))
    omega

/-- **Helmert–Kingman–Aldous `S_n`-Equicorrelation Spectral Decomposition**:
For every `n : Nat`, `a, b : Int`, and `u : Nat → Int`,
`n · Q_n(a, b; u) = (a + (n - 1) · b) · (∑_{i<n} u_i)² + (a - b) · ∑_{i<j<n} (u_i - u_j)²`. -/
theorem helmert_equicorrelation_quadratic_identity (n : Nat) (a b : Int) (u : Nat → Int) :
    (n : Int) * equicorrQuadForm n a b u =
      (a + ((n : Int) - 1) * b) * (sumRange n u * sumRange n u) +
        (a - b) * pairwiseDiffSqSum n u := by
  rw [equicorrQuadForm_eq_diag_plus_sum_sq, lagrange_pairwise_diff_sq_identity]
  let S2 := sumRange n u * sumRange n u
  let D := sumRange n (fun i => u i * u i)
  change (n : Int) * ((a - b) * D + b * S2) =
    (a + ((n : Int) - 1) * b) * S2 + (a - b) * ((n : Int) * D - S2)
  rw [Int.mul_add, Int.mul_sub]
  have h1 : (n : Int) * ((a - b) * D) = (a - b) * ((n : Int) * D) :=
    Int.mul_left_comm (n : Int) (a - b) D
  have h2 : (a + ((n : Int) - 1) * b) * S2 - (a - b) * S2 = (n : Int) * (b * S2) := by
    rw [← Int.sub_mul]
    have hcoef : (a + ((n : Int) - 1) * b) - (a - b) = (n : Int) * b := by
      rw [Int.sub_mul, Int.one_mul]
      omega
    rw [hcoef, Int.mul_assoc]
  omega

/-- **Exact PSD Sufficiency & Aldous–Kingman Finite-Exchangeability Floor**:
(1) `0 ≤ a - b` and `0 ≤ a + (n - 1) b` imply `0 ≤ Q_n(a, b; u)` for all `u : Nat → Int`.
(2) Conversely, for `1 ≤ n`, evaluating at `u ≡ 1` gives `Q_n(a, b; 1) = n · (a + (n - 1) b)`,
    forcing `0 ≤ a + (n - 1) b` (`b ≥ -a / (n - 1)`) whenever `Q_n` is PSD, attained with exact
    equality `0` by without-replacement urn draws `(a, b) = (n - 1, -1)`! -/
theorem equicorrelation_psd_and_aldous_kingman_floor (n : Nat) (a b : Int) :
    ((0 ≤ a - b ∧ 0 ≤ a + ((n : Int) - 1) * b) →
      ∀ u : Nat → Int, 0 ≤ equicorrQuadForm n a b u) ∧
    (1 ≤ n → 0 ≤ equicorrQuadForm n a b (fun _ => 1) →
      0 ≤ a + ((n : Int) - 1) * b) ∧
    (1 ≤ n → equicorrQuadForm n ((n : Int) - 1) (-1) (fun _ => 1) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨hab, heig⟩ u
    by_cases hn0 : n = 0
    · subst hn0
      simp [equicorrQuadForm]
    · have hn_pos : 0 < (n : Int) := by omega
      have hhelm := helmert_equicorrelation_quadratic_identity n a b u
      have ht1 : 0 ≤ (a + ((n : Int) - 1) * b) * (sumRange n u * sumRange n u) :=
        Int.mul_nonneg heig (sq_nonneg_int (sumRange n u))
      have ht2 : 0 ≤ (a - b) * pairwiseDiffSqSum n u :=
        Int.mul_nonneg hab (pairwiseDiffSqSum_nonneg n u)
      have hrhs : 0 ≤ (n : Int) * equicorrQuadForm n a b u := by omega
      have hz : (n : Int) * 0 ≤ (n : Int) * equicorrQuadForm n a b u := by
        simpa using hrhs
      exact cancel_pos_mul_left hn_pos hz
  · intro hn1 hones
    have hn_pos : 0 < (n : Int) := by omega
    have hval : equicorrQuadForm n a b (fun _ => 1) = (n : Int) * (a + ((n : Int) - 1) * b) := by
      rw [equicorrQuadForm_eq_diag_plus_sum_sq]
      have h1 : sumRange n (fun _ => (1 : Int) * 1) = (n : Int) := by
        rw [sumRange_const]
        omega
      have h2 : sumRange n (fun _ => (1 : Int)) = (n : Int) := by
        rw [sumRange_const]
        omega
      rw [h1, h2]
      have hexp :
          (a - b) * (n : Int) + b * ((n : Int) * (n : Int)) =
            (n : Int) * (a + ((n : Int) - 1) * b) := by
        rw [Int.sub_mul, Int.sub_mul, Int.one_mul, Int.mul_add, Int.mul_sub]
        have hc1 : a * (n : Int) = (n : Int) * a := Int.mul_comm a (n : Int)
        have hc2 : b * (n : Int) = (n : Int) * b := Int.mul_comm b (n : Int)
        have hc3 : b * ((n : Int) * (n : Int)) = (n : Int) * ((n : Int) * b) := by
          simp only [Int.mul_left_comm, Int.mul_comm]
        omega
      exact hexp
    rw [hval] at hones
    have hz : (n : Int) * 0 ≤ (n : Int) * (a + ((n : Int) - 1) * b) := by simpa using hones
    exact cancel_pos_mul_left hn_pos hz
  · intro _
    rw [equicorrQuadForm_eq_diag_plus_sum_sq]
    have h1 : sumRange n (fun _ => (1 : Int) * 1) = (n : Int) := by
      rw [sumRange_const]
      omega
    have h2 : sumRange n (fun _ => (1 : Int)) = (n : Int) := by
      rw [sumRange_const]
      omega
    rw [h1, h2]
    have hexp : (((n : Int) - 1) - (-1)) * (n : Int) + (-1) * ((n : Int) * (n : Int)) = 0 := by
      have hs : ((n : Int) - 1) - (-1) = (n : Int) := by omega
      rw [hs]
      omega
    exact hexp

/-- **Infinite Exchangeability Non-Negative Correlation Rigidity (`de Finetti Second-Moment Lock`)**:
If `0 ≤ a` and the Aldous–Kingman PSD condition `0 ≤ a + (n - 1) · b` holds for **every** finite
horizon `1 ≤ n` (`FullyExchangeable`), then **`0 ≤ b`**! -/
theorem infinite_exchangeable_nonneg_correlation_rigidity
    (a b : Int) (ha : 0 ≤ a)
    (hAll : ∀ n : Nat, 1 ≤ n → 0 ≤ a + ((n : Int) - 1) * b) :
    0 ≤ b := by
  by_cases hb : 0 ≤ b
  · exact hb
  · have hb_le : b ≤ -1 := by omega
    let n : Nat := a.toNat + 2
    have hn1 : 1 ≤ n := by omega
    have hspec := hAll n hn1
    have hcast_a : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
    have hn_cast : ((n : Int) - 1) = a + 1 := by
      dsimp [n]
      omega
    rw [hn_cast] at hspec
    have ha1_pos : 0 ≤ a + 1 := by omega
    have hmul : (a + 1) * b ≤ (a + 1) * (-1) := Int.mul_le_mul_of_nonneg_left hb_le ha1_pos
    omega

end CommonGround.Frontier.CramerRaoAndHelmertExchangeableRigidity
