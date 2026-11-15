/-
  Common Ground · Discovery 08 (Pure-Core Frontier Synthesis — Zero External Imports)
  ===================================================================================
  Module: `08-kakutani-and-galois-structural-duality/GaloisQuantileTransportAndSupermodularTopkisDuality.lean`

  Unifies four foundational order-theoretic & variational dualities in pure-core Lean 4.33.0
  (`0` imports, `0` sorrys, `0` floating-point or rational fractions):
    1. **Exact Discrete Galois Quantile–CDF Adjunction (`discQuantile N F u ≤ x ↔ u ≤ F x`)**:
       Proves for arbitrary grid size `N : Nat` and monotone schedule `F : Nat → Int` that
       `discQuantile N F` is left adjoint to `F`, with unit saturation `u ≤ F (discQuantile N F u)`
       and counit deflation `discQuantile N F (F x) ≤ x` — contrasted against BOTH non-monotone
       schedule breakdown (`2 ≤ F_nm 1` yet `discQuantile 3 F_nm 2 = 3 > 1`) and left-continuous
       strict-jump overshoot (`F_left = [0, 0, 1]` on `X ≡ 1` gives `2 > 1`).
    2. **Arbitrary-Grid 1D Kantorovich–Rubinstein Optimal Transport Attainment (`W₁ = ‖F_P - F_Q‖₁`)**:
       Proves exact Abel summation-by-parts `∑_{k≤N} δ_k φ_k = Δ_N φ_N - ∑_{k<N} Δ_k (φ_{k+1} - φ_k)`,
       deduces `⟨δ, φ⟩ ≤ ∑_{k<N} |Δ_k|` for every balanced mass difference (`Δ_N = 0`) and `1`-Lipschitz
       potential `φ`, and constructs an explicit `±1`-slope optimal potential `optPhi δ` achieving
       **exact equality** `⟨δ, optPhi δ⟩ = ∑_{k<N} |Δ_k|`!
    3. **Supermodular Monge Comonotone Quadratic Crossing Identity vs. Concave Metric Crossing**:
       Proves `((x₁ - y₁)² + (x₂ - y₂)²) + 2(x₂ - x₁)(y₂ - y₁) = (x₁ - y₂)² + (x₂ - y₁)²`, showing
       comonotone quantile pairing minimizes quadratic cost, whereas for the **concave metric**
       `g(0)=0, g(1)=3, g(2)=4` (satisfying triangle inequality!), comonotone `(0→1, 1→2)` is
       strictly suboptimal (`6 > 4`) compared to shared-mass book-keeping `(1→1, 0→2)`!
    4. **Constructive Knaster–Tarski Least Fixed Point on `{0, ..., N}` vs. Antitone Period-2 Flip**:
       Proves that `N` iterations from `0` of ANY monotone bounded map `T : Nat → Nat` on `{0, ..., N}`
       converge to the exact least fixed point (and least post-fixed point) of `T` without continuity
       or convexity — whereas antitone flip `T_anti(x) = 1 - x` on `{0, 1}` has **zero** fixed points
       and submodular payoffs reverse Topkis comparative statics (`1 → 0` as `θ` increases)!
-/

namespace GaloisQuantileTransportAndSupermodularTopkisDuality

/-! ## 1. Pure-Core Finite Sums, Integer Absolute Value & Lipschitz Sign Helpers -/

def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

theorem sumRange_congr {n : Nat} {f g : Nat → Int} (h : ∀ k, k < n → f k = g k) :
    sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [sumRange]
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h m (Nat.lt_succ_self m)]

theorem sumRange_le {n : Nat} {f g : Nat → Int} (h : ∀ k, k < n → f k ≤ g k) :
    sumRange n f ≤ sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih =>
    simp only [sumRange]
    have h1 := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have h2 := h m (Nat.lt_succ_self m)
    omega

theorem sumRange_neg (n : Nat) (f : Nat → Int) :
    -sumRange n f = sumRange n (fun k => -f k) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [sumRange]
    omega

def absInt (x : Int) : Int :=
  if 0 ≤ x then x else -x

def sgnInt (x : Int) : Int :=
  if 0 ≤ x then 1 else -1

theorem absInt_nonneg (x : Int) : 0 ≤ absInt x := by
  unfold absInt
  split <;> omega

theorem sgnInt_lipschitz (x : Int) : -1 ≤ -sgnInt x ∧ -sgnInt x ≤ 1 := by
  unfold sgnInt
  split <;> omega

theorem mul_neg_bounded_by_abs (d s : Int) (hs : -1 ≤ s ∧ s ≤ 1) :
    -(d * s) ≤ absInt d := by
  unfold absInt
  split
  · next hd =>
    have h1 : 0 ≤ d * (1 + s) := Int.mul_nonneg hd (by omega)
    rw [Int.mul_add, Int.mul_one] at h1
    omega
  · next hd =>
    have hnd : 0 ≤ -d := by omega
    have h2 : 0 ≤ (-d) * (1 - s) := Int.mul_nonneg hnd (by omega)
    rw [Int.mul_sub, Int.mul_one] at h2
    have h3 : (-d) * s = -(d * s) := by rw [Int.neg_mul]
    omega

theorem mul_neg_negSgn_eq_abs (d : Int) :
    -(d * (-sgnInt d)) = absInt d := by
  unfold sgnInt absInt
  split
  · simp
  · simp

/-! ## 2. Discrete Galois Quantile–CDF Adjunction (`discQuantile ⊣ F`) -/

/-- Constructive discrete quantile `min { x ≤ N | u ≤ F x }` scanned on `{0, ..., N}`. -/
def discQuantile : Nat → (Nat → Int) → Int → Nat
  | 0, _, _ => 0
  | n + 1, F, u => if u ≤ F n then discQuantile n F u else n + 1

theorem discQuantile_le (N : Nat) (F : Nat → Int) (u : Int) :
    discQuantile N F u ≤ N := by
  induction N with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    unfold discQuantile
    split
    · exact Nat.le_succ_of_le ih
    · exact Nat.le_refl (n + 1)

/-- Unit saturation (`le_cdf_quantile`): whenever `u ≤ F N`, `u ≤ F (discQuantile N F u)`. -/
theorem le_cdf_discQuantile {N : Nat} {F : Nat → Int} {u : Int} (hu : u ≤ F N) :
    u ≤ F (discQuantile N F u) := by
  induction N with
  | zero => exact hu
  | succ n ih =>
    unfold discQuantile
    split
    · next hle => exact ih hle
    · exact hu

/-- Counit & left-adjointness: if `F` is monotone on `{0, ..., N}`, `x ≤ N`, and `u ≤ F x`,
    then `discQuantile N F u ≤ x`. -/
theorem discQuantile_le_of_le_cdf {N : Nat} {F : Nat → Int}
    (hmono : ∀ i j, i ≤ j → j ≤ N → F i ≤ F j)
    {u : Int} {x : Nat} (hx : x ≤ N) (hux : u ≤ F x) :
    discQuantile N F u ≤ x := by
  induction N with
  | zero =>
    simp [discQuantile]
  | succ n ih =>
    by_cases hxeq : x = n + 1
    · rw [hxeq]
      exact discQuantile_le (n + 1) F u
    · have hxle : x ≤ n := by omega
      have hFn : F x ≤ F n := hmono x n hxle (Nat.le_succ n)
      have hun : u ≤ F n := by omega
      unfold discQuantile
      rw [if_pos hun]
      exact ih (fun i j hij hjn => hmono i j hij (Nat.le_succ_of_le hjn)) hxle

/-- **Exact Galois Quantile–CDF Adjunction**:
    For any monotone discrete CDF `F` on `{0, ..., N}`, threshold `u ≤ F N`, and point `x ≤ N`,
    `discQuantile N F u ≤ x ↔ u ≤ F x`, with counit `discQuantile N F (F x) ≤ x`. -/
theorem galois_quantile_cdf_adjunction {N : Nat} {F : Nat → Int}
    (hmono : ∀ i j, i ≤ j → j ≤ N → F i ≤ F j)
    {u : Int} (hu : u ≤ F N) {x : Nat} (hx : x ≤ N) :
    (discQuantile N F u ≤ x ↔ u ≤ F x) ∧
    u ≤ F (discQuantile N F u) ∧
    discQuantile N F (F x) ≤ x := by
  refine ⟨⟨?_, ?_⟩, le_cdf_discQuantile hu,
    discQuantile_le_of_le_cdf hmono hx (Int.le_refl (F x))⟩
  · intro hq
    have hsat := le_cdf_discQuantile hu
    have hFq : F (discQuantile N F u) ≤ F x := hmono (discQuantile N F u) x hq hx
    omega
  · intro hux
    exact discQuantile_le_of_le_cdf hmono hx hux

/-- Non-monotone schedule `F_nm = [0, 3, 1, 4]` and left-continuous strict-jump `F_left = [0, 0, 1]`
    on point-mass `X ≡ 1`:
    1. `F_nm` breaks `discQuantile 3 F_nm 2 ≤ 1 ↔ 2 ≤ F_nm 1` (`2 ≤ 3` yet `discQuantile = 3 > 1`).
    2. Replacing right-continuous `F_right(x) = P(X ≤ x) = [0, 1, 1]` by strict `F_left(x) = P(X < x) = [0, 0, 1]`
       shifts the quantile of `u = 1` out of the support `{1}` to `2`! -/
def cdfNonMono : Nat → Int
  | 0 => 0
  | 1 => 3
  | 2 => 1
  | _ => 4

def cdfRightAtom1 : Nat → Int
  | 0 => 0
  | _ => 1

def cdfLeftAtom1 : Nat → Int
  | 0 => 0
  | 1 => 0
  | _ => 1

theorem nonmonotone_and_left_continuous_strict_cdf_break_galois_adjunction :
    (2 ≤ cdfNonMono 1 ∧ discQuantile 3 cdfNonMono 2 = 3 ∧ ¬ (discQuantile 3 cdfNonMono 2 ≤ 1)) ∧
    (discQuantile 2 cdfRightAtom1 1 = 1 ∧ discQuantile 2 cdfLeftAtom1 1 = 2 ∧
      cdfLeftAtom1 1 < 1) := by
  decide

/-! ## 3. 1D Kantorovich–Rubinstein Dual Attainment (`W₁ = ‖F_P - F_Q‖₁`) & Monge Crossing -/

/-- Cumulative mass discrepancy `Δ_k = ∑_{j ≤ k} δ_j = F_P(k) - F_Q(k)`. -/
def cumSum (δ : Nat → Int) (k : Nat) : Int :=
  sumRange (k + 1) δ

theorem cumSum_zero (δ : Nat → Int) : cumSum δ 0 = δ 0 := by
  simp [cumSum, sumRange]

theorem cumSum_succ (δ : Nat → Int) (k : Nat) :
    cumSum δ (k + 1) = cumSum δ k + δ (k + 1) := by
  rfl

/-- **Exact Abel Summation-by-Parts Identity** for arbitrary grid size `N : Nat`:
    `∑_{k < N+1} δ_k φ_k = Δ_N φ_N - ∑_{k < N} Δ_k (φ_{k+1} - φ_k)`. -/
theorem abel_summation_by_parts (N : Nat) (δ φ : Nat → Int) :
    sumRange (N + 1) (fun k => δ k * φ k) =
      cumSum δ N * φ N - sumRange N (fun k => cumSum δ k * (φ (k + 1) - φ k)) := by
  induction N with
  | zero =>
    simp [sumRange, cumSum]
  | succ m ih =>
    have hlhs :
        sumRange (m + 2) (fun k => δ k * φ k) =
          sumRange (m + 1) (fun k => δ k * φ k) + δ (m + 1) * φ (m + 1) := rfl
    have hrhs_sum :
        sumRange (m + 1) (fun k => cumSum δ k * (φ (k + 1) - φ k)) =
          sumRange m (fun k => cumSum δ k * (φ (k + 1) - φ k)) +
            cumSum δ m * (φ (m + 1) - φ m) := rfl
    rw [hlhs, ih, hrhs_sum, cumSum_succ]
    rw [Int.add_mul, Int.mul_sub]
    omega

/-- Optimal `±1`-slope dual Kantorovich potential `φ*_0 = 0`, `φ*_{k+1} = φ*_k - sgn(Δ_k)`. -/
def optPhi (δ : Nat → Int) : Nat → Int
  | 0 => 0
  | k + 1 => optPhi δ k - sgnInt (cumSum δ k)

theorem optPhi_step (δ : Nat → Int) (k : Nat) :
    optPhi δ (k + 1) - optPhi δ k = -sgnInt (cumSum δ k) := by
  have hdef : optPhi δ (k + 1) = optPhi δ k - sgnInt (cumSum δ k) := rfl
  omega

theorem optPhi_is_one_lipschitz (δ : Nat → Int) (k : Nat) :
    -1 ≤ optPhi δ (k + 1) - optPhi δ k ∧ optPhi δ (k + 1) - optPhi δ k ≤ 1 := by
  rw [optPhi_step]
  exact sgnInt_lipschitz (cumSum δ k)

/-- **1D Kantorovich–Rubinstein Dual Upper Bound & Exact Attainment (`W₁ = ∑_{k<N} |F_P(k) - F_Q(k)|`)**:
    For any balanced mass difference `δ` (`cumSum δ N = 0`), every `1`-Lipschitz potential `φ`
    satisfies `⟨δ, φ⟩ ≤ ∑_{k<N} |Δ_k|`, and `optPhi δ` is `1`-Lipschitz and attains exact equality! -/
theorem kantorovich_rubinstein_duality_and_attainment (N : Nat) (δ : Nat → Int)
    (hbal : cumSum δ N = 0) :
    (∀ φ : Nat → Int, (∀ k, k < N → -1 ≤ φ (k + 1) - φ k ∧ φ (k + 1) - φ k ≤ 1) →
      sumRange (N + 1) (fun k => δ k * φ k) ≤ sumRange N (fun k => absInt (cumSum δ k))) ∧
    ((∀ k, k < N → -1 ≤ optPhi δ (k + 1) - optPhi δ k ∧ optPhi δ (k + 1) - optPhi δ k ≤ 1) ∧
      sumRange (N + 1) (fun k => δ k * optPhi δ k) = sumRange N (fun k => absInt (cumSum δ k))) := by
  constructor
  · intro φ hlip
    rw [abel_summation_by_parts, hbal, Int.zero_mul, Int.zero_sub, sumRange_neg]
    apply sumRange_le
    intro k hk
    exact mul_neg_bounded_by_abs (cumSum δ k) (φ (k + 1) - φ k) (hlip k hk)
  · refine ⟨fun k _ => optPhi_is_one_lipschitz δ k, ?_⟩
    rw [abel_summation_by_parts, hbal, Int.zero_mul, Int.zero_sub, sumRange_neg]
    apply sumRange_congr
    intro k _
    rw [optPhi_step]
    exact mul_neg_negSgn_eq_abs (cumSum δ k)

/-- **Monge–Fréchet–Hoeffding Quadratic Crossing Identity**:
    Comonotone sorting `(x₁,y₁), (x₂,y₂)` beats crossing `(x₁,y₂), (x₂,y₁)` by `2(x₂ - x₁)(y₂ - y₁) ≥ 0`. -/
theorem monge_comonotone_quadratic_crossing_identity (x₁ x₂ y₁ y₂ : Int) :
    ((x₁ - y₁) * (x₁ - y₁) + (x₂ - y₂) * (x₂ - y₂)) + 2 * ((x₂ - x₁) * (y₂ - y₁)) =
      (x₁ - y₂) * (x₁ - y₂) + (x₂ - y₁) * (x₂ - y₁) := by
  have h1 : (x₁ - y₁) * (x₁ - y₁) = x₁ * x₁ - 2 * (x₁ * y₁) + y₁ * y₁ := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm y₁ x₁]
    omega
  have h2 : (x₂ - y₂) * (x₂ - y₂) = x₂ * x₂ - 2 * (x₂ * y₂) + y₂ * y₂ := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm y₂ x₂]
    omega
  have h3 : (x₁ - y₂) * (x₁ - y₂) = x₁ * x₁ - 2 * (x₁ * y₂) + y₂ * y₂ := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm y₂ x₁]
    omega
  have h4 : (x₂ - y₁) * (x₂ - y₁) = x₂ * x₂ - 2 * (x₂ * y₁) + y₁ * y₁ := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm y₁ x₂]
    omega
  have h5 : (x₂ - x₁) * (y₂ - y₁) =
      x₂ * y₂ - x₂ * y₁ - x₁ * y₂ + x₁ * y₁ := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    omega
  omega

/-- Concave metric `g(0)=0, g(1)=3, g(2)=4` on `{0, 1, 2}`: satisfies the metric triangle inequality
    for ALL `x, y, z ∈ {0, 1, 2}`, yet for `P = (0, 1)` and `Q = (1, 2)`, comonotone quantile
    coupling `(0→1, 1→2)` costs `6` while shared-mass book-keeping `(1→1, 0→2)` costs `4 < 6`! -/
def concaveMetricDist (a b : Nat) : Int :=
  let d := if a ≤ b then b - a else a - b
  match d with
  | 0 => 0
  | 1 => 3
  | _ => 4

theorem concave_metric_breaks_comonotone_quantile_optimality_and_unbalanced_shift_failure :
    -- 1. `concaveMetricDist` is a genuine metric on `{0, 1, 2}` (symmetric, 0 on diagonal, triangle ineq)
    (∀ x : Fin 3, concaveMetricDist x.val x.val = 0) ∧
    (∀ x y z : Fin 3,
      concaveMetricDist x.val z.val ≤ concaveMetricDist x.val y.val + concaveMetricDist y.val z.val) ∧
    -- 2. Yet comonotone coupling `(0→1, 1→2)` costs `6 > 4` vs. non-comonotone `(1→1, 0→2)`!
    (concaveMetricDist 0 1 + concaveMetricDist 1 2 = 6 ∧
      concaveMetricDist 1 1 + concaveMetricDist 0 2 = 4) ∧
    -- 3. Unbalanced mass `δ = [1, 1]` (`Δ_1 = 2 ≠ 0`) violates potential shift invariance `⟨δ, φ + 5⟩ ≠ ⟨δ, φ⟩`
    (let δu := fun _ : Nat => (1 : Int)
     cumSum δu 1 = 2 ∧
     sumRange 2 (fun k => δu k * (0 + 5)) ≠ sumRange 2 (fun k => δu k * 0)) := by
  decide

/-! ## 4. Constructive Knaster–Tarski Least Fixed Point on `{0, ..., N}` vs. Antitone Cycle -/

def iterNat (T : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => T (iterNat T k x)

theorem iterNat_bdd {N : Nat} {T : Nat → Nat} (hbdd : ∀ a, a ≤ N → T a ≤ N) (k : Nat) :
    iterNat T k 0 ≤ N := by
  induction k with
  | zero => exact Nat.zero_le N
  | succ m ih =>
    simp only [iterNat]
    exact hbdd (iterNat T m 0) ih

theorem iterNat_asc {N : Nat} {T : Nat → Nat}
    (hmono : ∀ a b, a ≤ b → b ≤ N → T a ≤ T b)
    (hbdd : ∀ a, a ≤ N → T a ≤ N) (k : Nat) :
    iterNat T k 0 ≤ iterNat T (k + 1) 0 := by
  induction k with
  | zero => exact Nat.zero_le (T 0)
  | succ m ih =>
    simp only [iterNat]
    exact hmono (iterNat T m 0) (iterNat T (m + 1) 0) ih (iterNat_bdd hbdd (m + 1))

theorem iterNat_fixed_or_ge {N : Nat} {T : Nat → Nat}
    (hmono : ∀ a b, a ≤ b → b ≤ N → T a ≤ T b)
    (hbdd : ∀ a, a ≤ N → T a ≤ N) (k : Nat) :
    T (iterNat T k 0) = iterNat T k 0 ∨ k + 1 ≤ iterNat T (k + 1) 0 := by
  induction k with
  | zero =>
    simp only [iterNat]
    omega
  | succ m ih =>
    cases ih with
    | inl hfix =>
      left
      simp only [iterNat]
      rw [hfix, hfix]
    | inr hge =>
      have hasc : iterNat T (m + 1) 0 ≤ T (iterNat T (m + 1) 0) :=
        iterNat_asc hmono hbdd (m + 1)
      simp only [iterNat] at hge hasc ⊢
      omega

theorem iterNat_le_postfixed {N : Nat} {T : Nat → Nat}
    (hmono : ∀ a b, a ≤ b → b ≤ N → T a ≤ T b)
    {z : Nat} (hzN : z ≤ N) (hpost : T z ≤ z) (k : Nat) :
    iterNat T k 0 ≤ z := by
  induction k with
  | zero => exact Nat.zero_le z
  | succ m ih =>
    simp only [iterNat]
    have h1 : T (iterNat T m 0) ≤ T z := hmono (iterNat T m 0) z ih hzN
    omega

/-- **Constructive Knaster–Tarski Least Fixed-Point Theorem on `{0, ..., N}`**:
    For ANY monotone self-map `T` on `{0, ..., N}`, `x_* = iterNat T N 0` is both a genuine
    fixed point (`T x_* = x_* ≤ N`) and the least post-fixed point (`∀ z ≤ N, T z ≤ z → x_* ≤ z`). -/
theorem knaster_tarski_constructive_least_fixed_point (N : Nat) (T : Nat → Nat)
    (hmono : ∀ a b, a ≤ b → b ≤ N → T a ≤ T b)
    (hbdd : ∀ a, a ≤ N → T a ≤ N) :
    let xStar := iterNat T N 0
    xStar ≤ N ∧ T xStar = xStar ∧ (∀ z, z ≤ N → T z ≤ z → xStar ≤ z) := by
  refine ⟨iterNat_bdd hbdd N, ?_, fun z hzN hpost => iterNat_le_postfixed hmono hzN hpost N⟩
  have hdisj := iterNat_fixed_or_ge hmono hbdd N
  have htop := iterNat_bdd hbdd (N + 1)
  cases hdisj with
  | inl hfix => exact hfix
  | inr hge => omega

/-- **Topkis Supermodular Monotone Comparative Statics vs. Antitone Flip & Submodular Reversal**:
    1. If `U : Bool → Bool → Int` has strictly positive cross-difference
       `ΔU = U(1,1) - U(0,1) - (U(1,0) - U(0,0)) ≥ 0` and `x = true` already beats `x = false` at `θ = false`,
       then `x = true` continues to dominate `x = false` at `θ = true`.
    2. Antitone negation `T_anti(x) = 1 - x` on `{0, 1}` is bounded on `{0, 1}` yet has **zero** fixed points!
    3. Submodular payoff `U_sub(0,0)=0, U_sub(1,0)=1, U_sub(0,1)=3, U_sub(1,1)=2` (`ΔU = -2 < 0`)
       reverses the optimizer downward from `x*(0) = 1` to `x*(1) = 0`! -/
def submodPayoff : Bool → Bool → Int
  | false, false => 0
  | true,  false => 1
  | false, true  => 3
  | true,  true  => 2

theorem topkis_supermodular_persistence_vs_antitone_flip_and_submodular_reversal :
    -- 1. Supermodular comparative statics (`ΔU ≥ 0` preserves upward optimality)
    (∀ u00 u10 u01 u11 : Int,
      0 ≤ (u11 - u01) - (u10 - u00) → u00 ≤ u10 → u01 ≤ u11) ∧
    -- 2. Antitone flip `x ↦ 1 - x` on `{0, 1}` has zero fixed points
    (∀ x : Fin 2, (1 - x.val) ≤ 1 ∧ (1 - x.val) ≠ x.val) ∧
    -- 3. Submodular payoff (`ΔU = -2 < 0`) flips unique maximizer downward `1 → 0` as `θ : false → true`
    ((submodPayoff true true - submodPayoff false true) -
      (submodPayoff true false - submodPayoff false false) = -2 ∧
      submodPayoff false false < submodPayoff true false ∧
      submodPayoff true true < submodPayoff false true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u00 u10 u01 u11 hsup h0
    omega
  · decide
  · decide

end GaloisQuantileTransportAndSupermodularTopkisDuality
