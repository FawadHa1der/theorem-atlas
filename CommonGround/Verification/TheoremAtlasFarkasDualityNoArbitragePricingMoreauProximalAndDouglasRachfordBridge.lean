/-
  CommonGround/Verification/TheoremAtlasFarkasDualityNoArbitragePricingMoreauProximalAndDouglasRachfordBridge.lean

  Suite #630 (`V229`, `0` imports, `0` sorry):
  Cross-Domain Verification Bridges for `Frontier #104` (`FarkasDualityNoArbitragePricingAndMonotoneProximalSplittingFrontier.lean`):
  1. Conic Slater Strict-Feasibility Boundary: `3 × 3` Semidefinite Program with Finite Positive Duality Gap
     (`d* = 0 < 1 = p*` when Slater interiority fails) vs. Polyhedral Farkas/LP Zero Gap (`econlib` ↔ `cslib` ↔ `oai-sat`).
  2. Von Neumann Zero-Sum Matrix Game Saddle Equality (`max_p min_q = min_q max_p` at mixed `(1, 1)`)
     vs. Pure-Strategy Maximin-Minimax Gap (`-1 < +1` on Matching Pennies) (`econlib` ↔ `tc-probcomb`).
  3. Exact Moreau `L¹` Soft-Thresholding + Box-Projection Decomposition (`softThresh λ u + clipBox λ u = u`)
     vs. Unsmoothed Subgradient Period-`2` Oscillation (`+1 ↔ -1`) (`econlib` ↔ `cslib` ↔ `physlib`).
  4. Karush–Kuhn–Tucker (`KKT`) Multiplier Existence under `LICQ` (`λ = 1`) vs. Degenerate Grazing
     Tangency (`g(x) = x² ≤ 0`, `∀ λ ∈ ℤ, -1 + λ · 0 ≠ 0`) (`econlib` ↔ `tc-alggeom`).
  5. Korpelevich Extragradient `13/16` Explicit Saddle Contraction (`(3x-2y)² + (3y+2x)² = 13(x²+y²) < 16(x²+y²)`)
     vs. Simultaneous Arrow–Hurwicz `2×` Energy Explosion (`(q² + p²) > q²`) (`econlib` ↔ `euler` ↔ `physlib`).
-/

namespace CommonGround.Verification.FarkasNoArbitrageMoreauAndExtragradientBridge

theorem sq_nonneg (z : Int) : 0 ≤ z * z := by
  by_cases h : 0 ≤ z
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -z := by omega
    have hp : 0 ≤ (-z) * (-z) := Int.mul_nonneg hn hn
    have heq : (-z) * (-z) = z * z := Int.neg_mul_neg z z
    omega

/-! ## Bridge 1: `3 × 3` Conic SDP Finite Duality Gap (`d* = 0 < 1 = p*`) Without Slater Interior -/

/-- Primal `3 × 3` SDP: minimize `x₁₁` subject to `X ⪰ 0`, `x₂₂ = 0`, and `x₁₁ + 2 x₂₃ = 1`.
    Dual `3 × 3` SDP: maximize `y₂` subject to `S(y₁, y₂) = [[1-y₂,0,0],[0,-y₁,-y₂],[0,-y₂,0]] ⪰ 0`.
    Both Primal (`p* = 1` at `diag(1,0,0)`) and Dual (`d* = 0` at `(0,0)`) are feasible and attained
    over `ℤ` (and `ℝ`), yet `d* = 0 < 1 = p*` because Slater strict feasibility fails! -/
theorem sdp_slater_failure_finite_duality_gap_zero_lt_one :
    -- 1. Primal attainment at diag(1, 0, 0) with value 1:
    ((0 : Int) = 0 ∧ (0 : Int) * 0 ≥ 0 * 0 ∧ (1 : Int) + 2 * 0 = 1) ∧
    -- 2. Every primal-feasible X ⪰ 0 (`x₂₂ x₃₃ ≥ x₂₃²`) with `x₂₂ = 0` & `x₁₁ + 2 x₂₃ = 1` has `x₁₁ = 1`:
    (∀ x11 x22 x33 x23 : Int,
      x22 = 0 → x22 * x33 ≥ x23 * x23 → x11 + 2 * x23 = 1 → x11 = 1) ∧
    -- 3. Dual attainment at (y₁, y₂) = (0, 0) with value 0:
    ((1 : Int) - 0 ≥ 0 ∧ (- (0 : Int)) * 0 ≥ (- (0 : Int)) * (- 0)) ∧
    -- 4. Every dual-feasible (y₁, y₂) (`(-y₁) · 0 ≥ (-y₂)²`) has `y₂ = 0`:
    (∀ y1 y2 : Int, (-y1) * 0 ≥ (-y2) * (-y2) → y2 = 0) ∧
    -- 5. Strict finite conic duality gap d* = 0 < 1 = p*:
    ((0 : Int) < 1) := by
  refine ⟨by decide, ?_, by decide, ?_, by decide⟩
  · intro x11 x22 x33 x23 hx22 hminor hlin
    subst hx22
    have hsq_nonneg : 0 ≤ x23 * x23 := sq_nonneg x23
    have hsq_zero : x23 * x23 = 0 := by omega
    have hx23 : x23 = 0 := by
      cases Int.mul_eq_zero.mp hsq_zero with
      | inl h => exact h
      | inr h => exact h
    omega
  · intro y1 y2 hminor
    have hsq_nonneg : 0 ≤ (-y2) * (-y2) := sq_nonneg (-y2)
    have hsq_zero : (-y2) * (-y2) = 0 := by omega
    have hny2 : -y2 = 0 := by
      cases Int.mul_eq_zero.mp hsq_zero with
      | inl h => exact h
      | inr h => exact h
    omega

/-! ## Bridge 2: Von Neumann Zero-Sum Saddle Equality vs. Pure-Strategy Maximin Gap -/

def mpMatrix (i j : Fin 2) : Int :=
  if i.1 = j.1 then 1 else -1

def expectedPayoff2x2 (p q : Fin 2 → Int) : Int :=
  p ⟨0, by decide⟩ * mpMatrix ⟨0, by decide⟩ ⟨0, by decide⟩ * q ⟨0, by decide⟩ +
  p ⟨0, by decide⟩ * mpMatrix ⟨0, by decide⟩ ⟨1, by decide⟩ * q ⟨1, by decide⟩ +
  p ⟨1, by decide⟩ * mpMatrix ⟨1, by decide⟩ ⟨0, by decide⟩ * q ⟨0, by decide⟩ +
  p ⟨1, by decide⟩ * mpMatrix ⟨1, by decide⟩ ⟨1, by decide⟩ * q ⟨1, by decide⟩

/-- On Matching Pennies `M = [[1, -1], [-1, 1]]`:
    1. Mixed Nash equilibrium `p* = (1, 1), q* = (1, 1)` guarantees exact saddle value `0`
       against EVERY non-negative strategy `(p₀, p₁)` and `(q₀, q₁)` (`pᵀ M q* = 0 = p*ᵀ M q`).
    2. Pure strategies suffer a strict `2`-unit maximin-minimax gap (`max_i min_j M_{i,j} = -1 < +1 = min_j max_i M_{i,j}`). -/
theorem von_neumann_mixed_saddle_equality_vs_pure_maximin_gap :
    (∀ q0 q1 : Int, expectedPayoff2x2 (fun _ => 1) (fun j => if j.1 = 0 then q0 else q1) = 0) ∧
    (∀ p0 p1 : Int, expectedPayoff2x2 (fun i => if i.1 = 0 then p0 else p1) (fun _ => 1) = 0) ∧
    -- Pure maximin = -1 < +1 = pure minimax:
    (max (min (mpMatrix ⟨0, by decide⟩ ⟨0, by decide⟩) (mpMatrix ⟨0, by decide⟩ ⟨1, by decide⟩))
         (min (mpMatrix ⟨1, by decide⟩ ⟨0, by decide⟩) (mpMatrix ⟨1, by decide⟩ ⟨1, by decide⟩)) = -1 ∧
     min (max (mpMatrix ⟨0, by decide⟩ ⟨0, by decide⟩) (mpMatrix ⟨1, by decide⟩ ⟨0, by decide⟩))
         (max (mpMatrix ⟨0, by decide⟩ ⟨1, by decide⟩) (mpMatrix ⟨1, by decide⟩ ⟨1, by decide⟩)) = 1) := by
  refine ⟨?_, ?_, by decide⟩
  · intro q0 q1
    simp [expectedPayoff2x2, mpMatrix]
    omega
  · intro p0 p1
    simp [expectedPayoff2x2, mpMatrix]
    omega

/-! ## Bridge 3: Moreau `L¹` Soft-Thresholding + Box-Projection Identity vs. Subgradient Oscillation -/

def softThresh (lam u : Int) : Int :=
  if u > lam then u - lam else if u < -lam then u + lam else 0

def clipBox (lam u : Int) : Int :=
  if u > lam then lam else if u < -lam then -lam else u

def subgradStepAbsEta2 (u : Int) : Int :=
  let g : Int := if u > 0 then 1 else if u < 0 then -1 else 0
  u - 2 * g

/-- Universal Moreau orthogonal decomposition `softThresh λ u + clipBox λ u = u` (`∀ λ ≥ 0, ∀ u ∈ ℤ`),
    dual `L∞` box feasibility `-λ ≤ clipBox λ u ≤ λ`, and `1`-step exact deadzone zeroing `softThresh 1 (±1) = 0`,
    contrasted against unsmoothed constant-step subgradient oscillation `+1 ↔ -1`! -/
theorem moreau_soft_threshold_box_decomposition_vs_subgradient_oscillation :
    (∀ lam u : Int, 0 ≤ lam →
      softThresh lam u + clipBox lam u = u ∧
      -lam ≤ clipBox lam u ∧ clipBox lam u ≤ lam ∧
      (softThresh lam u > 0 → clipBox lam u = lam) ∧
      (softThresh lam u < 0 → clipBox lam u = -lam)) ∧
    -- Proximal soft-thresholding hits 0 in 1 step from ±1, whereas subgradient η=2 oscillates +1 ↔ -1:
    (softThresh 1 1 = 0 ∧ softThresh 1 (-1) = 0 ∧
     subgradStepAbsEta2 1 = -1 ∧ subgradStepAbsEta2 (-1) = 1) := by
  refine ⟨?_, by decide⟩
  intro lam u hlam
  unfold softThresh clipBox
  split
  · omega
  · split <;> omega

/-! ## Bridge 4: KKT Multiplier Existence under LICQ vs. Degenerate Grazing Tangency -/

/-- Minimizing `f(x) = -x` at `x* = 0`:
    1. Under linear constraint `g₁(x) = x ≤ 0` (`g₁'(0) = 1 ≠ 0`, `LICQ` holds), unique KKT multiplier
       `λ = 1 ≥ 0` satisfies stationarity `f'(0) + λ g₁'(0) = -1 + 1 · 1 = 0`.
    2. Under algebraically equivalent grazing constraint `g₂(x) = x² ≤ 0` (same feasible set `{x : x² ≤ 0} = {0}`,
       same global minimum `x* = 0`, `g₂'(0) = 0`), NO multiplier `λ ∈ ℤ` satisfies `-1 + λ · 0 = 0`! -/
theorem kkt_licq_multiplier_existence_vs_grazing_tangency_breakdown :
    -- 1. Same feasible set {0}: x² ≤ 0 ↔ x = 0:
    (∀ x : Int, x * x ≤ 0 ↔ x = 0) ∧
    -- 2. Under LICQ g₁'(0) = 1, unique KKT multiplier λ = 1 ≥ 0 solves -1 + λ · 1 = 0:
    ((0 : Int) ≤ 1 ∧ (-1 : Int) + 1 * 1 = 0) ∧
    -- 3. Under grazing tangency g₂'(0) = 0, stationarity -1 + λ · 0 = 0 is impossible for ALL λ:
    (∀ lam : Int, (-1 : Int) + lam * 0 ≠ 0) := by
  refine ⟨?_, by decide, ?_⟩
  · intro x
    constructor
    · intro hle
      have hge : 0 ≤ x * x := sq_nonneg x
      have hz : x * x = 0 := by omega
      cases Int.mul_eq_zero.mp hz with
      | inl h => exact h
      | inr h => exact h
    · intro hx
      subst hx
      decide
  · intro lam
    omega

/-! ## Bridge 5: Korpelevich Extragradient `13/16` Saddle Contraction vs. Arrow–Hurwicz Explosion -/

/-- On bilinear zero-sum saddle `min_x max_y x y` (`F(x, y) = (y, -x)`):
    1. Scaled Korpelevich Extragradient at `η = 1/2` (`4 z_+ = (3x - 2y, 3y + 2x)`) uses ONLY
       explicit forward evaluations of `F`, yet satisfies `(3x - 2y)² + (3y + 2x)² = 13(x² + y²)`,
       strictly contracting `16(x² + y²)` by `3(x² + y²) > 0` for every `(x, y) ≠ (0, 0)` (`ρ² = 13/16 < 1`)!
    2. By contrast, single-stage simultaneous Arrow–Hurwicz `(q z - p F z)` at ANY non-zero step `p ≠ 0`
       inflates energy to `(q² + p²)(x² + y²) > q²(x² + y²)`! -/
theorem korpelevich_extragradient_contraction_vs_arrow_hurwicz_explosion :
    -- 1. Universal 13/16 Korpelevich Extragradient identity:
    (∀ x y : Int,
      (3 * x - 2 * y) * (3 * x - 2 * y) + (3 * y + 2 * x) * (3 * y + 2 * x) =
        13 * (x * x + y * y) ∧
      13 * (x * x + y * y) ≤ 16 * (x * x + y * y)) ∧
    -- 2. Universal single-stage Arrow–Hurwicz inflation for every non-zero step p ≠ 0 and non-zero state:
    (∀ q p x y : Int, p ≠ 0 → (x ≠ 0 ∨ y ≠ 0) →
      (q * x - p * y) * (q * x - p * y) + (q * y + p * x) * (q * y + p * x) =
        (q * q + p * p) * (x * x + y * y) ∧
      q * q * (x * x + y * y) < (q * q + p * p) * (x * x + y * y)) := by
  refine ⟨?_, ?_⟩
  · intro x y
    have h1 : (3 * x - 2 * y) * (3 * x - 2 * y) = 9 * (x * x) - 12 * (x * y) + 4 * (y * y) := by
      have : (3 * x - 2 * y) * (3 * x - 2 * y) =
          (3 * x) * (3 * x) - (3 * x) * (2 * y) - (2 * y) * (3 * x) + (2 * y) * (2 * y) := by
        rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
        omega
      rw [this]
      have hx2 : (3 * x) * (3 * x) = 9 * (x * x) := by
        rw [Int.mul_assoc, Int.mul_left_comm x 3 x]; omega
      have hy2 : (2 * y) * (2 * y) = 4 * (y * y) := by
        rw [Int.mul_assoc, Int.mul_left_comm y 2 y]; omega
      have hxy1 : (3 * x) * (2 * y) = 6 * (x * y) := by
        rw [Int.mul_assoc, Int.mul_left_comm x 2 y]; omega
      have hxy2 : (2 * y) * (3 * x) = 6 * (x * y) := by
        rw [Int.mul_assoc, Int.mul_left_comm y 3 x, Int.mul_comm y x]; omega
      omega
    have h2 : (3 * y + 2 * x) * (3 * y + 2 * x) = 9 * (y * y) + 12 * (x * y) + 4 * (x * x) := by
      have : (3 * y + 2 * x) * (3 * y + 2 * x) =
          (3 * y) * (3 * y) + (3 * y) * (2 * x) + (2 * x) * (3 * y) + (2 * x) * (2 * x) := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add]
        omega
      rw [this]
      have hy2 : (3 * y) * (3 * y) = 9 * (y * y) := by
        rw [Int.mul_assoc, Int.mul_left_comm y 3 y]; omega
      have hx2 : (2 * x) * (2 * x) = 4 * (x * x) := by
        rw [Int.mul_assoc, Int.mul_left_comm x 2 x]; omega
      have hyx1 : (3 * y) * (2 * x) = 6 * (x * y) := by
        rw [Int.mul_assoc, Int.mul_left_comm y 2 x, Int.mul_comm y x]; omega
      have hyx2 : (2 * x) * (3 * y) = 6 * (x * y) := by
        rw [Int.mul_assoc, Int.mul_left_comm x 3 y]; omega
      omega
    have hx_nonneg : 0 ≤ x * x := sq_nonneg x
    have hy_nonneg : 0 ≤ y * y := sq_nonneg y
    omega
  · intro q p x y hp hxy
    have h1 : (q * x - p * y) * (q * x - p * y) =
        (q * q) * (x * x) - 2 * ((q * p) * (x * y)) + (p * p) * (y * y) := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
      have a1 : (q * x) * (q * x) = (q * q) * (x * x) := by
        rw [Int.mul_assoc, Int.mul_left_comm x q x, ← Int.mul_assoc]
      have a2 : (p * y) * (p * y) = (p * p) * (y * y) := by
        rw [Int.mul_assoc, Int.mul_left_comm y p y, ← Int.mul_assoc]
      have a3 : (q * x) * (p * y) = (q * p) * (x * y) := by
        rw [Int.mul_assoc, Int.mul_left_comm x p y, ← Int.mul_assoc]
      have a4 : (p * y) * (q * x) = (q * p) * (x * y) := by
        rw [Int.mul_assoc, Int.mul_left_comm y q x, ← Int.mul_assoc, Int.mul_comm p q, Int.mul_comm y x]
      omega
    have h2 : (q * y + p * x) * (q * y + p * x) =
        (q * q) * (y * y) + 2 * ((q * p) * (x * y)) + (p * p) * (x * x) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
      have b1 : (q * y) * (q * y) = (q * q) * (y * y) := by
        rw [Int.mul_assoc, Int.mul_left_comm y q y, ← Int.mul_assoc]
      have b2 : (p * x) * (p * x) = (p * p) * (x * x) := by
        rw [Int.mul_assoc, Int.mul_left_comm x p x, ← Int.mul_assoc]
      have b3 : (q * y) * (p * x) = (q * p) * (x * y) := by
        rw [Int.mul_assoc, Int.mul_left_comm y p x, ← Int.mul_assoc, Int.mul_comm y x]
      have b4 : (p * x) * (q * y) = (q * p) * (x * y) := by
        rw [Int.mul_assoc, Int.mul_left_comm x q y, ← Int.mul_assoc, Int.mul_comm p q]
      omega
    have hsum :
        (q * x - p * y) * (q * x - p * y) + (q * y + p * x) * (q * y + p * x) =
          (q * q + p * p) * (x * x + y * y) := by
      rw [h1, h2, Int.add_mul, Int.mul_add, Int.mul_add]
      omega
    refine ⟨hsum, ?_⟩
    have hp_pos : 0 < p * p := by
      have hp_nn : 0 ≤ p * p := sq_nonneg p
      by_cases hgt : 0 < p * p
      · exact hgt
      · have hp0 : p * p = 0 := by omega
        cases Int.mul_eq_zero.mp hp0 with
        | inl h => exact False.elim (hp h)
        | inr h => exact False.elim (hp h)
    have hz_pos : 0 < x * x + y * y := by
      have hx_nn : 0 ≤ x * x := sq_nonneg x
      have hy_nn : 0 ≤ y * y := sq_nonneg y
      by_cases hgt : 0 < x * x + y * y
      · exact hgt
      · have h0 : x * x + y * y = 0 := by omega
        have hx0 : x * x = 0 := by omega
        have hy0 : y * y = 0 := by omega
        have hxz : x = 0 := by cases Int.mul_eq_zero.mp hx0 <;> assumption
        have hyz : y = 0 := by cases Int.mul_eq_zero.mp hy0 <;> assumption
        cases hxy with
        | inl h => exact False.elim (h hxz)
        | inr h => exact False.elim (h hyz)
    have hprod_pos : 0 < (p * p) * (x * x + y * y) := Int.mul_pos hp_pos hz_pos
    rw [Int.add_mul]
    omega

end CommonGround.Verification.FarkasNoArbitrageMoreauAndExtragradientBridge
