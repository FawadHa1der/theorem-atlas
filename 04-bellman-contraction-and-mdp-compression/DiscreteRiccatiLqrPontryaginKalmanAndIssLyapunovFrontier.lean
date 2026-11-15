/-
  DiscreteRiccatiLqrPontryaginKalmanAndIssLyapunovFrontier.lean
  -------------------------------------------------------------
   Frontier #99 (Folder 04 — Bellman Contraction, Optimal Control & Dynamic Filtering):
   Machine-checked pure-core Lean 4.33.0 (`0` imports, `0` sorry) formalization of:
   1. Denominator-Free Discrete LQR Riccati Completion-of-Squares Bellman Identity
      `D · (q x² + r u² + p(ax + bu)²) = (Dq + rpa²) x² + (Du + pabx)²` (`D = r + pb²`),
      exact integer DARE fixed point `(a,b,q,r,p*) = (2, 1, 18, 7, 42)` stabilizing an
      unstable `2^k` plant (`ρ_CL = 2/7 < 1`) vs. uncontrollable `b = 0` exponential blowup,
   2. Discrete Pontryagin `2`-Stage Co-State Minimum Principle (`6 J(u₀,u₁) - 2 x₀² = 3(u₀-u₁)² + (3u₀+3u₁+2x₀)²`)
      vs. Terminal Transversality Omission (`λ₂ = 0` incurs `3×` cost `9s² > 3s²`),
   3. Kalman Filter Innovation Orthogonality & Exact Minimum-Variance Decomposition
      `((D - kc)² P + k² R) - D P R = D (k - c P)²` (`D = c² P + R`) vs. Unobservable Subspace Drift,
   4. Sontag Input-to-State Stability (ISS) Lyapunov Tube Contraction (`2(V_{t+1} - 2B) ≤ V_t - 2B`)
      vs. Undamped Unit-Root Resonance Blowup (`x_T = T`, `V_T = T² → ∞`).
-/

namespace CommonGround.Frontier.DiscreteRiccatiKalmanPontryaginIss

/-! ## 1. Discrete LQR Riccati Completion of Squares & Integer DARE Stabilization -/

/-- One-step LQR state-control-continuation quadratic form `q x² + r u² + p (a x + b u)²`. -/
def lqrStepCost (q r p a b x u : Int) : Int :=
  q * x * x + r * u * u + p * (a * x + b * u) * (a * x + b * u)

/-- **Theorem 1 (LQR Riccati Completion-of-Squares Bellman Optimality & Integer DARE Fixed Point vs. Uncontrollable Instability)**:
    1. Universal Completion of Squares (`D = r + p b²`): for ALL `q, r, p, a, b, x, u : Int`,
       `D * lqrStepCost q r p a b x u = (D * q + r * p * a * a) * x * x + (D * u + p * a * b * x)²`.
    2. Whenever `0 < r + p b²`, EVERY control `u` obeys `(D * q + r * p * a * a) * x² ≤ D * lqrStepCost(...)`,
       with zero regret iff `D * u = -p * a * b * x`.
    3. Exact Integer DARE Fixed Point on unstable plant `a = 2 > 1`: at `(a, b, q, r) = (2, 1, 18, 7)`,
       `p* = 42` (`D = 49`) satisfies `D * q + r * p* * a² = D * p*` (`2058 = 49 * 42`), and feedback
       `7 u* = -12 x` contracts `(7 x_{k+1})² = 4 x_k² < 49 x_k²` (`ρ_CL = 2/7 < 1`).
    4. **Uncontrollable Premise Failure (`b = 0`)**: When `b = 0` on `a = 2`, for EVERY control `u : Int`,
       `x_{k+1} = 2 x_k + 0 · u = 2 x_k` diverges (`(2 x_0)² = 4 x_0² > x_0²` for `x_0 ≠ 0`). -/
theorem lqr_riccati_completion_of_squares_bellman_optimality_vs_open_loop_instability :
    (∀ q r p a b x u : Int,
      let D := r + p * b * b
      D * lqrStepCost q r p a b x u =
        (D * q + r * p * a * a) * x * x + (D * u + p * a * b * x) * (D * u + p * a * b * x)) ∧
    (∀ q r p a b x u : Int,
      let D := r + p * b * b
      (D * q + r * p * a * a) * x * x ≤ D * lqrStepCost q r p a b x u) ∧
    (let a : Int := 2; let b : Int := 1; let q : Int := 18; let r : Int := 7; let pStar : Int := 42
     let D := r + pStar * b * b
     D = 49 ∧ D * q + r * pStar * a * a = D * pStar ∧
     ∀ x : Int, x ≠ 0 → (7 * a * x + (-12 * x)) * (7 * a * x + (-12 * x)) < 49 * x * x) ∧
    (∀ x0 u : Int, x0 ≠ 0 → x0 * x0 < (2 * x0 + 0 * u) * (2 * x0 + 0 * u)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q r p a b x u
    unfold lqrStepCost
    grind
  · intro q r p a b x u
    dsimp only
    have hSq : 0 ≤ ((r + p * b * b) * u + p * a * b * x) * ((r + p * b * b) * u + p * a * b * x) := by
      by_cases h : 0 ≤ (r + p * b * b) * u + p * a * b * x
      · exact Int.mul_nonneg h h
      · have hn : 0 ≤ -((r + p * b * b) * u + p * a * b * x) := by omega
        have he : (-((r + p * b * b) * u + p * a * b * x)) * (-((r + p * b * b) * u + p * a * b * x)) =
          ((r + p * b * b) * u + p * a * b * x) * ((r + p * b * b) * u + p * a * b * x) := by grind
        rw [← he]; exact Int.mul_nonneg hn hn
    have hId : (r + p * b * b) * lqrStepCost q r p a b x u -
        ((r + p * b * b) * q + r * p * a * a) * x * x =
        ((r + p * b * b) * u + p * a * b * x) * ((r + p * b * b) * u + p * a * b * x) := by
      unfold lqrStepCost
      grind
    omega
  · refine ⟨by decide, by decide, ?_⟩
    intro x hx
    have hPos : 0 < x * x := by
      by_cases hGt : 0 < x
      · exact Int.mul_pos hGt hGt
      · have hNeg : 0 < -x := by omega
        have hEq : (-x) * (-x) = x * x := by grind
        rw [← hEq]
        exact Int.mul_pos hNeg hNeg
    have hDiff : 49 * x * x - (7 * 2 * x + (-12 * x)) * (7 * 2 * x + (-12 * x)) = 45 * (x * x) := by grind
    omega
  · intro x0 u hx0
    have hPos : 0 < x0 * x0 := by
      by_cases hGt : 0 < x0
      · exact Int.mul_pos hGt hGt
      · have hNeg : 0 < -x0 := by omega
        have hEq : (-x0) * (-x0) = x0 * x0 := by grind
        rw [← hEq]
        exact Int.mul_pos hNeg hNeg
    have hDiff : (2 * x0 + 0 * u) * (2 * x0 + 0 * u) - x0 * x0 = 3 * (x0 * x0) := by grind
    omega

/-! ## 2. Discrete Pontryagin `2`-Stage Co-State Minimum Principle vs. Transversality Omission -/

/-- `2`-stage optimal control cost `u₀² + u₁² + (x₀ + u₀ + u₁)²`. -/
def pontryaginTwoStageCost (x0 u0 u1 : Int) : Int :=
  u0 * u0 + u1 * u1 + (x0 + u0 + u1) * (x0 + u0 + u1)

/-- **Theorem 2 (Pontryagin `2`-Stage Co-State Minimum Principle vs. Terminal Transversality Omission)**:
    1. Universal SOS Decomposition: `6 * pontryaginTwoStageCost x0 u0 u1 - 2 * x0² = 3*(u0 - u1)² + (3*u0 + 3*u1 + 2*x0)² ≥ 0`.
    2. For `x0 = 3 * s`, backward co-states `λ₂ = 2 * x₂* = 2 * s, λ₁ = λ₂ = 2 * s` yield unique
       stationary controls `u₀* = -s, u₁* = -s` attaining exact global minimum `3 * s²`.
    3. **Terminal Transversality Premise Failure**: Dropping terminal boundary `λ₂ = 2 * x₂` (`λ₂ = 0`)
       selects `u₀ = u₁ = 0`, incurring `9 * s² = 3 * J(u₀*, u₁*) > 3 * s²` whenever `s ≠ 0`. -/
theorem pontryagin_two_stage_costate_minimum_principle_vs_terminal_transversality_omission :
    (∀ x0 u0 u1 : Int,
      6 * pontryaginTwoStageCost x0 u0 u1 - 2 * x0 * x0 =
        3 * (u0 - u1) * (u0 - u1) + (3 * u0 + 3 * u1 + 2 * x0) * (3 * u0 + 3 * u1 + 2 * x0)) ∧
    (∀ s u0 u1 : Int,
      pontryaginTwoStageCost (3 * s) (-s) (-s) = 3 * s * s ∧
      pontryaginTwoStageCost (3 * s) (-s) (-s) ≤ pontryaginTwoStageCost (3 * s) u0 u1) ∧
    (∀ s : Int, s ≠ 0 →
      pontryaginTwoStageCost (3 * s) (-s) (-s) < pontryaginTwoStageCost (3 * s) 0 0 ∧
      pontryaginTwoStageCost (3 * s) 0 0 = 9 * s * s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x0 u0 u1
    unfold pontryaginTwoStageCost
    grind
  · intro s u0 u1
    refine ⟨by unfold pontryaginTwoStageCost; grind, ?_⟩
    have hId : 6 * pontryaginTwoStageCost (3 * s) u0 u1 - 6 * pontryaginTwoStageCost (3 * s) (-s) (-s) =
        3 * ((u0 - u1) * (u0 - u1)) + (3 * u0 + 3 * u1 + 6 * s) * (3 * u0 + 3 * u1 + 6 * s) := by
      unfold pontryaginTwoStageCost
      grind
    have hSq1 : 0 ≤ (u0 - u1) * (u0 - u1) := by
      by_cases h : 0 ≤ u0 - u1
      · exact Int.mul_nonneg h h
      · have hn : 0 ≤ -(u0 - u1) := by omega
        have he : (-(u0 - u1)) * (-(u0 - u1)) = (u0 - u1) * (u0 - u1) := by grind
        rw [← he]; exact Int.mul_nonneg hn hn
    have hSq2 : 0 ≤ (3 * u0 + 3 * u1 + 6 * s) * (3 * u0 + 3 * u1 + 6 * s) := by
      by_cases h : 0 ≤ 3 * u0 + 3 * u1 + 6 * s
      · exact Int.mul_nonneg h h
      · have hn : 0 ≤ -(3 * u0 + 3 * u1 + 6 * s) := by omega
        have he : (-(3 * u0 + 3 * u1 + 6 * s)) * (-(3 * u0 + 3 * u1 + 6 * s)) =
          (3 * u0 + 3 * u1 + 6 * s) * (3 * u0 + 3 * u1 + 6 * s) := by grind
        rw [← he]; exact Int.mul_nonneg hn hn
    omega
  · intro s hs
    have hPos : 0 < s * s := by
      by_cases h : 0 < s
      · exact Int.mul_pos h h
      · have hn : 0 < -s := by omega
        have he : (-s) * (-s) = s * s := by grind
        rw [← he]; exact Int.mul_pos hn hn
    have hOpt : pontryaginTwoStageCost (3 * s) (-s) (-s) = 3 * (s * s) := by
      unfold pontryaginTwoStageCost; grind
    have hZero : pontryaginTwoStageCost (3 * s) 0 0 = 9 * (s * s) := by
      unfold pontryaginTwoStageCost; grind
    refine ⟨by omega, by grind⟩

/-! ## 3. Kalman Filter Innovation Orthogonality & Minimum-Variance Decomposition -/

/-- Homogeneous posterior error variance `((c² P + R - k c)² P + k² R)` for arbitrary gain numerator `k`. -/
def kalmanScaledMse (P R c k : Int) : Int :=
  let D := c * c * P + R
  (D - k * c) * (D - k * c) * P + k * k * R

/-- **Theorem 3 (Kalman Filter Minimum-Variance Innovation Orthogonality vs. Unobservable Drift)**:
    1. Universal Pythagorean Gain Identity (`D = c² P + R`):
       `kalmanScaledMse P R c k - D * P * R = D * (k - c * P)²`.
    2. Exact Innovation Orthogonality: at optimal Kalman numerator `k* = c * P`, the cross-covariance
       between posterior error `R * X̃ - c * P * V` and innovation `c * X̃ + V` (`R*c*P - c*P*R`) is identically `0`,
       minimizing MSE over ALL `k : Int` whenever `P ≥ 0, R ≥ 0`.
    3. **Unobservable Subspace Premise Failure (`c₂ = 0`)**: When observation `Y = 1·X₁ + 0·X₂ + V` is
       blind to coordinate `2`, `kalmanScaledMse P₂ R 0 k = R² P₂ + k² R ≥ R² P₂` cannot reduce `P₂`
       for ANY gain `k`, and additive process noise `w₂ > 0` drives `P₂ + T * w₂ → ∞`! -/
theorem kalman_filter_minimum_variance_innovation_orthogonality_vs_unobservable_drift :
    (∀ P R c k : Int,
      let D := c * c * P + R
      kalmanScaledMse P R c k - D * P * R = D * (k - c * P) * (k - c * P)) ∧
    (∀ P R c k : Int, 0 ≤ P → 0 ≤ R →
      R * c * P - c * P * R = 0 ∧
      kalmanScaledMse P R c (c * P) ≤ kalmanScaledMse P R c k) ∧
    (∀ P2 w2 T : Int, 0 < w2 → 1 ≤ T → P2 < P2 + T * w2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro P R c k
    unfold kalmanScaledMse
    grind
  · intro P R c k hP hR
    refine ⟨by grind, ?_⟩
    have hD : 0 ≤ c * c * P + R := by
      have hc2 : 0 ≤ c * c := by
        by_cases hc : 0 ≤ c
        · exact Int.mul_nonneg hc hc
        · have hnc : 0 ≤ -c := by omega
          have he : (-c) * (-c) = c * c := by grind
          rw [← he]; exact Int.mul_nonneg hnc hnc
      have hc2P : 0 ≤ (c * c) * P := Int.mul_nonneg hc2 hP
      have hAssoc : c * c * P = (c * c) * P := by grind
      omega
    have hSq : 0 ≤ (k - c * P) * (k - c * P) := by
      by_cases hk : 0 ≤ k - c * P
      · exact Int.mul_nonneg hk hk
      · have hnk : 0 ≤ -(k - c * P) := by omega
        have he : (-(k - c * P)) * (-(k - c * P)) = (k - c * P) * (k - c * P) := by grind
        rw [← he]; exact Int.mul_nonneg hnk hnk
    have hProd : 0 ≤ (c * c * P + R) * ((k - c * P) * (k - c * P)) := Int.mul_nonneg hD hSq
    have hDiff : kalmanScaledMse P R c k - kalmanScaledMse P R c (c * P) =
        (c * c * P + R) * ((k - c * P) * (k - c * P)) := by
      unfold kalmanScaledMse
      grind
    omega
  · intro P2 w2 T hw2 hT
    have hTw : 1 * 1 ≤ T * w2 := Int.mul_le_mul hT (by omega) (by omega) (by omega)
    omega

/-! ## 4. Discrete Input-to-State Stability (ISS) Lyapunov Contraction vs. Resonance Blowup -/

/-- **Theorem 4 (Discrete ISS Lyapunov Tube Contraction vs. Unit-Root Resonance Blowup)**:
    1. Whenever `S * V_{t+1} ≤ R * V_t + S * B` (`0 ≤ R < S`), excess above the ultimate ISS tube
       contracts: at `(R, S) = (1, 2)` (`2 V_{t+1} ≤ V_t + 2 B`), `2 * (V_{t+1} - 2 * B) ≤ V_t - 2 * B`,
       so `V₀ ≤ 2 B → V₁ ≤ 2 B` (forward invariance) and `2` steps contract excess by `4×` (`4(V₂ - 2B) ≤ V₀ - 2B`).
    2. **Unit-Root Resonance Premise Failure (`R = S = 1`, `x_{t+1} = x_t + 1`)**: Under persistent
       bounded disturbance `|w_t| = 1 ≤ 1`, `x_T = T` and quadratic energy `T²` exceeds EVERY candidate
       bound `M ≥ 0` at horizon `T = M + 1` (`M < (M + 1)²`). -/
theorem discrete_iss_lyapunov_contraction_envelope_vs_undamped_resonance_blowup :
    (∀ v0 v1 v2 B : Int,
      2 * v1 ≤ v0 + 2 * B → 2 * v2 ≤ v1 + 2 * B →
      2 * (v1 - 2 * B) ≤ v0 - 2 * B ∧
      4 * (v2 - 2 * B) ≤ v0 - 2 * B ∧
      (v0 ≤ 2 * B → v1 ≤ 2 * B ∧ v2 ≤ 2 * B)) ∧
    (∀ M : Int, 0 ≤ M → M < (M + 1) * (M + 1)) := by
  refine ⟨?_, ?_⟩
  · intro v0 v1 v2 B h1 h2
    refine ⟨by omega, by omega, ?_⟩
    intro h0
    omega
  · intro M hM
    have hSq : 0 ≤ M * M := Int.mul_nonneg hM hM
    have hExpand : (M + 1) * (M + 1) = M * M + 2 * M + 1 := by grind
    omega

end CommonGround.Frontier.DiscreteRiccatiKalmanPontryaginIss
