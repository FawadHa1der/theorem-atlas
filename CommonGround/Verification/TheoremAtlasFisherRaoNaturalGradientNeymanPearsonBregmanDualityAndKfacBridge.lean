/-
  CommonGround Verification Suite #626 (V225 Synthesis):
  Chentsov Fisher Information Monotonicity, Wald SPRT Anytime Stopping,
  Exponential-Family Moment-Matching vs. Complete Separation, Gauss–Newton PSD Curvature,
  and Jeffreys Prior Square-Root Invariance

  Pure-core Lean 4.33.0 (`0` imports, `0` sorry, `0` admit, `0` axioms):
  1. `chentsov_markov_fisher_information_monotonicity_vs_insufficient_coarse_graining_drop`:
     Merging two tangent score fibers `(q₁, δ₁)` and `(q₂, δ₂)` satisfies the exact identity
     `(q₁ + q₂)(q₂ δ₁² + q₁ δ₂²) - q₁ q₂ (δ₁ + δ₂)² = (q₂ δ₁ - q₁ δ₂)² ≥ 0` (Chentsov's Fisher
     monotonicity + tangent sufficiency iff `q₂ δ₁ = q₁ δ₂`), contrasted with opposite-score
     coarse-graining `(q₁, q₂) = (1, 1), (δ₁, δ₂) = (3, -3)` losing `100%` of Fisher info (`36 → 0`).
  2. `wald_sprt_likelihood_ratio_stopping_bound_vs_optional_peeking_inflation`:
     Over arbitrary finite trajectory spaces `Fin Ω`, any stopping set `A₁` where `q · L₁(ω) ≥ B · L₀(ω)`
     satisfies `B · ∑_{A₁} L₀(ω) ≤ q · ∑_{A₁} L₁(ω) ≤ q · ∑_Ω L₁(ω)` (Wald's universal anytime-valid
     Type-I bound!), contrasted with unadjusted 2-look optional peeking inflating null rejection from
     `4 / 16` (`25%`) to `7 / 16` (`43.75%`).
  3. `exponential_family_moment_matching_mle_gradient_identity_vs_complete_separation_divergence`:
     Proves exact algebraic equivalence between exponential-family log-likelihood stationarity and
     empirical-vs-model sufficient-statistic moment matching, plus non-negative Lagrange–Fisher
     curvature, contrasted with Albert–Anderson / Hauck–Donner complete boundary separation
     `c = (0, 0, n)` on `T = (0, 1, 2)` where `(W₀+W₁+W₂)(2n) - n(W₁+2W₂) = n(2W₀+W₁) > 0` for all
     positive interior Boltzmann weights `W₀, W₁, W₂ > 0` (no finite interior MLE exists!).
  4. `gauss_newton_generalized_fisher_psd_vs_indefinite_hessian_negative_curvature_ascent`:
     Proves generalized Fisher / Gauss–Newton curvature `J² ≥ 0` always yields weak descent
     `g · (-J² g) ≤ 0`, contrasted with non-convex residual `(r, J, r'') = (-5, 1, 2)` where full
     Hessian `H = J² + r·r'' = -9 < 0` drives exact Newton step uphill (`(-5)*5 < 0` fails, inner
     product `g · Δ_Newton = (-5)*(-5) = +25 > 0` after clearing `9`!).
  5. `jeffreys_prior_square_root_fisher_invariance_vs_uniform_prior_coordinate_paradox`:
     Proves Jeffreys half-density `s_φ = c · s_θ` (`s_φ² = c² F_θ = F_φ`) preserves interval mass
     `s_φ · Δφ = s_θ · Δθ` identically under `θ = c · φ`, whereas Laplace's flat uniform rule assigns
     `1 : 1` to `[0,1]` vs `[1,2]` in `θ` yet `1 : 3` (`[0,1]` vs `[1,4]`) in `ψ = θ²`.
-/

namespace CommonGround.Verification.TheoremAtlasFisherRaoNaturalGradientNeymanPearsonBregmanDualityAndKfacBridge

private theorem sq_nonneg (z : Int) : 0 ≤ z * z := by
  by_cases h : 0 ≤ z
  · exact Int.mul_nonneg h h
  · have hneg : 0 ≤ -z := by omega
    have hmul : 0 ≤ (-z) * (-z) := Int.mul_nonneg hneg hneg
    grind

/-- Finite integer sum over `Fin N`. -/
def sumFin : (N : Nat) → (Fin N → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumFin n (fun i => f ⟨i.val, by omega⟩) + f ⟨n, by omega⟩

/-! ## Bridge 1: Chentsov Markov Fisher Monotonicity vs. Insufficient Score Cancellation -/

/-- Bridge 1: Denominator-free two-fiber Fisher information merging identity
    `(q₁ + q₂)(q₂ δ₁² + q₁ δ₂²) - q₁ q₂ (δ₁ + δ₂)² = (q₂ δ₁ - q₁ δ₂)² ≥ 0`,
    plus total Fisher collapse (`36 → 0`) under symmetric opposite-score coarse-graining. -/
theorem chentsov_markov_fisher_information_monotonicity_vs_insufficient_coarse_graining_drop :
    -- (A) Exact Chentsov tangent-sufficiency identity & monotonicity:
    (∀ q1 q2 d1 d2 : Int,
      (q1 + q2) * (q2 * d1 * d1 + q1 * d2 * d2) - q1 * q2 * (d1 + d2) * (d1 + d2) =
      (q2 * d1 - q1 * d2) * (q2 * d1 - q1 * d2) ∧
      q1 * q2 * (d1 + d2) * (d1 + d2) ≤ (q1 + q2) * (q2 * d1 * d1 + q1 * d2 * d2)) ∧
    -- (B) Zero Fisher loss iff tangent score proportionality `q₂ δ₁ = q₁ δ₂`:
    (∀ q1 q2 d1 d2 : Int,
      (q1 + q2) * (q2 * d1 * d1 + q1 * d2 * d2) = q1 * q2 * (d1 + d2) * (d1 + d2) ↔
      q2 * d1 = q1 * d2) ∧
    -- (C) Premise failure: merging `(q₁,q₂)=(1,1)` with opposite scores `(3,-3)` drops Fisher to `0`:
    ((1 + 1) * (1 * 3 * 3 + 1 * (-3) * (-3)) = 36 ∧
     1 * 1 * (3 + (-3)) * (3 + (-3)) = 0) := by
  refine ⟨?_, ?_, by decide⟩
  · intro q1 q2 d1 d2
    have hId :
        (q1 + q2) * (q2 * d1 * d1 + q1 * d2 * d2) - q1 * q2 * (d1 + d2) * (d1 + d2) =
        (q2 * d1 - q1 * d2) * (q2 * d1 - q1 * d2) := by grind
    have hPos : 0 ≤ (q2 * d1 - q1 * d2) * (q2 * d1 - q1 * d2) := sq_nonneg (q2 * d1 - q1 * d2)
    refine ⟨hId, by omega⟩
  · intro q1 q2 d1 d2
    constructor
    · intro hEq
      have hSqZero : (q2 * d1 - q1 * d2) * (q2 * d1 - q1 * d2) = 0 := by grind
      by_cases hDiff : q2 * d1 = q1 * d2
      · exact hDiff
      · exfalso
        by_cases hgt : 0 < q2 * d1 - q1 * d2
        · have : 0 < (q2 * d1 - q1 * d2) * (q2 * d1 - q1 * d2) := Int.mul_pos hgt hgt
          omega
        · have hlt : 0 < q1 * d2 - q2 * d1 := by omega
          have : 0 < (q1 * d2 - q2 * d1) * (q1 * d2 - q2 * d1) := Int.mul_pos hlt hlt
          grind
    · intro hProp
      grind

/-! ## Bridge 2: Wald SPRT Likelihood-Ratio Stopping Bound vs. Optional Peeking Inflation -/

/-- Universal Wald stopping-set domination over `Fin Ω`. -/
theorem wald_sprt_stopping_sum_bound :
    ∀ (Ω : Nat) (L0 L1 acceptH1 : Fin Ω → Int) (B q : Int),
      0 ≤ q →
      (∀ w : Fin Ω, (acceptH1 w = 0 ∨ acceptH1 w = 1) ∧ 0 ≤ L1 w) →
      (∀ w : Fin Ω, acceptH1 w = 1 → B * L0 w ≤ q * L1 w) →
      B * sumFin Ω (fun w => acceptH1 w * L0 w) ≤ q * sumFin Ω L1
  | 0, _, _, _, _, _, _, _, _ => by simp [sumFin]
  | n + 1, L0, L1, acceptH1, B, q, hq, hValid, hThresh => by
      have ih := wald_sprt_stopping_sum_bound n
        (fun i => L0 ⟨i.val, by omega⟩)
        (fun i => L1 ⟨i.val, by omega⟩)
        (fun i => acceptH1 ⟨i.val, by omega⟩)
        B q hq
        (fun i => hValid ⟨i.val, by omega⟩)
        (fun i h => hThresh ⟨i.val, by omega⟩ h)
      have hLastValid := hValid ⟨n, by omega⟩
      rcases hLastValid with ⟨hBit, hL1Nonneg⟩
      simp only [sumFin]
      rw [Int.mul_add, Int.mul_add]
      cases hBit with
      | inl hZero =>
        have hqLast : 0 ≤ q * L1 ⟨n, by omega⟩ := Int.mul_nonneg hq hL1Nonneg
        rw [hZero, Int.zero_mul, Int.mul_zero]
        omega
      | inr hOne =>
        have hStep := hThresh ⟨n, by omega⟩ hOne
        rw [hOne, Int.one_mul]
        omega

/-- Bridge 2: Wald's anytime-valid likelihood-ratio barrier `B · α ≤ q` vs. unadjusted 2-look
    optional peeking on `16` equiprobable 2-draw paths (`p_null = 1/4` per look) inflating false
    positives from `4` paths (`25%`) to `7` paths (`43.75%`). -/
theorem wald_sprt_likelihood_ratio_stopping_bound_vs_optional_peeking_inflation :
    -- (A) Universal Wald SPRT stopping inequality across arbitrary `Fin Ω`:
    (∀ (Ω : Nat) (L0 L1 acceptH1 : Fin Ω → Int) (B q : Int),
      0 ≤ q →
      (∀ w : Fin Ω, (acceptH1 w = 0 ∨ acceptH1 w = 1) ∧ 0 ≤ L1 w) →
      (∀ w : Fin Ω, acceptH1 w = 1 → B * L0 w ≤ q * L1 w) →
      B * sumFin Ω (fun w => acceptH1 w * L0 w) ≤ q * sumFin Ω L1) ∧
    -- (B) Unadjusted 2-look optional peeking (`1 - (3/4)² = 7/16 > 4/16`):
    (let singleLookNullMass := 1 * 4
     let twoLookPeekNullMass := 1 * 4 + 3 * 1
     singleLookNullMass = 4 ∧ twoLookPeekNullMass = 7 ∧ singleLookNullMass < twoLookPeekNullMass) := by
  exact ⟨wald_sprt_stopping_sum_bound, by decide⟩

/-! ## Bridge 3: Exponential-Family Moment Matching `↔` MLE vs. Complete Separation -/

/-- Bridge 3: Three-state exponential family `W = (w₀, w₁, w₂) > 0`, sufficient statistic `T = (t₀, t₁, t₂)`,
    and empirical counts `c = (c₀, c₁, c₂)`:
    (A) Log-likelihood score vanishes iff empirical sum matches Boltzmann-expected sufficient statistic,
    (B) Scaled Fisher curvature `2(Z ∑ w_i t_i² - (∑ w_i t_i)²)` is an exact sum of squares `≥ 0`,
    (C) Complete boundary separation `c = (0, 0, n)` (`n ≥ 1`) on `T = (0, 1, 2)` leaves strictly
        positive score residual `n(2 w₀ + w₁) > 0` for ALL interior positive weights `w₀, w₁, w₂ > 0`! -/
theorem exponential_family_moment_matching_mle_gradient_identity_vs_complete_separation_divergence :
    -- (A) Exact score-to-moment-matching algebraic identity:
    (∀ c0 c1 c2 w0 w1 w2 t0 t1 t2 : Int,
      let Z := w0 + w1 + w2
      let muW := w0 * t0 + w1 * t1 + w2 * t2
      c0 * (Z * t0 - muW) + c1 * (Z * t1 - muW) + c2 * (Z * t2 - muW) =
      Z * (c0 * t0 + c1 * t1 + c2 * t2) - (c0 + c1 + c2) * muW) ∧
    -- (B) Non-negative Fisher Hessian curvature on positive Boltzmann weights:
    (∀ w0 w1 w2 t0 t1 t2 : Int,
      0 ≤ w0 → 0 ≤ w1 → 0 ≤ w2 →
      (w0 + w1 + w2) * (w0 * t0 * t0 + w1 * t1 * t1 + w2 * t2 * t2) -
      (w0 * t0 + w1 * t1 + w2 * t2) * (w0 * t0 + w1 * t1 + w2 * t2) =
      w0 * w1 * (t0 - t1) * (t0 - t1) +
      w0 * w2 * (t0 - t2) * (t0 - t2) +
      w1 * w2 * (t1 - t2) * (t1 - t2)) ∧
    -- (C) Hauck–Donner / Albert–Anderson complete separation (`c = (0, 0, n)` on `T = (0, 1, 2)`):
    (∀ n w0 w1 w2 : Int,
      1 ≤ n → 1 ≤ w0 → 1 ≤ w1 → 1 ≤ w2 →
      0 < (w0 + w1 + w2) * (0 * 0 + 0 * 1 + n * 2) - (0 + 0 + n) * (w0 * 0 + w1 * 1 + w2 * 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c0 c1 c2 w0 w1 w2 t0 t1 t2
    grind
  · intro w0 w1 w2 t0 t1 t2 _ _ _
    grind
  · intro n w0 w1 w2 hn hw0 hw1 hw2
    have hId :
        (w0 + w1 + w2) * (0 * 0 + 0 * 1 + n * 2) - (0 + 0 + n) * (w0 * 0 + w1 * 1 + w2 * 2) =
        n * (2 * w0 + w1) := by grind
    have hPosFactor : 0 < 2 * w0 + w1 := by omega
    have hProd : 0 < n * (2 * w0 + w1) := Int.mul_pos (by omega) hPosFactor
    omega

/-! ## Bridge 4: Gauss–Newton / Generalized Fisher PSD vs. Indefinite Hessian Saddle Ascent -/

/-- Bridge 4: For nonlinear residual `½ r(θ)²` with gradient `g = r · J`, Gauss–Newton curvature
    `G = J² ≥ 0` guarantees weak descent `g · (-J² g) ≤ 0` everywhere, whereas at concave large
    residual `(r, J, r'') = (-5, 1, 2)`, full Hessian `H = J² + r·r'' = -9 < 0` points the Newton
    step `-g / H` strictly uphill (`(-H) · g · (-g) < 0` fails: `g · (-g * (-1))` gives `+25 > 0`!). -/
theorem gauss_newton_generalized_fisher_psd_vs_indefinite_hessian_negative_curvature_ascent :
    -- (A) Universal Gauss–Newton / Generalized Fisher PSD & descent guarantee:
    (∀ r J : Int,
      let g := r * J
      let gnCurv := J * J
      0 ≤ gnCurv ∧ g * (-(gnCurv * g)) ≤ 0) ∧
    -- (B) Indefinite full Hessian `H = J² + r·r'' = -9 < 0` at `(r, J, r'') = (-5, 1, 2)`:
    --     Solving `H · Δ = -9 · Δ = -g = 5` gives `9 · Δ = -5`, so `9 * (g * Δ) = (-5) * (-5) = +25 > 0` (uphill ascent!):
    (let r := -5
     let J := 1
     let r2 := 2
     let g := r * J
     let fullH := J * J + r * r2
     let scaledNewtonStep := -5 -- satisfies `fullH * (-5) = 45 = 9 * (-g)`!
     fullH = -9 ∧
     fullH * scaledNewtonStep = 9 * (-g) ∧
     0 < g * scaledNewtonStep) := by
  refine ⟨?_, by decide⟩
  · intro r J
    have hJ : 0 ≤ J * J := sq_nonneg J
    have hgJ : 0 ≤ (r * J * J) * (r * J * J) := sq_nonneg (r * J * J)
    have hEq : (r * J) * (-((J * J) * (r * J))) = -((r * J * J) * (r * J * J)) := by grind
    exact ⟨hJ, by omega⟩

/-! ## Bridge 5: Jeffreys Prior Square-Root Fisher Invariance vs. Uniform-Prior Paradox -/

/-- Bridge 5: Under `θ = c · φ` (`c > 0`), Jeffreys root-Fisher density `s_φ = c · s_θ` satisfies
    `s_φ² = c² F_θ = F_φ` and preserves exact interval measure `s_φ · Δφ = s_θ · (c · Δφ) = s_θ · Δθ`,
    whereas flat uniform density on `θ ∈ [0, 2]` assigns equal `1 : 1` length to `[0, 1]` and `[1, 2]`
    yet `1 : 3` length (`1` vs `4 - 1 = 3`) in squared parameterization `ψ = θ²`! -/
theorem jeffreys_prior_square_root_fisher_invariance_vs_uniform_prior_coordinate_paradox :
    -- (A) Exact Jeffreys square-root Fisher transformation & interval measure invariance:
    (∀ c fTheta sTheta dPhi : Int,
      sTheta * sTheta = fTheta →
      (c * sTheta) * (c * sTheta) = (c * c) * fTheta ∧
      (c * sTheta) * dPhi = sTheta * (c * dPhi)) ∧
    -- (B) Uniform-prior coordinate paradox under `ψ = θ²` on `[0, 1]` vs `[1, 2]`:
    ((1 - 0 = 2 - 1) ∧ (1 * 1 - 0 * 0 = 1) ∧ (2 * 2 - 1 * 1 = 3) ∧ (1 ≠ 3)) := by
  refine ⟨?_, by decide⟩
  · intro c fTheta sTheta dPhi hRoot
    exact ⟨by grind, by grind⟩

end CommonGround.Verification.TheoremAtlasFisherRaoNaturalGradientNeymanPearsonBregmanDualityAndKfacBridge
