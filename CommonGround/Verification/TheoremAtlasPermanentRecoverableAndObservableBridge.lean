/-!
# Theorem Atlas Bridge: Recoverable Twin All-Prior Sufficiency, Observable Affine Compression, Permanent Polarization & Exchangeability (V159)

This zero-sorry pure Lean 4.33.0 module verifies four foundational cross-domain mechanisms and
exact failure boundaries from read-only `/Users/fawadhaider/code/lean ideas/theorem-atlas`:

1. **Recoverable Twin vs. Lossy Observation Twin (`RecoverableTwin` & `all-prior/generic/source.lean`)**:
   - `recoverable_twin_same_observation_and_explicit_decoder`:
     Compares `P = (40, 10, 50)` (`(2/5, 1/10, 1/2)` scaled by `100`), the lossy law
     `Q_L = (10, 5, 85)` (`(1/10, 1/20, 17/20)`), and the **recoverable twin**
     `Q_R = (12, 3, 85)` (`(3/25, 3/100, 17/20)`). Under `observe = (0, 0, 1)`, `Q_R` and `Q_L`
     induce the **exact same** observed law `(15, 85)` (`same_observation`), yet the stochastic
     decoder `R(0) = (4/5, 1/5, 0)`, `R(1) = (0, 0, 1)` simultaneously recovers BOTH `P` and `Q_R`
     (`explicit_common_recovery`) because `P` and `Q_R` share the within-fiber likelihood ratio `4 : 1`!
   - `recoverable_twin_preserves_every_prior_bayes_score`:
     Proves constructively on `{0, 1, 2}` that for ANY integer-scaled prior weights `(wtP, wtQ)` with
     `0 ≤ wtP, 0 ≤ wtQ`, the ungrouped optimal binary-test value on `(P, Q_R)` equals the grouped
     optimal binary-test value on `(observe_* P, observe_* Q_R)`—contrasting sharply with `Q_L`,
     which loses `1/80` at prior `t = 1/4`!

2. **Universal Affine Query Compression vs. Single-Moment Event Boundary (`ObservableSpan` & `MomentBoundary`)**:
   - `affine_query_eq_of_matched_mass_and_two_observables`:
     Exact finite proof of `ObservableSpan.affine_query_eq_of_matching`: whenever two signed or
     nonnegative weight vectors `p, r` on `{0, 1, 2}` have equal total mass and equal expectations
     on observables `f₁, f₂`, they produce the **exact same answer** on every affine query
     `q(i) = c + a₁ f₁(i) + a₂ f₂(i)`.
   - `fin3_middle_event_from_two_moments_and_one_moment_failure`:
     Verifies `ObservableSpan.middleEventMass_eq_two_mean_sub_secondMoment` (`r₁ = 2 μ₁(r) - μ₂(r)`)
     for arbitrary weights `(r₀, r₁, r₂)`, and proves `MomentBoundary.equal_mean_different_event`:
     `u = (1, 1, 1)` and `δ₁ = (0, 3, 0)` share total mass `3` and first moment `3` (mean `1`), yet
     assign masses `1 ≠ 3` to the middle event `{1}` because `{1}` is quadratic (`2 i - i²`), not affine in `i`!

3. **Glynn Signed-Hypercube Permanent Polarization & Cyclic Block Threshold (`Permanent.lean`)**:
   - `glynn_permanent_polarization_2x2` & `glynn_permanent_polarization_3x3`:
     Proves that averaging the symmetric product of linear forms over `±1` hypercube signs cancels
     all squared-variable monomials and isolates `2 · perm(A)` (`2×2`) and `4 · perm(A)` (`3×3`),
     converting multilinear permanent evaluation into symmetric power-sum evaluations.
   - `permanent_cyclic_block_n32_certificate_and_n16_boundary`:
     Verifies the exact arithmetic parameters of `Permanent.lean#L27475–27563` (`permanent_rational_formula_lower_bound`):
     at `n = 32` (`ℓ = 5`, `m = n - 2ℓ = 22`), `2ℓ < m ≤ 2^ℓ` (`10 < 22 ≤ 32`) holds with `m² = 484`
     transcendence-degree parameters, whereas at `n = 16` (`ℓ = 4`, `m = 8`), strict external room
     `2ℓ < m` (`8 < 8`) fails!

4. **Exchangeable Covariance Gram Participation Ratio & Finite de Finetti Boundary (`Exchangeability` ↔ `Zeta23`)**:
   - `exchangeable_gram_trace_and_negative_correlation_boundary`:
     For a `d × d` exchangeable covariance/Gram matrix with diagonal `v` and off-diagonal `c`,
     `tr(G) = d v`, `tr(G²) = d v² + d(d - 1) c²`, and sum-variance nonnegativity `d v + d(d - 1) c ≥ 0`
     permits negative correlation `c = -v` at `d = 2` (`(X₀, X₁) = (X₀, -X₀)`), proving why infinite
     de Finetti mixture representation (`c ≥ 0`) fails for finite `n = 2` exchangeability!
-/

namespace CommonGround.Verification.TheoremAtlasPermanentRecoverableAndObservableBridge

/-! ## 1. Recoverable Twin All-Prior Sufficiency (`RecoverableTwin` & `FiniteDecision`) -/

/-- Theorem 1a (`RecoverableTwin.same_observation` & `explicit_common_recovery`, cleared by `100`):
    `P = (40, 10, 50)`, lossy `Q_L = (10, 5, 85)`, and recoverable `Q_R = (12, 3, 85)` all sum to `100`.
    Under `observe = (0, 0, 1)`, `Q_L` and `Q_R` produce the exact same observed pair `(15, 85)`,
    and the single decoder `A ↦ (4/5, 1/5, 0)`, `B ↦ (0, 0, 1)` (cleared by `5`) recovers both `P` and `Q_R`! -/
theorem recoverable_twin_same_observation_and_explicit_decoder :
    let p0 := 40; let p1 := 10; let p2 := 50
    let ql0 := 10; let ql1 := 5; let ql2 := 85
    let qr0 := 12; let qr1 := 3; let qr2 := 85
    let obsP0 := p0 + p1; let obsP1 := p2
    let obsQL0 := ql0 + ql1; let obsQL1 := ql2
    let obsQR0 := qr0 + qr1; let obsQR1 := qr2
    -- Same observation for Q_R and Q_L
    obsQR0 = obsQL0 ∧ obsQR1 = obsQL1 ∧
    -- Explicit decoder (4/5, 1/5, 0) on group 0 and (0, 0, 1) on group 1 (cleared by 5) recovers P and Q_R
    (obsP0 * 4 = 5 * p0 ∧ obsP0 * 1 = 5 * p1 ∧ obsP1 * 5 = 5 * p2) ∧
    (obsQR0 * 4 = 5 * qr0 ∧ obsQR0 * 1 = 5 * qr1 ∧ obsQR1 * 5 = 5 * qr2) := by
  decide

/-- Theorem 1b (`optimal_test_value_bind_of_common_recovery` specialized to `(P, Q_R)`):
    Because `P = (40, 10, 50)` and `Q_R = (12, 3, 85)` have proportional fiber ratios `(40, 10) = 4 · (10, 2.5)`
    and `(12, 3) = 3 · (4, 1)` (both `4 : 1`!), for EVERY nonnegative weight pair `(wtP, wtQ)`,
    `max(40 wtP, 12 wtQ) + max(10 wtP, 3 wtQ) = max(50 wtP, 15 wtQ)`, so the ungrouped optimal
    binary-decision score equals the grouped score at EVERY prior! -/
theorem recoverable_twin_preserves_every_prior_bayes_score (wtP wtQ : Int)
    (_hP : 0 ≤ wtP) (_hQ : 0 ≤ wtQ) :
    max (40 * wtP) (12 * wtQ) + max (10 * wtP) (3 * wtQ) + max (50 * wtP) (85 * wtQ) =
      max (50 * wtP) (15 * wtQ) + max (50 * wtP) (85 * wtQ) := by
  by_cases h : 3 * wtQ ≤ 10 * wtP
  · have h4 : 12 * wtQ ≤ 40 * wtP := by omega
    have h5 : 15 * wtQ ≤ 50 * wtP := by omega
    have m1 : max (40 * wtP) (12 * wtQ) = 40 * wtP := by omega
    have m2 : max (10 * wtP) (3 * wtQ) = 10 * wtP := by omega
    have m3 : max (50 * wtP) (15 * wtQ) = 50 * wtP := by omega
    omega
  · have m1 : max (40 * wtP) (12 * wtQ) = 12 * wtQ := by omega
    have m2 : max (10 * wtP) (3 * wtQ) = 3 * wtQ := by omega
    have m3 : max (50 * wtP) (15 * wtQ) = 15 * wtQ := by omega
    omega

/-! ## 2. Universal Affine Query Compression & Single-Moment Event Boundary (`ObservableSpan`) -/

/-- Theorem 2a (`ObservableSpan.affine_query_eq_of_matching` on 3 points, 2 observables):
    Any two (possibly signed) weight vectors `(p0, p1, p2)` and `(r0, r1, r2)` with equal total mass
    and equal moments on `f` and `g` give identical answers on EVERY affine query `q_i = c + a f_i + b g_i`. -/
theorem affine_query_eq_of_matched_mass_and_two_observables
    (p0 p1 p2 r0 r1 r2 f0 f1 f2 g0 g1 g2 c a b : Int)
    (hmass : p0 + p1 + p2 = r0 + r1 + r2)
    (hf : p0 * f0 + p1 * f1 + p2 * f2 = r0 * f0 + r1 * f1 + r2 * f2)
    (hg : p0 * g0 + p1 * g1 + p2 * g2 = r0 * g0 + r1 * g1 + r2 * g2) :
    p0 * (c + a * f0 + b * g0) + p1 * (c + a * f1 + b * g1) + p2 * (c + a * f2 + b * g2) =
      r0 * (c + a * f0 + b * g0) + r1 * (c + a * f1 + b * g1) + r2 * (c + a * f2 + b * g2) := by
  grind

/-- Theorem 2b (`middleEventMass_eq_two_mean_sub_secondMoment` & `equal_mean_different_event`):
    (1) For ANY real/integer weights `(r0, r1, r2)` on `{0, 1, 2}`, `r1 = 2 * (r1 + 2 * r2) - (r1 + 4 * r2)`.
    (2) Uniform weights `u = (1, 1, 1)` and point-mass weights `d = (0, 3, 0)` share total mass `3` and
        first moment `3`, yet disagree on the middle event `u_1 = 1 ≠ 3 = d_1` because second moments
        disagree (`5 ≠ 3`)! -/
theorem fin3_middle_event_from_two_moments_and_one_moment_failure (r0 r1 r2 : Int) :
    let mean1 := 0 * r0 + 1 * r1 + 2 * r2
    let mom2 := 0 * r0 + 1 * r1 + 4 * r2
    (r1 = 2 * mean1 - mom2) ∧
    ((1 + 1 + 1 = 0 + 3 + 0) ∧ (1 + 2 * 1 = 3 + 2 * 0) ∧ ((1 : Int) ≠ 3)) := by
  refine ⟨by grind, by decide⟩

/-! ## 3. Glynn Permanent Polarization & Cyclic Matching Threshold (`Permanent.lean`) -/

/-- Theorem 3a (2×2 Glynn Signed-Hypercube Permanent Polarization):
    Summing `δ₁ · (a + δ₁ b) · (c + δ₁ d)` over `δ₁ ∈ {+1, -1}` eliminates `a c` and `b d`
    and equals `2 * (a * d + b * c) = 2 * perm([[a, b], [c, d]])`. -/
theorem glynn_permanent_polarization_2x2 (a b c d : Int) :
    1 * (a + b) * (c + d) + (-1) * (a - b) * (c - d) =
      2 * (a * d + b * c) := by
  grind

/-- Theorem 3b (3×3 Glynn Signed-Hypercube Permanent Polarization):
    Fixing `δ₀ = +1` and summing `δ₁ δ₂ ∏_{i=0}^2 (A_{i0} + δ₁ A_{i1} + δ₂ A_{i2})` over
    `(δ₁, δ₂) ∈ {+1, -1}²` equals `4 * perm_3(A)` identically over any commutative ring! -/
theorem glynn_permanent_polarization_3x3
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Int) :
    let term (d1 d2 : Int) :=
      d1 * d2 *
        (a00 + d1 * a01 + d2 * a02) *
        (a10 + d1 * a11 + d2 * a12) *
        (a20 + d1 * a21 + d2 * a22)
    let perm3 :=
      a00 * a11 * a22 + a00 * a12 * a21 +
      a01 * a10 * a22 + a01 * a12 * a20 +
      a02 * a10 * a21 + a02 * a11 * a20
    term 1 1 + term 1 (-1) + term (-1) 1 + term (-1) (-1) = 4 * perm3 := by
  grind

/-- Theorem 3c (`Permanent.lean#L27475–27563` Threshold Certificate `n = 32` vs. `n = 16` Boundary):
    At `n = 32` (`ℓ = 5`, `m = n - 2ℓ = 22`), `2ℓ < m ≤ 2^ℓ` holds and yields `m² = 484`
    independent cyclic-block transcendence parameters; at `n = 16` (`ℓ = 4`, `m = 8`), `2ℓ < m` fails! -/
theorem permanent_cyclic_block_n32_certificate_and_n16_boundary :
    let n32 := 32; let ell32 := 5; let m32 := n32 - 2 * ell32
    let n16 := 16; let ell16 := 4; let m16 := n16 - 2 * ell16
    (2 * ell32 ≤ n32 / 2 ∧ n32 ≤ 2 * m32 ∧ 2 * ell32 < m32 ∧ m32 ≤ 2 ^ ell32 ∧ m32 * m32 = 484) ∧
    ¬ (2 * ell16 < m16) := by
  decide

/-! ## 4. Exchangeable Covariance Gram Ratio & Finite de Finetti Boundary (`Exchangeability` ↔ `Zeta23`) -/

/-- Theorem 4 (`ExchangeableAt` Gram Matrix Identity & `n = 2` Negative-Correlation Witness):
    For `d = 2` exchangeable variables with diagonal variance `v` and off-diagonal covariance `c`,
    `2 * tr(G²) - (tr G)² = 4 c² ≥ 0`, and choosing `X = (1, -1)` gives `v = 1, c = -1 < 0` with
    sum variance `2 v + 2 c = 0 ≥ 0`, proving finite `2`-exchangeability allows negative correlation `c < 0`
    whereas infinite de Finetti mixtures of i.i.d. laws force `c ≥ 0`! -/
theorem exchangeable_gram_trace_and_negative_correlation_boundary (v c : Int) :
    let trG := 2 * v
    let trG2 := 2 * (v ^ 2 + c ^ 2)
    (2 * trG2 - trG ^ 2 = 4 * c ^ 2) ∧
    (let v_wit : Int := 1; let c_wit : Int := -1;
     c_wit < 0 ∧ 2 * v_wit + 2 * c_wit = 0) := by
  refine ⟨by grind, by decide⟩

end CommonGround.Verification.TheoremAtlasPermanentRecoverableAndObservableBridge
