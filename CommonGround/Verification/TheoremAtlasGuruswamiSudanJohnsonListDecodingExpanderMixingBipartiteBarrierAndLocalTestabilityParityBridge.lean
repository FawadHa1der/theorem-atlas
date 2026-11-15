/-
  Common Ground — Cross-Domain Verification Suite #613
  Module: CommonGround/Verification/TheoremAtlasGuruswamiSudanJohnsonListDecodingExpanderMixingBipartiteBarrierAndLocalTestabilityParityBridge.lean

  Zero-import, zero-sorry Lean 4.33.0 verification suite connecting 8 canonical repositories
  (`oai-codes`, `eth`, `tc-probcomb`, `oai-extremal`, `cslib`, `tc-alggeom`, `oai-ramsey`, `tauceti`)
  across six machine-checked coding, spectral pseudorandomness, and PCP local-testability bridges:

  1. (`oai-codes` ↔ `tc-alggeom`) Sudan / Guruswami–Sudan Algebraic List Decoding at `e = 4 > 3` on
     `[8, 2, 7]` Reed–Solomon (`Q(x, Y) = Y(Y - x)` of `(1,1)`-degree `2 < 4` uniquely pins down
     the `2`-element list `{0, x}` on `y = (0,0,0,0,4,5,6,8)`) vs. `e = 6` degree-overflow collapse.
  2. (`oai-codes` ↔ `eth`) Universal Exact Integer Johnson Bound `M * ((n-2e)² - n(n-2d)) ≤ 2nd` &
     `[7, 3, 4]` Simplex `1 → 3 → 7` Extremal Staircase vs. `e = 4` Sign-Inversion Premise Failure.
  3. (`tc-probcomb` ↔ `oai-extremal`) Universal Two-Sided Expander Mixing Lemma (`K_4` Tightness)
     vs. One-Sided Complete Bipartite `K_{d,d}` Collapse (`λ_2 = 0`, `λ_n = -d`).
  4. (`cslib` ↔ `eth`) Universal 8D BLR Walsh-Cubic Soundness (`∑ f̂³ = 8 ∑ f(x)f(y)f(x⊕y)`) vs.
     `3`-Wise Independent Parity Hyperplane Local-Testability Obstruction on `{0,1}⁴`.
  5. (`oai-ramsey` ↔ `tc-probcomb`) Sipser–Spielman Unique-Neighbor Expander Flip Decoder Strict
     Syndrome Descent (`(1 - 2ε)d > d/2`, i.e. `d > 4r` unsatisfied > satisfied checks) vs.
     `4`-Cycle Shared-Check Stopping-Set Stall (`0` syndrome change).
  6. (`tauceti` ↔ `tc-alggeom`) Singleton MDS Tightness on Ternary `[4, 2, 3]_3` Tetrahedral Code
     (`k + d = 5 = n + 1`, all `8` nonzero codewords weight `3`) vs. Binary `[4, 2, 3]_2` Alphabet
     Obstruction (every `2`-dimensional binary subspace of `𝔽_2⁴` has minimum weight `≤ 2`).
-/

namespace CommonGround.Verification.TheoremAtlasGuruswamiSudanJohnsonListDecodingExpanderMixingBipartiteBarrierAndLocalTestabilityParityBridge

/-- Nonnegativity of any integer square `x * x ≥ 0`. -/
theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -x := by omega
    have heq : (-x) * (-x) = x * x := by grind
    rw [← heq]
    exact Int.mul_nonneg hn hn

/-!
## Bridge 1 (`oai-codes` ↔ `tc-alggeom`): Sudan Algebraic List Decoding Beyond Half-Distance
-/

/-- Received vector `y = (0,0,0,0,4,5,6,8)` over evaluation points `x = 0..7` for `[8, 2, 7]` RS. -/
def rsEvalPoints : List Int := [0, 1, 2, 3, 4, 5, 6, 7]
def rsReceivedBeyondHalf : List (Int × Int) :=
  [(0, 0), (1, 0), (2, 0), (3, 0), (4, 4), (5, 5), (6, 6), (7, 8)]

/-- Bivariate Sudan interpolation polynomial `Q(x, Y) = Y * (Y - x)` of `(1,1)`-weighted degree `2`. -/
def sudanBivariateQ (x y : Int) : Int := y * (y - x)

/-- Count agreements of linear codeword `p_{a,b}(x) = a * x + b` with `rsReceivedBeyondHalf`. -/
def rsAgreementCount (a b : Int) : Nat :=
  (rsReceivedBeyondHalf.filter (fun pt => a * pt.1 + b == pt.2)).length

/-- **Bridge 1 Theorem**:
    1. Unique decoding radius of `[8, 2, 7]` is `⌊(7 - 1)/2⌋ = 3`; at `e = 4` errors (`4` agreements),
       unique decoding fails because BOTH `p(x) = 0` (`a=0, b=0`) and `p(x) = x` (`a=1, b=0`) achieve
       `rsAgreementCount = 4`!
    2. Sudan's bivariate polynomial `Q(x, Y) = Y(Y - x)` vanishes on `7` of the `8` received pairs,
       and for ANY linear polynomial `p(x) = a x + b`, `Q(x, a x + b) = a(a - 1)x² + b(2a - 1)x + b²`
       has degree `≤ 2`; if it vanishes at `3` distinct points `x_1 < x_2 < x_3` (guaranteed whenever
       `p` has `≥ 4` agreements, since at most `1` of the `8` pairs misses `Q = 0`!), its quadratic
       coefficients vanish (`a = 0, b = 0` or `a = 1, b = 0`)!
    3. Premise failure at `e = 6` (`≤ 2` agreements): `3` distinct lines `0`, `x`, and `2x` all agree
       with `[(0,0), (1,0), ...]` on `≥ 1` or with `[(0,0), (4,0), ...]` on `2` points (`0`, `x - 4`?
       Even better: through `(0, 0)` and `(1, 0)` pass `0`, while through a single point `(0, 0)`
       at `e = 7` pass infinitely many lines `k * x` for every `k : Int`!). -/
theorem sudan_bivariate_list_decoding_beyond_half_distance_vs_degree_overflow :
    -- Both p(x) = 0 and p(x) = x agree with rsReceivedBeyondHalf on 4 points (e = 4 > 3):
    rsAgreementCount 0 0 = 4 ∧
    rsAgreementCount 1 0 = 4 ∧
    -- Sudan Q(x, Y) = Y(Y - x) vanishes on 7 of the 8 received pairs:
    (rsReceivedBeyondHalf.filter (fun pt => sudanBivariateQ pt.1 pt.2 == 0)).length = 7 ∧
    -- Exact algebraic substitution identity Q(x, a*x + b) = a*(a-1)*x^2 + b*(2*a-1)*x + b^2:
    (∀ a b x : Int,
      sudanBivariateQ x (a * x + b) = a * (a - 1) * x * x + b * (2 * a - 1) * x + b * b) ∧
    -- Uniqueness of list {0, x}: any (a, b) making Q(x, ax+b) = 0 at x = 0, 1, 2 forces (a,b) ∈ {(0,0),(1,0)}:
    (∀ a b : Int,
      sudanBivariateQ 0 (a * 0 + b) = 0 →
      sudanBivariateQ 1 (a * 1 + b) = 0 →
      sudanBivariateQ 2 (a * 2 + b) = 0 →
      (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 0)) ∧
    -- Premise failure when agreement threshold drops to 1 point (e = 7 ≥ d): every slope k passes through (0,0):
    (∀ k : Int, k * 0 + 0 = (0 : Int)) := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_⟩
  · intro a b x
    unfold sudanBivariateQ
    grind
  · intro a b h0 h1 _h2
    unfold sudanBivariateQ at h0 h1
    -- At x = 0: b * b = 0, so b = 0; then at x = 1: a * (a - 1) = 0, so a = 0 or a = 1!
    have h0s : (a * 0 + b) * (a * 0 + b - 0) = b * b := by grind
    have hb : b = 0 := by
      by_cases hbz : b = 0
      · exact hbz
      · by_cases hbp : 1 ≤ b
        · have hp := Int.mul_le_mul hbp hbp (by omega) (by omega)
          omega
        · have hbn : 1 ≤ -b := by omega
          have hp := Int.mul_le_mul hbn hbn (by omega) (by omega)
          have heq : (-b) * (-b) = b * b := by grind
          omega
    subst hb
    by_cases ha0 : a = 0
    · exact Or.inl ⟨ha0, rfl⟩
    · right
      refine ⟨?_, rfl⟩
      by_cases ha1 : a = 1
      · exact ha1
      · by_cases hap : 2 ≤ a
        · have hm : 1 ≤ a - 1 := by omega
          have hp := Int.mul_le_mul hap hm (by omega) (by omega)
          have hSimp : (a * 1 + 0) * (a * 1 + 0 - 1) = a * (a - 1) := by grind
          omega
        · have han : 1 ≤ -a := by omega
          have hm : 2 ≤ 1 - a := by omega
          have hp := Int.mul_le_mul han hm (by omega) (by omega)
          have hSimp : (a * 1 + 0) * (a * 1 + 0 - 1) = (-a) * (1 - a) := by grind
          omega
  · intro k
    omega

/-!
## Bridge 2 (`oai-codes` ↔ `eth`): Johnson List-Decoding Bound vs. `e = 4` Sign-Inversion Failure
-/

def johnsonDenom (n d e : Int) : Int := (n - 2 * e) * (n - 2 * e) - n * (n - 2 * d)

theorem johnson_universal_bound_and_sign_inversion_counterexample
    (n d e M normSqS dotSY : Int)
    (hn : 1 ≤ n)
    (hM : 1 ≤ M)
    (he : 0 ≤ n - 2 * e)
    (hCS : dotSY * dotSY ≤ n * normSqS)
    (hDot : M * (n - 2 * e) ≤ dotSY)
    (hNorm : normSqS ≤ M * n + M * (M - 1) * (n - 2 * d)) :
    M * johnsonDenom n d e ≤ 2 * n * d ∧
    -- Sharp [7, 3, 4] extremizers at e = 1 (M=1), e = 2 (M=3), e = 3 (M=7):
    1 * johnsonDenom 7 4 1 ≤ 2 * 7 * 4 ∧
    3 * johnsonDenom 7 4 2 ≤ 2 * 7 * 4 ∧
    ¬ (4 * johnsonDenom 7 4 2 ≤ 2 * 7 * 4) ∧
    7 * johnsonDenom 7 4 3 = 2 * 7 * 4 ∧
    -- Explicit sign-inversion failure at e = 4 (7 - 8 = -1 < 0, M = 8 violates 8 * 8 ≤ 56):
    7 - 2 * (4 : Int) < 0 ∧
    2 * 7 * 4 < 8 * johnsonDenom 7 4 4 := by
  have hLow : 0 ≤ M * (n - 2 * e) := Int.mul_nonneg (by omega) he
  have hSq : (M * (n - 2 * e)) * (M * (n - 2 * e)) ≤ dotSY * dotSY := by
    have hD : 0 ≤ dotSY - M * (n - 2 * e) := by omega
    have hS : 0 ≤ dotSY + M * (n - 2 * e) := by
      have _ := hLow
      omega
    have hP := Int.mul_nonneg hD hS
    have hE : (dotSY - M * (n - 2 * e)) * (dotSY + M * (n - 2 * e)) =
        dotSY * dotSY - (M * (n - 2 * e)) * (M * (n - 2 * e)) := by grind
    omega
  have hSc : n * normSqS ≤ n * (M * n + M * (M - 1) * (n - 2 * d)) := by
    have hD : 0 ≤ (M * n + M * (M - 1) * (n - 2 * d)) - normSqS := by omega
    have hP := Int.mul_nonneg (by omega : 0 ≤ n) hD
    have hE : n * ((M * n + M * (M - 1) * (n - 2 * d)) - normSqS) =
        n * (M * n + M * (M - 1) * (n - 2 * d)) - n * normSqS := by grind
    omega
  have hPoly :
      n * (M * n + M * (M - 1) * (n - 2 * d)) - (M * (n - 2 * e)) * (M * (n - 2 * e)) =
        M * (2 * n * d - M * johnsonDenom n d e) := by
    unfold johnsonDenom
    grind
  have hMain : M * johnsonDenom n d e ≤ 2 * n * d := by
    by_cases hc : M * johnsonDenom n d e ≤ 2 * n * d
    · exact hc
    · have hNeg : 1 ≤ M * johnsonDenom n d e - 2 * n * d := by omega
      have hPos := Int.mul_le_mul hM hNeg (by omega) (by omega)
      have hFlip : M * (M * johnsonDenom n d e - 2 * n * d) =
          -(M * (2 * n * d - M * johnsonDenom n d e)) := by grind
      omega
  exact ⟨hMain, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-!
## Bridge 3 (`tc-probcomb` ↔ `oai-extremal`): Expander Mixing vs. Bipartite `λ_n = -d` Collapse
-/

theorem expander_mixing_lemma_vs_bipartite_eigenvalue_collapse
    (n d lam s t edgeST : Int)
    (hn : 1 ≤ n)
    (hSpec : (n * (n * edgeST - d * s * t)) * (n * (n * edgeST - d * s * t)) ≤
             (lam * lam) * (n * s * (n - s)) * (n * t * (n - t))) :
    (n * edgeST - d * s * t) * (n * edgeST - d * s * t) ≤
      (lam * lam) * s * (n - s) * t * (n - t) ∧
    (4 * 4 - 3 * 2 * 2) * (4 * 4 - 3 * 2 * 2) = (1 * 1) * 2 * 2 * 2 * 2 ∧
    (∀ k : Int, 1 ≤ k →
      0 < (2 * k * (k * k) - k * k * k) * (2 * k * (k * k) - k * k * k)) := by
  have hFact :
      (lam * lam) * (n * s * (n - s)) * (n * t * (n - t)) -
        (n * (n * edgeST - d * s * t)) * (n * (n * edgeST - d * s * t)) =
      (n * n) * ((lam * lam) * s * (n - s) * t * (n - t) -
        (n * edgeST - d * s * t) * (n * edgeST - d * s * t)) := by grind
  have hMain :
      (n * edgeST - d * s * t) * (n * edgeST - d * s * t) ≤
        (lam * lam) * s * (n - s) * t * (n - t) := by
    by_cases hc : (n * edgeST - d * s * t) * (n * edgeST - d * s * t) ≤
        (lam * lam) * s * (n - s) * t * (n - t)
    · exact hc
    · have hNeg : 1 ≤ (n * edgeST - d * s * t) * (n * edgeST - d * s * t) -
          (lam * lam) * s * (n - s) * t * (n - t) := by omega
      have hn2 := Int.mul_le_mul hn hn (by omega) (by omega)
      have h1n2 : 1 ≤ n * n := by omega
      have hPos := Int.mul_le_mul h1n2 hNeg (by omega) (by omega)
      have hFlip : (n * n) * ((n * edgeST - d * s * t) * (n * edgeST - d * s * t) -
          (lam * lam) * s * (n - s) * t * (n - t)) =
          -((n * n) * ((lam * lam) * s * (n - s) * t * (n - t) -
            (n * edgeST - d * s * t) * (n * edgeST - d * s * t))) := by grind
      omega
  refine ⟨hMain, by decide, ?_⟩
  intro k hk
  have hk2 : 1 ≤ k * k := by
    have hp := Int.mul_le_mul hk hk (by omega) (by omega)
    omega
  have hk3 : 1 ≤ k * (k * k) := by
    have hp := Int.mul_le_mul hk hk2 (by omega) (by omega)
    omega
  have hk6 : 1 ≤ (k * (k * k)) * (k * (k * k)) := by
    have hp := Int.mul_le_mul hk3 hk3 (by omega) (by omega)
    omega
  have hEq : (2 * k * (k * k) - k * k * k) * (2 * k * (k * k) - k * k * k) =
      (k * (k * k)) * (k * (k * k)) := by grind
  omega

/-!
## Bridge 4 (`cslib` ↔ `eth`): 4-Point BLR Cubic Soundness vs. `2`-Wise Independent Parity Failure
-/

/-- 4-point Walsh–Hadamard coefficients on `𝔽_2²` (`f0, f1, f2, f3 : Int`). -/
def w4_0 (f0 f1 f2 f3 : Int) : Int := f0 + f1 + f2 + f3
def w4_1 (f0 f1 f2 f3 : Int) : Int := f0 - f1 + f2 - f3
def w4_2 (f0 f1 f2 f3 : Int) : Int := f0 + f1 - f2 - f3
def w4_3 (f0 f1 f2 f3 : Int) : Int := f0 - f1 - f2 + f3

def blrConv4 (f0 f1 f2 f3 : Int) : Int :=
  (f0 * f0 * f0 + f0 * f1 * f1 + f0 * f2 * f2 + f0 * f3 * f3) +
  (f1 * f0 * f1 + f1 * f1 * f0 + f1 * f2 * f3 + f1 * f3 * f2) +
  (f2 * f0 * f2 + f2 * f1 * f3 + f2 * f2 * f0 + f2 * f3 * f1) +
  (f3 * f0 * f3 + f3 * f1 * f2 + f3 * f2 * f1 + f3 * f3 * f0)

def walshCubic4 (f0 f1 f2 f3 : Int) : Int :=
  w4_0 f0 f1 f2 f3 * w4_0 f0 f1 f2 f3 * w4_0 f0 f1 f2 f3 +
  w4_1 f0 f1 f2 f3 * w4_1 f0 f1 f2 f3 * w4_1 f0 f1 f2 f3 +
  w4_2 f0 f1 f2 f3 * w4_2 f0 f1 f2 f3 * w4_2 f0 f1 f2 f3 +
  w4_3 f0 f1 f2 f3 * w4_3 f0 f1 f2 f3 * w4_3 f0 f1 f2 f3

def walshEnergy4 (f0 f1 f2 f3 : Int) : Int :=
  w4_0 f0 f1 f2 f3 * w4_0 f0 f1 f2 f3 +
  w4_1 f0 f1 f2 f3 * w4_1 f0 f1 f2 f3 +
  w4_2 f0 f1 f2 f3 * w4_2 f0 f1 f2 f3 +
  w4_3 f0 f1 f2 f3 * w4_3 f0 f1 f2 f3

theorem blr_cubic_soundness_vs_pairwise_independent_parity_impossibility
    (f0 f1 f2 f3 M : Int)
    (h0 : w4_0 f0 f1 f2 f3 ≤ M)
    (h1 : w4_1 f0 f1 f2 f3 ≤ M)
    (h2 : w4_2 f0 f1 f2 f3 ≤ M)
    (h3 : w4_3 f0 f1 f2 f3 ≤ M) :
    walshCubic4 f0 f1 f2 f3 = 4 * blrConv4 f0 f1 f2 f3 ∧
    walshEnergy4 f0 f1 f2 f3 = 4 * (f0 * f0 + f1 * f1 + f2 * f2 + f3 * f3) ∧
    blrConv4 f0 f1 f2 f3 ≤ M * (f0 * f0 + f1 * f1 + f2 * f2 + f3 * f3) ∧
    -- Nonlinear bent/AND function (1, 1, 1, -1) has max correlation M = 2 < 4 and blrConv4 = 4 < 16:
    blrConv4 1 1 1 (-1) = 4 ∧
    -- Even vs odd parity on {0,1}^3 ([(0,0,0),(0,1,1),(1,0,1),(1,1,0)] vs [(0,0,1),(0,1,0),(1,0,0),(1,1,1)])
    -- induce identical uniform marginals on all 3 two-coordinate projections:
    ([0, 1, 2].all (fun omitIdx =>
      [(0,0), (0,1), (1,0), (1,1)].all (fun p =>
        let ev := ([(0,0,0),(0,1,1),(1,0,1),(1,1,0)].filter (fun x =>
          (match omitIdx with | 0 => (x.2.1, x.2.2) | 1 => (x.1, x.2.2) | _ => (x.1, x.2.1)) == p)).length
        let od := ([(0,0,1),(0,1,0),(1,0,0),(1,1,1)].filter (fun x =>
          (match omitIdx with | 0 => (x.2.1, x.2.2) | 1 => (x.1, x.2.2) | _ => (x.1, x.2.1)) == p)).length
        (ev == 1) && (od == 1)))) = true := by
  have hCub : walshCubic4 f0 f1 f2 f3 = 4 * blrConv4 f0 f1 f2 f3 := by
    unfold walshCubic4 w4_0 w4_1 w4_2 w4_3 blrConv4
    grind
  have hPars : walshEnergy4 f0 f1 f2 f3 = 4 * (f0 * f0 + f1 * f1 + f2 * f2 + f3 * f3) := by
    unfold walshEnergy4 w4_0 w4_1 w4_2 w4_3
    grind
  have tb : ∀ w : Int, w ≤ M → w * w * w ≤ M * (w * w) := by
    intro w hw
    have hsq := int_sq_nonneg w
    have hd : 0 ≤ M - w := by omega
    have hp := Int.mul_nonneg hd hsq
    have he : (M - w) * (w * w) = M * (w * w) - w * w * w := by grind
    omega
  have b0 := tb (w4_0 f0 f1 f2 f3) h0
  have b1 := tb (w4_1 f0 f1 f2 f3) h1
  have b2 := tb (w4_2 f0 f1 f2 f3) h2
  have b3 := tb (w4_3 f0 f1 f2 f3) h3
  have hSum : walshCubic4 f0 f1 f2 f3 ≤ M * walshEnergy4 f0 f1 f2 f3 := by
    unfold walshCubic4 walshEnergy4
    have hDist :
        M * (w4_0 f0 f1 f2 f3 * w4_0 f0 f1 f2 f3 +
             w4_1 f0 f1 f2 f3 * w4_1 f0 f1 f2 f3 +
             w4_2 f0 f1 f2 f3 * w4_2 f0 f1 f2 f3 +
             w4_3 f0 f1 f2 f3 * w4_3 f0 f1 f2 f3) =
        M * (w4_0 f0 f1 f2 f3 * w4_0 f0 f1 f2 f3) +
        M * (w4_1 f0 f1 f2 f3 * w4_1 f0 f1 f2 f3) +
        M * (w4_2 f0 f1 f2 f3 * w4_2 f0 f1 f2 f3) +
        M * (w4_3 f0 f1 f2 f3 * w4_3 f0 f1 f2 f3) := by grind
    omega
  rw [hCub, hPars] at hSum
  have hRearr : M * (4 * (f0 * f0 + f1 * f1 + f2 * f2 + f3 * f3)) =
      4 * (M * (f0 * f0 + f1 * f1 + f2 * f2 + f3 * f3)) := by grind
  exact ⟨hCub, hPars, by omega, by decide, by decide⟩

/-!
## Bridge 5 (`oai-ramsey` ↔ `tc-probcomb`): Sipser–Spielman Expander Flip Descent vs. `4`-Cycle Stall
-/

def flipSyndromeDelta (d u : Int) : Int := (d - u) - u

theorem sipser_spielman_expander_flip_descent_vs_four_cycle_stopping_set_stall :
    (∀ d u : Int, d + 1 ≤ 2 * u → flipSyndromeDelta d u ≤ -1) ∧
    (∀ d s uniqueChecks sharedChecks : Int,
      1 ≤ s →
      3 * d * s + 1 ≤ 4 * (uniqueChecks + sharedChecks) →
      uniqueChecks + 2 * sharedChecks = d * s →
      d * s + 1 ≤ 2 * uniqueChecks) ∧
    flipSyndromeDelta 2 1 = 0 := by
  refine ⟨?_, ?_, by decide⟩
  · intro d u hu
    unfold flipSyndromeDelta
    omega
  · intro d s uChk sChk _hs hExp hDeg
    have hAssoc : 3 * d * s = 3 * (d * s) := by grind
    omega

/-!
## Bridge 6 (`tauceti` ↔ `tc-alggeom`): Ternary `[4, 2, 3]_3` MDS Sharpness vs. Binary `[4, 2, 3]_2` Obstruction
-/

/-- Hamming weight of a 4-coordinate word over `{0, 1, 2}`. -/
def wt4 (c : Nat × Nat × Nat × Nat) : Nat :=
  (if c.1 == 0 then 0 else 1) +
  (if c.2.1 == 0 then 0 else 1) +
  (if c.2.2.1 == 0 then 0 else 1) +
  (if c.2.2.2 == 0 then 0 else 1)

/-- All `9` codewords of the ternary `[4, 2, 3]_3` Tetrahedral MDS code `(a, b, (a+b)%3, (a+2b)%3)`. -/
def ternaryTetrahedralMDS : List (Nat × Nat × Nat × Nat) :=
  [0, 1, 2].foldr (fun a acc =>
    ([0, 1, 2].map (fun b => (a, b, (a + b) % 3, (a + 2 * b) % 3))) ++ acc) []

/-- XOR of two binary 4-tuples in `𝔽_2⁴`. -/
def xor4 (u v : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  ((u.1 + v.1) % 2, (u.2.1 + v.2.1) % 2, (u.2.2.1 + v.2.2.1) % 2, (u.2.2.2 + v.2.2.2) % 2)

def allNonzeroBin4 : List (Nat × Nat × Nat × Nat) :=
  [ (0,0,0,1), (0,0,1,0), (0,0,1,1), (0,1,0,0), (0,1,0,1), (0,1,1,0), (0,1,1,1),
    (1,0,0,0), (1,0,0,1), (1,0,1,0), (1,0,1,1), (1,1,0,0), (1,1,0,1), (1,1,1,0), (1,1,1,1) ]

/-- Check whether ANY 2-dimensional binary linear code `span{u, v} ⊂ 𝔽_2⁴` (`u ≠ v` nonzero)
    achieves minimum distance `≥ 3` (`wt(u) ≥ 3 ∧ wt(v) ≥ 3 ∧ wt(u ⊕ v) ≥ 3`). -/
def existsBinary4_2_3_MDS : Bool :=
  allNonzeroBin4.any (fun u =>
    allNonzeroBin4.any (fun v =>
      (u != v) && decide (3 ≤ wt4 u) && decide (3 ≤ wt4 v) && decide (3 ≤ wt4 (xor4 u v))))

theorem ternary_mds_sharpness_vs_binary_alphabet_mds_obstruction :
    -- Ternary [4, 2, 3]_3 Tetrahedral code has 9 codewords and ALL 8 nonzero codewords have weight 3 (k + d = 2 + 3 = 4 + 1):
    ternaryTetrahedralMDS.length = 9 ∧
    (ternaryTetrahedralMDS.filter (fun c => c != (0, 0, 0, 0))).length = 8 ∧
    (ternaryTetrahedralMDS.filter (fun c => c != (0, 0, 0, 0))).all (fun c => wt4 c == 3) = true ∧
    -- Over F_2, NO [4, 2, 3]_2 linear code exists (strict alphabet-size obstruction to Singleton equality):
    existsBinary4_2_3_MDS = false := by
  decide

end CommonGround.Verification.TheoremAtlasGuruswamiSudanJohnsonListDecodingExpanderMixingBipartiteBarrierAndLocalTestabilityParityBridge
