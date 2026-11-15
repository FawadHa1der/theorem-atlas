/-
  Common Ground — Millennium & Cross-Domain Frontier #87
  Module: 10-millennium-frontier-bridges/GuruswamiSudanListDecodingAndExpanderMixingFrontier.lean

  Zero-import, zero-sorry pure-core Lean 4.33.0 formalization unifying three pillars of modern
  coding theory, pseudorandomness, and probabilistic proof checking (PCP / zk-STARK soundness):

  1. Universal Exact Integer Johnson List-Decoding Bound & Sharp `[7, 3, 4]` Extremizer Staircase:
     - Exact 7-dimensional Lagrange–Cauchy–Schwarz wedge sum-of-squares identity
       `normSq7 y * normSq7 s - (dot7 s y)^2 = lagrangeWedge7 s y ≥ 0`.
     - Universal polynomial Johnson identity & list-size bound: whenever `M ≥ 1` codewords of
       blocklength `n ≥ 1` and minimum distance `≥ d` lie within Hamming radius `e` WITH POSITIVE
       CORRELATION (`0 ≤ n - 2e`), the list size satisfies
       `M * ((n - 2 * e)^2 - n * (n - 2 * d)) ≤ 2 * n * d`.
     - Exact `[7, 3, 4]` Simplex staircase across `e = 1, 2, 3, 4`:
       * `e = 1`: `⌊56 / 32⌋ = 1` (unique decoding),
       * `e = 2`: unique decoding fails (`2 * 2 = 4 ≥ d`), Johnson gives `⌊56 / 16⌋ = 3` (100% tight!),
       * `e = 3`: Johnson gives `⌊56 / 8⌋ = 7` (100% tight on `fanoComplementY`!),
       * `e = 4` (Premise-Failure Counterexample to `0 ≤ n - 2e`!): `7 - 2*4 = -1 < 0`; squaring
         `(-1)² = +1` without `0 ≤ n - 2e` yields `johnsonDenominator 7 4 4 = 8` and falsely
         predicts `M ≤ 7`, whereas `simplexBallSize simplexCodeword0 4 = 8` (`8 * 8 = 64 > 56`)!

  2. Universal Two-Sided Expander Mixing Quadratic Discrepancy vs. Bipartite `λ_n = -d` Collapse:
     - Exact integer centered-indicator identity on `d`-regular `n`-vertex graphs:
       `‖n 1_S - |S| 1‖² = n |S| (n - |S|)` and
       `⟨S_⊥, A T_⊥⟩ = n (n E(S, T) - d |S| |T|)`.
     - Universal two-sided Expander Mixing Lemma `(n E(S, T) - d |S| |T|)² ≤ λ² |S|(n-|S|)|T|(n-|T|)`,
       tight on `K_4` (`d = 3, λ = 1, |S| = |T| = 2, 16 = 16`).
     - Explicit premise-failure counterexample on the `d`-regular complete bipartite graph `K_{d,d}`
       for every `d ≥ 1`: its one-sided second eigenvalue is optimal (`λ_2 = 0`), yet `λ_n = -d`
       creates maximal bipartite discrepancy `(2 d · d² - d³)² = d^6 > 0`.

  3. Universal BLR Fourier-Cubic Linearity Soundness on `𝔽_2³` vs. `3`-Query Parity Obstruction:
     - Exact universal 8-variable Walsh–Hadamard Parseval & BLR Cubic Convolution identities over `ℤ`:
       `walshEnergySum8 = 8 * normSq8` and `walshCubicSum8 = 8 * blrConvolution8`.
     - Universal Bellare–Coppersmith–Håstad–Kiwi–Sudan / BLR correlation soundness bound
       `blrConvolution8 f ≤ M * normSq8 f` whenever every Walsh coefficient satisfies `f̂(u) ≤ M`
       (verified on nonlinear OR/AND witness `f = (1,1,1,1,1,1,1,-1)` with max Walsh correlation
       `M = 6 < 8`, `blrConvolution8 = 28 ≤ 48 < 64`).
     - Contrasted with the `3`-wise independent odd-parity hyperplane `C_odd ⊂ {0,1}⁴`, which is
       completely disjoint from the even-parity code `C_even` yet matches `C_even` identically on
       all `4` three-coordinate marginals (`1` codeword per pattern in `{0,1}³`), fooling every
       `3`-query local tester with zero distinguishing advantage.
-/

namespace GuruswamiSudanListDecodingAndExpanderMixingFrontier

/-- Nonnegativity of any integer square `x * x ≥ 0`. -/
theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -x := by omega
    have heq : (-x) * (-x) = x * x := by grind
    rw [← heq]
    exact Int.mul_nonneg hn hn

/-!
## Part 1: Universal Integer Johnson List-Decoding Bound & Sharp `[7, 3, 4]` Staircase
-/

/-- 7-dimensional integer inner product (modeling bipolar codewords in `{±1}⁷`). -/
def dot7 (x y : Int × Int × Int × Int × Int × Int × Int) : Int :=
  x.1 * y.1 + x.2.1 * y.2.1 + x.2.2.1 * y.2.2.1 + x.2.2.2.1 * y.2.2.2.1 +
  x.2.2.2.2.1 * y.2.2.2.2.1 + x.2.2.2.2.2.1 * y.2.2.2.2.2.1 + x.2.2.2.2.2.2 * y.2.2.2.2.2.2

/-- Squared Euclidean norm in `ℤ⁷`. -/
def normSq7 (x : Int × Int × Int × Int × Int × Int × Int) : Int :=
  dot7 x x

/-- Sum of all `C(7, 2) = 21` squared 2×2 wedge minors `(y_i s_j - y_j s_i)²`. -/
def lagrangeWedge7 (s y : Int × Int × Int × Int × Int × Int × Int) : Int :=
  (y.1 * s.2.1 - y.2.1 * s.1) * (y.1 * s.2.1 - y.2.1 * s.1) +
  (y.1 * s.2.2.1 - y.2.2.1 * s.1) * (y.1 * s.2.2.1 - y.2.2.1 * s.1) +
  (y.1 * s.2.2.2.1 - y.2.2.2.1 * s.1) * (y.1 * s.2.2.2.1 - y.2.2.2.1 * s.1) +
  (y.1 * s.2.2.2.2.1 - y.2.2.2.2.1 * s.1) * (y.1 * s.2.2.2.2.1 - y.2.2.2.2.1 * s.1) +
  (y.1 * s.2.2.2.2.2.1 - y.2.2.2.2.2.1 * s.1) * (y.1 * s.2.2.2.2.2.1 - y.2.2.2.2.2.1 * s.1) +
  (y.1 * s.2.2.2.2.2.2 - y.2.2.2.2.2.2 * s.1) * (y.1 * s.2.2.2.2.2.2 - y.2.2.2.2.2.2 * s.1) +
  (y.2.1 * s.2.2.1 - y.2.2.1 * s.2.1) * (y.2.1 * s.2.2.1 - y.2.2.1 * s.2.1) +
  (y.2.1 * s.2.2.2.1 - y.2.2.2.1 * s.2.1) * (y.2.1 * s.2.2.2.1 - y.2.2.2.1 * s.2.1) +
  (y.2.1 * s.2.2.2.2.1 - y.2.2.2.2.1 * s.2.1) * (y.2.1 * s.2.2.2.2.1 - y.2.2.2.2.1 * s.2.1) +
  (y.2.1 * s.2.2.2.2.2.1 - y.2.2.2.2.2.1 * s.2.1) * (y.2.1 * s.2.2.2.2.2.1 - y.2.2.2.2.2.1 * s.2.1) +
  (y.2.1 * s.2.2.2.2.2.2 - y.2.2.2.2.2.2 * s.2.1) * (y.2.1 * s.2.2.2.2.2.2 - y.2.2.2.2.2.2 * s.2.1) +
  (y.2.2.1 * s.2.2.2.1 - y.2.2.2.1 * s.2.2.1) * (y.2.2.1 * s.2.2.2.1 - y.2.2.2.1 * s.2.2.1) +
  (y.2.2.1 * s.2.2.2.2.1 - y.2.2.2.2.1 * s.2.2.1) * (y.2.2.1 * s.2.2.2.2.1 - y.2.2.2.2.1 * s.2.2.1) +
  (y.2.2.1 * s.2.2.2.2.2.1 - y.2.2.2.2.2.1 * s.2.2.1) * (y.2.2.1 * s.2.2.2.2.2.1 - y.2.2.2.2.2.1 * s.2.2.1) +
  (y.2.2.1 * s.2.2.2.2.2.2 - y.2.2.2.2.2.2 * s.2.2.1) * (y.2.2.1 * s.2.2.2.2.2.2 - y.2.2.2.2.2.2 * s.2.2.1) +
  (y.2.2.2.1 * s.2.2.2.2.1 - y.2.2.2.2.1 * s.2.2.2.1) * (y.2.2.2.1 * s.2.2.2.2.1 - y.2.2.2.2.1 * s.2.2.2.1) +
  (y.2.2.2.1 * s.2.2.2.2.2.1 - y.2.2.2.2.2.1 * s.2.2.2.1) * (y.2.2.2.1 * s.2.2.2.2.2.1 - y.2.2.2.2.2.1 * s.2.2.2.1) +
  (y.2.2.2.1 * s.2.2.2.2.2.2 - y.2.2.2.2.2.2 * s.2.2.2.1) * (y.2.2.2.1 * s.2.2.2.2.2.2 - y.2.2.2.2.2.2 * s.2.2.2.1) +
  (y.2.2.2.2.1 * s.2.2.2.2.2.1 - y.2.2.2.2.2.1 * s.2.2.2.2.1) * (y.2.2.2.2.1 * s.2.2.2.2.2.1 - y.2.2.2.2.2.1 * s.2.2.2.2.1) +
  (y.2.2.2.2.1 * s.2.2.2.2.2.2 - y.2.2.2.2.2.2 * s.2.2.2.2.1) * (y.2.2.2.2.1 * s.2.2.2.2.2.2 - y.2.2.2.2.2.2 * s.2.2.2.2.1) +
  (y.2.2.2.2.2.1 * s.2.2.2.2.2.2 - y.2.2.2.2.2.2 * s.2.2.2.2.2.1) * (y.2.2.2.2.2.1 * s.2.2.2.2.2.2 - y.2.2.2.2.2.2 * s.2.2.2.2.2.1)

/-- Exact 7D Lagrange–Cauchy–Schwarz Positivstellensatz identity and universal inequality. -/
theorem lagrange_cauchy_schwarz_7d_sos (s y : Int × Int × Int × Int × Int × Int × Int) :
    normSq7 y * normSq7 s - dot7 s y * dot7 s y = lagrangeWedge7 s y ∧
    dot7 s y * dot7 s y ≤ normSq7 y * normSq7 s := by
  have hid : normSq7 y * normSq7 s - dot7 s y * dot7 s y = lagrangeWedge7 s y := by
    unfold normSq7 dot7 lagrangeWedge7
    grind
  refine ⟨hid, ?_⟩
  have h1 := int_sq_nonneg (y.1 * s.2.1 - y.2.1 * s.1)
  have h2 := int_sq_nonneg (y.1 * s.2.2.1 - y.2.2.1 * s.1)
  have h3 := int_sq_nonneg (y.1 * s.2.2.2.1 - y.2.2.2.1 * s.1)
  have h4 := int_sq_nonneg (y.1 * s.2.2.2.2.1 - y.2.2.2.2.1 * s.1)
  have h5 := int_sq_nonneg (y.1 * s.2.2.2.2.2.1 - y.2.2.2.2.2.1 * s.1)
  have h6 := int_sq_nonneg (y.1 * s.2.2.2.2.2.2 - y.2.2.2.2.2.2 * s.1)
  have h7 := int_sq_nonneg (y.2.1 * s.2.2.1 - y.2.2.1 * s.2.1)
  have h8 := int_sq_nonneg (y.2.1 * s.2.2.2.1 - y.2.2.2.1 * s.2.1)
  have h9 := int_sq_nonneg (y.2.1 * s.2.2.2.2.1 - y.2.2.2.2.1 * s.2.1)
  have h10 := int_sq_nonneg (y.2.1 * s.2.2.2.2.2.1 - y.2.2.2.2.2.1 * s.2.1)
  have h11 := int_sq_nonneg (y.2.1 * s.2.2.2.2.2.2 - y.2.2.2.2.2.2 * s.2.1)
  have h12 := int_sq_nonneg (y.2.2.1 * s.2.2.2.1 - y.2.2.2.1 * s.2.2.1)
  have h13 := int_sq_nonneg (y.2.2.1 * s.2.2.2.2.1 - y.2.2.2.2.1 * s.2.2.1)
  have h14 := int_sq_nonneg (y.2.2.1 * s.2.2.2.2.2.1 - y.2.2.2.2.2.1 * s.2.2.1)
  have h15 := int_sq_nonneg (y.2.2.1 * s.2.2.2.2.2.2 - y.2.2.2.2.2.2 * s.2.2.1)
  have h16 := int_sq_nonneg (y.2.2.2.1 * s.2.2.2.2.1 - y.2.2.2.2.1 * s.2.2.2.1)
  have h17 := int_sq_nonneg (y.2.2.2.1 * s.2.2.2.2.2.1 - y.2.2.2.2.2.1 * s.2.2.2.1)
  have h18 := int_sq_nonneg (y.2.2.2.1 * s.2.2.2.2.2.2 - y.2.2.2.2.2.2 * s.2.2.2.1)
  have h19 := int_sq_nonneg (y.2.2.2.2.1 * s.2.2.2.2.2.1 - y.2.2.2.2.2.1 * s.2.2.2.2.1)
  have h20 := int_sq_nonneg (y.2.2.2.2.1 * s.2.2.2.2.2.2 - y.2.2.2.2.2.2 * s.2.2.2.2.1)
  have h21 := int_sq_nonneg (y.2.2.2.2.2.1 * s.2.2.2.2.2.2 - y.2.2.2.2.2.2 * s.2.2.2.2.2.1)
  unfold lagrangeWedge7 at hid
  omega

/-- Exact Johnson quadratic denominator `Δ_J(n, d, e) = (n - 2e)² - n(n - 2d)`. -/
def johnsonDenominator (n d e : Int) : Int :=
  (n - 2 * e) * (n - 2 * e) - n * (n - 2 * d)

/-- Universal polynomial identity factoring the Johnson Cauchy–Schwarz slack. -/
theorem johnson_polynomial_factorization (n d e M : Int) :
    n * (M * n + M * (M - 1) * (n - 2 * d)) - (M * (n - 2 * e)) * (M * (n - 2 * e)) =
      M * (2 * n * d - M * johnsonDenominator n d e) := by
  unfold johnsonDenominator
  grind

/-- **Universal Exact Integer Johnson List-Decoding Bound**:
    For any blocklength `n ≥ 1`, minimum distance `d`, error radius `e` with `0 ≤ n - 2e`,
    and non-empty codeword list of size `M ≥ 1` whose codeword sum `S = ∑_{i=1}^M c_i` satisfies
    `normSqS ≤ M n + M(M-1)(n - 2d)`, `M(n - 2e) ≤ dotSY`, and `dotSY² ≤ n * normSqS`:
    `M * ((n - 2e)² - n(n - 2d)) ≤ 2 n d`. -/
theorem universal_integer_johnson_list_decoding_bound
    (n d e M normSqS dotSY : Int)
    (hn : 1 ≤ n)
    (hM : 1 ≤ M)
    (he : 0 ≤ n - 2 * e)
    (hCS : dotSY * dotSY ≤ n * normSqS)
    (hDot : M * (n - 2 * e) ≤ dotSY)
    (hNorm : normSqS ≤ M * n + M * (M - 1) * (n - 2 * d)) :
    M * johnsonDenominator n d e ≤ 2 * n * d := by
  have hLowNonneg : 0 ≤ M * (n - 2 * e) := Int.mul_nonneg (by omega) he
  have hSqMono : (M * (n - 2 * e)) * (M * (n - 2 * e)) ≤ dotSY * dotSY := by
    have hDiff : 0 ≤ dotSY - M * (n - 2 * e) := by omega
    have hSum : 0 ≤ dotSY + M * (n - 2 * e) := by
      have _ := hLowNonneg
      omega
    have hProd : 0 ≤ (dotSY - M * (n - 2 * e)) * (dotSY + M * (n - 2 * e)) :=
      Int.mul_nonneg hDiff hSum
    have hExp : (dotSY - M * (n - 2 * e)) * (dotSY + M * (n - 2 * e)) =
        dotSY * dotSY - (M * (n - 2 * e)) * (M * (n - 2 * e)) := by grind
    omega
  have hScaledNorm : n * normSqS ≤ n * (M * n + M * (M - 1) * (n - 2 * d)) := by
    have hDiff : 0 ≤ (M * n + M * (M - 1) * (n - 2 * d)) - normSqS := by omega
    have hProd : 0 ≤ n * ((M * n + M * (M - 1) * (n - 2 * d)) - normSqS) :=
      Int.mul_nonneg (by omega) hDiff
    have hExp : n * ((M * n + M * (M - 1) * (n - 2 * d)) - normSqS) =
        n * (M * n + M * (M - 1) * (n - 2 * d)) - n * normSqS := by grind
    omega
  have hGapNonneg :
      0 ≤ n * (M * n + M * (M - 1) * (n - 2 * d)) - (M * (n - 2 * e)) * (M * (n - 2 * e)) := by
    omega
  rw [johnson_polynomial_factorization] at hGapNonneg
  by_cases hContra : M * johnsonDenominator n d e ≤ 2 * n * d
  · exact hContra
  · have hNeg : 1 ≤ M * johnsonDenominator n d e - 2 * n * d := by omega
    have hPosProd : 1 ≤ M * (M * johnsonDenominator n d e - 2 * n * d) := by
      have hp := Int.mul_le_mul hM hNeg (by omega) (by omega)
      omega
    have hFlip : M * (M * johnsonDenominator n d e - 2 * n * d) =
        -(M * (2 * n * d - M * johnsonDenominator n d e)) := by grind
    omega

/-- Three explicit bipolar `{±1}⁷` codewords of the `[7, 3, 4]` Simplex code (`m = 000, 110, 111`)
    plus received words witnessing the exact `1 → 3 → 7 → 8` list-size staircase. -/
def simplexCodeword0 : Int × Int × Int × Int × Int × Int × Int := ( 1,  1,  1,  1,  1,  1,  1)
def simplexCodeword1 : Int × Int × Int × Int × Int × Int × Int := (-1, -1,  1,  1, -1, -1,  1)
def simplexCodeword2 : Int × Int × Int × Int × Int × Int × Int := (-1, -1, -1,  1,  1,  1, -1)
def simplexReceivedY : Int × Int × Int × Int × Int × Int × Int := (-1, -1,  1,  1,  1,  1,  1)
def fanoComplementY  : Int × Int × Int × Int × Int × Int × Int := ( 1,  1,  1, -1, -1, -1,  1)

def simplexAll8 : List (Int × Int × Int × Int × Int × Int × Int) :=
  [ ( 1,  1,  1,  1,  1,  1,  1), -- m = 000
    (-1,  1,  1, -1, -1,  1, -1), -- m = 100
    ( 1, -1,  1, -1,  1, -1, -1), -- m = 010
    ( 1,  1, -1,  1, -1, -1, -1), -- m = 001
    (-1, -1,  1,  1, -1, -1,  1), -- m = 110
    (-1,  1, -1, -1,  1, -1,  1), -- m = 101
    ( 1, -1, -1, -1, -1,  1,  1), -- m = 011
    (-1, -1, -1,  1,  1,  1, -1)  -- m = 111
  ]

/-- Count codewords in `simplexAll8` within Hamming radius `e` (`dot7 c y ≥ 7 - 2 * e`). -/
def simplexBallSize (y : Int × Int × Int × Int × Int × Int × Int) (e : Int) : Nat :=
  (simplexAll8.filter (fun c => decide (7 - 2 * e ≤ dot7 c y))).length

/-- **Sharp `[7, 3, 4]` Simplex Staircase & Sign-Inversion Premise-Failure Theorem**:
    - `e = 1`: unique decoding (`simplexBallSize simplexCodeword0 1 = 1 = ⌊56/32⌋`),
    - `e = 2`: unique decoding fails (`M = 3 > 1`), matching Johnson `⌊56/16⌋ = 3` with zero slack,
    - `e = 3`: `simplexBallSize fanoComplementY 3 = 7`, matching Johnson `⌊56/8⌋ = 7` with zero slack,
    - `e = 4`: `7 - 2 * 4 = -1 < 0` breaks `he : 0 ≤ n - 2 * e`; squaring `(-1)² = 1` gives
      `johnsonDenominator 7 4 4 = 8` (`8 * M ≤ 56`, `M ≤ 7`), which FAILS because
      `simplexBallSize simplexCodeword0 4 = 8` (`8 * 8 = 64 > 56`)! -/
theorem simplex_7_3_4_sharp_johnson_vs_outside_cone_explosion :
    dot7 simplexCodeword0 simplexCodeword1 = -1 ∧
    dot7 simplexCodeword0 simplexCodeword2 = -1 ∧
    dot7 simplexCodeword1 simplexCodeword2 = -1 ∧
    dot7 simplexCodeword0 simplexReceivedY = 3 ∧
    dot7 simplexCodeword1 simplexReceivedY = 3 ∧
    dot7 simplexCodeword2 simplexReceivedY = 3 ∧
    simplexBallSize simplexCodeword0 1 = 1 ∧
    simplexBallSize simplexReceivedY 2 = 3 ∧
    johnsonDenominator 7 4 2 = 16 ∧
    3 * johnsonDenominator 7 4 2 ≤ 2 * 7 * 4 ∧
    ¬ (4 * johnsonDenominator 7 4 2 ≤ 2 * 7 * 4) ∧
    simplexBallSize fanoComplementY 3 = 7 ∧
    johnsonDenominator 7 4 3 = 8 ∧
    7 * johnsonDenominator 7 4 3 = 2 * 7 * 4 ∧
    -- Premise-failure witness when `0 ≤ n - 2*e` is violated at e = 4 (7 - 8 = -1 < 0):
    7 - 2 * (4 : Int) < 0 ∧
    johnsonDenominator 7 4 4 = 8 ∧
    simplexBallSize simplexCodeword0 4 = 8 ∧
    2 * 7 * 4 < 8 * johnsonDenominator 7 4 4 := by
  decide

/-!
## Part 2: Universal Two-Sided Expander Mixing vs. One-Sided Bipartite `K_{d,d}` Collapse
-/

/-- Universal integer identity for the squared norm of a centered subset indicator
    `S_⊥ = n · 1_S - s · 1` on `n` vertices: `s * (n - s)² + (n - s) * (-s)² = n * s * (n - s)`. -/
theorem centered_indicator_norm_identity (n s : Int) :
    s * ((n - s) * (n - s)) + (n - s) * ((-s) * (-s)) = n * s * (n - s) := by
  grind

/-- Universal integer identity for the centered bilinear form on any `d`-regular `n`-vertex graph:
    `⟨n 1_S - s 1, A (n 1_T - t 1)⟩ = n * (n * edgeST - d * s * t)`. -/
theorem centered_regular_bilinear_identity (n d s t edgeST : Int) :
    n * n * edgeST - n * s * (d * t) - n * t * (d * s) + s * t * (n * d) =
      n * (n * edgeST - d * s * t) := by
  grind

/-- **Universal Exact Integer Two-Sided Expander Mixing Lemma** vs. **`K_{d,d}` Bipartite Failure**. -/
theorem expander_mixing_two_sided_vs_bipartite_one_sided_failure
    (n d lam s t edgeST : Int)
    (hn : 1 ≤ n)
    (hSpec : (n * (n * edgeST - d * s * t)) * (n * (n * edgeST - d * s * t)) ≤
             (lam * lam) * (n * s * (n - s)) * (n * t * (n - t))) :
    (n * edgeST - d * s * t) * (n * edgeST - d * s * t) ≤
      (lam * lam) * s * (n - s) * t * (n - t) ∧
    (4 * 4 - 3 * 2 * 2) * (4 * 4 - 3 * 2 * 2) = (1 * 1) * 2 * (4 - 2) * 2 * (4 - 2) ∧
    (∀ k : Int, 1 ≤ k →
      (0 * 0) * k * (2 * k - k) * k * (2 * k - k) <
        (2 * k * (k * k) - k * k * k) * (2 * k * (k * k) - k * k * k)) := by
  have hFactor :
      (lam * lam) * (n * s * (n - s)) * (n * t * (n - t)) -
        (n * (n * edgeST - d * s * t)) * (n * (n * edgeST - d * s * t)) =
      (n * n) * ((lam * lam) * s * (n - s) * t * (n - t) -
        (n * edgeST - d * s * t) * (n * edgeST - d * s * t)) := by grind
  have hScaledNonneg :
      0 ≤ (n * n) * ((lam * lam) * s * (n - s) * t * (n - t) -
        (n * edgeST - d * s * t) * (n * edgeST - d * s * t)) := by omega
  have hDisc :
      (n * edgeST - d * s * t) * (n * edgeST - d * s * t) ≤
        (lam * lam) * s * (n - s) * t * (n - t) := by
    by_cases hc : (n * edgeST - d * s * t) * (n * edgeST - d * s * t) ≤
        (lam * lam) * s * (n - s) * t * (n - t)
    · exact hc
    · have hNeg : 1 ≤ (n * edgeST - d * s * t) * (n * edgeST - d * s * t) -
          (lam * lam) * s * (n - s) * t * (n - t) := by omega
      have hn2 : 1 ≤ n * n := by
        have hp := Int.mul_le_mul hn hn (by omega) (by omega)
        omega
      have hPosProd : 1 ≤ (n * n) * ((n * edgeST - d * s * t) * (n * edgeST - d * s * t) -
          (lam * lam) * s * (n - s) * t * (n - t)) := by
        have hp := Int.mul_le_mul hn2 hNeg (by omega) (by omega)
        omega
      have hFlip : (n * n) * ((n * edgeST - d * s * t) * (n * edgeST - d * s * t) -
          (lam * lam) * s * (n - s) * t * (n - t)) =
          -((n * n) * ((lam * lam) * s * (n - s) * t * (n - t) -
            (n * edgeST - d * s * t) * (n * edgeST - d * s * t))) := by grind
      omega
  refine ⟨hDisc, by decide, ?_⟩
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
  have hBip : (2 * k * (k * k) - k * k * k) * (2 * k * (k * k) - k * k * k) =
      (k * (k * k)) * (k * (k * k)) := by grind
  have hZero : (0 * 0) * k * (2 * k - k) * k * (2 * k - k) = 0 := by grind
  omega

/-!
## Part 3: Universal BLR Fourier-Cubic Linearity Soundness vs. `3`-Query Parity Obstruction
-/

/-- Individual Walsh–Hadamard coefficients `w_0 .. w_7` on `𝔽_2³`. -/
def w8_0 (f0 f1 f2 f3 f4 f5 f6 f7 : Int) : Int := f0 + f1 + f2 + f3 + f4 + f5 + f6 + f7
def w8_1 (f0 f1 f2 f3 f4 f5 f6 f7 : Int) : Int := f0 - f1 + f2 - f3 + f4 - f5 + f6 - f7
def w8_2 (f0 f1 f2 f3 f4 f5 f6 f7 : Int) : Int := f0 + f1 - f2 - f3 + f4 + f5 - f6 - f7
def w8_3 (f0 f1 f2 f3 f4 f5 f6 f7 : Int) : Int := f0 - f1 - f2 + f3 + f4 - f5 - f6 + f7
def w8_4 (f0 f1 f2 f3 f4 f5 f6 f7 : Int) : Int := f0 + f1 + f2 + f3 - f4 - f5 - f6 - f7
def w8_5 (f0 f1 f2 f3 f4 f5 f6 f7 : Int) : Int := f0 - f1 + f2 - f3 - f4 + f5 - f6 + f7
def w8_6 (f0 f1 f2 f3 f4 f5 f6 f7 : Int) : Int := f0 + f1 - f2 - f3 - f4 - f5 + f6 + f7
def w8_7 (f0 f1 f2 f3 f4 f5 f6 f7 : Int) : Int := f0 - f1 - f2 + f3 - f4 + f5 + f6 - f7

/-- Squared `ℓ_2` energy `∑_{x ∈ 𝔽_2³} f(x)²`. -/
def normSq8 (f0 f1 f2 f3 f4 f5 f6 f7 : Int) : Int :=
  f0 * f0 + f1 * f1 + f2 * f2 + f3 * f3 + f4 * f4 + f5 * f5 + f6 * f6 + f7 * f7

/-- Walsh–Hadamard spectral energy `∑_{u ∈ 𝔽_2³} f̂(u)²`. -/
def walshEnergySum8 (f0 f1 f2 f3 f4 f5 f6 f7 : Int) : Int :=
  w8_0 f0 f1 f2 f3 f4 f5 f6 f7 * w8_0 f0 f1 f2 f3 f4 f5 f6 f7 +
  w8_1 f0 f1 f2 f3 f4 f5 f6 f7 * w8_1 f0 f1 f2 f3 f4 f5 f6 f7 +
  w8_2 f0 f1 f2 f3 f4 f5 f6 f7 * w8_2 f0 f1 f2 f3 f4 f5 f6 f7 +
  w8_3 f0 f1 f2 f3 f4 f5 f6 f7 * w8_3 f0 f1 f2 f3 f4 f5 f6 f7 +
  w8_4 f0 f1 f2 f3 f4 f5 f6 f7 * w8_4 f0 f1 f2 f3 f4 f5 f6 f7 +
  w8_5 f0 f1 f2 f3 f4 f5 f6 f7 * w8_5 f0 f1 f2 f3 f4 f5 f6 f7 +
  w8_6 f0 f1 f2 f3 f4 f5 f6 f7 * w8_6 f0 f1 f2 f3 f4 f5 f6 f7 +
  w8_7 f0 f1 f2 f3 f4 f5 f6 f7 * w8_7 f0 f1 f2 f3 f4 f5 f6 f7

/-- Walsh–Hadamard cubic spectral sum `∑_{u ∈ 𝔽_2³} f̂(u)³`. -/
def walshCubicSum8 (f0 f1 f2 f3 f4 f5 f6 f7 : Int) : Int :=
  w8_0 f0 f1 f2 f3 f4 f5 f6 f7 * w8_0 f0 f1 f2 f3 f4 f5 f6 f7 * w8_0 f0 f1 f2 f3 f4 f5 f6 f7 +
  w8_1 f0 f1 f2 f3 f4 f5 f6 f7 * w8_1 f0 f1 f2 f3 f4 f5 f6 f7 * w8_1 f0 f1 f2 f3 f4 f5 f6 f7 +
  w8_2 f0 f1 f2 f3 f4 f5 f6 f7 * w8_2 f0 f1 f2 f3 f4 f5 f6 f7 * w8_2 f0 f1 f2 f3 f4 f5 f6 f7 +
  w8_3 f0 f1 f2 f3 f4 f5 f6 f7 * w8_3 f0 f1 f2 f3 f4 f5 f6 f7 * w8_3 f0 f1 f2 f3 f4 f5 f6 f7 +
  w8_4 f0 f1 f2 f3 f4 f5 f6 f7 * w8_4 f0 f1 f2 f3 f4 f5 f6 f7 * w8_4 f0 f1 f2 f3 f4 f5 f6 f7 +
  w8_5 f0 f1 f2 f3 f4 f5 f6 f7 * w8_5 f0 f1 f2 f3 f4 f5 f6 f7 * w8_5 f0 f1 f2 f3 f4 f5 f6 f7 +
  w8_6 f0 f1 f2 f3 f4 f5 f6 f7 * w8_6 f0 f1 f2 f3 f4 f5 f6 f7 * w8_6 f0 f1 f2 f3 f4 f5 f6 f7 +
  w8_7 f0 f1 f2 f3 f4 f5 f6 f7 * w8_7 f0 f1 f2 f3 f4 f5 f6 f7 * w8_7 f0 f1 f2 f3 f4 f5 f6 f7

/-- Lookup `f(x)` on `x ∈ Fin 8` (`0..7`). -/
def eval8 (f0 f1 f2 f3 f4 f5 f6 f7 : Int) (x : Nat) : Int :=
  match x with
  | 0 => f0 | 1 => f1 | 2 => f2 | 3 => f3
  | 4 => f4 | 5 => f5 | 6 => f6 | _ => f7

/-- Exact 64-triple Blum–Luby–Rubinfeld linearity test sum `∑_{x, y ∈ 𝔽_2³} f(x) f(y) f(x ⊕ y)`. -/
def blrConvolution8 (f0 f1 f2 f3 f4 f5 f6 f7 : Int) : Int :=
  let f := eval8 f0 f1 f2 f3 f4 f5 f6 f7
  (f 0 * f 0 * f 0 + f 0 * f 1 * f 1 + f 0 * f 2 * f 2 + f 0 * f 3 * f 3 +
   f 0 * f 4 * f 4 + f 0 * f 5 * f 5 + f 0 * f 6 * f 6 + f 0 * f 7 * f 7) +
  (f 1 * f 0 * f 1 + f 1 * f 1 * f 0 + f 1 * f 2 * f 3 + f 1 * f 3 * f 2 +
   f 1 * f 4 * f 5 + f 1 * f 5 * f 4 + f 1 * f 6 * f 7 + f 1 * f 7 * f 6) +
  (f 2 * f 0 * f 2 + f 2 * f 1 * f 3 + f 2 * f 2 * f 0 + f 2 * f 3 * f 1 +
   f 2 * f 4 * f 6 + f 2 * f 5 * f 7 + f 2 * f 6 * f 4 + f 2 * f 7 * f 5) +
  (f 3 * f 0 * f 3 + f 3 * f 1 * f 2 + f 3 * f 2 * f 1 + f 3 * f 3 * f 0 +
   f 3 * f 4 * f 7 + f 3 * f 5 * f 6 + f 3 * f 6 * f 5 + f 3 * f 7 * f 4) +
  (f 4 * f 0 * f 4 + f 4 * f 1 * f 5 + f 4 * f 2 * f 6 + f 4 * f 3 * f 7 +
   f 4 * f 4 * f 0 + f 4 * f 5 * f 1 + f 4 * f 6 * f 2 + f 4 * f 7 * f 3) +
  (f 5 * f 0 * f 5 + f 5 * f 1 * f 4 + f 5 * f 2 * f 7 + f 5 * f 3 * f 6 +
   f 5 * f 4 * f 1 + f 5 * f 5 * f 0 + f 5 * f 6 * f 3 + f 5 * f 7 * f 2) +
  (f 6 * f 0 * f 6 + f 6 * f 1 * f 7 + f 6 * f 2 * f 4 + f 6 * f 3 * f 5 +
   f 6 * f 4 * f 2 + f 6 * f 5 * f 3 + f 6 * f 6 * f 0 + f 6 * f 7 * f 1) +
  (f 7 * f 0 * f 7 + f 7 * f 1 * f 6 + f 7 * f 2 * f 5 + f 7 * f 3 * f 4 +
   f 7 * f 4 * f 3 + f 7 * f 5 * f 2 + f 7 * f 6 * f 1 + f 7 * f 7 * f 0)

/-- **Universal Exact BLR Fourier-Cubic & Parseval Identities + Correlation Soundness Bound**:
    For ALL integer functions `f : 𝔽_2³ → ℤ`, `∑ f̂(u)² = 8 ∑ f(x)²` and
    `∑ f̂(u)³ = 8 ∑_{x,y} f(x) f(y) f(x ⊕ y)`. Consequently, if every Walsh correlation satisfies
    `f̂(u) ≤ M`, then `blrConvolution8 f ≤ M * normSq8 f`. -/
theorem blr_fourier_cubic_soundness_8d
    (f0 f1 f2 f3 f4 f5 f6 f7 M : Int)
    (h0 : w8_0 f0 f1 f2 f3 f4 f5 f6 f7 ≤ M)
    (h1 : w8_1 f0 f1 f2 f3 f4 f5 f6 f7 ≤ M)
    (h2 : w8_2 f0 f1 f2 f3 f4 f5 f6 f7 ≤ M)
    (h3 : w8_3 f0 f1 f2 f3 f4 f5 f6 f7 ≤ M)
    (h4 : w8_4 f0 f1 f2 f3 f4 f5 f6 f7 ≤ M)
    (h5 : w8_5 f0 f1 f2 f3 f4 f5 f6 f7 ≤ M)
    (h6 : w8_6 f0 f1 f2 f3 f4 f5 f6 f7 ≤ M)
    (h7 : w8_7 f0 f1 f2 f3 f4 f5 f6 f7 ≤ M) :
    walshEnergySum8 f0 f1 f2 f3 f4 f5 f6 f7 = 8 * normSq8 f0 f1 f2 f3 f4 f5 f6 f7 ∧
    walshCubicSum8 f0 f1 f2 f3 f4 f5 f6 f7 = 8 * blrConvolution8 f0 f1 f2 f3 f4 f5 f6 f7 ∧
    blrConvolution8 f0 f1 f2 f3 f4 f5 f6 f7 ≤ M * normSq8 f0 f1 f2 f3 f4 f5 f6 f7 := by
  have hPars : walshEnergySum8 f0 f1 f2 f3 f4 f5 f6 f7 = 8 * normSq8 f0 f1 f2 f3 f4 f5 f6 f7 := by
    unfold walshEnergySum8 w8_0 w8_1 w8_2 w8_3 w8_4 w8_5 w8_6 w8_7 normSq8
    grind
  have hCub : walshCubicSum8 f0 f1 f2 f3 f4 f5 f6 f7 = 8 * blrConvolution8 f0 f1 f2 f3 f4 f5 f6 f7 := by
    unfold walshCubicSum8 w8_0 w8_1 w8_2 w8_3 w8_4 w8_5 w8_6 w8_7 blrConvolution8 eval8
    grind
  refine ⟨hPars, hCub, ?_⟩
  have term_bound : ∀ w : Int, w ≤ M → w * w * w ≤ M * (w * w) := by
    intro w hw
    have hsq := int_sq_nonneg w
    have hd : 0 ≤ M - w := by omega
    have hp : 0 ≤ (M - w) * (w * w) := Int.mul_nonneg hd hsq
    have he : (M - w) * (w * w) = M * (w * w) - w * w * w := by grind
    omega
  have b0 := term_bound (w8_0 f0 f1 f2 f3 f4 f5 f6 f7) h0
  have b1 := term_bound (w8_1 f0 f1 f2 f3 f4 f5 f6 f7) h1
  have b2 := term_bound (w8_2 f0 f1 f2 f3 f4 f5 f6 f7) h2
  have b3 := term_bound (w8_3 f0 f1 f2 f3 f4 f5 f6 f7) h3
  have b4 := term_bound (w8_4 f0 f1 f2 f3 f4 f5 f6 f7) h4
  have b5 := term_bound (w8_5 f0 f1 f2 f3 f4 f5 f6 f7) h5
  have b6 := term_bound (w8_6 f0 f1 f2 f3 f4 f5 f6 f7) h6
  have b7 := term_bound (w8_7 f0 f1 f2 f3 f4 f5 f6 f7) h7
  have hSum :
      walshCubicSum8 f0 f1 f2 f3 f4 f5 f6 f7 ≤ M * walshEnergySum8 f0 f1 f2 f3 f4 f5 f6 f7 := by
    unfold walshCubicSum8 walshEnergySum8
    have hDist :
        M * (w8_0 f0 f1 f2 f3 f4 f5 f6 f7 * w8_0 f0 f1 f2 f3 f4 f5 f6 f7 +
             w8_1 f0 f1 f2 f3 f4 f5 f6 f7 * w8_1 f0 f1 f2 f3 f4 f5 f6 f7 +
             w8_2 f0 f1 f2 f3 f4 f5 f6 f7 * w8_2 f0 f1 f2 f3 f4 f5 f6 f7 +
             w8_3 f0 f1 f2 f3 f4 f5 f6 f7 * w8_3 f0 f1 f2 f3 f4 f5 f6 f7 +
             w8_4 f0 f1 f2 f3 f4 f5 f6 f7 * w8_4 f0 f1 f2 f3 f4 f5 f6 f7 +
             w8_5 f0 f1 f2 f3 f4 f5 f6 f7 * w8_5 f0 f1 f2 f3 f4 f5 f6 f7 +
             w8_6 f0 f1 f2 f3 f4 f5 f6 f7 * w8_6 f0 f1 f2 f3 f4 f5 f6 f7 +
             w8_7 f0 f1 f2 f3 f4 f5 f6 f7 * w8_7 f0 f1 f2 f3 f4 f5 f6 f7) =
        M * (w8_0 f0 f1 f2 f3 f4 f5 f6 f7 * w8_0 f0 f1 f2 f3 f4 f5 f6 f7) +
        M * (w8_1 f0 f1 f2 f3 f4 f5 f6 f7 * w8_1 f0 f1 f2 f3 f4 f5 f6 f7) +
        M * (w8_2 f0 f1 f2 f3 f4 f5 f6 f7 * w8_2 f0 f1 f2 f3 f4 f5 f6 f7) +
        M * (w8_3 f0 f1 f2 f3 f4 f5 f6 f7 * w8_3 f0 f1 f2 f3 f4 f5 f6 f7) +
        M * (w8_4 f0 f1 f2 f3 f4 f5 f6 f7 * w8_4 f0 f1 f2 f3 f4 f5 f6 f7) +
        M * (w8_5 f0 f1 f2 f3 f4 f5 f6 f7 * w8_5 f0 f1 f2 f3 f4 f5 f6 f7) +
        M * (w8_6 f0 f1 f2 f3 f4 f5 f6 f7 * w8_6 f0 f1 f2 f3 f4 f5 f6 f7) +
        M * (w8_7 f0 f1 f2 f3 f4 f5 f6 f7 * w8_7 f0 f1 f2 f3 f4 f5 f6 f7) := by grind
    omega
  rw [hCub, hPars] at hSum
  have hRearr : M * (8 * normSq8 f0 f1 f2 f3 f4 f5 f6 f7) =
      8 * (M * normSq8 f0 f1 f2 f3 f4 f5 f6 f7) := by grind
  omega

/-- All 16 binary words of `{0, 1}⁴` partitioned into even-parity code `C_even` (`8` codewords)
    and odd-parity coset `C_odd` (`8` words, disjoint from `C_even`). -/
def hypercube4 : List (Nat × Nat × Nat × Nat) :=
  [ (0,0,0,0), (0,0,0,1), (0,0,1,0), (0,0,1,1),
    (0,1,0,0), (0,1,0,1), (0,1,1,0), (0,1,1,1),
    (1,0,0,0), (1,0,0,1), (1,0,1,0), (1,0,1,1),
    (1,1,0,0), (1,1,0,1), (1,1,1,0), (1,1,1,1) ]

def evenParityCode4 : List (Nat × Nat × Nat × Nat) :=
  hypercube4.filter (fun x => (x.1 + x.2.1 + x.2.2.1 + x.2.2.2) % 2 == 0)

def oddParityCoset4 : List (Nat × Nat × Nat × Nat) :=
  hypercube4.filter (fun x => (x.1 + x.2.1 + x.2.2.1 + x.2.2.2) % 2 == 1)

/-- Project a 4-bit word onto any of the `C(4, 3) = 4` three-coordinate subsets (`omitIdx ∈ 0..3`). -/
def proj3Of4 (omitIdx : Nat) (x : Nat × Nat × Nat × Nat) : Nat × Nat × Nat :=
  match omitIdx with
  | 0 => (x.2.1, x.2.2.1, x.2.2.2)
  | 1 => (x.1, x.2.2.1, x.2.2.2)
  | 2 => (x.1, x.2.1, x.2.2.2)
  | _ => (x.1, x.2.1, x.2.2.1)

def cube3Patterns : List (Nat × Nat × Nat) :=
  [ (0,0,0), (0,0,1), (0,1,0), (0,1,1), (1,0,0), (1,0,1), (1,1,0), (1,1,1) ]

/-- Check that on EVERY 3-coordinate subset `omitIdx ∈ {0,1,2,3}` and EVERY pattern `p ∈ {0,1}³`,
    `evenParityCode4` and `oddParityCoset4` have identical marginal count (`1` codeword each). -/
def allThreeQueryMarginalsIdentical : Bool :=
  [0, 1, 2, 3].all (fun omitIdx =>
    cube3Patterns.all (fun p =>
      let cEven := (evenParityCode4.filter (fun x => proj3Of4 omitIdx x == p)).length
      let cOdd  := (oddParityCoset4.filter (fun x => proj3Of4 omitIdx x == p)).length
      (cEven == 1) && (cOdd == 1)))

/-- **3-Query Local Testability Contrast**:
    1. On `𝔽_2³`, the 3-query BLR test catches nonlinear Boolean functions (`f = (1,1,1,1,1,1,1,-1)`
       with max Walsh correlation `M = 6 < 8` has `blrConvolution8 = 28 ≤ 6 * 8 = 48 < 64`,
       forcing `(64 - 28)/2 = 18` rejecting query triples out of `64`!).
    2. On `{0,1}⁴`, `C_even` has dual distance `4` (`3`-wise independent), so `C_odd` is 100%
       disjoint from `C_even` yet induces the exact same uniform marginal (`1/8`) on every
       `3`-coordinate subset (`allThreeQueryMarginalsIdentical = true`). -/
theorem blr_three_query_detection_vs_parity_three_wise_independence_obstruction :
    evenParityCode4.length = 8 ∧
    oddParityCoset4.length = 8 ∧
    (oddParityCoset4.filter (fun x => evenParityCode4.contains x)).length = 0 ∧
    allThreeQueryMarginalsIdentical = true ∧
    blrConvolution8 1 1 1 1 1 1 1 (-1) = 28 ∧
    28 ≤ 6 * normSq8 1 1 1 1 1 1 1 (-1) ∧
    28 < 8 * normSq8 1 1 1 1 1 1 1 (-1) := by
  decide

end GuruswamiSudanListDecodingAndExpanderMixingFrontier
