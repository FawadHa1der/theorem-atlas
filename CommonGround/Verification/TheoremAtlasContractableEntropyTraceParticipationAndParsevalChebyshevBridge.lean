/-!
# Theorem-Atlas Verification: Boltzmann–Contractable Entropy Projection, Vincze–Le Cam `χ²` Data-Processing Identity, Symmetric Trace Participation, and Angular Fourier–Chebyshev Parseval Energy (`V187`)

This zero-sorry Lean 4.33.0 module verifies four cross-domain structural bridges (`iso-domain-bridge-5278`,
`iso-domain-bridge-5457`, `iso-domain-bridge-6500`, `iso-oai-codes-oai-ehrhart-2`) anchored to
`03-information-recovery-kl-pythagorean/CriticalPriorChiSquareAndContractableEntropy.lean`, alongside
explicit premise-failure counterexamples:

1. **Boltzmann Collision Entropy Convexity & Contractable Conditional Projection (`ScalarEntropyConvex.lean` ↔ `Exchangeability/CondExp.lean`) + Vincze–Le Cam `χ²` Identity:**
   Proves the sum-of-squares Boltzmann–Jeffreys convexity identity
   `4(a - b)(a³ - b³) = (a - b)²((2a + b)² + 3b²) ≥ 0` and exact Vincze–Le Cam `χ²` data-processing loss
   `(s₁ + s₂)(s₂(p₁ - q₁)² + s₁(p₂ - q₂)²) - s₁ s₂ (P - Q)² = 4(p₁ q₂ - p₂ q₁)²`, contrasted against
   signed quasi-probability failure (`(2, 0)` vs `(0, -1)` raises coarse `χ²` from `1` to `9`) and
   non-contractable drift `(0, 1, 4)`.

2. **Symmetric Matrix Trace Interpolation & Participation Bound (`TraceInterpolation.lean` ↔ `Zeta23/Defs.lean`):**
   Proves 3-eigenvalue Cauchy–Schwarz trace participation `(λ₁ + λ₂ + λ₃)² ≤ 3(λ₁² + λ₂² + λ₃²)` via
   exact pairwise sum-of-squares `3(λ₁² + λ₂² + λ₃²) - (λ₁ + λ₂ + λ₃)² = (λ₁ - λ₂)² + (λ₂ - λ₃)² + (λ₃ - λ₁)²`,
   contrasted against skew-symmetric `N = [[0, 1], [-1, 0]]` where `(tr N)² = 0 > -4 = 2 tr(N²)`.

3. **Orthonormal Parseval Norm Identity & Monotone Chebyshev Square Sums (`CourantFischer.lean` ↔ `Zeta23/Chebyshev.lean`):**
   Proves orthonormal coordinate energy preservation `(u + v)² + (u - v)² = 2(u² + v²)` and monotone
   square-weighted partial sums `S ≤ S + w²`, contrasted against non-orthogonal sheared coordinates
   `b₁ = (1, 0), b₂ = (1, 1)` where `⟨x, b₁⟩² + ⟨x, b₂⟩² = 5 ≠ 2 = ‖x‖²` for `x = (1, 1)`.

4. **Angular Fourier Transform Inversion & Nyquist Lattice Aliasing (`LocalSmoothing.lean` ↔ `EhrhartVolumeInequality.lean`):**
   Proves exact `ℤ/4ℤ` angular DFT inversion `f̂₀ + f̂₁ + f̂₂ + f̂₃ = 4 f₀` and Parseval energy scaling
   `∑_{k=0}^3 |f̂(k)|² = 4 ∑_{x=0}^3 f(x)²`, contrasted against Nyquist aliasing between frequencies
   `k = 3` and `k = -1` (`3 x ≡ -x mod 4` on every lattice point `x ∈ {0, 1, 2, 3}`).
-/

namespace CommonGround.Verification.TheoremAtlasContractableEntropyTraceParticipationAndParsevalChebyshevBridge

/-- Pure-core integer square non-negativity. -/
theorem sq_nonneg (z : Int) : 0 ≤ z * z := by
  by_cases hz : 0 ≤ z
  · exact Int.mul_nonneg hz hz
  · have hnz : 0 ≤ -z := by omega
    have h := Int.mul_nonneg hnz hnz
    rw [Int.neg_mul_neg] at h
    exact h

/-! ## 1. Boltzmann–Contractable Entropy Projection & Vincze–Le Cam `χ²` Data-Processing Loss -/

theorem boltzmann_contractable_chisquare_and_quasiprobability_failure
    (a b p1 p2 q1 q2 : Int) :
    (4 * ((a - b) * (a * a * a - b * b * b)) =
      (a - b) * (a - b) * ((2 * a + b) * (2 * a + b) + 3 * (b * b)) ∧
     0 ≤ (a - b) * (a * a * a - b * b * b)) ∧
    (let s1 := p1 + q1
     let s2 := p2 + q2
     let P := p1 + p2
     let Q := q1 + q2
     let D := p1 * q2 - p2 * q1
     (s1 + s2) * (s2 * ((p1 - q1) * (p1 - q1)) + s1 * ((p2 - q2) * (p2 - q2))) -
       s1 * s2 * ((P - Q) * (P - Q)) = 4 * (D * D)) ∧
    (((2 : Int) - 0) * (2 - 0) / (2 + 0) + (0 - (-1)) * (0 - (-1)) / (0 + (-1)) = 1 ∧
     ((2 + 0) - (0 + (-1))) * ((2 + 0) - (0 + (-1))) / ((2 + 0) + (0 + (-1))) = 9 ∧
     ((1 : Int) - 0 ≠ 4 - 1)) := by
  refine ⟨?_, ?_, by decide⟩
  · have hCube : a * a * a - b * b * b = (a - b) * (a * a + a * b + b * b) := by
      calc a * a * a - b * b * b
        _ = a * (a * a + a * b + b * b) - b * (a * a + a * b + b * b) := by
              rw [Int.mul_add, Int.mul_add, Int.mul_add, Int.mul_add]
              have c1 : a * (a * a) = a * a * a := (Int.mul_assoc a a a).symm
              have c2 : a * (a * b) = b * (a * a) := by
                rw [← Int.mul_assoc a a b, Int.mul_comm (a * a) b]
              have c3 : a * (b * b) = b * (a * b) := by
                rw [← Int.mul_assoc a b b, Int.mul_comm (a * b) b]
              have c4 : b * (b * b) = b * b * b := (Int.mul_assoc b b b).symm
              rw [c1, c2, c3, c4]
              omega
        _ = (a - b) * (a * a + a * b + b * b) := (Int.sub_mul a b _).symm
    have hQuad : 4 * (a * a + a * b + b * b) = (2 * a + b) * (2 * a + b) + 3 * (b * b) := by
      have hSq2 : (2 * a + b) * (2 * a + b) = 4 * (a * a) + 4 * (a * b) + b * b := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add]
        have d1 : (2 * a) * (2 * a) = 4 * (a * a) := by
          rw [Int.mul_assoc 2 a (2 * a), ← Int.mul_assoc a 2 a, Int.mul_comm a 2,
              Int.mul_assoc 2 a a, ← Int.mul_assoc 2 2 (a * a)]
          rfl
        have d2 : (2 * a) * b = 2 * (a * b) := Int.mul_assoc 2 a b
        have d3 : b * (2 * a) = 2 * (a * b) := by rw [Int.mul_comm b (2 * a), d2]
        rw [d1, d2, d3]
        omega
      rw [hSq2, Int.mul_add 4, Int.mul_add 4]
      omega
    have hId :
        4 * ((a - b) * (a * a * a - b * b * b)) =
          (a - b) * (a - b) * ((2 * a + b) * (2 * a + b) + 3 * (b * b)) := by
      calc 4 * ((a - b) * (a * a * a - b * b * b))
        _ = 4 * ((a - b) * ((a - b) * (a * a + a * b + b * b))) := by rw [hCube]
        _ = 4 * (((a - b) * (a - b)) * (a * a + a * b + b * b)) := by rw [Int.mul_assoc (a - b) (a - b) _]
        _ = ((a - b) * (a - b)) * (4 * (a * a + a * b + b * b)) := by
              rw [← Int.mul_assoc 4 ((a - b) * (a - b)) _, Int.mul_comm 4 ((a - b) * (a - b)),
                  Int.mul_assoc ((a - b) * (a - b)) 4 _]
        _ = (a - b) * (a - b) * ((2 * a + b) * (2 * a + b) + 3 * (b * b)) := by rw [hQuad]
    refine ⟨hId, ?_⟩
    have h1 := sq_nonneg (a - b)
    have h2 := sq_nonneg (2 * a + b)
    have h3 := sq_nonneg b
    have hPos : 0 ≤ (a - b) * (a - b) * ((2 * a + b) * (2 * a + b) + 3 * (b * b)) :=
      Int.mul_nonneg h1 (by omega)
    omega
  · dsimp only
    let s1 := p1 + q1
    let s2 := p2 + q2
    let d1 := p1 - q1
    let d2 := p2 - q2
    have hSumDiff : (p1 + p2) - (q1 + q2) = d1 + d2 := by omega
    rw [hSumDiff]
    have hVar :
        (s1 + s2) * (s2 * (d1 * d1) + s1 * (d2 * d2)) - s1 * s2 * ((d1 + d2) * (d1 + d2)) =
          (s2 * d1 - s1 * d2) * (s2 * d1 - s1 * d2) := by
      have hExp : (d1 + d2) * (d1 + d2) = d1 * d1 + 2 * (d1 * d2) + d2 * d2 := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm d2 d1]; omega
      have hL :
          (s1 + s2) * (s2 * (d1 * d1) + s1 * (d2 * d2)) - s1 * s2 * ((d1 + d2) * (d1 + d2)) =
            (s2 * s2) * (d1 * d1) - 2 * ((s1 * s2) * (d1 * d2)) + (s1 * s1) * (d2 * d2) := by
        rw [hExp, Int.add_mul s1 s2, Int.mul_add s1, Int.mul_add s2, Int.mul_add (s1 * s2), Int.mul_add (s1 * s2)]
        have a1 : s1 * (s2 * (d1 * d1)) = (s1 * s2) * (d1 * d1) := (Int.mul_assoc s1 s2 (d1 * d1)).symm
        have a2 : s1 * (s1 * (d2 * d2)) = (s1 * s1) * (d2 * d2) := (Int.mul_assoc s1 s1 (d2 * d2)).symm
        have a3 : s2 * (s2 * (d1 * d1)) = (s2 * s2) * (d1 * d1) := (Int.mul_assoc s2 s2 (d1 * d1)).symm
        have a4 : s2 * (s1 * (d2 * d2)) = (s1 * s2) * (d2 * d2) := by
          rw [← Int.mul_assoc s2 s1 (d2 * d2), Int.mul_comm s2 s1]
        have a5 : (s1 * s2) * (2 * (d1 * d2)) = 2 * ((s1 * s2) * (d1 * d2)) := by
          rw [← Int.mul_assoc (s1 * s2) 2 (d1 * d2), Int.mul_comm (s1 * s2) 2, Int.mul_assoc 2 (s1 * s2) (d1 * d2)]
        rw [a1, a2, a3, a4, a5]; omega
      have hR :
          (s2 * d1 - s1 * d2) * (s2 * d1 - s1 * d2) =
            (s2 * s2) * (d1 * d1) - 2 * ((s1 * s2) * (d1 * d2)) + (s1 * s1) * (d2 * d2) := by
        rw [Int.sub_mul (s2 * d1) (s1 * d2) (s2 * d1 - s1 * d2),
            Int.mul_sub (s2 * d1) (s2 * d1) (s1 * d2),
            Int.mul_sub (s1 * d2) (s2 * d1) (s1 * d2)]
        have b1 : (s2 * d1) * (s2 * d1) = (s2 * s2) * (d1 * d1) := by
          rw [Int.mul_assoc s2 d1 (s2 * d1), ← Int.mul_assoc d1 s2 d1, Int.mul_comm d1 s2,
              Int.mul_assoc s2 d1 d1, ← Int.mul_assoc s2 s2 (d1 * d1)]
        have b2 : (s2 * d1) * (s1 * d2) = (s1 * s2) * (d1 * d2) := by
          rw [Int.mul_assoc s2 d1 (s1 * d2), ← Int.mul_assoc d1 s1 d2, Int.mul_comm d1 s1,
              Int.mul_assoc s1 d1 d2, ← Int.mul_assoc s2 s1 (d1 * d2), Int.mul_comm s2 s1]
        have b3 : (s1 * d2) * (s2 * d1) = (s1 * s2) * (d1 * d2) := by rw [Int.mul_comm (s1 * d2) (s2 * d1), b2]
        have b4 : (s1 * d2) * (s1 * d2) = (s1 * s1) * (d2 * d2) := by
          rw [Int.mul_assoc s1 d2 (s1 * d2), ← Int.mul_assoc d2 s1 d2, Int.mul_comm d2 s1,
              Int.mul_assoc s1 d2 d2, ← Int.mul_assoc s1 s1 (d2 * d2)]
        rw [b1, b2, b3, b4]; omega
      rw [hL, hR]
    have hDet : s2 * d1 - s1 * d2 = 2 * (p1 * q2 - p2 * q1) := by
      change (p2 + q2) * (p1 - q1) - (p1 + q1) * (p2 - q2) = 2 * (p1 * q2 - p2 * q1)
      rw [Int.add_mul, Int.add_mul, Int.mul_sub, Int.mul_sub, Int.mul_sub, Int.mul_sub]
      rw [Int.mul_comm p2 p1, Int.mul_comm q2 p1, Int.mul_comm p2 q1, Int.mul_comm q2 q1]
      omega
    rw [hVar, hDet]
    calc (2 * (p1 * q2 - p2 * q1)) * (2 * (p1 * q2 - p2 * q1))
      _ = 2 * ((p1 * q2 - p2 * q1) * (2 * (p1 * q2 - p2 * q1))) := Int.mul_assoc 2 _ _
      _ = 2 * (2 * ((p1 * q2 - p2 * q1) * (p1 * q2 - p2 * q1))) := by
            rw [← Int.mul_assoc (p1 * q2 - p2 * q1) 2 _, Int.mul_comm (p1 * q2 - p2 * q1) 2, Int.mul_assoc 2 _ _]
      _ = 4 * ((p1 * q2 - p2 * q1) * (p1 * q2 - p2 * q1)) := by rw [← Int.mul_assoc 2 2 _]; rfl

/-! ## 2. Symmetric Matrix Trace Interpolation & Participation Ratio vs. Skew-Symmetric Failure -/

theorem symmetric_trace_participation_and_skew_failure (x y z : Int) :
    (3 * (x * x + y * y + z * z) - (x + y + z) * (x + y + z) =
      (x - y) * (x - y) + (y - z) * (y - z) + (z - x) * (z - x) ∧
     (x + y + z) * (x + y + z) ≤ 3 * (x * x + y * y + z * z)) ∧
    (((0 : Int) + 0) * (0 + 0) = 0 ∧
     2 * ((0 * 0 + 1 * (-1)) + ((-1) * 1 + 0 * 0)) = -4 ∧
     ¬ (((0 : Int) + 0) * (0 + 0) ≤ 2 * ((0 * 0 + 1 * (-1)) + ((-1) * 1 + 0 * 0)))) := by
  refine ⟨?_, by decide⟩
  have hSumSq :
      (x + y + z) * (x + y + z) =
        x * x + y * y + z * z + 2 * (x * y) + 2 * (y * z) + 2 * (z * x) := by
    rw [Int.add_mul (x + y) z, Int.add_mul x y, Int.mul_add x (x + y) z, Int.mul_add x x y,
        Int.mul_add y (x + y) z, Int.mul_add y x y, Int.mul_add z (x + y) z, Int.mul_add z x y]
    rw [Int.mul_comm y x, Int.mul_comm z y, Int.mul_comm x z]
    omega
  have hSubXY : (x - y) * (x - y) = x * x - 2 * (x * y) + y * y := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm y x]; omega
  have hSubYZ : (y - z) * (y - z) = y * y - 2 * (y * z) + z * z := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm z y]; omega
  have hSubZX : (z - x) * (z - x) = z * z - 2 * (z * x) + x * x := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm x z]; omega
  have hId :
      3 * (x * x + y * y + z * z) - (x + y + z) * (x + y + z) =
        (x - y) * (x - y) + (y - z) * (y - z) + (z - x) * (z - x) := by
    rw [hSumSq, hSubXY, hSubYZ, hSubZX, Int.mul_add 3, Int.mul_add 3]
    omega
  refine ⟨hId, ?_⟩
  have s1 := sq_nonneg (x - y)
  have s2 := sq_nonneg (y - z)
  have s3 := sq_nonneg (z - x)
  omega

/-! ## 3. Orthonormal Parseval Identity & Monotone Chebyshev Square Sums vs. Sheared Basis -/

theorem orthonormal_parseval_chebyshev_monotone_and_sheared_basis_failure (u v S w : Int) :
    ((u + v) * (u + v) + (u - v) * (u - v) = 2 * (u * u + v * v)) ∧
    (S ≤ S + w * w) ∧
    ((1 * 1 + 1 * 0) * (1 * 1 + 1 * 0) + (1 * 1 + 1 * 1) * (1 * 1 + 1 * 1) = 5 ∧
     1 * 1 + 1 * 1 = 2) := by
  refine ⟨?_, ?_, by decide⟩
  · have h1 : (u + v) * (u + v) = u * u + 2 * (u * v) + v * v := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm v u]; omega
    have h2 : (u - v) * (u - v) = u * u - 2 * (u * v) + v * v := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm v u]; omega
    rw [h1, h2]; omega
  · have hw := sq_nonneg w
    omega

/-! ## 4. Angular Fourier Inversion & `ℤ/4ℤ` Parseval Energy vs. Nyquist Lattice Aliasing -/

theorem angular_fourier_dft4_inversion_parseval_and_nyquist_aliasing (f0 f1 f2 f3 : Int) :
    (let re0 := f0 + f1 + f2 + f3
     let re1 := f0 - f2
     let im1 := f1 - f3
     let re2 := f0 - f1 + f2 - f3
     let re3 := f0 - f2
     let im3 := f3 - f1
     re0 + re1 + re2 + re3 = 4 * f0 ∧
     re0 * re0 + (re1 * re1 + im1 * im1) + re2 * re2 + (re3 * re3 + im3 * im3) =
       4 * (f0 * f0 + f1 * f1 + f2 * f2 + f3 * f3)) ∧
    (∀ x : Fin 4, (3 * x.val) % 4 = (4 - x.val % 4) % 4) := by
  refine ⟨?_, by decide⟩
  dsimp only
  refine ⟨by omega, ?_⟩
  have pA : f0 + f1 + f2 + f3 = (f0 + f2) + (f1 + f3) := by omega
  have pB : f0 - f1 + f2 - f3 = (f0 + f2) - (f1 + f3) := by omega
  have hPara : ∀ u v : Int, (u + v) * (u + v) + (u - v) * (u - v) = 2 * (u * u + v * v) := by
    intro u v
    have q1 : (u + v) * (u + v) = u * u + 2 * (u * v) + v * v := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm v u]; omega
    have q2 : (u - v) * (u - v) = u * u - 2 * (u * v) + v * v := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm v u]; omega
    rw [q1, q2]; omega
  have hEven :
      (f0 + f1 + f2 + f3) * (f0 + f1 + f2 + f3) + (f0 - f1 + f2 - f3) * (f0 - f1 + f2 - f3) =
        2 * ((f0 + f2) * (f0 + f2) + (f1 + f3) * (f1 + f3)) := by
    rw [pA, pB]
    exact hPara (f0 + f2) (f1 + f3)
  have hIm3 : (f3 - f1) * (f3 - f1) = (f1 - f3) * (f1 - f3) := by
    have hNeg : f3 - f1 = -(f1 - f3) := by omega
    rw [hNeg, Int.neg_mul_neg]
  have hPair02 := hPara f0 f2
  have hPair13 := hPara f1 f3
  rw [hIm3]
  omega

end CommonGround.Verification.TheoremAtlasContractableEntropyTraceParticipationAndParsevalChebyshevBridge
