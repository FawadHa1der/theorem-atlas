/-!
# Theorem-Atlas Verification: Floer Cotangent Energy–Action & Spectral Four-Measure, Radial Fourier Orbit Averaging, Symmetric-Gradient Korn Kernels, and Moment Determinacy (`V186`)

This zero-sorry Lean 4.33.0 module verifies four cross-domain structural bridges (`iso-domain-bridge-5398`,
`iso-domain-bridge-5749`, `iso-domain-bridge-5777`, `iso-domain-bridge-5786`) alongside explicit
premise-failure counterexamples:

1. **Floer Cotangent Energy–Action & Spectral Four-Measure (`ConnesRigidity.lean` ↔ `Cotangent/Action.lean`):**
   Proves discrete antipodal spectral-difference scaling `(u - (-u))² = 4 u²` alongside the exact
   Bogomol'nyi–Floer identity `qs² + ps² + qt² + pt² = (qs - pt)² + (ps + qt)² + 2(qs pt - ps qt)`,
   contrasted against anti-holomorphic orientation reversal `(1, 0, 0, -1)` where energy is `2 > 0`
   yet symplectic area is `-1 < 0`.

2. **Unitary/Orthogonal Norm Preservation & Radial Fourier Orbit Averaging (`EhrhartVolumeInequality.lean` ↔ `SpherePacking.lean`):**
   Proves `(c x - s y)² + (s x + c y)² = (c² + s²)(x² + y²)` and `D₄` radial orbit symmetrization
   `2(a + c)(x² + y²)`, contrasted against Cohn–Elkies LP inadmissibility when `a + c = -1 < 0`.

3. **Symmetric-Gradient Strain–Vorticity Split vs. Korn Rotation Kernel (`SymmetricGradientDerivative.lean` ↔ `Zeta23/Defs.lean`):**
   Proves `tr(J + Jᵀ) = 2 tr(J)` and `‖J + Jᵀ‖_F² + ‖J - Jᵀ‖_F² = 4 ‖J‖_F²`, contrasted against
   `J_rot = [[0, -1], [1, 0]]` where `J_rot + J_rotᵀ = 0` yet `‖J_rot‖_F² = 2 > 0`.

4. **Vandermonde Moment Determinacy vs. Four-Point Collision (`EhrhartVolumeInequality.lean` ↔ `Moments/Determinacy.lean`):**
   Proves unique recovery on `{-1, 0, 1}` from `(μ₀, μ₁, μ₂)` (`2 p₋₁ = μ₂ - μ₁`, `p₀ = μ₀ - μ₂`,
   `2 p₁ = μ₂ + μ₁`), contrasted against disjoint-support measures `p = (1, 0, 3, 0)` and
   `q = (0, 3, 0, 1)` on `{0, 1, 2, 3}` agreeing on `0`th, `1`st, and `2`nd moments (`4, 6, 12`)
   while diverging at the `3`rd (`24 ≠ 30`).
-/

namespace CommonGround.Verification.TheoremAtlasFloerCotangentActionRadialFourierKornAndMomentDeterminacyBridge

/-! ## 1. Floer Cotangent Energy–Action & Antipodal Spectral Four-Measure -/

theorem floer_cotangent_energy_spectral_four_mul_and_antiholomorphic_failure
    (u qs ps qt pt : Int) :
    (u - (-u)) * (u - (-u)) = 4 * (u * u) ∧
    qs * qs + ps * ps + qt * qt + pt * pt =
      ((qs - pt) * (qs - pt) + (ps + qt) * (ps + qt)) + 2 * (qs * pt - ps * qt) ∧
    ((1 : Int) * 1 + 0 * 0 + 0 * 0 + (-1) * (-1) = 2 ∧ (1 : Int) * (-1) - 0 * 0 = -1) := by
  refine ⟨?_, ?_, by decide⟩
  · have hTwo : u - (-u) = 2 * u := by omega
    rw [hTwo]
    calc (2 * u) * (2 * u)
      _ = 2 * (u * (2 * u)) := Int.mul_assoc 2 u (2 * u)
      _ = 2 * (2 * (u * u)) := by rw [← Int.mul_assoc u 2 u, Int.mul_comm u 2, Int.mul_assoc 2 u u]
      _ = 4 * (u * u) := by rw [← Int.mul_assoc 2 2 (u * u)]; rfl
  · have h1 : (qs - pt) * (qs - pt) = qs * qs - 2 * (qs * pt) + pt * pt := by
      calc (qs - pt) * (qs - pt)
        _ = qs * (qs - pt) - pt * (qs - pt) := Int.sub_mul qs pt (qs - pt)
        _ = (qs * qs - qs * pt) - (pt * qs - pt * pt) := by rw [Int.mul_sub, Int.mul_sub]
        _ = qs * qs - 2 * (qs * pt) + pt * pt := by rw [Int.mul_comm pt qs]; omega
    have h2 : (ps + qt) * (ps + qt) = ps * ps + 2 * (ps * qt) + qt * qt := by
      calc (ps + qt) * (ps + qt)
        _ = ps * (ps + qt) + qt * (ps + qt) := Int.add_mul ps qt (ps + qt)
        _ = (ps * ps + ps * qt) + (qt * ps + qt * qt) := by rw [Int.mul_add, Int.mul_add]
        _ = ps * ps + 2 * (ps * qt) + qt * qt := by rw [Int.mul_comm qt ps]; omega
    rw [h1, h2]
    omega

/-! ## 2. Orthogonal/Unitary Norm Identity & Radial Fourier Orbit Symmetrization -/

theorem hermitian_norm_sq_radial_orbit_average_and_indefinite_shell_failure
    (c s x y a b d : Int) :
    (c * x - s * y) * (c * x - s * y) + (s * x + c * y) * (s * x + c * y) =
      (c * c + s * s) * (x * x + y * y) ∧
    ((a * x * x + 2 * b * x * y + d * y * y) + (a * x * x - 2 * b * x * y + d * y * y) +
     (a * y * y + 2 * b * y * x + d * x * x) + (a * y * y - 2 * b * y * x + d * x * x) =
       2 * (a + d) * (x * x + y * y)) ∧
    (2 * ((-1 : Int) + 0) * (1 * 1 + 0 * 0) = -2) := by
  refine ⟨?_, ?_, by decide⟩
  · have hL1 : (c * x - s * y) * (c * x - s * y) =
        c * c * (x * x) - 2 * (c * s * (x * y)) + s * s * (y * y) := by
      calc (c * x - s * y) * (c * x - s * y)
        _ = (c * x) * (c * x) - ((c * x) * (s * y) + (s * y) * (c * x)) + (s * y) * (s * y) := by
              rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
              omega
        _ = c * c * (x * x) - 2 * (c * s * (x * y)) + s * s * (y * y) := by
              have q1 : (c * x) * (c * x) = c * c * (x * x) := by
                rw [Int.mul_assoc c x (c * x), ← Int.mul_assoc x c x, Int.mul_comm x c, Int.mul_assoc c x x, ← Int.mul_assoc c c (x * x)]
              have q2 : (c * x) * (s * y) = c * s * (x * y) := by
                rw [Int.mul_assoc c x (s * y), ← Int.mul_assoc x s y, Int.mul_comm x s, Int.mul_assoc s x y, ← Int.mul_assoc c s (x * y)]
              have q3 : (s * y) * (c * x) = c * s * (x * y) := by
                rw [Int.mul_comm (s * y) (c * x), q2]
              have q4 : (s * y) * (s * y) = s * s * (y * y) := by
                rw [Int.mul_assoc s y (s * y), ← Int.mul_assoc y s y, Int.mul_comm y s, Int.mul_assoc s y y, ← Int.mul_assoc s s (y * y)]
              rw [q1, q2, q3, q4]
              omega
    have hL2 : (s * x + c * y) * (s * x + c * y) =
        s * s * (x * x) + 2 * (c * s * (x * y)) + c * c * (y * y) := by
      calc (s * x + c * y) * (s * x + c * y)
        _ = (s * x) * (s * x) + ((s * x) * (c * y) + (c * y) * (s * x)) + (c * y) * (c * y) := by
              rw [Int.add_mul, Int.mul_add, Int.mul_add]
              omega
        _ = s * s * (x * x) + 2 * (c * s * (x * y)) + c * c * (y * y) := by
              have r1 : (s * x) * (s * x) = s * s * (x * x) := by
                rw [Int.mul_assoc s x (s * x), ← Int.mul_assoc x s x, Int.mul_comm x s, Int.mul_assoc s x x, ← Int.mul_assoc s s (x * x)]
              have r2 : (s * x) * (c * y) = c * s * (x * y) := by
                rw [Int.mul_assoc s x (c * y), ← Int.mul_assoc x c y, Int.mul_comm x c, Int.mul_assoc c x y, ← Int.mul_assoc s c (x * y), Int.mul_comm s c]
              have r3 : (c * y) * (s * x) = c * s * (x * y) := by
                rw [Int.mul_comm (c * y) (s * x), r2]
              have r4 : (c * y) * (c * y) = c * c * (y * y) := by
                rw [Int.mul_assoc c y (c * y), ← Int.mul_assoc y c y, Int.mul_comm y c, Int.mul_assoc c y y, ← Int.mul_assoc c c (y * y)]
              rw [r1, r2, r3, r4]
              omega
    have hRHS : (c * c + s * s) * (x * x + y * y) =
        c * c * (x * x) + s * s * (x * x) + c * c * (y * y) + s * s * (y * y) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
      omega
    rw [hL1, hL2, hRHS]
    omega
  · have p1 : a * x * x = a * (x * x) := Int.mul_assoc a x x
    have p2 : d * y * y = d * (y * y) := Int.mul_assoc d y y
    have p3 : a * y * y = a * (y * y) := Int.mul_assoc a y y
    have p4 : d * x * x = d * (x * x) := Int.mul_assoc d x x
    rw [p1, p2, p3, p4]
    have hR : 2 * (a + d) * (x * x + y * y) =
        2 * (a * (x * x) + d * (x * x) + a * (y * y) + d * (y * y)) := by
      rw [Int.mul_assoc 2 (a + d) (x * x + y * y), Int.mul_add (a + d), Int.add_mul a d (x * x), Int.add_mul a d (y * y)]
      omega
    rw [hR]
    omega

/-! ## 3. Symmetric-Gradient Strain–Vorticity Split vs. Korn Infinitesimal Rotation -/

theorem symmetric_gradient_trace_frobenius_and_korn_rotation_failure (a b c d : Int) :
    (2 * a + 2 * d = 2 * (a + d)) ∧
    ((2 * a) * (2 * a) + (b + c) * (b + c) + (c + b) * (c + b) + (2 * d) * (2 * d)) +
      ((b - c) * (b - c) + (c - b) * (c - b)) =
        4 * (a * a + b * b + c * c + d * d) ∧
    (((2 * (0 : Int)) * (2 * 0) + ((-1 : Int) + 1) * (-1 + 1) + (1 + (-1)) * (1 + (-1)) + (2 * 0) * (2 * 0) = 0) ∧
     ((0 : Int) * 0 + (-1) * (-1) + 1 * 1 + 0 * 0 = 2)) := by
  refine ⟨by omega, ?_, by decide⟩
  have h2a : (2 * a) * (2 * a) = 4 * (a * a) := by
    calc (2 * a) * (2 * a)
      _ = 2 * (a * (2 * a)) := Int.mul_assoc 2 a (2 * a)
      _ = 2 * (2 * (a * a)) := by rw [← Int.mul_assoc a 2 a, Int.mul_comm a 2, Int.mul_assoc 2 a a]
      _ = 4 * (a * a) := by rw [← Int.mul_assoc 2 2 (a * a)]; rfl
  have h2d : (2 * d) * (2 * d) = 4 * (d * d) := by
    calc (2 * d) * (2 * d)
      _ = 2 * (d * (2 * d)) := Int.mul_assoc 2 d (2 * d)
      _ = 2 * (2 * (d * d)) := by rw [← Int.mul_assoc d 2 d, Int.mul_comm d 2, Int.mul_assoc 2 d d]
      _ = 4 * (d * d) := by rw [← Int.mul_assoc 2 2 (d * d)]; rfl
  have hPara : (b + c) * (b + c) + (b - c) * (b - c) = 2 * (b * b + c * c) := by
    calc (b + c) * (b + c) + (b - c) * (b - c)
      _ = (b * (b + c) + c * (b + c)) + (b * (b - c) - c * (b - c)) := by rw [Int.add_mul, Int.sub_mul]
      _ = (b * b + b * c + (c * b + c * c)) + (b * b - b * c - (c * b - c * c)) := by
            rw [Int.mul_add, Int.mul_add, Int.mul_sub, Int.mul_sub]
      _ = 2 * (b * b + c * c) := by rw [Int.mul_comm c b]; omega
  have hComm : c + b = b + c := Int.add_comm c b
  have hSub : (c - b) * (c - b) = (b - c) * (b - c) := by
    have hNeg : c - b = -(b - c) := by omega
    rw [hNeg, Int.neg_mul_neg]
  rw [h2a, h2d, hComm, hSub]
  omega

/-! ## 4. Vandermonde Moment Determinacy vs. Four-Point Stieltjes Collision -/

theorem moment_determinacy_vandermonde_and_four_point_stieltjes_collision
    (pm1 p0 pp1 : Int) :
    (let m0 := pm1 + p0 + pp1
     let m1 := -pm1 + pp1
     let m2 := pm1 + pp1
     2 * pm1 = m2 - m1 ∧ p0 = m0 - m2 ∧ 2 * pp1 = m2 + m1) ∧
    ((1 + 0 + 3 + 0 = 0 + 3 + 0 + 1) ∧
     (1 * 0 + 0 * 1 + 3 * 2 + 0 * 3 = 0 * 0 + 3 * 1 + 0 * 2 + 1 * 3) ∧
     (1 * 0 + 0 * 1 + 3 * 4 + 0 * 9 = 0 * 0 + 3 * 1 + 0 * 4 + 1 * 9) ∧
     (1 * 0 + 0 * 1 + 3 * 8 + 0 * 27 = 24 ∧ 0 * 0 + 3 * 1 + 0 * 8 + 1 * 27 = 30)) := by
  refine ⟨by dsimp only; omega, by decide⟩

end CommonGround.Verification.TheoremAtlasFloerCotangentActionRadialFourierKornAndMomentDeterminacyBridge
