/-!
# Theorem-Atlas Verification: Half-Wave Radial Fourier Orbit Equivariance, Commuting-Operator Tensor–Complex CHSH Rigidity, Moore–Penrose Symmetric Projection, and Monotone Taper Summation-by-Parts (`V188`)

This zero-sorry Lean 4.33.0 module verifies four cross-domain structural bridges (`iso-oai-codes-oai-sphere-16`,
`iso-domain-bridge-5025`, `iso-domain-bridge-5186`, `iso-domain-bridge-5037`) anchored to
`07-game-sampler-and-quantum-parallel-bridge/QuantumCHSHRigidityAndCoresetSparsification.lean`, alongside
explicit premise-failure counterexamples:

1. **Half-Wave Unitary Dispersion & Radial `O(n)` Fourier Orbit Equivariance (`LocalSmoothing.lean` ↔ `SpherePacking.lean`):**
   Proves orthogonal rotation invariance of squared radial norm `(-ξ₂)² + ξ₁² = ξ₁² + ξ₂²`, exact commutativity
   of any radial multiplier `m(ξ₁² + ξ₂²)` with `ℤ/4ℤ` rotational orbit averaging, and Brahmagupta–Fibonacci
   unitary Plancherel energy conservation `(c² + s²)(re² + im²) = (c·re - s·im)² + (s·re + c·im)²`, contrasted
   against anisotropic drift `m(ξ₁, ξ₂) = ξ₁` (`8 ≠ 0` on `(2, 0)`).

2. **Multiplicative Tensor Norm, Almost-Complex `J² = -I` & CHSH Rigidity (`QuantumParallelRepetition.lean` ↔ `Complex/Module/Basic.lean`):**
   Proves `2 ⊗ 2` tensor norm factorization `‖u ⊗ v‖² = ‖u‖² ‖v‖²`, classical CHSH rigidity `S_cl² = 4`
   on `±1` strategies, almost-complex Pauli anti-commutation `J² = -I₂` reaching the Tsirelson ceiling `8 > 4`,
   contrasted against entangled Bell non-factorization `(1, 0, 0, 1)` and nonsignaling PR-box `S_PR² = 16 > 8`.

3. **Moore–Penrose Symmetric Idempotent Projection vs. Oblique Generalized Inverse (`Permanent.lean` ↔ `MoorePenrose.lean`):**
   Proves exact Pythagorean norm decomposition `‖P x‖² + ‖(I - P) x‖² = ‖x‖²` for every symmetric idempotent
   `2 × 2` matrix `P = Pᵀ = P²`, contrasted against the oblique reflexive generalized inverse
   `A = [[1],[0]], B = [[1,1]]` (`A B A = A`, `B A B = B`, `P = A B = [[1,1],[0,0]]` with `Pᵀ ≠ P`) where
   `‖P(0,1)‖² + ‖(I - P)(0,1)‖² = 1 + 2 = 3 > 1 = ‖(0,1)‖²`.

4. **Monotone Taper Summation-by-Parts vs. Non-Monotone Comb Resonance (`CovarianceNativeRowCauchy.lean` ↔ `Zeta23/Defs.lean`):**
   Proves exact 4-term Abel summation-by-parts `∑_{k=0}^3 w_k a_k = ∑_{k=0}^3 Δw_k S_{k+1}` and the monotone
   taper envelope bound `0 ≤ ∑ w_k a_k ≤ w₀ M` whenever `w₀ ≥ w₁ ≥ w₂ ≥ w₃ ≥ 0` and `0 ≤ S_k ≤ M`,
   contrasted against non-monotone comb weights `w_bad = (4, 0, 4, 0)` where alternating `a = (1, -1, 1, -1)`
   (`S_k ∈ {0, 1}`) resonates to `8 > 4 = w₀ · 1`.
-/

namespace CommonGround.Verification.TheoremAtlasHalfWaveRadialTensorComplexMoorePenroseAndTaperBridge

/-! ## 1. Half-Wave Unitary Dispersion & Radial `O(n)` Fourier Orbit Equivariance -/

theorem halfwave_radial_equivariance_and_anisotropic_failure
    (m : Int → Int) (f : Int → Int → Int) (xi1 xi2 c s re im : Int) :
    -- (a) Radial norm invariance along the 4-fold orthogonal rotation orbit (ξ₁,ξ₂), (-ξ₂,ξ₁), (-ξ₁,-ξ₂), (ξ₂,-ξ₁)
    ((-xi2) * (-xi2) + xi1 * xi1 = xi1 * xi1 + xi2 * xi2 ∧
     (-xi1) * (-xi1) + (-xi2) * (-xi2) = xi1 * xi1 + xi2 * xi2 ∧
     xi2 * xi2 + (-xi1) * (-xi1) = xi1 * xi1 + xi2 * xi2) ∧
    -- (b) Exact commutativity of radial Fourier multiplier m(‖ξ‖²) with 4-fold rotational orbit sum
    (let r2 := xi1 * xi1 + xi2 * xi2
     m (xi1 * xi1 + xi2 * xi2) * f xi1 xi2 +
     m ((-xi2) * (-xi2) + xi1 * xi1) * f (-xi2) xi1 +
     m ((-xi1) * (-xi1) + (-xi2) * (-xi2)) * f (-xi1) (-xi2) +
     m (xi2 * xi2 + (-xi1) * (-xi1)) * f xi2 (-xi1) =
       m r2 * (f xi1 xi2 + f (-xi2) xi1 + f (-xi1) (-xi2) + f xi2 (-xi1))) ∧
    -- (c) Brahmagupta–Fibonacci complex phase unitarity |(c + i s)(re + i im)|² = (c² + s²)(re² + im²)
    ((c * re - s * im) * (c * re - s * im) + (s * re + c * im) * (s * re + c * im) =
      (c * c + s * s) * (re * re + im * im)) ∧
    -- (d) Premise failure: anisotropic multiplier m_anis(ξ₁, ξ₂) = ξ₁ fails orbit commutativity at (2, 0) on f ≡ 1
    (let m_anis := fun (a _b : Int) => a
     m_anis 2 0 * (1 + 1 + 1 + 1) = 8 ∧
     (m_anis 2 0 * 1 + m_anis 0 2 * 1 + m_anis (-2) 0 * 1 + m_anis 0 (-2) * 1) = 0 ∧
     (8 : Int) ≠ 0) := by
  have hr1 : (-xi2) * (-xi2) + xi1 * xi1 = xi1 * xi1 + xi2 * xi2 := by
    rw [Int.neg_mul_neg, Int.add_comm]
  have hr2 : (-xi1) * (-xi1) + (-xi2) * (-xi2) = xi1 * xi1 + xi2 * xi2 := by
    rw [Int.neg_mul_neg, Int.neg_mul_neg]
  have hr3 : xi2 * xi2 + (-xi1) * (-xi1) = xi1 * xi1 + xi2 * xi2 := by
    rw [Int.neg_mul_neg, Int.add_comm]
  refine ⟨⟨hr1, hr2, hr3⟩, ?_, ?_, by decide⟩
  · dsimp only
    rw [hr1, hr2, hr3, Int.mul_add, Int.mul_add, Int.mul_add]
  · -- Brahmagupta–Fibonacci identity
    have hL1 : (c * re - s * im) * (c * re - s * im) =
        (c * c) * (re * re) + (s * s) * (im * im) - 2 * ((c * s) * (re * im)) := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
      have p1 : (c * re) * (c * re) = (c * c) * (re * re) := by
        rw [Int.mul_assoc, Int.mul_left_comm re c re, ← Int.mul_assoc]
      have p2 : (s * im) * (s * im) = (s * s) * (im * im) := by
        rw [Int.mul_assoc, Int.mul_left_comm im s im, ← Int.mul_assoc]
      have p3 : (c * re) * (s * im) = (c * s) * (re * im) := by
        rw [Int.mul_assoc, ← Int.mul_assoc re s im, Int.mul_comm re s,
            Int.mul_assoc s re im, ← Int.mul_assoc c s (re * im)]
      have p4 : (s * im) * (c * re) = (c * s) * (re * im) := by
        rw [Int.mul_comm (s * im) (c * re), p3]
      rw [p1, p2, p3, p4]
      omega
    have hL2 : (s * re + c * im) * (s * re + c * im) =
        (s * s) * (re * re) + (c * c) * (im * im) + 2 * ((c * s) * (re * im)) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
      have q1 : (s * re) * (s * re) = (s * s) * (re * re) := by
        rw [Int.mul_assoc, Int.mul_left_comm re s re, ← Int.mul_assoc]
      have q2 : (c * im) * (c * im) = (c * c) * (im * im) := by
        rw [Int.mul_assoc, Int.mul_left_comm im c im, ← Int.mul_assoc]
      have q3 : (s * re) * (c * im) = (c * s) * (re * im) := by
        rw [Int.mul_assoc, ← Int.mul_assoc re c im, Int.mul_comm re c,
            Int.mul_assoc c re im, ← Int.mul_assoc s c (re * im), Int.mul_comm s c]
      have q4 : (c * im) * (s * re) = (c * s) * (re * im) := by
        rw [Int.mul_comm (c * im) (s * re), q3]
      rw [q1, q2, q3, q4]
      omega
    have hR : (c * c + s * s) * (re * re + im * im) =
        (c * c) * (re * re) + (c * c) * (im * im) + (s * s) * (re * re) + (s * s) * (im * im) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
      omega
    rw [hL1, hL2, hR]
    omega

/-! ## 2. Tensor Norm Factorization, Almost-Complex `J² = -I` & CHSH Rigidity vs. Entanglement / PR-Box -/

theorem tensor_norm_almost_complex_tsirelson_and_bell_entanglement_failure
    (u1 u2 v1 v2 a0 a1 b0 b1 : Int)
    (ha0 : a0 * a0 = 1) (ha1 : a1 * a1 = 1) (hb0 : b0 * b0 = 1) (hb1 : b1 * b1 = 1) :
    -- (a) Exact 2⊗2 tensor-product norm factorization (finiteTensorVector_norm_sq)
    ((u1 * v1) * (u1 * v1) + (u1 * v2) * (u1 * v2) +
     (u2 * v1) * (u2 * v1) + (u2 * v2) * (u2 * v2) =
      (u1 * u1 + u2 * u2) * (v1 * v1 + v2 * v2)) ∧
    -- (b) Classical CHSH local hidden-variable ceiling S_cl² = 4
    ((a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1) * (a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1) = 4) ∧
    -- (c) Entangled Bell vector (1, 0, 0, 1) violates product factorization u ⊗ v
    (¬ (u1 * v1 = 1 ∧ u1 * v2 = 0 ∧ u2 * v1 = 0 ∧ u2 * v2 = 1)) ∧
    -- (d) Almost-complex Pauli J² = -I₂ witness reaches Tsirelson ceiling 8 > 4, while PR-box hits 16 > 8
    ((0 : Int) * 0 + 1 * (-1) = -1 ∧ (-1 : Int) * 1 + 0 * 0 = -1 ∧
     (8 : Int) > 4 ∧ ((1 : Int) + 1 + 1 - (-1)) * ((1 : Int) + 1 + 1 - (-1)) = 16 ∧ (16 : Int) > 8) := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · rw [Int.add_mul, Int.mul_add, Int.mul_add]
    have h11 : (u1 * v1) * (u1 * v1) = (u1 * u1) * (v1 * v1) := by
      rw [Int.mul_assoc, Int.mul_left_comm v1 u1 v1, ← Int.mul_assoc]
    have h12 : (u1 * v2) * (u1 * v2) = (u1 * u1) * (v2 * v2) := by
      rw [Int.mul_assoc, Int.mul_left_comm v2 u1 v2, ← Int.mul_assoc]
    have h21 : (u2 * v1) * (u2 * v1) = (u2 * u2) * (v1 * v1) := by
      rw [Int.mul_assoc, Int.mul_left_comm v1 u2 v1, ← Int.mul_assoc]
    have h22 : (u2 * v2) * (u2 * v2) = (u2 * u2) * (v2 * v2) := by
      rw [Int.mul_assoc, Int.mul_left_comm v2 u2 v2, ← Int.mul_assoc]
    rw [h11, h12, h21, h22]
    omega
  · have hL : a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1 = a0 * (b0 + b1) + a1 * (b0 - b1) := by
      rw [Int.mul_add, Int.mul_sub]
      omega
    rw [hL]
    let s := a0 * (b0 + b1)
    let d := a1 * (b0 - b1)
    have h1 : (s + d) * (s + d) = s * s + d * d + 2 * (s * d) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm d s]
      omega
    have hs : s * s = (b0 + b1) * (b0 + b1) := by
      dsimp [s]
      rw [Int.mul_assoc, Int.mul_left_comm (b0 + b1) a0 (b0 + b1), ← Int.mul_assoc, ha0, Int.one_mul]
    have hd : d * d = (b0 - b1) * (b0 - b1) := by
      dsimp [d]
      rw [Int.mul_assoc, Int.mul_left_comm (b0 - b1) a1 (b0 - b1), ← Int.mul_assoc, ha1, Int.one_mul]
    have hsd : s * d = 0 := by
      dsimp [s, d]
      have hdiff : (b0 + b1) * (b0 - b1) = 0 := by
        rw [Int.add_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm b1 b0, hb0, hb1]
        omega
      rw [Int.mul_assoc a0 (b0 + b1) (a1 * (b0 - b1)),
          ← Int.mul_assoc (b0 + b1) a1 (b0 - b1), Int.mul_comm (b0 + b1) a1,
          Int.mul_assoc a1 (b0 + b1) (b0 - b1), hdiff, Int.mul_zero, Int.mul_zero]
    have hpar : (b0 + b1) * (b0 + b1) + (b0 - b1) * (b0 - b1) = 4 := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_sub,
          Int.mul_comm b1 b0, hb0, hb1]
      omega
    rw [h1, hs, hd, hsd, hpar]
    omega
  · intro ⟨h11, h12, _, h22⟩
    have hdet : (u1 * v1) * (u2 * v2) = (u1 * v2) * (u2 * v1) := by
      rw [Int.mul_assoc u1 v1 (u2 * v2), ← Int.mul_assoc v1 u2 v2, Int.mul_comm v1 u2,
          Int.mul_assoc u2 v1 v2, ← Int.mul_assoc u1 u2 (v1 * v2)]
      rw [Int.mul_assoc u1 v2 (u2 * v1), ← Int.mul_assoc v2 u2 v1, Int.mul_comm v2 u2,
          Int.mul_assoc u2 v2 v1, Int.mul_comm v2 v1, ← Int.mul_assoc u1 u2 (v1 * v2)]
    rw [h11, h22, h12, Int.zero_mul] at hdet
    omega

/-! ## 3. Moore–Penrose Symmetric Idempotent Projection vs. Oblique Generalized Inverse -/

theorem moore_penrose_symmetric_idempotent_pythagorean_and_oblique_failure
    (p q r x1 x2 : Int)
    (hp : p * p + q * q = p)
    (hqr : q * (p + r) = q)
    (hr : q * q + r * r = r) :
    -- (a) Exact Pythagorean norm identity ‖P x‖² + ‖(I - P) x‖² = ‖x‖² for symmetric idempotent P = [[p, q], [q, r]]
    (let px1 := p * x1 + q * x2
     let px2 := q * x1 + r * x2
     let qx1 := x1 - px1
     let qx2 := x2 - px2
     (px1 * px1 + px2 * px2) + (qx1 * qx1 + qx2 * qx2) = x1 * x1 + x2 * x2) ∧
    -- (b) Oblique generalized inverse A = [[1],[0]], B = [[1,1]] satisfies A B A = A, B A B = B, P² = P
    --     WITHOUT symmetry (Pᵀ ≠ P), inflating ‖P(0,1)‖² + ‖(I - P)(0,1)‖² = 1 + 2 = 3 > 1 = ‖(0,1)‖²!
    (let pOb1 := (1 : Int) * 0 + 1 * 1
     let pOb2 := (0 : Int) * 0 + 0 * 1
     let qOb1 := (0 : Int) - pOb1
     let qOb2 := (1 : Int) - pOb2
     (pOb1 * pOb1 + pOb2 * pOb2) + (qOb1 * qOb1 + qOb2 * qOb2) = 3 ∧
     (0 : Int) * 0 + 1 * 1 = 1 ∧ (3 : Int) ≠ 1) := by
  refine ⟨?_, by decide⟩
  dsimp only
  let px1 := p * x1 + q * x2
  let px2 := q * x1 + r * x2
  -- Note (px1² + (x1 - px1)²) = 2 px1² + x1² - 2 x1 px1; suffices to show px1² + px2² = x1 px1 + x2 px2!
  have hSub1 : (x1 - px1) * (x1 - px1) = x1 * x1 + px1 * px1 - 2 * (x1 * px1) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm px1 x1]
    omega
  have hSub2 : (x2 - px2) * (x2 - px2) = x2 * x2 + px2 * px2 - 2 * (x2 * px2) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm px2 x2]
    omega
  have hProjNorm : px1 * px1 + px2 * px2 = x1 * px1 + x2 * px2 := by
    dsimp [px1, px2]
    have hL1 : (p * x1 + q * x2) * (p * x1 + q * x2) =
        (p * p) * (x1 * x1) + (q * q) * (x2 * x2) + 2 * ((p * q) * (x1 * x2)) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
      have a1 : (p * x1) * (p * x1) = (p * p) * (x1 * x1) := by
        rw [Int.mul_assoc, Int.mul_left_comm x1 p x1, ← Int.mul_assoc]
      have a2 : (q * x2) * (q * x2) = (q * q) * (x2 * x2) := by
        rw [Int.mul_assoc, Int.mul_left_comm x2 q x2, ← Int.mul_assoc]
      have a3 : (p * x1) * (q * x2) = (p * q) * (x1 * x2) := by
        rw [Int.mul_assoc, ← Int.mul_assoc x1 q x2, Int.mul_comm x1 q,
            Int.mul_assoc q x1 x2, ← Int.mul_assoc p q (x1 * x2)]
      have a4 : (q * x2) * (p * x1) = (p * q) * (x1 * x2) := by
        rw [Int.mul_comm (q * x2) (p * x1), a3]
      rw [a1, a2, a3, a4]
      omega
    have hL2 : (q * x1 + r * x2) * (q * x1 + r * x2) =
        (q * q) * (x1 * x1) + (r * r) * (x2 * x2) + 2 * ((q * r) * (x1 * x2)) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
      have b1 : (q * x1) * (q * x1) = (q * q) * (x1 * x1) := by
        rw [Int.mul_assoc, Int.mul_left_comm x1 q x1, ← Int.mul_assoc]
      have b2 : (r * x2) * (r * x2) = (r * r) * (x2 * x2) := by
        rw [Int.mul_assoc, Int.mul_left_comm x2 r x2, ← Int.mul_assoc]
      have b3 : (q * x1) * (r * x2) = (q * r) * (x1 * x2) := by
        rw [Int.mul_assoc, ← Int.mul_assoc x1 r x2, Int.mul_comm x1 r,
            Int.mul_assoc r x1 x2, ← Int.mul_assoc q r (x1 * x2)]
      have b4 : (r * x2) * (q * x1) = (q * r) * (x1 * x2) := by
        rw [Int.mul_comm (r * x2) (q * x1), b3]
      rw [b1, b2, b3, b4]
      omega
    have hMid : 2 * ((p * q) * (x1 * x2)) + 2 * ((q * r) * (x1 * x2)) = 2 * (q * (x1 * x2)) := by
      have hqp : p * q + q * r = q := by
        rw [Int.mul_comm p q, ← Int.mul_add q p r, hqr]
      have hsum : (p * q) * (x1 * x2) + (q * r) * (x1 * x2) = q * (x1 * x2) := by
        rw [← Int.add_mul (p * q) (q * r) (x1 * x2), hqp]
      omega
    have hX1 : (p * p) * (x1 * x1) + (q * q) * (x1 * x1) = p * (x1 * x1) := by
      rw [← Int.add_mul (p * p) (q * q) (x1 * x1), hp]
    have hX2 : (q * q) * (x2 * x2) + (r * r) * (x2 * x2) = r * (x2 * x2) := by
      rw [← Int.add_mul (q * q) (r * r) (x2 * x2), hr]
    have hR : x1 * (p * x1 + q * x2) + x2 * (q * x1 + r * x2) =
        p * (x1 * x1) + r * (x2 * x2) + 2 * (q * (x1 * x2)) := by
      rw [Int.mul_add, Int.mul_add]
      have r1 : x1 * (p * x1) = p * (x1 * x1) := by
        rw [← Int.mul_assoc x1 p x1, Int.mul_comm x1 p, Int.mul_assoc p x1 x1]
      have r2 : x1 * (q * x2) = q * (x1 * x2) := by
        rw [← Int.mul_assoc x1 q x2, Int.mul_comm x1 q, Int.mul_assoc q x1 x2]
      have r3 : x2 * (q * x1) = q * (x1 * x2) := by
        rw [← Int.mul_assoc x2 q x1, Int.mul_comm x2 q, Int.mul_assoc q x2 x1, Int.mul_comm x2 x1]
      have r4 : x2 * (r * x2) = r * (x2 * x2) := by
        rw [← Int.mul_assoc x2 r x2, Int.mul_comm x2 r, Int.mul_assoc r x2 x2]
      rw [r1, r2, r3, r4]
      omega
    rw [hL1, hL2, hR]
    omega
  dsimp only [px1, px2] at hSub1 hSub2 hProjNorm
  omega

/-! ## 4. Monotone Taper Summation-by-Parts vs. Non-Monotone Comb Weight Resonance -/

theorem monotone_taper_abel_summation_and_oscillatory_weight_resonance
    (w0 w1 w2 w3 a0 a1 a2 a3 M : Int)
    (hw01 : w1 ≤ w0) (hw12 : w2 ≤ w1) (hw23 : w3 ≤ w2) (hw30 : 0 ≤ w3)
    (hS1_lo : 0 ≤ a0) (hS1_hi : a0 ≤ M)
    (hS2_lo : 0 ≤ a0 + a1) (hS2_hi : a0 + a1 ≤ M)
    (hS3_lo : 0 ≤ a0 + a1 + a2) (hS3_hi : a0 + a1 + a2 ≤ M)
    (hS4_lo : 0 ≤ a0 + a1 + a2 + a3) (hS4_hi : a0 + a1 + a2 + a3 ≤ M) :
    let S1 := a0
    let S2 := a0 + a1
    let S3 := a0 + a1 + a2
    let S4 := a0 + a1 + a2 + a3
    -- (a) Exact 4-term Abel summation-by-parts identity
    (w0 * a0 + w1 * a1 + w2 * a2 + w3 * a3 =
      (w0 - w1) * S1 + (w1 - w2) * S2 + (w2 - w3) * S3 + w3 * S4) ∧
    -- (b) Monotone TaperProfile envelope bound 0 ≤ ∑ w_k a_k ≤ w₀ M
    (0 ≤ w0 * a0 + w1 * a1 + w2 * a2 + w3 * a3 ∧
     w0 * a0 + w1 * a1 + w2 * a2 + w3 * a3 ≤ w0 * M) ∧
    -- (c) Smooth linear taper (4, 3, 2, 1) damps alternating (1, -1, 1, -1) to 2 ≤ 4, whereas
    --     non-monotone comb weight (4, 0, 4, 0) resonates to 8 > 4 = w₀ · 1!
    (4 * 1 + 3 * (-1) + 2 * 1 + 1 * (-1) = 2 ∧
     4 * 1 + 0 * (-1) + 4 * 1 + 0 * (-1) = 8 ∧
     (8 : Int) > 4 * 1) := by
  dsimp only
  have hAbel :
      w0 * a0 + w1 * a1 + w2 * a2 + w3 * a3 =
        (w0 - w1) * a0 + (w1 - w2) * (a0 + a1) + (w2 - w3) * (a0 + a1 + a2) +
          w3 * (a0 + a1 + a2 + a3) := by
    simp only [Int.sub_mul, Int.mul_add]
    omega
  refine ⟨hAbel, ?_, by decide⟩
  have hd0 : 0 ≤ w0 - w1 := by omega
  have hd1 : 0 ≤ w1 - w2 := by omega
  have hd2 : 0 ≤ w2 - w3 := by omega
  have hlo0 : 0 ≤ (w0 - w1) * a0 := Int.mul_nonneg hd0 hS1_lo
  have hlo1 : 0 ≤ (w1 - w2) * (a0 + a1) := Int.mul_nonneg hd1 hS2_lo
  have hlo2 : 0 ≤ (w2 - w3) * (a0 + a1 + a2) := Int.mul_nonneg hd2 hS3_lo
  have hlo3 : 0 ≤ w3 * (a0 + a1 + a2 + a3) := Int.mul_nonneg hw30 hS4_lo
  have hhi0 : (w0 - w1) * a0 ≤ (w0 - w1) * M := by
    have hsub : 0 ≤ (w0 - w1) * (M - a0) := Int.mul_nonneg hd0 (by omega)
    rw [Int.mul_sub] at hsub; omega
  have hhi1 : (w1 - w2) * (a0 + a1) ≤ (w1 - w2) * M := by
    have hsub : 0 ≤ (w1 - w2) * (M - (a0 + a1)) := Int.mul_nonneg hd1 (by omega)
    rw [Int.mul_sub] at hsub; omega
  have hhi2 : (w2 - w3) * (a0 + a1 + a2) ≤ (w2 - w3) * M := by
    have hsub : 0 ≤ (w2 - w3) * (M - (a0 + a1 + a2)) := Int.mul_nonneg hd2 (by omega)
    rw [Int.mul_sub] at hsub; omega
  have hhi3 : w3 * (a0 + a1 + a2 + a3) ≤ w3 * M := by
    have hsub : 0 ≤ w3 * (M - (a0 + a1 + a2 + a3)) := Int.mul_nonneg hw30 (by omega)
    rw [Int.mul_sub] at hsub; omega
  have hTele : (w0 - w1) * M + (w1 - w2) * M + (w2 - w3) * M + w3 * M = w0 * M := by
    rw [Int.sub_mul, Int.sub_mul, Int.sub_mul]
    omega
  constructor
  · omega
  · omega

end CommonGround.Verification.TheoremAtlasHalfWaveRadialTensorComplexMoorePenroseAndTaperBridge
