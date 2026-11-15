/-
  SoftmaxPolynomialRankRoPESymplecticAndDeltaRuleMemoryFrontier.lean
  ------------------------------------------------------------------
  Pure-core Lean 4.33.0 frontier formalization (0 imports, 0 sorry) unifying
  Folders 02, 05, 06, and 08 around four foundational operator-algebraic laws
  of modern sequence & transformer architectures:

  1. Linear-Attention Rank-2 Syzygy Bottleneck vs. Degree-2 Polynomial / Taylor-Softmax
     Kernel Full-Rank Separation (`det G₂ = 135 > 0` & Schur–Hadamard Rank Squaring).
  2. Rotary Position Embedding (`RoPE`) Planar `SO(2)` Group Homomorphism, Symplectic
     Norm/Area Preservation & Exact Relative-Position Score Invariance vs. Modular
     Wavelength Aliasing (`J⁴ = I₂`) and Non-Orthogonal Shear Drift (`SL₂` without `SO₂`).
  3. Generalized Householder / Delta-Rule Associative Memory (`β = 1` Exact Overwrite +
     Orthogonal Subspace Preservation + Idempotent Erase vs. `β = 2` Involutive Reflection)
     vs. Naive Hebbian Crosstalk Accumulation and `β = 3` Spectral Blowup.
  4. Exponential Gibbs Margin Concentration (`B^Δ` Suppressing `D` Distractors) vs.
     Affine Linear-Attention `O(1/D)` Distractor Dilution.
-/

namespace CommonGround.Frontier.SoftmaxRoPEAndDeltaRule

/-- Exact integer squaring helper. -/
def sqInt (x : Int) : Int := x * x

/-- 2D Euclidean dot product over `Int`. -/
def dot2 (ax ay bx by_ : Int) : Int := ax * bx + ay * by_

/-- 2D symplectic determinant `det([a, b]) = ax * by - ay * bx`. -/
def det2 (ax ay bx by_ : Int) : Int := ax * by_ - ay * bx

/-- Linear-attention scalar readout `f_w(k) = ⟨w, k⟩` from a compressed 2D state vector `w`. -/
def linReadout2 (w0 w1 kx ky : Int) : Int := w0 * kx + w1 * ky

/-- Degree-2 polynomial / 2nd-order Taylor-Softmax kernel `K₂(q, k) = (1 + ⟨q, k⟩)²`. -/
def polyKernel2 (qx qy kx ky : Int) : Int :=
  sqInt (1 + dot2 qx qy kx ky)

/-- Explicit 6D feature map `φ₂(x, y) = (1, x, y, x², x*y, y²)` witnessing `K₂(q, k)` as a
    weighted positive inner product in `ℤ⁶`. -/
def poly2WeightedInner (qx qy kx ky : Int) : Int :=
  1 * 1 + 2 * (qx * kx) + 2 * (qy * ky) +
    (qx * qx) * (kx * kx) + 2 * (qx * qy) * (kx * ky) + (qy * qy) * (ky * ky)

/-- 3x3 determinant over `Int`. -/
def det3
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Int) : Int :=
  a00 * (a11 * a22 - a12 * a21) -
  a01 * (a10 * a22 - a12 * a20) +
  a02 * (a10 * a21 - a11 * a20)

theorem sqInt_nonneg (x : Int) : 0 ≤ sqInt x := by
  unfold sqInt
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have hn : x ≤ 0 := Int.le_of_lt (Int.lt_of_not_ge h)
    exact Int.mul_nonneg_of_nonpos_of_nonpos hn hn

/-!
## 1. Linear-Attention Rank Bottleneck vs. Quadratic Kernel Full-Rank Separation
-/

/-- **Theorem 1 (Linear-Attention 2D Cramer Syzygy Wall vs. Degree-2 Kernel Full-Rank Separation)**:
  1. **Universal Rank-2 Linear Syzygy**: For ANY linear memory readout `w = (w0, w1)` and ANY
     three 2D keys `k0, k1, k2`, `det(k1,k2) f(k0) - det(k0,k2) f(k1) + det(k0,k1) f(k2) = 0`.
  2. **Impossibility of Uniform or Single-Slot Lookup on 3 Keys in 2D**: On `k0 = (1,0)`,
     `k1 = (0,1)`, `k2 = (-1,-1)`, every linear-attention state satisfies
     `f(k0) + f(k1) + f(k2) = 0`, so neither `(1, 1, 1)` nor indicator `(1, 0, 0)` is realizable.
  3. **Schur–Hadamard Rank-Squaring & Exact 6D Feature Expansion**: `(a0*b0 + a1*b1)² =
     a0²*b0² + 2*(a0*a1)*(b0*b1) + a1²*b1²` and `polyKernel2 = poly2WeightedInner`.
  4. **Full-Rank Degree-2 Kernel Gram Matrix (`det G₂ = 135 > 0`)**: On the exact same 3 keys
     `k0 = (1,0), k1 = (0,1), k2 = (-1,-1)`, `G₂ = [[4,1,0],[1,4,0],[0,0,9]]` has `det G₂ = 135`
     and realizes both uniform `(45, 45, 45)` via `α = (9, 9, 5)` and single-key indicator
     `(15, 0, 0)` via `α = (4, -1, 0)`! -/
theorem linear_attention_rank_bottleneck_vs_quadratic_kernel_full_rank_separation :
    (∀ w0 w1 x0 y0 x1 y1 x2 y2 : Int,
      det2 x1 y1 x2 y2 * linReadout2 w0 w1 x0 y0 -
      det2 x0 y0 x2 y2 * linReadout2 w0 w1 x1 y1 +
      det2 x0 y0 x1 y1 * linReadout2 w0 w1 x2 y2 = 0) ∧
    (∀ w0 w1 : Int,
      linReadout2 w0 w1 1 0 + linReadout2 w0 w1 0 1 + linReadout2 w0 w1 (-1) (-1) = 0 ∧
      ¬ (linReadout2 w0 w1 1 0 = 1 ∧ linReadout2 w0 w1 0 1 = 1 ∧ linReadout2 w0 w1 (-1) (-1) = 1) ∧
      ¬ (linReadout2 w0 w1 1 0 = 1 ∧ linReadout2 w0 w1 0 1 = 0 ∧ linReadout2 w0 w1 (-1) (-1) = 0)) ∧
    (∀ qx qy kx ky : Int,
      sqInt (dot2 qx qy kx ky) =
        (qx * qx) * (kx * kx) + 2 * (qx * qy) * (kx * ky) + (qy * qy) * (ky * ky) ∧
      polyKernel2 qx qy kx ky = poly2WeightedInner qx qy kx ky) ∧
    (det3
      (polyKernel2 1 0 1 0) (polyKernel2 1 0 0 1) (polyKernel2 1 0 (-1) (-1))
      (polyKernel2 0 1 1 0) (polyKernel2 0 1 0 1) (polyKernel2 0 1 (-1) (-1))
      (polyKernel2 (-1) (-1) 1 0) (polyKernel2 (-1) (-1) 0 1) (polyKernel2 (-1) (-1) (-1) (-1)) = 135 ∧
      9 * polyKernel2 1 0 1 0 + 9 * polyKernel2 1 0 0 1 + 5 * polyKernel2 1 0 (-1) (-1) = 45 ∧
      9 * polyKernel2 0 1 1 0 + 9 * polyKernel2 0 1 0 1 + 5 * polyKernel2 0 1 (-1) (-1) = 45 ∧
      9 * polyKernel2 (-1) (-1) 1 0 + 9 * polyKernel2 (-1) (-1) 0 1 + 5 * polyKernel2 (-1) (-1) (-1) (-1) = 45 ∧
      4 * polyKernel2 1 0 1 0 + (-1) * polyKernel2 1 0 0 1 + 0 * polyKernel2 1 0 (-1) (-1) = 15 ∧
      4 * polyKernel2 0 1 1 0 + (-1) * polyKernel2 0 1 0 1 + 0 * polyKernel2 0 1 (-1) (-1) = 0 ∧
      4 * polyKernel2 (-1) (-1) 1 0 + (-1) * polyKernel2 (-1) (-1) 0 1 + 0 * polyKernel2 (-1) (-1) (-1) (-1) = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w0 w1 x0 y0 x1 y1 x2 y2
    unfold det2 linReadout2
    grind
  · intro w0 w1
    unfold linReadout2
    refine ⟨by omega, ?_, ?_⟩
    · intro h
      omega
    · intro h
      omega
  · intro qx qy kx ky
    unfold polyKernel2 poly2WeightedInner sqInt dot2
    constructor <;> grind
  · decide

/-!
## 2. RoPE Symplectic Rotation Group Law & Relative-Position Invariance vs. Aliasing & Shear Drift
-/

/-- Planar rotation-scale action `R(c, s)(x, y) = (c*x - s*y, s*x + c*y)`. -/
def ropeRotX (c s x y : Int) : Int := c * x - s * y
def ropeRotY (c s x y : Int) : Int := s * x + c * y

/-- Exact quarter-turn symplectic generator `J(x, y) = (-y, x)`. -/
def stepJ (p : Int × Int) : Int × Int := (-p.2, p.1)

/-- Iterated exact quarter-turn RoPE position embedding `J^n p`. -/
def ropeQuarterTurn : Nat → Int × Int → Int × Int
  | 0, p => p
  | n + 1, p => stepJ (ropeQuarterTurn n p)

/-- Upper-triangular `SL₂(ℤ)` shear `S(x, y) = (x + y, y)` (unit determinant `det = 1`,
    yet NOT orthogonal!). -/
def shearX (x y : Int) : Int := x + y
def shearY (_x y : Int) : Int := y

theorem stepJ_dot_invariant (p q : Int × Int) :
    dot2 (stepJ p).1 (stepJ p).2 (stepJ q).1 (stepJ q).2 = dot2 p.1 p.2 q.1 q.2 := by
  unfold stepJ dot2
  grind

theorem ropeQuarterTurn_shift_invariance (m : Nat) (d : Nat) (qx qy kx ky : Int) :
    dot2 (ropeQuarterTurn (d + m) (qx, qy)).1 (ropeQuarterTurn (d + m) (qx, qy)).2
         (ropeQuarterTurn m (kx, ky)).1 (ropeQuarterTurn m (kx, ky)).2 =
      dot2 (ropeQuarterTurn d (qx, qy)).1 (ropeQuarterTurn d (qx, qy)).2 kx ky := by
  induction m with
  | zero =>
    rfl
  | succ m ih =>
    have h1 : d + (m + 1) = (d + m) + 1 := rfl
    rw [h1]
    simp only [ropeQuarterTurn]
    rw [stepJ_dot_invariant]
    exact ih

theorem ropeQuarterTurn_period_four (n : Nat) (qx qy : Int) :
    ropeQuarterTurn (n + 4) (qx, qy) = ropeQuarterTurn n (qx, qy) := by
  have h4 : ∀ p : Int × Int, stepJ (stepJ (stepJ (stepJ p))) = p := by
    intro ⟨a, b⟩
    unfold stepJ
    simp
  exact h4 (ropeQuarterTurn n (qx, qy))

/-- **Theorem 2 (RoPE Symplectic Group Law & Relative-Position Invariance vs. Aliasing & Shear)**:
  1. **Exact `SO(2)` Group Composition**: `R(c1, s1)(R(c2, s2)(x, y)) = R(c1*c2 - s1*s2, c1*s2 + s1*c2)(x, y)`.
  2. **Brahmagupta–Fibonacci Norm & Symplectic `2`-Form Scaling**:
     `‖R(c, s) v‖₂² = (c² + s²) ‖v‖₂²` and `det(R(c, s) u, R(c, s) v) = (c² + s²) det(u, v)`.
  3. **Exact Relative-Position Attention Score Invariance**:
     `⟨J^(d + m) q, J^m k⟩ = ⟨J^d q, k⟩` depends ONLY on relative offset `d`, never absolute index `m`.
  4. **Premise Failures (Wavelength Aliasing & `SL₂ \ SO₂` Shear Drift)**:
     - Periodic RoPE wraps modulo wavelength (`J^(n + 4) q = J^n q`), causing distant position `n + 4`
       to alias `n` identically.
     - Area-preserving `SL₂(ℤ)` shear `S(x, y) = (x + y, y)` satisfies `det(S u, S v) = det(u, v)`,
       yet fails orthogonality: `‖S(0,1)‖₂² = 2 ≠ 1` and `⟨S(1,0), S(0,1)⟩ = 1 ≠ 0 = ⟨(1,0), (0,1)⟩`. -/
theorem rope_symplectic_relative_position_invariance_vs_aliasing_and_shear_drift :
    (∀ c1 s1 c2 s2 x y : Int,
      ropeRotX c1 s1 (ropeRotX c2 s2 x y) (ropeRotY c2 s2 x y) =
        ropeRotX (c1 * c2 - s1 * s2) (c1 * s2 + s1 * c2) x y ∧
      ropeRotY c1 s1 (ropeRotX c2 s2 x y) (ropeRotY c2 s2 x y) =
        ropeRotY (c1 * c2 - s1 * s2) (c1 * s2 + s1 * c2) x y) ∧
    (∀ c s ux uy vx vy : Int,
      dot2 (ropeRotX c s vx vy) (ropeRotY c s vx vy) (ropeRotX c s vx vy) (ropeRotY c s vx vy) =
        (sqInt c + sqInt s) * dot2 vx vy vx vy ∧
      det2 (ropeRotX c s ux uy) (ropeRotY c s ux uy) (ropeRotX c s vx vy) (ropeRotY c s vx vy) =
        (sqInt c + sqInt s) * det2 ux uy vx vy) ∧
    (∀ m d : Nat, ∀ qx qy kx ky : Int,
      dot2 (ropeQuarterTurn (d + m) (qx, qy)).1 (ropeQuarterTurn (d + m) (qx, qy)).2
           (ropeQuarterTurn m (kx, ky)).1 (ropeQuarterTurn m (kx, ky)).2 =
        dot2 (ropeQuarterTurn d (qx, qy)).1 (ropeQuarterTurn d (qx, qy)).2 kx ky) ∧
    ((∀ n : Nat, ∀ qx qy : Int, ropeQuarterTurn (n + 4) (qx, qy) = ropeQuarterTurn n (qx, qy)) ∧
      (∀ ux uy vx vy : Int, det2 (shearX ux uy) (shearY ux uy) (shearX vx vy) (shearY vx vy) = det2 ux uy vx vy) ∧
      dot2 (shearX 0 1) (shearY 0 1) (shearX 0 1) (shearY 0 1) = 2 ∧
      dot2 0 1 0 1 = 1 ∧
      dot2 (shearX 1 0) (shearY 1 0) (shearX 0 1) (shearY 0 1) = 1 ∧
      dot2 1 0 0 1 = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c1 s1 c2 s2 x y
    unfold ropeRotX ropeRotY
    constructor <;> grind
  · intro c s ux uy vx vy
    unfold dot2 det2 ropeRotX ropeRotY sqInt
    constructor <;> grind
  · intro m d qx qy kx ky
    exact ropeQuarterTurn_shift_invariance m d qx qy kx ky
  · refine ⟨ropeQuarterTurn_period_four, ?_, by decide, by decide, by decide, by decide⟩
    intro ux uy vx vy
    unfold det2 shearX shearY
    grind

/-!
## 3. Generalized Householder / Delta-Rule Associative Memory vs. Hebbian Crosstalk & β = 3 Blowup
-/

/-- Denominator-free Delta-Rule (`β = 1`) memory update scaled by `r = kx² + ky²`:
    `m' = r * m - ⟨m, k⟩ k + vNew * k`. -/
def deltaUpdateX (m0 m1 kx ky vNew : Int) : Int :=
  (kx * kx + ky * ky) * m0 - (m0 * kx + m1 * ky) * kx + vNew * kx

def deltaUpdateY (m0 m1 kx ky vNew : Int) : Int :=
  (kx * kx + ky * ky) * m1 - (m0 * kx + m1 * ky) * ky + vNew * ky

/-- Generalized `β`-Householder linear operator `T_β(k)(u) = ‖k‖₂² u - β ⟨k, u⟩ k`. -/
def householderBetaX (beta kx ky ux uy : Int) : Int :=
  (kx * kx + ky * ky) * ux - beta * (kx * ux + ky * uy) * kx

def householderBetaY (beta kx ky ux uy : Int) : Int :=
  (kx * kx + ky * ky) * uy - beta * (kx * ux + ky * uy) * ky

/-- Naive Hebbian (`β = 0` erase) additive state update `m_Hebb = m + vNew * k`. -/
def hebbianUpdateX (m0 kx vNew : Int) : Int := m0 + vNew * kx
def hebbianUpdateY (m1 ky vNew : Int) : Int := m1 + vNew * ky

/-- **Theorem 3 (Delta-Rule Exact Overwrite, Orthogonal Preservation & `β = 2` Householder Involution vs. Hebbian Crosstalk & `β = 3` Blowup)**:
  1. **Exact Key Overwrite (Zero Stale Value Bleed)**: Querying the updated Delta-Rule state along
     the written key `k = (kx, ky)` yields `(kx² + ky²) * vNew`, completely independent of prior memory `(m0, m1)`.
  2. **Exact Orthogonal Subspace Preservation**: For any query `u = (ux, uy)` orthogonal to `k`
     (`kx * ux + ky * uy = 0`), the Delta-Rule state preserves prior memory `(kx² + ky²) * (m0*ux + m1*uy)`.
  3. **`β = 1` Idempotent Projection vs. `β = 2` Involutive Isometric Reflection**:
     - `T₁(k)(T₁(k)(u)) = ‖k‖₂² · T₁(k)(u)` (aperiodic reset semigroup `P² = P` at unit norm),
     - `T₂(k)(T₂(k)(u)) = ‖k‖₂⁴ · u` AND `‖T₂(k)(u)‖₂² = ‖k‖₂⁴ · ‖u‖₂²` (involutive orthogonal group `H² = I`).
  4. **Premise Failures (`β = 0` Hebbian Crosstalk & `β = 3` Spectral Explosion)**:
     - Writing `vNew = -3` at `k = (1, 0)` onto prior memory `m = (5, 0)` under Hebbian linear attention
       returns `+2 ≠ -3` (stale memory `+5` corrupts the overwrite!).
     - Over-relaxed `β = 3` at `k = (1, 0), u = (1, 0)` amplifies norm squared from `1` to `4` per step. -/
theorem delta_rule_householder_exact_overwrite_vs_hebbian_crosstalk_accumulation :
    (∀ m0 m1 kx ky vNew : Int,
      dot2 (deltaUpdateX m0 m1 kx ky vNew) (deltaUpdateY m0 m1 kx ky vNew) kx ky =
        (kx * kx + ky * ky) * vNew) ∧
    (∀ m0 m1 kx ky vNew ux uy : Int,
      dot2 kx ky ux uy = 0 →
      dot2 (deltaUpdateX m0 m1 kx ky vNew) (deltaUpdateY m0 m1 kx ky vNew) ux uy =
        (kx * kx + ky * ky) * dot2 m0 m1 ux uy) ∧
    (∀ kx ky ux uy : Int,
      householderBetaX 1 kx ky (householderBetaX 1 kx ky ux uy) (householderBetaY 1 kx ky ux uy) =
        (kx * kx + ky * ky) * householderBetaX 1 kx ky ux uy ∧
      householderBetaY 1 kx ky (householderBetaX 1 kx ky ux uy) (householderBetaY 1 kx ky ux uy) =
        (kx * kx + ky * ky) * householderBetaY 1 kx ky ux uy ∧
      householderBetaX 2 kx ky (householderBetaX 2 kx ky ux uy) (householderBetaY 2 kx ky ux uy) =
        sqInt (kx * kx + ky * ky) * ux ∧
      householderBetaY 2 kx ky (householderBetaX 2 kx ky ux uy) (householderBetaY 2 kx ky ux uy) =
        sqInt (kx * kx + ky * ky) * uy ∧
      dot2 (householderBetaX 2 kx ky ux uy) (householderBetaY 2 kx ky ux uy)
           (householderBetaX 2 kx ky ux uy) (householderBetaY 2 kx ky ux uy) =
        sqInt (kx * kx + ky * ky) * dot2 ux uy ux uy) ∧
    (dot2 (hebbianUpdateX 5 1 (-3)) (hebbianUpdateY 0 0 (-3)) 1 0 = 2 ∧
      dot2 (deltaUpdateX 5 0 1 0 (-3)) (deltaUpdateY 5 0 1 0 (-3)) 1 0 = -3 ∧
      dot2 (householderBetaX 3 1 0 1 0) (householderBetaY 3 1 0 1 0)
           (householderBetaX 3 1 0 1 0) (householderBetaY 3 1 0 1 0) = 4) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m0 m1 kx ky vNew
    unfold dot2 deltaUpdateX deltaUpdateY
    grind
  · intro m0 m1 kx ky vNew ux uy horth
    unfold dot2 deltaUpdateX deltaUpdateY at *
    have hcalc :
        ((kx * kx + ky * ky) * m0 - (m0 * kx + m1 * ky) * kx + vNew * kx) * ux +
        ((kx * kx + ky * ky) * m1 - (m0 * kx + m1 * ky) * ky + vNew * ky) * uy =
        (kx * kx + ky * ky) * (m0 * ux + m1 * uy) +
        (vNew - (m0 * kx + m1 * ky)) * (kx * ux + ky * uy) := by
      grind
    rw [hcalc, horth]
    omega
  · intro kx ky ux uy
    unfold householderBetaX householderBetaY sqInt dot2
    refine ⟨by grind, by grind, by grind, by grind, by grind⟩
  · decide

/-!
## 4. Exponential Gibbs Margin Concentration vs. Affine Linear-Attention Dilution
-/

/-- Integer power `B^n` for exact Gibbs logit exponentiation. -/
def powInt (B : Int) : Nat → Int
  | 0 => 1
  | n + 1 => B * powInt B n

theorem powInt_add (B : Int) (a b : Nat) :
    powInt B (a + b) = powInt B a * powInt B b := by
  induction b with
  | zero =>
    simp [powInt]
  | succ b ih =>
    have hrew : a + (b + 1) = (a + b) + 1 := by omega
    rw [hrew]
    simp only [powInt]
    rw [ih]
    grind

theorem powInt_pos (B : Int) (n : Nat) (hB : 0 < B) : 0 < powInt B n := by
  induction n with
  | zero =>
    simp [powInt]
  | succ n ih =>
    simp only [powInt]
    exact Int.mul_pos hB ih

/-- **Theorem 4 (Gibbs Exponential Margin Concentration vs. Linear-Attention `O(1/D)` Dilution)**:
  1. **Universal Base-Invariance & Exponential Margin Dominance**: With 1 target key at logit
     `s0 + Δ` and `D` distractor keys at logit `s0` (`B > 0`), whenever `B^Δ ≥ Γ * D`, the target's
     unnormalized Gibbs mass `B^(s0 + Δ)` is at least `Γ` times the COMBINED mass `D * B^s0`
     of all `D` distractors, independent of baseline shift `s0`!
  2. **Sharp 100-Token Retrieval Witness (`D = 99` distractors, `B = 2, Δ = 10`)**:
     Gibbs target mass `2^10 = 1024` exceeds `10 ×` total distractor mass `99` (`1024 / 1123 > 91.1%`),
     whereas affine non-negative linear attention (`1 + ⟨q, k⟩`: target `2` vs `99` distractors of `1`)
     dilutes target mass to `2 / 101 < 2%` (`49.5×` weaker than distractors!). -/
theorem gibbs_exponential_margin_concentration_vs_uniform_linear_dilution :
    (∀ B D gamma : Int, ∀ s0 delta : Nat,
      0 < B →
      gamma * D ≤ powInt B delta →
      gamma * (D * powInt B s0) ≤ powInt B (s0 + delta)) ∧
    (10 * (99 * powInt 2 3) < powInt 2 (3 + 10) ∧
      powInt 2 10 = 1024 ∧
      (2 : Int) * 49 < 99 * 1) := by
  refine ⟨?_, ?_⟩
  · intro B D gamma s0 delta hB hmargin
    rw [powInt_add]
    have hs0 : 0 ≤ powInt B s0 := Int.le_of_lt (powInt_pos B s0 hB)
    have hmul := Int.mul_le_mul_of_nonneg_right hmargin hs0
    have hlhs : gamma * D * powInt B s0 = gamma * (D * powInt B s0) := by grind
    have hrhs : powInt B delta * powInt B s0 = powInt B s0 * powInt B delta := by grind
    rw [← hlhs, ← hrhs]
    exact hmul
  · decide

end CommonGround.Frontier.SoftmaxRoPEAndDeltaRule
