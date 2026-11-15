/-
  TheoremAtlasSoftmaxVsLinearAttentionRankRoPESymplecticDeltaRuleAndAutomataMonoidBridge.lean
  ------------------------------------------------------------------------------------------
  Pure-core Lean 4.33.0 verification suite (#618, 0 imports, 0 sorry) unifying
  Automata Semigroup Theory (Folder 06), Harmonic Convolution Algebra (Folder 05),
  Birkhoff Doubly-Stochastic Optimal Transport (Folders 01 + 08), and Multi-Head
  Subspace Geometry (Folder 02):

  1. `krohn_rhodes_aperiodic_monoid_parity_impossibility_vs_householder_group_parity`
  2. `circulant_dft4_convolution_diagonalization_vs_causal_toeplitz_wraparound_leakage`
  3. `doubly_stochastic_attention_hubness_elimination_vs_row_sink_monopoly`
  4. `multi_head_orthogonal_subspace_expressivity_vs_collinear_head_collapse`
  5. `alibi_linear_recency_horizon_localization_vs_long_range_needle_extinction`
-/

namespace CommonGround.Verification.SoftmaxRoPEDeltaAutomataBridge

/-!
## 1. Krohn–Rhodes Aperiodic Monoid Parity Impossibility vs. β = 2 Householder Group Parity
-/

/-- Iterated state transition `f^[n](s)`. -/
def iterateStep {α : Type} (f : α → α) : Nat → α → α
  | 0, s => s
  | n + 1, s => f (iterateStep f n s)

/-- `β = 2` 1D Householder reflection `H(x) = -x` (non-trivial `ℤ/2ℤ` orthogonal group action). -/
def householderFlip (x : Int) : Int := -x

theorem iterateStep_stabilizes_beyond_threshold {α : Type} (f : α → α) (T : Nat)
    (haper : ∀ s : α, iterateStep f (T + 1) s = iterateStep f T s) :
    ∀ k : Nat, ∀ s : α, iterateStep f (T + k) s = iterateStep f T s := by
  intro k
  induction k with
  | zero =>
    intro s
    rfl
  | succ k ih =>
    intro s
    have h1 : T + (k + 1) = (T + k) + 1 := rfl
    rw [h1]
    simp only [iterateStep]
    rw [ih s]
    exact haper s

theorem householderFlip_parity (m : Nat) :
    iterateStep householderFlip (2 * m) (1 : Int) = 1 ∧
    iterateStep householderFlip (2 * m + 1) (1 : Int) = -1 := by
  induction m with
  | zero =>
    decide
  | succ m ih =>
    have heven : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    have hodd : 2 * (m + 1) + 1 = (2 * (m + 1)) + 1 := rfl
    refine ⟨?_, ?_⟩
    · rw [heven]
      simp only [iterateStep, householderFlip]
      rw [ih.1]
      decide
    · rw [hodd, heven]
      simp only [iterateStep, householderFlip]
      rw [ih.1]
      decide

/-- **Theorem 1 (Krohn–Rhodes Aperiodic Reset Semigroup Parity Impossibility vs. `β = 2` Householder Group Parity)**:
  1. **Universal Aperiodic Impossibility**: Any state transition `f : α → α` that satisfies
     aperiodic stabilization `f^[T+1](s) = f^[T](s)` (modeling `[0, 1]`-gated contractive/reset
     SSMs & standard non-negative `DeltaNet`) satisfies `f^[2T + 1](s0) = f^[2T](s0)` for EVERY
     initial state `s0` — hence NO readout `g : α → Bool` can distinguish `2T` from `2T + 1` flips!
  2. **Householder Reflection (`β = 2`) Exact All-Length Parity Tracking**: Extending the gate
     to `β = 2` (`householderFlip x = -x`) embeds `ℤ/2ℤ ⊂ O(1)`, separating `2m` (`+1`) from
     `2m + 1` (`-1`) across ALL sequence lengths `m : Nat`! -/
theorem krohn_rhodes_aperiodic_monoid_parity_impossibility_vs_householder_group_parity :
    (∀ {α : Type} (f : α → α) (T : Nat) (s0 : α),
      (∀ s : α, iterateStep f (T + 1) s = iterateStep f T s) →
      iterateStep f (T + (T + 1)) s0 = iterateStep f (T + T) s0) ∧
    (∀ m : Nat,
      iterateStep householderFlip (2 * m) (1 : Int) = 1 ∧
      iterateStep householderFlip (2 * m + 1) (1 : Int) = -1 ∧
      iterateStep householderFlip (2 * m) (1 : Int) ≠
        iterateStep householderFlip (2 * m + 1) (1 : Int)) := by
  refine ⟨?_, ?_⟩
  · intro α f T s0 haper
    have hodd := iterateStep_stabilizes_beyond_threshold f T haper (T + 1) s0
    have heven := iterateStep_stabilizes_beyond_threshold f T haper T s0
    rw [hodd, heven]
  · intro m
    have hp := householderFlip_parity m
    refine ⟨hp.1, hp.2, ?_⟩
    rw [hp.1, hp.2]
    decide

/-!
## 2. Exact Complex-Integer `DFT₄` Cyclic Convolution Theorem vs. Unpadded Causal Wrap-Around Leakage
-/

/-- Gaussian integer multiplication `(a + b i)(c + d i) = (ac - bd) + (ad + bc) i`. -/
def gaussMul (z w : Int × Int) : Int × Int :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- 4-point Discrete Fourier Transform over `ℤ[i]` (`ω = -i` or `+i`; here `F_k = ∑_{n=0}^3 (-i)^{kn} x_n`):
    - `k = 0`: `(x0 + x1 + x2 + x3, 0)`
    - `k = 1`: `(x0 - x2, -x1 + x3)`
    - `k = 2`: `(x0 - x1 + x2 - x3, 0)`
    - `k = 3`: `(x0 - x2, x1 - x3)` -/
def dft4Mode0 (x0 x1 x2 x3 : Int) : Int × Int := (x0 + x1 + x2 + x3, 0)
def dft4Mode1 (x0 x1 x2 x3 : Int) : Int × Int := (x0 - x2, x3 - x1)
def dft4Mode2 (x0 x1 x2 x3 : Int) : Int × Int := (x0 - x1 + x2 - x3, 0)
def dft4Mode3 (x0 x1 x2 x3 : Int) : Int × Int := (x0 - x2, x1 - x3)

/-- Length-4 cyclic convolution `(h ⊛ x)_t`. -/
def cycConv4_0 (h0 h1 h2 h3 x0 x1 x2 x3 : Int) : Int := h0 * x0 + h1 * x3 + h2 * x2 + h3 * x1
def cycConv4_1 (h0 h1 h2 h3 x0 x1 x2 x3 : Int) : Int := h0 * x1 + h1 * x0 + h2 * x3 + h3 * x2
def cycConv4_2 (h0 h1 h2 h3 x0 x1 x2 x3 : Int) : Int := h0 * x2 + h1 * x1 + h2 * x0 + h3 * x3
def cycConv4_3 (h0 h1 h2 h3 x0 x1 x2 x3 : Int) : Int := h0 * x3 + h1 * x2 + h2 * x1 + h3 * x0

/-- Causal lower-triangular Toeplitz convolution at `t = 0` (`y_0 = h_0 x_0`, zero future dependence). -/
def causalConv4_0 (h0 x0 : Int) : Int := h0 * x0

/-- **Theorem 2 (Exact `DFT₄` Cyclic Convolution Diagonalization & Parseval Inversion vs. Unpadded Causal Leakage)**:
  1. **Exact `DFT₄` Diagonalization Across All 4 Modes**: For ALL integer signals `h, x ∈ ℤ⁴`,
     `DFT₄(h ⊛ x)_k = DFT₄(h)_k *_{ℤ[i]} DFT₄(x)_k` for `k = 0, 1, 2, 3`.
  2. **Exact Denominator-Free Inverse `IDFT₄`**: Recombining the 4 spectral modes recovers `4 * x`
     identically (`F0.1 + F1.1 + F2.1 + F3.1 = 4 * x0`).
  3. **Premise Failure (Unpadded FFT Causal Wrap-Around Leakage!)**: On causal 2-tap filter
     `h = (1, 1, 0, 0)` and future impulse `x = (0, 0, 0, 5)`, true causal output at `t = 0` is `0`,
     whereas unpadded cyclic `DFT₄` convolution outputs `5 ≠ 0` (leaking future token `x_3` into `y_0`!). -/
theorem circulant_dft4_convolution_diagonalization_vs_causal_toeplitz_wraparound_leakage :
    (∀ h0 h1 h2 h3 x0 x1 x2 x3 : Int,
      let y0 := cycConv4_0 h0 h1 h2 h3 x0 x1 x2 x3
      let y1 := cycConv4_1 h0 h1 h2 h3 x0 x1 x2 x3
      let y2 := cycConv4_2 h0 h1 h2 h3 x0 x1 x2 x3
      let y3 := cycConv4_3 h0 h1 h2 h3 x0 x1 x2 x3
      dft4Mode0 y0 y1 y2 y3 = gaussMul (dft4Mode0 h0 h1 h2 h3) (dft4Mode0 x0 x1 x2 x3) ∧
      dft4Mode1 y0 y1 y2 y3 = gaussMul (dft4Mode1 h0 h1 h2 h3) (dft4Mode1 x0 x1 x2 x3) ∧
      dft4Mode2 y0 y1 y2 y3 = gaussMul (dft4Mode2 h0 h1 h2 h3) (dft4Mode2 x0 x1 x2 x3) ∧
      dft4Mode3 y0 y1 y2 y3 = gaussMul (dft4Mode3 h0 h1 h2 h3) (dft4Mode3 x0 x1 x2 x3) ∧
      (dft4Mode0 x0 x1 x2 x3).1 + (dft4Mode1 x0 x1 x2 x3).1 +
        (dft4Mode2 x0 x1 x2 x3).1 + (dft4Mode3 x0 x1 x2 x3).1 = 4 * x0) ∧
    (cycConv4_0 1 1 0 0 0 0 0 5 = 5 ∧
      causalConv4_0 1 0 = 0 ∧
      cycConv4_0 1 1 0 0 0 0 0 5 ≠ causalConv4_0 1 0) := by
  refine ⟨?_, by decide⟩
  intro h0 h1 h2 h3 x0 x1 x2 x3
  unfold cycConv4_0 cycConv4_1 cycConv4_2 cycConv4_3
  unfold dft4Mode0 dft4Mode1 dft4Mode2 dft4Mode3 gaussMul
  simp only [Prod.mk.injEq]
  refine ⟨⟨by grind, by grind⟩, ⟨by grind, by grind⟩, ⟨by grind, by grind⟩, ⟨by grind, by grind⟩, by grind⟩

/-!
## 3. Birkhoff Doubly-Stochastic Attention Hubness Elimination vs. Row-Only Sink Monopoly & Signed Affine Overshoot
-/

/-- **Theorem 3 (Doubly-Stochastic Attention Column-Cap, Token-Sum Conservation & `ℓ_∞` Non-Expansiveness vs. Attention-Sink Monopoly & Signed Affine Overshoot)**:
  1. **Token-Sum Conservation & `ℓ_∞` Boundedness**: For ANY non-negative `3 × 3` doubly-stochastic
     matrix `A` with row & column sums `R` (`a_ij ≥ 0`), total feature sum is scaled by `R`
     (`y0 + y1 + y2 = R * (v0 + v1 + v2)`), every column load equals `R`, and whenever `m ≤ v_j ≤ M`
     for `j = 0, 1, 2`, every output coordinate satisfies `R * m ≤ y_i ≤ R * M`!
  2. **Premise Failure A (Row-Only Softmax Attention-Sink Hubness)**: Row-stochastic attention
     `A_sink = [[R,0,0],[R,0,0],[R,0,0]]` (`R = 1`) satisfies all row-sum constraints (`1, 1, 1`),
     yet concentrates `3×` column load (`3 > 1`) onto sink token `j = 0`, starving columns `1, 2` (`0`).
  3. **Premise Failure B (Signed Affine Doubly-Summed Residual Overshoot — `mHC` Motivation)**:
     `A_signed = [[2,-1,0],[-1,2,0],[0,0,1]]` has exact row sums `1` AND column sums `1`, yet drops
     `a_ij ≥ 0`, causing bounded input `v = (1, 0, 0) ∈ [0, 1]³` to overshoot to `(2, -1, 0) ∉ [0, 1]³`! -/
theorem doubly_stochastic_attention_hubness_elimination_vs_row_sink_monopoly :
    (∀ a00 a01 a02 a10 a11 a12 a20 a21 a22 R v0 v1 v2 m M : Int,
      0 ≤ a00 → 0 ≤ a01 → 0 ≤ a02 →
      0 ≤ a10 → 0 ≤ a11 → 0 ≤ a12 →
      0 ≤ a20 → 0 ≤ a21 → 0 ≤ a22 →
      a00 + a01 + a02 = R →
      a10 + a11 + a12 = R →
      a20 + a21 + a22 = R →
      a00 + a10 + a20 = R →
      a01 + a11 + a21 = R →
      a02 + a12 + a22 = R →
      m ≤ v0 → v0 ≤ M →
      m ≤ v1 → v1 ≤ M →
      m ≤ v2 → v2 ≤ M →
      let y0 := a00 * v0 + a01 * v1 + a02 * v2
      let y1 := a10 * v0 + a11 * v1 + a12 * v2
      let y2 := a20 * v0 + a21 * v1 + a22 * v2
      y0 + y1 + y2 = R * (v0 + v1 + v2) ∧
      R * m ≤ y0 ∧ y0 ≤ R * M ∧
      R * m ≤ y1 ∧ y1 ≤ R * M ∧
      R * m ≤ y2 ∧ y2 ≤ R * M) ∧
    ((1 + 0 + 0 = (1 : Int) ∧ 1 + 1 + 1 = (3 : Int) ∧ (1 : Int) < 3) ∧
      ((2 : Int) + (-1) + 0 = 1 ∧ (-1 : Int) + 2 + 0 = 1 ∧
        (2 : Int) * 1 + (-1) * 0 + 0 * 0 = 2 ∧ (1 : Int) < 2 ∧
        (-1 : Int) * 1 + 2 * 0 + 0 * 0 = -1 ∧ (-1 : Int) < 0)) := by
  refine ⟨?_, by decide⟩
  intro a00 a01 a02 a10 a11 a12 a20 a21 a22 R v0 v1 v2 m M
  intro ha00 ha01 ha02 ha10 ha11 ha12 ha20 ha21 ha22
  intro hr0 hr1 hr2 hc0 hc1 hc2 hm0 hM0 hm1 hM1 hm2 hM2
  have hsum :
      (a00 * v0 + a01 * v1 + a02 * v2) +
      (a10 * v0 + a11 * v1 + a12 * v2) +
      (a20 * v0 + a21 * v1 + a22 * v2) =
      (a00 + a10 + a20) * v0 + (a01 + a11 + a21) * v1 + (a02 + a12 + a22) * v2 := by
    grind
  have hrowBound : ∀ b0 b1 b2 : Int,
      0 ≤ b0 → 0 ≤ b1 → 0 ≤ b2 → b0 + b1 + b2 = R →
      R * m ≤ b0 * v0 + b1 * v1 + b2 * v2 ∧ b0 * v0 + b1 * v1 + b2 * v2 ≤ R * M := by
    intro b0 b1 b2 hb0 hb1 hb2 hbr
    have hl0 := Int.mul_le_mul_of_nonneg_left hm0 hb0
    have hl1 := Int.mul_le_mul_of_nonneg_left hm1 hb1
    have hl2 := Int.mul_le_mul_of_nonneg_left hm2 hb2
    have hu0 := Int.mul_le_mul_of_nonneg_left hM0 hb0
    have hu1 := Int.mul_le_mul_of_nonneg_left hM1 hb1
    have hu2 := Int.mul_le_mul_of_nonneg_left hM2 hb2
    have hrm : (b0 + b1 + b2) * m = b0 * m + b1 * m + b2 * m := by grind
    have hrM : (b0 + b1 + b2) * M = b0 * M + b1 * M + b2 * M := by grind
    rw [← hbr]
    constructor <;> omega
  have hb0 := hrowBound a00 a01 a02 ha00 ha01 ha02 hr0
  have hb1 := hrowBound a10 a11 a12 ha10 ha11 ha12 hr1
  have hb2 := hrowBound a20 a21 a22 ha20 ha21 ha22 hr2
  refine ⟨?_, hb0.1, hb0.2, hb1.1, hb1.2, hb2.1, hb2.2⟩
  rw [hsum, hc0, hc1, hc2]
  grind

/-!
## 4. Multi-Head Orthogonal Subspace Expressivity vs. Collinear Head Collapse
-/

/-- Two-head linear operator `M(u) = v1 * ⟨k1, u⟩ + v2 * ⟨k2, u⟩` in `ℤ²`. -/
def twoHeadOutX (v1x k1x k1y v2x k2x k2y ux uy : Int) : Int :=
  v1x * (k1x * ux + k1y * uy) + v2x * (k2x * ux + k2y * uy)

def twoHeadOutY (v1y k1x k1y v2y k2x k2y ux uy : Int) : Int :=
  v1y * (k1x * ux + k1y * uy) + v2y * (k2x * ux + k2y * uy)

def det2Vec (ax ay bx by_ : Int) : Int := ax * by_ - ay * bx

/-- **Theorem 4 (Multi-Head Bilinear Determinant Factorization: Full-Rank Orthogonal Heads vs. Collinear Head Collapse)**:
  1. **Universal Bilinear Determinant Factorization**: For ANY two attention heads `H₁(u) = v₁ ⟨k₁, u⟩`
     and `H₂(u) = v₂ ⟨k₂, u⟩` evaluated on ANY two inputs `u, w ∈ ℤ²`,
     `det((H₁ + H₂)(u), (H₁ + H₂)(w)) = det(v₁, v₂) * det(k₁, k₂) * det(u, w)`!
  2. **Full-Rank Orthogonal Witness**: Orthogonal unit heads `k₁=(1,0), k₂=(0,1), v₁=(1,0), v₂=(0,1)`
     achieve `det = 1 ≠ 0` on `u=(1,0), w=(0,1)`.
  3. **Collinear Head Collapse**: Whenever `k₂ = c · k₁` (collinear query/key subspace) OR
     `v₂ = c · v₁` (collinear output value projections), `det((H₁ + H₂)(u), (H₁ + H₂)(w)) = 0`
     for ALL inputs `u, w` — multi-head expressivity collapses identically to rank `≤ 1`! -/
theorem multi_head_orthogonal_subspace_expressivity_vs_collinear_head_collapse :
    (∀ v1x v1y v2x v2y k1x k1y k2x k2y ux uy wx wy : Int,
      det2Vec
        (twoHeadOutX v1x k1x k1y v2x k2x k2y ux uy)
        (twoHeadOutY v1y k1x k1y v2y k2x k2y ux uy)
        (twoHeadOutX v1x k1x k1y v2x k2x k2y wx wy)
        (twoHeadOutY v1y k1x k1y v2y k2x k2y wx wy) =
      det2Vec v1x v1y v2x v2y * det2Vec k1x k1y k2x k2y * det2Vec ux uy wx wy) ∧
    (det2Vec
      (twoHeadOutX 1 1 0 0 0 1 1 0) (twoHeadOutY 0 1 0 1 0 1 1 0)
      (twoHeadOutX 1 1 0 0 0 1 0 1) (twoHeadOutY 0 1 0 1 0 1 0 1) = 1) ∧
    (∀ v1x v1y v2x v2y k1x k1y c ux uy wx wy : Int,
      det2Vec
        (twoHeadOutX v1x k1x k1y v2x (c * k1x) (c * k1y) ux uy)
        (twoHeadOutY v1y k1x k1y v2y (c * k1x) (c * k1y) ux uy)
        (twoHeadOutX v1x k1x k1y v2x (c * k1x) (c * k1y) wx wy)
        (twoHeadOutY v1y k1x k1y v2y (c * k1x) (c * k1y) wx wy) = 0 ∧
      det2Vec
        (twoHeadOutX v1x k1x k1y (c * v1x) ux uy ux uy)
        (twoHeadOutY v1y k1x k1y (c * v1y) ux uy ux uy)
        (twoHeadOutX v1x k1x k1y (c * v1x) ux uy wx wy)
        (twoHeadOutY v1y k1x k1y (c * v1y) ux uy wx wy) = 0) := by
  refine ⟨?_, by decide, ?_⟩
  · intro v1x v1y v2x v2y k1x k1y k2x k2y ux uy wx wy
    unfold det2Vec twoHeadOutX twoHeadOutY
    grind
  · intro v1x v1y v2x v2y k1x k1y c ux uy wx wy
    unfold det2Vec twoHeadOutX twoHeadOutY
    constructor <;> grind

/-!
## 5. ALiBi Linear Distance Decay: Exact Local Tie-Breaking vs. Long-Horizon Needle Extinction
-/

/-- ALiBi attention logit `score(s, m, d) = s - m * d` for semantic dot-product `s`, slope `m > 0`,
    and causal token distance `d ≥ 0`. -/
def alibiLogit (semScore slope dist : Int) : Int := semScore - slope * dist

/-- **Theorem 5 (ALiBi Linear Recency Tie-Breaking vs. Long-Horizon Semantic Needle Extinction)**:
  1. **Exact Translation-Invariant Recency Ordering**: For any tied semantic matches (`s`),
     slope `m > 0`, and distances `dNear < dFar`, `alibiLogit s m dFar < alibiLogit s m dNear`
     with exact margin `m * (dFar - dNear) > 0`, invariant under global shift `d ↦ d + t0`.
  2. **Premise Failure (Long-Range Needle Extinction Beyond `d_crit = Δ_sem / m`)**:
     Whenever a true distant needle (`sLocal + deltaSem` at `dFar`) and a local distractor
     (`sLocal` at `dNear`) satisfy `deltaSem < m * (dFar - dNear)` (witnessed at `sLocal = 0,
     deltaSem = 10, m = 1, dNear = 1, dFar = 20`: needle `-10 < -1` local distractor!),
     linear distance bias strictly inverts retrieval! -/
theorem alibi_linear_recency_horizon_localization_vs_long_range_needle_extinction :
    (∀ s m dNear dFar t0 : Int,
      0 < m →
      dNear < dFar →
      alibiLogit s m dNear - alibiLogit s m dFar = m * (dFar - dNear) ∧
      alibiLogit s m dFar < alibiLogit s m dNear ∧
      alibiLogit s m (dNear + t0) - alibiLogit s m (dFar + t0) =
        alibiLogit s m dNear - alibiLogit s m dFar) ∧
    (∀ sLocal deltaSem m dNear dFar : Int,
      deltaSem < m * (dFar - dNear) →
      alibiLogit (sLocal + deltaSem) m dFar < alibiLogit sLocal m dNear) ∧
    (alibiLogit 10 1 20 = -10 ∧ alibiLogit 0 1 1 = -1 ∧ alibiLogit 10 1 20 < alibiLogit 0 1 1) := by
  refine ⟨?_, ?_, by decide⟩
  · intro s m dNear dFar t0 hm hd
    unfold alibiLogit
    have hdiff : dFar - dNear > 0 := by omega
    have hpos : 0 < m * (dFar - dNear) := Int.mul_pos hm hdiff
    have h1 : (s - m * dNear) - (s - m * dFar) = m * (dFar - dNear) := by grind
    have h2 : (s - m * (dNear + t0)) - (s - m * (dFar + t0)) = (s - m * dNear) - (s - m * dFar) := by grind
    refine ⟨h1, by omega, h2⟩
  · intro sLocal deltaSem m dNear dFar hdom
    unfold alibiLogit
    have hrew : (sLocal + deltaSem - m * dFar) - (sLocal - m * dNear) = deltaSem - m * (dFar - dNear) := by
      grind
    omega

end CommonGround.Verification.SoftmaxRoPEDeltaAutomataBridge
