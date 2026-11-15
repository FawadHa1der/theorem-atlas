/-
  02-universal-affine-query-compression/BatsonSpielmanSrivastavaBarrierAndKadisonSingerFrontier.lean

  Wave V215 Frontier Formalization (Zero External Imports · Zero `sorry` · Pure-Core Lean 4.33.0):
  Unifies Folder 02 (Universal Coreset & Subspace Sparsification), Folder 05 (Matrix Resolvent
  Potentials), Folder 07 (Quantum / Tight Operator Frames), Folder 09 (Effective Resistance
  Leverage), and Folder 10 (Spectral Graph Sparsifiers):

  1. Universal Denominator-Free 2×2 Sherman–Morrison Rank-1 Determinant & Batson–Spielman–Srivastava
     (BSS) Upper-Barrier Potential Identity:
       • det(M - t v vᵀ) = det(M) - t (vᵀ adj(M) v)   (t² cancels identically!)
       • det(M) · tr(adj(M - t v vᵀ)) - det(M - t v vᵀ) · tr(adj(M)) = t · ‖adj(M) v‖₂² ≥ 0 (t ≥ 0)
       • Explicit BSS shifted-barrier step Φ^{u+δ}(A + t e₁ e₁ᵀ) < Φ^u(A) (`42 < 48`),
     paired with the explicit overshot step-size counterexample (`t (vᵀ M⁻¹ v) > 1` ⟹ `det(M') < 0`),
     where the top eigenvalue jumps past the barrier pole `u` and flips `Φ^u` negative!
  2. Exact Two-Sided Spectral Graph Sparsification (`K₄` 6 Edges → Weighted `2·C₄` 4 Edges, κ = 2):
       • Lower Loewner SOS: xᵀ L_{2C₄} x - xᵀ L_{K₄} x = (x₀ - x₁ + x₂ - x₃)² ≥ 0
       • Upper Loewner SOS: 2 xᵀ L_{K₄} x - xᵀ L_{2C₄} x = 2(x₀ - x₂)² + 2(x₁ - x₃)² ≥ 0
     paired with sharpness witnesses and unweighted bridge-drop spectral collapse (`0 < 4`).
  3. Constructive Marcus–Spielman–Srivastava / Weaver KS₂ Frame Paving vs. High-Leverage Barriers:
       • Positive KS₂ Witness: 6-vector D₃ cuboctahedral tight Parseval frame in ℤ³
         (∑ u_i u_iᵀ = 4 I₃, leverage δ = 1/2) paved into P₁ = {0,1,2}, P₂ = {3,4,5} with strict
         two-sided Loewner bounds ‖x‖₂² < 2 xᵀ M_k x < 7 ‖x‖₂² < 8 ‖x‖₂² for all x ≠ 0!
       • Exhaustive Weaver Tetrahedron Impossibility (δ = 3/4 > 1/2): Across ALL 2⁴ = 16 subsets
         of the Hadamard tetrahedron in ℤ³ (∑ w_i w_iᵀ = 4 I₃), ZERO 2-pavings achieve < 4 ‖x‖₂²!
       • Universal 3-Vector 2D KS₂ Impossibility: For ANY 3 vectors in ℤ² and ANY 2-coloring,
         one color class has ≤ 1 vector, leaving a non-zero orthogonal direction where the other
         color class absorbs 100% of the total quadratic form!
-/

namespace CommonGround.UniversalQueryCompression.BatsonSpielmanKadisonSinger

/-! ## 1. Universal 2×2 Sherman–Morrison Determinant & BSS Upper-Barrier Potential Identity -/

/-- Symmetric 2×2 integer matrix `[[a, b], [b, d]]` representing `M = u I - A`. -/
structure Sym2 where
  a : Int
  b : Int
  d : Int
  deriving DecidableEq, Repr

/-- Exact determinant `det(M) = a d - b²`. -/
def detSym2 (M : Sym2) : Int :=
  M.a * M.d - M.b * M.b

/-- Trace of the 2×2 adjugate `adj([[a, b], [b, d]]) = [[d, -b], [-b, a]]`, equal to `a + d`. -/
def trAdjSym2 (M : Sym2) : Int :=
  M.a + M.d

/-- Rank-1 update `M - t v vᵀ` corresponding to `(u I - A) - t v vᵀ = u I - (A + t v vᵀ)`. -/
def rankOneSubSym2 (M : Sym2) (t x y : Int) : Sym2 :=
  { a := M.a - t * (x * x)
    b := M.b - t * (x * y)
    d := M.d - t * (y * y) }

/-- Scaled rank-1 resolvent leverage numerator `vᵀ adj(M) v = d x² - 2 b x y + a y²`. -/
def adjQuadSym2 (M : Sym2) (x y : Int) : Int :=
  M.d * (x * x) - 2 * M.b * (x * y) + M.a * (y * y)

/-- Scaled squared-resolvent sensitivity numerator `‖adj(M) v‖₂² = (d x - b y)² + (-b x + a y)²`. -/
def adjSqNormSym2 (M : Sym2) (x y : Int) : Int :=
  (M.d * x - M.b * y) * (M.d * x - M.b * y) +
  (M.a * y - M.b * x) * (M.a * y - M.b * x)

theorem sq_nonneg_int (z : Int) : 0 ≤ z * z := by
  by_cases h : 0 ≤ z
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -z := by omega
    have hmul : 0 ≤ (-z) * (-z) := Int.mul_nonneg hn hn
    have heq : (-z) * (-z) = z * z := by
      calc
        (-z) * (-z) = -(z * (-z)) := Int.neg_mul z (-z)
        _ = -(-(z * z)) := by rw [Int.mul_neg]
        _ = z * z := Int.neg_neg (z * z)
    rw [← heq]
    exact hmul

/-- Helper: exact integer ring identity proved by standard associative/distributive normalization.
    Wait: since we have 0 imports (no Mathlib `ring`), let's prove both polynomial identities
    directly from core `Int` distributivity & commutativity lemmas! -/
theorem rank_one_det_lemma_sym2 (M : Sym2) (t x y : Int) :
    detSym2 (rankOneSubSym2 M t x y) = detSym2 M - t * adjQuadSym2 M x y := by
  unfold detSym2 rankOneSubSym2 adjQuadSym2
  -- Use core Lean 4 grind / omega? Wait: Lean 4.33.0 core has `grind`! Let's check or write clean calc!
  grind

theorem bss_upper_barrier_numerator_identity_sym2 (M : Sym2) (t x y : Int) :
    detSym2 M * trAdjSym2 (rankOneSubSym2 M t x y) -
      detSym2 (rankOneSubSym2 M t x y) * trAdjSym2 M =
    t * adjSqNormSym2 M x y := by
  unfold detSym2 trAdjSym2 rankOneSubSym2 adjSqNormSym2
  grind

/-- Universal Sherman–Morrison + Batson–Spielman–Srivastava Barrier Monotonicity Theorem:
    1. `det(M - t v vᵀ) = det(M) - t (vᵀ adj(M) v)` identically (`t²` cancels),
    2. `det(M) tr(adj(M')) - det(M') tr(adj(M)) = t · ‖adj(M) v‖₂² ≥ 0` for all `t ≥ 0`,
    3. Explicit barrier-shift witness: starting from `M₀ = 6 I₂` (`Φ⁶(0) = 12 / 36 = 1 / 3`),
       shifting `u : 6 ↦ 8` while adding `2 e₁ e₁ᵀ` gives `M₁ = diag(6, 8)` with
       `det(M₁) = 48 > 0` and `Φ⁸(2 e₁ e₁ᵀ) = 14 / 48 < 12 / 36` (`14 · 36 = 504 < 576 = 12 · 48`)! -/
theorem sherman_morrison_rank_one_determinant_and_bss_barrier_identity :
    (∀ (M : Sym2) (t x y : Int),
      detSym2 (rankOneSubSym2 M t x y) = detSym2 M - t * adjQuadSym2 M x y) ∧
    (∀ (M : Sym2) (t x y : Int),
      0 ≤ t →
      0 ≤ detSym2 M * trAdjSym2 (rankOneSubSym2 M t x y) -
            detSym2 (rankOneSubSym2 M t x y) * trAdjSym2 M) ∧
    (let M0 : Sym2 := { a := 6, b := 0, d := 6 }
     let MShift : Sym2 := { a := 8, b := 0, d := 8 }
     let M1 : Sym2 := rankOneSubSym2 MShift 2 1 0
     0 < detSym2 M1 ∧
     trAdjSym2 M1 * detSym2 M0 < trAdjSym2 M0 * detSym2 M1) := by
  refine ⟨rank_one_det_lemma_sym2, ?_, ?_⟩
  · intro M t x y ht
    rw [bss_upper_barrier_numerator_identity_sym2]
    unfold adjSqNormSym2
    have h1 : 0 ≤ (M.d * x - M.b * y) * (M.d * x - M.b * y) := sq_nonneg_int _
    have h2 : 0 ≤ (M.a * y - M.b * x) * (M.a * y - M.b * x) := sq_nonneg_int _
    exact Int.mul_nonneg ht (Int.add_nonneg h1 h2)
  · decide

/-- Premise-Failure Counterexample (`t · (vᵀ M⁻¹ v) > 1` Pole-Crossing Inversion):
    At `M = 2 I₂` (`u = 2, A = 0`), `det(M) = 4 > 0` and `Φ²(0) = tr(adj(M))/det(M) = 4/4 = +1`.
    Taking `v = (1, 0)` with overshot step `t = 3` (`t · adjQuad = 6 > 4 = det(M)`) yields
    `M' = diag(-1, 2)` with `det(M') = -2 < 0` and `tr(adj(M')) = +1`, so the raw rational trace
    `1 / (-2) = -1/2 < +1` appears smaller ONLY because `λ₁(A') = 3 > 2 = u` crossed the pole! -/
theorem overshot_rank_one_step_poles_barrier_inversion_counterexample :
    let M : Sym2 := { a := 2, b := 0, d := 2 }
    let M' : Sym2 := rankOneSubSym2 M 3 1 0
    detSym2 M = 4 ∧
    3 * adjQuadSym2 M 1 0 = 6 ∧
    detSym2 M' = -2 ∧
    trAdjSym2 M' = 1 := by
  decide

/-! ## 2. Exact Two-Sided Spectral Graph Sparsification (`K₄` → `2·C₄`, `κ = 2`) vs. Cut Collapse -/

/-- Quadratic energy of complete graph `K₄` on `x = (x₀, x₁, x₂, x₃) ∈ ℤ⁴` (`6` edges). -/
def lapQuadK4 (x0 x1 x2 x3 : Int) : Int :=
  (x0 - x1) * (x0 - x1) + (x0 - x2) * (x0 - x2) + (x0 - x3) * (x0 - x3) +
  (x1 - x2) * (x1 - x2) + (x1 - x3) * (x1 - x3) + (x2 - x3) * (x2 - x3)

/-- Quadratic energy of weighted `4`-cycle `2 · C₄` (`0-1-2-3-0`, `4` edges of weight `2`). -/
def lapQuad2C4 (x0 x1 x2 x3 : Int) : Int :=
  2 * ((x0 - x1) * (x0 - x1) + (x1 - x2) * (x1 - x2) +
       (x2 - x3) * (x2 - x3) + (x3 - x0) * (x3 - x0))

/-- Disconnected `2`-edge matching subgraph `M₂` obtained when bridge edges `{1,2}` and `{3,0}` are dropped. -/
def lapQuadDisconnectedM2 (x0 x1 x2 x3 : Int) : Int :=
  (x0 - x1) * (x0 - x1) + (x2 - x3) * (x2 - x3)

/-- Two-Sided Spectral Sparsification Theorem & Bridge-Drop Counterexample:
    1. Exact lower SOS: `xᵀ L_{2C₄} x - xᵀ L_{K₄} x = (x₀ - x₁ + x₂ - x₃)² ≥ 0`,
    2. Exact upper SOS: `2 xᵀ L_{K₄} x - xᵀ L_{2C₄} x = 2(x₀ - x₂)² + 2(x₁ - x₃)² ≥ 0`,
    3. Hence `L_{K₄} ≼ L_{2C₄} ≼ 2 L_{K₄}` universally across `ℤ⁴` (`33.3%` fewer edges, `κ = 2`),
       attained sharply at `(1, 1, -1, -1)` (lower) and `(1, -1, 1, -1)` (upper),
    4. Premise failure: dropping `{1, 2}` and `{3, 0}` without positive reweighting collapses
       `lapQuadDisconnectedM2 1 1 (-1) (-1) = 0` while `lapQuadK4 1 1 (-1) (-1) = 16 > 0`! -/
theorem two_sided_k4_cycle_spectral_sparsifier_vs_bridge_cut_collapse :
    (∀ x0 x1 x2 x3 : Int,
      lapQuad2C4 x0 x1 x2 x3 - lapQuadK4 x0 x1 x2 x3 =
        (x0 - x1 + x2 - x3) * (x0 - x1 + x2 - x3)) ∧
    (∀ x0 x1 x2 x3 : Int,
      2 * lapQuadK4 x0 x1 x2 x3 - lapQuad2C4 x0 x1 x2 x3 =
        2 * ((x0 - x2) * (x0 - x2)) + 2 * ((x1 - x3) * (x1 - x3))) ∧
    (∀ x0 x1 x2 x3 : Int,
      lapQuadK4 x0 x1 x2 x3 ≤ lapQuad2C4 x0 x1 x2 x3 ∧
      lapQuad2C4 x0 x1 x2 x3 ≤ 2 * lapQuadK4 x0 x1 x2 x3) ∧
    (lapQuad2C4 1 1 (-1) (-1) = lapQuadK4 1 1 (-1) (-1) ∧
     lapQuad2C4 1 (-1) 1 (-1) = 2 * lapQuadK4 1 (-1) 1 (-1)) ∧
    (lapQuadDisconnectedM2 1 1 (-1) (-1) = 0 ∧ lapQuadK4 1 1 (-1) (-1) = 16) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x0 x1 x2 x3
    unfold lapQuad2C4 lapQuadK4
    grind
  · intro x0 x1 x2 x3
    unfold lapQuad2C4 lapQuadK4
    grind
  · intro x0 x1 x2 x3
    have hLowEq : lapQuad2C4 x0 x1 x2 x3 - lapQuadK4 x0 x1 x2 x3 =
        (x0 - x1 + x2 - x3) * (x0 - x1 + x2 - x3) := by
      unfold lapQuad2C4 lapQuadK4; grind
    have hUpEq : 2 * lapQuadK4 x0 x1 x2 x3 - lapQuad2C4 x0 x1 x2 x3 =
        2 * ((x0 - x2) * (x0 - x2)) + 2 * ((x1 - x3) * (x1 - x3)) := by
      unfold lapQuad2C4 lapQuadK4; grind
    have hLowNonneg : 0 ≤ (x0 - x1 + x2 - x3) * (x0 - x1 + x2 - x3) := sq_nonneg_int _
    have hSq1 : 0 ≤ (x0 - x2) * (x0 - x2) := sq_nonneg_int _
    have hSq2 : 0 ≤ (x1 - x3) * (x1 - x3) := sq_nonneg_int _
    omega
  · decide
  · decide

/-! ## 3. Constructive Kadison–Singer `KS₂` Paving (`D₃` Cuboctahedral Frame) vs. Weaver Tetrahedron & 2D 3-Vector Impossibility -/

/-- Squared Euclidean norm `x₁² + x₂² + x₃²` on `ℤ³`. -/
def normSq3 (x1 x2 x3 : Int) : Int :=
  x1 * x1 + x2 * x2 + x3 * x3

/-- `6`-vector `D₃` cuboctahedral tight Parseval frame in `ℤ³`:
    `u₀=(1,1,0), u₁=(1,-1,0), u₂=(1,0,1), u₃=(1,0,-1), u₄=(0,1,1), u₅=(0,1,-1)`
    satisfying `∑_{i<6} ⟨u_i, x⟩² = 4 ‖x‖₂²` and uniform leverage `‖u_i‖₂² / 4 = 2 / 4 = 1/2`. -/
def d3PavingSide1Quad (x1 x2 x3 : Int) : Int :=
  (x1 + x2) * (x1 + x2) + (x1 - x2) * (x1 - x2) + (x1 + x3) * (x1 + x3)

def d3PavingSide2Quad (x1 x2 x3 : Int) : Int :=
  (x1 - x3) * (x1 - x3) + (x2 + x3) * (x2 + x3) + (x2 - x3) * (x2 - x3)

/-- Weaver's `4`-vector Hadamard tetrahedron in `ℤ³` (`δ = 3/4 > 1/2`):
    `w₀=(1,1,1), w₁=(1,-1,-1), w₂=(-1,1,-1), w₃=(-1,-1,1)`. -/
def tetraDot (idx : Fin 4) (x1 x2 x3 : Int) : Int :=
  match idx.val with
  | 0 => x1 + x2 + x3
  | 1 => x1 - x2 - x3
  | 2 => -x1 + x2 - x3
  | _ => -x1 - x2 + x3

def tetraSubsetQuad (mask : Nat) (x1 x2 x3 : Int) : Int :=
  (if ((mask >>> 0) &&& 1) == 1 then (tetraDot ⟨0, by omega⟩ x1 x2 x3) ^ 2 else 0) +
  (if ((mask >>> 1) &&& 1) == 1 then (tetraDot ⟨1, by omega⟩ x1 x2 x3) ^ 2 else 0) +
  (if ((mask >>> 2) &&& 1) == 1 then (tetraDot ⟨2, by omega⟩ x1 x2 x3) ^ 2 else 0) +
  (if ((mask >>> 3) &&& 1) == 1 then (tetraDot ⟨3, by omega⟩ x1 x2 x3) ^ 2 else 0)

/-- Finite test set of `6` non-zero axes/face-diagonals in `{-1, 0, 1}³ \ {0}` sufficient to witness
    that EVERY one of the `16` subsets `S ⊆ {0,1,2,3}` fails `KS₂` paving (`max(M_S, M_{S^c}) = 4 I₃`)! -/
def tetraCollisionDirs : List (Int × Int × Int) :=
  [(1, 0, 0), (0, 1, 1), (0, 1, -1), (1, 1, 0), (1, -1, 0), (1, 0, 1)]

def maskHitsFullFour (mask : Nat) : Bool :=
  tetraCollisionDirs.any fun (x1, x2, x3) =>
    let n2 := normSq3 x1 x2 x3
    (n2 > 0) &&
    ((tetraSubsetQuad mask x1 x2 x3 == 4 * n2) ||
     (tetraSubsetQuad (15 - mask) x1 x2 x3 == 4 * n2))

def allSixteenTetraSubsetsFailKS2 : Bool :=
  (List.range 16).all maskHitsFullFour

theorem pos_of_d3_sos1 (x1 x2 x3 : Int) (hne : x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0) :
    0 < (x1 - 2 * x3) * (x1 - 2 * x3) + 3 * (x2 * x2) + x3 * x3 := by
  have h1 : 0 ≤ (x1 - 2 * x3) * (x1 - 2 * x3) := sq_nonneg_int _
  have h2 : 0 ≤ x2 * x2 := sq_nonneg_int _
  have h3 : 0 ≤ x3 * x3 := sq_nonneg_int _
  by_cases hx3 : x3 = 0
  · subst hx3
    by_cases hx2 : x2 = 0
    · subst hx2
      have hx1 : x1 ≠ 0 := by
        cases hne with
        | inl h => exact h
        | inr h => cases h with
          | inl h => exact False.elim (h rfl)
          | inr h => exact False.elim (h rfl)
      have hx1pos : 0 < x1 * x1 := by
        by_cases hp : 0 < x1
        · exact Int.mul_pos hp hp
        · have hn : 0 < -x1 := by omega
          have hm : 0 < (-x1) * (-x1) := Int.mul_pos hn hn
          grind
      grind
    · have hx2pos : 0 < x2 * x2 := by
        by_cases hp : 0 < x2
        · exact Int.mul_pos hp hp
        · have hn : 0 < -x2 := by omega
          have hm : 0 < (-x2) * (-x2) := Int.mul_pos hn hn
          grind
      omega
  · have hx3pos : 0 < x3 * x3 := by
      by_cases hp : 0 < x3
      · exact Int.mul_pos hp hp
      · have hn : 0 < -x3 := by omega
        have hm : 0 < (-x3) * (-x3) := Int.mul_pos hn hn
        grind
    omega

theorem pos_of_d3_sos2 (x1 x2 x3 : Int) (hne : x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0) :
    0 < (2 * x1 + x3) * (2 * x1 + x3) + x1 * x1 + 3 * (x2 * x2) := by
  have h1 : 0 ≤ (2 * x1 + x3) * (2 * x1 + x3) := sq_nonneg_int _
  have h2 : 0 ≤ x1 * x1 := sq_nonneg_int _
  have h3 : 0 ≤ x2 * x2 := sq_nonneg_int _
  by_cases hx1 : x1 = 0
  · subst hx1
    by_cases hx2 : x2 = 0
    · subst hx2
      have hx3 : x3 ≠ 0 := by
        cases hne with
        | inl h => exact False.elim (h rfl)
        | inr h => cases h with
          | inl h => exact False.elim (h rfl)
          | inr h => exact h
      have hx3pos : 0 < x3 * x3 := by
        by_cases hp : 0 < x3
        · exact Int.mul_pos hp hp
        · have hn : 0 < -x3 := by omega
          have hm : 0 < (-x3) * (-x3) := Int.mul_pos hn hn
          grind
      grind
    · have hx2pos : 0 < x2 * x2 := by
        by_cases hp : 0 < x2
        · exact Int.mul_pos hp hp
        · have hn : 0 < -x2 := by omega
          have hm : 0 < (-x2) * (-x2) := Int.mul_pos hn hn
          grind
      omega
  · have hx1pos : 0 < x1 * x1 := by
      by_cases hp : 0 < x1
      · exact Int.mul_pos hp hp
      · have hn : 0 < -x1 := by omega
        have hm : 0 < (-x1) * (-x1) := Int.mul_pos hn hn
        grind
    omega

/-- Constructive Kadison–Singer `KS₂` Paving vs. Weaver Tetrahedron Impossibility Theorem:
    1. Parseval resolution of identity: `d3PavingSide1Quad + d3PavingSide2Quad = 4 · normSq3`,
    2. Strict two-sided `KS₂` paving: for EVERY `x ≠ (0, 0, 0)` in `ℤ³`, BOTH halves satisfy
       `normSq3 x < 2 · M_k(x) < 7 · normSq3 x < 8 · normSq3 x` (`‖M_k‖_op < 7/2 < 4`!),
    3. Weaver Tetrahedron `KS₂` Impossibility (`δ = 3/4 > 1/2`): the Hadamard tetrahedron also
       satisfies `∑_{i<4} ⟨w_i, x⟩² = 4 · normSq3`, YET `allSixteenTetraSubsetsFailKS2 = true` —
       every single `2`-partition hits `4 · normSq3` (`0%` spectral norm drop)! -/
theorem kadison_singer_cuboctahedral_two_paving_vs_weaver_tetrahedron_impossibility :
    (∀ x1 x2 x3 : Int,
      d3PavingSide1Quad x1 x2 x3 + d3PavingSide2Quad x1 x2 x3 = 4 * normSq3 x1 x2 x3) ∧
    (∀ x1 x2 x3 : Int,
      (x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0) →
      normSq3 x1 x2 x3 < 2 * d3PavingSide1Quad x1 x2 x3 ∧
      2 * d3PavingSide1Quad x1 x2 x3 < 7 * normSq3 x1 x2 x3 ∧
      normSq3 x1 x2 x3 < 2 * d3PavingSide2Quad x1 x2 x3 ∧
      2 * d3PavingSide2Quad x1 x2 x3 < 7 * normSq3 x1 x2 x3) ∧
    (∀ x1 x2 x3 : Int,
      tetraSubsetQuad 15 x1 x2 x3 = 4 * normSq3 x1 x2 x3) ∧
    allSixteenTetraSubsetsFailKS2 = true := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro x1 x2 x3
    unfold d3PavingSide1Quad d3PavingSide2Quad normSq3
    grind
  · intro x1 x2 x3 hne
    have hSum : d3PavingSide1Quad x1 x2 x3 + d3PavingSide2Quad x1 x2 x3 = 4 * normSq3 x1 x2 x3 := by
      unfold d3PavingSide1Quad d3PavingSide2Quad normSq3; grind
    have hId1 : 7 * normSq3 x1 x2 x3 - 2 * d3PavingSide1Quad x1 x2 x3 =
        (x1 - 2 * x3) * (x1 - 2 * x3) + 3 * (x2 * x2) + x3 * x3 := by
      unfold normSq3 d3PavingSide1Quad; grind
    have hId2 : 7 * normSq3 x1 x2 x3 - 2 * d3PavingSide2Quad x1 x2 x3 =
        (2 * x1 + x3) * (2 * x1 + x3) + x1 * x1 + 3 * (x2 * x2) := by
      unfold normSq3 d3PavingSide2Quad; grind
    have hPos1 : 0 < 7 * normSq3 x1 x2 x3 - 2 * d3PavingSide1Quad x1 x2 x3 := by
      rw [hId1]; exact pos_of_d3_sos1 x1 x2 x3 hne
    have hPos2 : 0 < 7 * normSq3 x1 x2 x3 - 2 * d3PavingSide2Quad x1 x2 x3 := by
      rw [hId2]; exact pos_of_d3_sos2 x1 x2 x3 hne
    omega
  · intro x1 x2 x3
    unfold tetraSubsetQuad tetraDot normSq3
    grind

/-- Universal `3`-Vector `2D` `KS₂` Orthogonal-Complement Impossibility Theorem:
    For ANY three non-zero vectors `v₀, v₁, v₂ ∈ ℤ²` and ANY `2`-coloring `c : Fin 3 → Bool`,
    at least one color class contains `≤ 1` vector `v_i = (a_i, b_i)`, so on its non-zero
    90°-rotated direction `(-b_i, a_i)` that color class evaluates to `0` and the complementary
    color class absorbs `100%` of the total frame quadratic form! -/
def dot2 (v x : Int × Int) : Int :=
  v.1 * x.1 + v.2 * x.2

def frame3TotalQuad2 (v0 v1 v2 x : Int × Int) : Int :=
  (dot2 v0 x) * (dot2 v0 x) + (dot2 v1 x) * (dot2 v1 x) + (dot2 v2 x) * (dot2 v2 x)

def frame3ColorQuad2 (v0 v1 v2 : Int × Int) (c : Fin 3 → Bool) (col : Bool) (x : Int × Int) : Int :=
  (if c ⟨0, by omega⟩ == col then (dot2 v0 x) * (dot2 v0 x) else 0) +
  (if c ⟨1, by omega⟩ == col then (dot2 v1 x) * (dot2 v1 x) else 0) +
  (if c ⟨2, by omega⟩ == col then (dot2 v2 x) * (dot2 v2 x) else 0)

theorem three_vector_two_dim_ks2_orthogonal_barrier
    (v0 v1 v2 : Int × Int)
    (hv0 : v0 ≠ (0, 0)) (hv1 : v1 ≠ (0, 0)) (hv2 : v2 ≠ (0, 0))
    (c : Fin 3 → Bool) :
    ∃ (col : Bool) (x : Int × Int),
      x ≠ (0, 0) ∧
      frame3ColorQuad2 v0 v1 v2 c col x = frame3TotalQuad2 v0 v1 v2 x := by
  have rot_ne : ∀ v : Int × Int, v ≠ (0, 0) → (-v.2, v.1) ≠ (0, 0) := by
    intro (a, b) hne hzero
    injection hzero with h1 h2
    apply hne
    have hb : b = 0 := by omega
    subst hb h2
    rfl
  by_cases hc01 : c ⟨0, by omega⟩ = c ⟨1, by omega⟩
  · by_cases hc02 : c ⟨0, by omega⟩ = c ⟨2, by omega⟩
    · -- All 3 vectors have the same color `c 0`: pick `(1, 0) ≠ (0, 0)`!
      refine ⟨c ⟨0, by omega⟩, (1, 0), by decide, ?_⟩
      unfold frame3ColorQuad2 frame3TotalQuad2
      rw [← hc01, ← hc02]
      cases h : c ⟨0, by omega⟩ <;> simp
    · -- `v0, v1` share `c 0`, while `v2` is alone in `!c 0`: test `x = (-v2.2, v2.1)`!
      refine ⟨c ⟨0, by omega⟩, (-v2.2, v2.1), rot_ne v2 hv2, ?_⟩
      unfold frame3ColorQuad2 frame3TotalQuad2 dot2
      rw [← hc01]
      cases h0 : c ⟨0, by omega⟩ <;> cases h2 : c ⟨2, by omega⟩
      · exact False.elim (hc02 (by rw [h0, h2]))
      · simp; grind
      · simp; grind
      · exact False.elim (hc02 (by rw [h0, h2]))
  · by_cases hc02 : c ⟨0, by omega⟩ = c ⟨2, by omega⟩
    · -- `v0, v2` share `c 0`, while `v1` is alone: test `x = (-v1.2, v1.1)`!
      refine ⟨c ⟨0, by omega⟩, (-v1.2, v1.1), rot_ne v1 hv1, ?_⟩
      unfold frame3ColorQuad2 frame3TotalQuad2 dot2
      rw [← hc02]
      cases h0 : c ⟨0, by omega⟩ <;> cases h1 : c ⟨1, by omega⟩
      · exact False.elim (hc01 (by rw [h0, h1]))
      · simp; grind
      · simp; grind
      · exact False.elim (hc01 (by rw [h0, h1]))
    · -- `v0` differs from both `v1` and `v2`, so `v1` and `v2` share `c 1` while `v0` is alone!
      refine ⟨c ⟨1, by omega⟩, (-v0.2, v0.1), rot_ne v0 hv0, ?_⟩
      unfold frame3ColorQuad2 frame3TotalQuad2 dot2
      cases h0 : c ⟨0, by omega⟩ <;> cases h1 : c ⟨1, by omega⟩ <;> cases h2 : c ⟨2, by omega⟩
      · exact False.elim (hc01 (by rw [h0, h1]))
      · exact False.elim (hc01 (by rw [h0, h1]))
      · exact False.elim (hc02 (by rw [h0, h2]))
      · simp; grind
      · simp; grind
      · exact False.elim (hc02 (by rw [h0, h2]))
      · exact False.elim (hc01 (by rw [h0, h1]))
      · exact False.elim (hc01 (by rw [h0, h1]))

end CommonGround.UniversalQueryCompression.BatsonSpielmanKadisonSinger
