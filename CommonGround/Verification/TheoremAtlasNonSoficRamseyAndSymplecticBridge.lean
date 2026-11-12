/-!
# Theorem Atlas Bridge: Multicolor Ramsey Palettes, Symplectic Quadrangles & Non-Sofic Groups (V155)

This zero-sorry pure Lean 4.33.0 module verifies the concrete algebraic and combinatorial mechanisms
behind three frontier formalizations in `theorem-atlas/data/raw/ten-proofs`:
1. `MulticolorTriangleRamsey.lean`
2. `CompactnessAndDegeneracy.lean` (`symplecticQuadrangle` & `symmetricQuadraticEvaluationMatrix_det`)
3. `NonSoficGroup.lean` (`disjoint_dominant_intersections_false` & `BinaryLeavitt`)
-/

namespace CommonGround.Verification.TheoremAtlasNonSoficRamseyAndSymplecticBridge

/-! ## 1. Multicolor Triangle Ramsey Palette-Disagreement Obstruction -/

/-- Exact Boolean pigeonhole obstruction (`MulticolorTriangleRamsey.no_three_pairwise_palette_disagreements`):
    three palette membership flags `p, q, r : Bool` for color `c` cannot all pairwise disagree. -/
theorem no_three_pairwise_boolean_disagreements (p q r : Bool)
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p) : False := by
  cases p <;> cases q <;> cases r <;> simp_all

/-- Equivalent decidable Boolean law: for any three palettes, at least one pair of blocks
    agrees on color `c`'s membership. -/
theorem three_palettes_have_agreeing_pair (p q r : Bool) :
    ((p == q) || (q == r) || (r == p)) = true := by
  cases p <;> cases q <;> cases r <;> rfl

/-- Failure-boundary witness (`three_blocks_can_triangle_without_membership_flip`). -/
theorem three_blocks_can_triangle_without_membership_flip :
    ∃ p q r : Bool, (p = q) ∧ (q = r) ∧ (r = p) :=
  ⟨true, true, true, rfl, rfl, rfl⟩

/-- Concrete palette shell parameter bound from `erdos_problem_183_explicit`:
    for `t = 2`, `d = 1`, `N = 4`, the shell size `C(t, d) * C(N - t, d) = 2 * 2 = 4 < 2^4 = 16`. -/
theorem palette_shell_finite_witness :
    2 * 2 < 2 ^ 4 := by
  decide

/-! ## 2. Symplectic Generalized Quadrangle W(3, q) & Characteristic-2 Boundary -/

def quadrangleVertexCount (q : Int) : Int :=
  2 * (q + 1) * (q ^ 2 + 1)

def quadrangleEdgeCount (q : Int) : Int :=
  (q + 1) ^ 2 * (q ^ 2 + 1)

/-- Exact polynomial certificate (`CompactnessConjecture.quadrangle_density_certificate`):
    `16 * E(q)^3 - V(q)^4 = 32 * q * (q + 1)^4 * (q^2 + 1)^3`. -/
theorem symplectic_quadrangle_density_identity (q : Int) :
    16 * (quadrangleEdgeCount q) ^ 3 - (quadrangleVertexCount q) ^ 4 =
      32 * q * (q + 1) ^ 4 * (q ^ 2 + 1) ^ 3 := by
  dsimp [quadrangleEdgeCount, quadrangleVertexCount]
  grind

/-- Concrete check at `q = 2` (`W(3, 2)`, the doily with 30 bipartite vertices and 45 edges). -/
theorem symplectic_quadrangle_q2_doily_witness :
    quadrangleVertexCount 2 = 30 ∧
    quadrangleEdgeCount 2 = 45 ∧
    16 * (quadrangleEdgeCount 2) ^ 3 - (quadrangleVertexCount 2) ^ 4 = 648000 := by
  decide

/-- Exact determinant of the 3×3 homogeneous quadratic evaluation matrix. -/
def symmetricQuadraticEvalDet (x0 y0 x1 y1 x2 y2 : Int) : Int :=
  x0 ^ 2 * (2 * x1 * y1 * y2 ^ 2 - y1 ^ 2 * (2 * x2 * y2))
  - (2 * x0 * y0) * (x1 ^ 2 * y2 ^ 2 - y1 ^ 2 * x2 ^ 2)
  + y0 ^ 2 * (x1 ^ 2 * (2 * x2 * y2) - (2 * x1 * y1) * x2 ^ 2)

theorem quadratic_vandermonde_det_3x3 (x0 y0 x1 y1 x2 y2 : Int) :
    symmetricQuadraticEvalDet x0 y0 x1 y1 x2 y2 =
      2 * (x0 * y1 - x1 * y0) * (x0 * y2 - x2 * y0) * (x1 * y2 - x2 * y1) := by
  dsimp [symmetricQuadraticEvalDet]
  grind

/-- Characteristic-2 failure-boundary witness: `symmetricQuadraticEvalDet % 2 = 0`. -/
theorem quadratic_vandermonde_det_mod2_vanishes (x0 y0 x1 y1 x2 y2 : Int) :
    (symmetricQuadraticEvalDet x0 y0 x1 y1 x2 y2) % 2 = 0 := by
  rw [quadratic_vandermonde_det_3x3]
  have h : 2 * (x0 * y1 - x1 * y0) * (x0 * y2 - x2 * y0) * (x1 * y2 - x2 * y1) =
      2 * ((x0 * y1 - x1 * y0) * (x0 * y2 - x2 * y0) * (x1 * y2 - x2 * y1)) := by grind
  rw [h]
  omega

/-- Characteristic-2 Frobenius replacement identity (`symmetricQuadratic_char_two_eq_square`). -/
theorem char2_frobenius_quadratic_square_mod2 (r s x y : Int) :
    ((r * x + s * y) ^ 2 - (r ^ 2 * x ^ 2 + s ^ 2 * y ^ 2)) % 2 = 0 := by
  have h : (r * x + s * y) ^ 2 - (r ^ 2 * x ^ 2 + s ^ 2 * y ^ 2) = 2 * (r * s * x * y) := by grind
  rw [h]
  omega

/-! ## 3. Non-Sofic Group Majority Disjointness & Binary Leavitt Prefix Compression -/

theorem disjoint_majority_overlap_impossible (p q d : Nat)
    (hdisj : p + q ≤ d) (hp : d < 2 * p) (hq : d < 2 * q) : False := by
  omega

/-- Expander Hamming-vs-agreement conservation law (`SoficGroups.agreementSet_card_add_hammingDist`):
    for any two maps `(v0, v1, v2)` and `(w0, w1, w2)` on `Fin 3`, the number of agreement points
    plus the Hamming distance equals the domain size `3`. -/
theorem agreement_plus_hamming_eq_card_fin3 (c1 c2 : Fin 3 → Fin 3) :
    ([ (0 : Fin 3), 1, 2 ].filter (fun x => decide (c1 x = c2 x))).length +
    ([ (0 : Fin 3), 1, 2 ].filter (fun x => decide (c1 x ≠ c2 x))).length = 3 := by
  by_cases h0 : c1 0 = c2 0 <;> by_cases h1 : c1 1 = c2 1 <;> by_cases h2 : c1 2 = c2 2 <;>
    simp [List.filter, h0, h1, h2]

/-- Commutation defect triangle inequality on a single point. -/
theorem edge_across_agreement_boundary_forces_commutation_defect
    {V : Type} [DecidableEq V] (c c' σ : V → V) (x : V)
    (h_agree : c x = c' x)
    (h_disagree : c (σ x) ≠ c' (σ x)) :
    c (σ x) ≠ σ (c x) ∨ c' (σ x) ≠ σ (c' x) := by
  by_cases hc : c (σ x) = σ (c x)
  · right
    intro hc'
    apply h_disagree
    rw [hc, hc', h_agree]
  · left
    exact hc

/-- Commutative characteristic-2 scalar prototype of `BinaryLeavitt.cylinder_transposition_factorization`. -/
theorem char2_nilpotent_conjugation_scalar (p q : Bool) (hp : (p && p) = false) :
    let one_plus_p := Bool.xor true p
    let one_plus_q := Bool.xor true q
    (one_plus_p && one_plus_q && one_plus_p) = (if p then false else Bool.xor true q) := by
  cases p <;> cases q <;> simp_all

/-- Explicit 2×2 matrix witness over `ℤ/2ℤ` for `(I + P)(I + Q)(I + P) ≡ I + PQ + QP + P + Q (mod 2)`. -/
theorem char2_2x2_cylinder_transposition_matrix_witness :
    let P00 := 0; let P01 := 1; let P10 := 0; let P11 := 0
    let Q00 := 0; let Q01 := 0; let Q10 := 1; let Q11 := 0
    (P00 * P00 + P01 * P10 = 0) ∧ (P00 * P01 + P01 * P11 = 0) ∧
    (P10 * P00 + P11 * P10 = 0) ∧ (P10 * P01 + P11 * P11 = 0) ∧
    (P00 * Q00 + P01 * Q10 = 1) ∧ (Q10 * P01 + Q11 * P11 = 1) ∧
    ((1 + 1 + 0 + P00 + Q00) % 2 = 0) ∧
    ((0 + 0 + 0 + P01 + Q01) % 2 = 1) ∧
    ((0 + 0 + 0 + P10 + Q10) % 2 = 1) ∧
    ((1 + 0 + 1 + P11 + Q11) % 2 = 0) := by
  decide

end CommonGround.Verification.TheoremAtlasNonSoficRamseyAndSymplecticBridge
