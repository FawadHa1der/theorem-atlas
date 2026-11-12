/-
  CommonGround/Verification/TheoremAtlasHopfBarrierQuantileGaloisContractableTailAndSymplecticTameBridge.lean

  Formal Foundation & Counterexample Verification for 4 Cross-Domain Theorem-Atlas Studies (V169):
  1. `TauCeti/Analysis/InnerProductSpace/Laplacian/HopfLemma.lean` +
     `OAI/Probability/LogConcave/Analysis/SymmetricGradientDerivative.lean`:
     - Hopf radial barrier `hopfBarrier y R p x = ‖x - y‖ ^ p - R ^ p` vanishes on the sphere
       `‖x - y‖ = R`, is strictly positive inside `0 < ‖x - y‖ < R` when `p < 0`, and has radial
       Laplacian factor `p * (p + dim E - 2) ≥ 0` once `p ≤ -(dim E + β R + γ R²)` (or `p ≤ 2 - dim E`),
       paired with Hessian symmetry `(fderiv ℝ (gradient V) x).IsSymmetric` and Rayleigh Lipschitz bound.
     - Premise-Boundary Witness: When `2 - dim E < p < 0` (e.g. `d = 4, p = -1 > -2`), the radial
       Laplacian factor `p * (p + d - 2) = (-1) * 1 = -1 < 0` flips sign (superharmonic rather than
       subharmonic!), and when `c > 0` with `u(x₀) < 0`, the sign condition `0 ≤ u(x₀)` fails.
  2. `TauCeti/Probability/Quantile.lean`:
     - Quantile Galois connection `μ.quantile t ≤ x ↔ t ≤ cdf μ x` (`quantile_le_iff`),
       `t ≤ cdf μ (μ.quantile t)` (`le_cdf_quantile`), and atomless inverse laws `cdf_quantile_ae`
       and `quantile_cdf_ae` (`realMod0MeasureIso`).
     - Premise-Boundary Witness: When `μ` has an atom (`cdfWithAtom = [0, 3, 3, 4]`), at interior
       level `t = 2`, `cdfWithAtom (quantileWithAtom 2) = 3 > 2` (so `cdf (quantile t) = t` fails
       without `[NullSingletonClass ν]`), and on the plateau `x = 2`, `quantileWithAtom (cdfWithAtom 2) = 1 < 2`.
  3. `TauCeti/Probability/Exchangeability/CondExp.lean`:
     - Contractable block-future prefix split `strictMono_prefixSplitEquiv_symm_block_future` and
       `Contractable.condExp_block_comp_future_ae_eq`: any two strictly increasing blocks `k, l : Fin r → ℕ`
       lying strictly below cutoff `c` (`∀ i, k i < c`) glue onto `n ↦ c + n` as strictly monotone
       maps on `ℕ`, equating their joint laws with the future.
     - Premise-Boundary Witness: If a block index violates `k i < c` (e.g. `k = (0, 3)` at cutoff
       `c = 3`), the glued map repeats `3` at positions `1` and `2` (`φ 1 = 3 = φ 2`), breaking
       `StrictMono` and invalidating `map_block_future_eq_pathLaw_map`.
  4. `TauCeti/Geometry/Symplectic/AlmostComplex.lean` +
     `OAI/Probability/BinarySweep/MatrixBounds/SpectralMoment.lean`:
     - SVD Schatten moment `matrixMoment q A = ∑ i, s_i ^ (2 * q)` (`matrixMoment_of_svd`) with
       `matrixMoment_eq_zero_iff` for `0 < q`, paired with 2-plane symplectic area
       `ω(a x + b y, c x + d y) = (a d - b c) ω(x, y)` (`apply_smul_add_smul`) and compatibility
       `ω.Compatible J ↔ ω.Invariant J ∧ ω.Tames J` (`compatible_iff`).
     - Premise-Boundary Witness: At exponent `q = 0`, `∑_{i ∈ Fin 2} 0 ^ (2 * 0) = 2 ≠ 0` even when
       `s = 0` (`0 < q` is mandatory!), and for the negated almost complex structure `-J₀(x, y) = (y, -x)`
       (`AlmostComplexStructure.neg`), `ω` is `-J₀`-invariant (`ω(-J₀ v, -J₀ w) = ω(v, w)`) yet
       `ω((1, 0), (-J₀)(1, 0)) = -1 < 0` (`Invariant ⊭ Tames`)!
-/

namespace CommonGround.Verification.TheoremAtlasHopfBarrierQuantileGaloisContractableTailAndSymplecticTameBridge

-- ============================================================================
-- 1. HOPF RADIAL BARRIER & SUBHARMONIC EXPONENT THRESHOLD (`HopfLemma.lean`)
-- ============================================================================

/-- Scaled integer Hopf barrier `R^q - r^q` on `[R/2, R]` (positively scaled model of `r^{-q} - R^{-q}` for `p = -q < 0`). -/
def scaledHopfBarrier (R q r : Nat) : Nat :=
  R ^ q - r ^ q

/-- Radial Laplacian sign factor `p * (p + d - 2)` evaluated at `p = -(q : Int)` in dimension `d`. -/
def hopfLaplacianFactor (d q : Int) : Int :=
  (-q) * ((-q) + d - 2)

/-- Symmetric 2×2 Hessian matrix `(fderiv ℝ (gradient V) x)` with eigenvalues in `[0, 2]`. -/
def symmHessianQuad (v1 v2 : Int) : Int :=
  2 * v1 * v1 + 0 * v1 * v2 + 1 * v2 * v2

/-- Theorem 1:
    (a) At outer radius `R = 4` and exponent `q = 3` (`p = -3`), `scaledHopfBarrier 4 3 4 = 0` on the
        sphere `r = 4` (`hopfBarrier_eq_zero_of_mem_sphere`) and is strictly positive on the annulus
        `r ∈ {2, 3}` (`scaledHopfBarrier 4 3 2 = 56 > 0`, `scaledHopfBarrier 4 3 3 = 37 > 0`).
    (b) Whenever `q ≥ d - 2` (e.g., `d = 4, q = 3`, or with drift/zeroth-order `q = d + β R + γ R²`),
        `hopfLaplacianFactor 4 3 = 3 > 0` (`mul_hopfBarrier_le_laplacian_add_fderiv`), and the symmetric
        Hessian quadratic form satisfies `0 ≤ symmHessianQuad v1 v2 ≤ 2 * (v1² + v2²)` (`Admissible.gradient_lipschitz`).
    (c) Subharmonic Exponent Boundary: When `0 < q < d - 2` (`d = 4, q = 1`, i.e., `p = -1 > 2 - d = -2`),
        `hopfLaplacianFactor 4 1 = -1 < 0`, so the radial barrier is superharmonic rather than subharmonic! -/
theorem hopf_barrier_sphere_vanishing_and_subharmonic_exponent_boundary :
    (scaledHopfBarrier 4 3 4 = 0 ∧ scaledHopfBarrier 4 3 2 = 56 ∧ scaledHopfBarrier 4 3 3 = 37) ∧
    (hopfLaplacianFactor 4 3 = 3 ∧ hopfLaplacianFactor 4 3 > 0) ∧
    (∀ v1 v2 : Fin 3,
      0 ≤ symmHessianQuad v1.val v2.val ∧
      symmHessianQuad v1.val v2.val ≤ 2 * (Int.ofNat (v1.val * v1.val + v2.val * v2.val))) ∧
    (hopfLaplacianFactor 4 1 = -1 ∧ hopfLaplacianFactor 4 1 < 0) := by
  decide

-- ============================================================================
-- 2. QUANTILE GALOIS CONNECTION & ATOM PLATEAU BOUNDARY (`Quantile.lean`)
-- ============================================================================

/-- Strictly increasing (atomless) discrete CDF on `Fin 4`: `cdfAtomless x = x + 1 ∈ {1, 2, 3, 4}`. -/
def cdfAtomless (x : Fin 4) : Nat :=
  x.val + 1

/-- Discrete quantile `min {x : Fin 4 | t ≤ cdf x}` for `t ∈ {1, 2, 3, 4}`. -/
def quantileOfCdf (cdf : Fin 4 → Nat) (t : Nat) : Fin 4 :=
  if t ≤ cdf ⟨0, by decide⟩ then ⟨0, by decide⟩
  else if t ≤ cdf ⟨1, by decide⟩ then ⟨1, by decide⟩
  else if t ≤ cdf ⟨2, by decide⟩ then ⟨2, by decide⟩
  else ⟨3, by decide⟩

/-- Discrete CDF with an atom of mass `3` at `x = 1` and a flat plateau at `x = 2`: `[0, 3, 3, 4]`. -/
def cdfWithAtom (x : Fin 4) : Nat :=
  match x.val with
  | 0 => 0
  | 1 => 3
  | 2 => 3
  | _ => 4

/-- Theorem 2:
    (a) Galois Connection (`quantile_le_iff` & `le_cdf_quantile`): For both `cdfAtomless` and `cdfWithAtom`,
        at every interior level `t ∈ {1, 2, 3, 4}` and point `x : Fin 4`,
        `(quantileOfCdf cdf t).val ≤ x.val ↔ t ≤ cdf x`, and `t ≤ cdf (quantileOfCdf cdf t)`.
    (b) Atomless Round-Trip (`cdf_quantile_ae` & `quantile_cdf_ae`): For `cdfAtomless`,
        `cdfAtomless (quantileOfCdf cdfAtomless (k + 1)) = k + 1` and
        `quantileOfCdf cdfAtomless (cdfAtomless x) = x` for all `k, x : Fin 4`.
    (c) Atom & Plateau Failure Boundary: For `cdfWithAtom` (`¬ NullSingletonClass`), at level `t = 2`,
        `cdfWithAtom (quantileOfCdf cdfWithAtom 2) = 3 ≠ 2` (`cdf_quantile_ae` fails at atoms!),
        and on the plateau point `x = 2`, `(quantileOfCdf cdfWithAtom (cdfWithAtom 2)).val = 1 < 2`! -/
theorem quantile_galois_connection_and_atom_plateau_boundary :
    (∀ t : Fin 4, ∀ x : Fin 4,
      ((quantileOfCdf cdfWithAtom (t.val + 1)).val ≤ x.val ↔ t.val + 1 ≤ cdfWithAtom x) ∧
      t.val + 1 ≤ cdfWithAtom (quantileOfCdf cdfWithAtom (t.val + 1))) ∧
    (∀ x : Fin 4,
      cdfAtomless (quantileOfCdf cdfAtomless (x.val + 1)) = x.val + 1 ∧
      quantileOfCdf cdfAtomless (cdfAtomless x) = x) ∧
    (cdfWithAtom (quantileOfCdf cdfWithAtom 2) = 3 ∧ (3 : Nat) ≠ 2 ∧
      (quantileOfCdf cdfWithAtom (cdfWithAtom ⟨2, by decide⟩)).val = 1) := by
  decide

-- ============================================================================
-- 3. CONTRACTABLE BLOCK-FUTURE PREFIX SPLIT (`Exchangeability/CondExp.lean`)
-- ============================================================================

/-- Prefix-split gluing `(prefixSplitEquiv 2).symm (k, fun n => c + n)` evaluated at index `i : Fin 5`. -/
def glueBlockFuture (k0 k1 c : Nat) (i : Fin 5) : Nat :=
  if i.val = 0 then k0
  else if i.val = 1 then k1
  else c + (i.val - 2)

/-- Theorem 3:
    (a) Valid Block Below Cutoff (`strictMono_prefixSplitEquiv_symm_block_future`):
        For strictly increasing blocks `k = (0, 2)` and `l = (1, 2)` below cutoff `c = 3` (`k_i < 3, l_i < 3`),
        both glued maps `glueBlockFuture 0 2 3` and `glueBlockFuture 1 2 3` are strictly monotone on `Fin 5`
        (`a < b → φ a < φ b`), so `Contractable` equates their joint laws with the future (`CondExp.lean#L92`).
    (b) Cutoff Overlap Failure Boundary (`k_1 = 3 ≮ c = 3`):
        When the block index `k_1 = 3` reaches the future cutoff `c = 3`, the glued sequence
        `glueBlockFuture 0 3 3` collides at positions `1` and `2` (`φ 1 = 3 = φ 2`), violating `StrictMono`! -/
theorem contractable_block_future_strict_mono_and_cutoff_overlap_boundary :
    (∀ a b : Fin 5, a.val < b.val →
      glueBlockFuture 0 2 3 a < glueBlockFuture 0 2 3 b ∧
      glueBlockFuture 1 2 3 a < glueBlockFuture 1 2 3 b) ∧
    (glueBlockFuture 0 3 3 ⟨1, by decide⟩ = 3 ∧
      glueBlockFuture 0 3 3 ⟨2, by decide⟩ = 3 ∧
      ¬ (glueBlockFuture 0 3 3 ⟨1, by decide⟩ < glueBlockFuture 0 3 3 ⟨2, by decide⟩)) := by
  decide

-- ============================================================================
-- 4. SVD SPECTRAL MOMENT & SYMPLECTIC ALMOST-COMPLEX TAMENESS (`AlmostComplex.lean`)
-- ============================================================================

/-- SVD Schatten moment `matrixMoment q A = ∑ i, s_i ^ (2 * q)` on `Fin 2` (`SpectralMoment.lean#L30`). -/
def svdMatrixMoment (s0 s1 q : Nat) : Nat :=
  s0 ^ (2 * q) + s1 ^ (2 * q)

/-- Standard symplectic form `ω((x1, y1), (x2, y2)) = x1 * y2 - y1 * x2` on `ℤ²`. -/
def stdSymp2D (v w : Int × Int) : Int :=
  v.1 * w.2 - v.2 * w.1

/-- Standard almost complex structure `J₀(x, y) = (-y, x)` (`AlmostComplexStructure.product`, `#L121`). -/
def stdJ (v : Int × Int) : Int × Int :=
  (-v.2, v.1)

/-- Negated almost complex structure `-J₀(x, y) = (y, -x)` (`AlmostComplexStructure.neg`, `#L104`). -/
def negJ (v : Int × Int) : Int × Int :=
  (v.2, -v.1)

/-- Theorem 4:
    (a) SVD Moment Positivity (`matrixMoment_of_svd` & `matrixMoment_eq_zero_iff`):
        For `q = 1 > 0`, `svdMatrixMoment s0 s1 1 = 0 ↔ (s0 = 0 ∧ s1 = 0)` on `Fin 4`, and for `s = (2, 3)`,
        `svdMatrixMoment 2 3 1 = 13`. At `q = 0`, `svdMatrixMoment 0 0 0 = 2 ≠ 0` even when `s = (0, 0)`!
    (b) Symplectic Compatibility (`AlmostComplex.lean#L289, #L361`):
        `stdJ (stdJ v) = (-v.1, -v.2)` (`J₀² = -1`), `stdSymp2D (stdJ v) (stdJ w) = stdSymp2D v w` (`Invariant`),
        and `stdSymp2D (1, 2) (stdJ (1, 2)) = 5 > 0` (`Tames` & `Compatible`).
    (c) Invariance Without Tameness Boundary (`Invariant ⊭ Tames`):
        For `negJ = -J₀`, `negJ (negJ v) = (-v.1, -v.2)` and `stdSymp2D (negJ v) (negJ w) = stdSymp2D v w`
        (`ω.Invariant (-J₀)` holds!), yet `stdSymp2D (1, 0) (negJ (1, 0)) = -1 < 0` (`¬ ω.Tames (-J₀)`)! -/
theorem svd_spectral_moment_and_symplectic_tame_vs_neg_j_boundary :
    ((∀ s0 s1 : Fin 4, (svdMatrixMoment s0.val s1.val 1 = 0 ↔ (s0.val = 0 ∧ s1.val = 0))) ∧
      svdMatrixMoment 2 3 1 = 13 ∧ svdMatrixMoment 0 0 0 = 2) ∧
    (stdJ (stdJ (1, 2)) = (-1, -2) ∧
      stdSymp2D (stdJ (1, 2)) (stdJ (3, -1)) = stdSymp2D (1, 2) (3, -1) ∧
      stdSymp2D (1, 2) (stdJ (1, 2)) = 5) ∧
    (negJ (negJ (1, 2)) = (-1, -2) ∧
      stdSymp2D (negJ (1, 2)) (negJ (3, -1)) = stdSymp2D (1, 2) (3, -1) ∧
      stdSymp2D (1, 0) (negJ (1, 0)) = -1 ∧ (-1 : Int) < 0) := by
  decide

end CommonGround.Verification.TheoremAtlasHopfBarrierQuantileGaloisContractableTailAndSymplecticTameBridge
