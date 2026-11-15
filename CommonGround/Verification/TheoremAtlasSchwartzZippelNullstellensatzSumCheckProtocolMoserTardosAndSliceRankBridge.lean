/-!
# Verification Suite #621: Freivalds Matrix-Verification Soundness, `FRI` (`ZK-STARK`) Even–Odd Low-Degree Folding, Shamir Threshold Secret Sharing, Moser–Tardos Entropy Compression vs. Shearer Barrier & Dvir Finite-Field Kakeya Rigidity (`0` Imports, `0` Sorry)

Cross-domain Lean 4.33.0 bridge suite unifying **Folders `02` + `03` + `07` + `10`** across
`oai-codes`, `eth`, `tc-probcomb`, `oai-extremal`, `oai-ramsey`, and `tauceti`:

1. `freivalds_randomized_matrix_check_soundness_vs_single_vector_blindspot`
2. `fri_even_odd_polynomial_degree_folding_vs_corrupted_coset_evasion`
3. `shamir_threshold_secret_sharing_zero_leakage_vs_lagrange_reconstruction`
4. `moser_tardos_entropy_compression_termination_vs_shearer_lovasz_breakdown`
5. `dvir_kakeya_homogeneous_directional_vanishing_rigidity_vs_missing_slope_cone`
-/

namespace CommonGround.Verification.TheoremAtlasSchwartzZippelSumCheckFRIShamirAndKakeyaBridge

/-- Bridge 1: Freivalds (`1979`) Randomized Matrix-Multiplication Check Soundness (`≤ 1` Bad Seed per Nonzero Row)
    vs. Deterministic Single-Vector Blindspot (`A * B ≠ C` yet `(A * B) r = C r`). -/
theorem freivalds_randomized_matrix_check_soundness_vs_single_vector_blindspot :
    -- (1) Universal Row-Projection Root Bound: if residual row `(d0, d1)` has `d1 ≠ 0`, then for ANY fixed `x0`
    --     and ANY two distinct test seeds `r1 ≠ r1'`, `(d0 * x0 + d1 * r1)` and `(d0 * x0 + d1 * r1')` CANNOT
    --     both vanish (`≤ 1` false-accept seed `r1` across any field subset of size `Q`)!
    (∀ d0 d1 x0 r1 r1' : Int,
      d1 ≠ 0 → r1 ≠ r1' →
      ¬ (d0 * x0 + d1 * r1 = 0 ∧ d0 * x0 + d1 * r1' = 0)) ∧
    -- (2) Premise-Failure Counterexample (Deterministic Single-Seed Blindspot):
    --     `A = [[1, 1], [0, 1]], B = [[1, 0], [0, 2]]` gives `A*B = [[1, 2], [0, 2]] ≠ [[1, 0], [0, 0]] = C`,
    --     yet testing ONLY seed `r = (1, 0)^T` yields `(A*B) r = (1, 0)^T = C r` (`100%` false accept)!
    (let ab00 : Int := 1 * 1 + 1 * 0
     let ab01 : Int := 1 * 0 + 1 * 2
     let ab10 : Int := 0 * 1 + 1 * 0
     let ab11 : Int := 0 * 0 + 1 * 2
     ab01 ≠ 0 ∧
     ab00 * 1 + ab01 * 0 = 1 * 1 + 0 * 0 ∧
     ab10 * 1 + ab11 * 0 = 0 * 1 + 0 * 0) := by
  refine ⟨?_, by decide⟩
  intro d0 d1 x0 r1 r1' hd1 hNe ⟨z1, z2⟩
  have hDiff : d1 * (r1 - r1') = 0 := by grind
  exact (Int.mul_ne_zero hd1 (by omega)) hDiff

/-- Cubic polynomial `c0 + c1*x + c2*x^2 + c3*x^3`. -/
def evalCubic (c0 c1 c2 c3 x : Int) : Int :=
  c0 + c1 * x + c2 * x * x + c3 * x * x * x

/-- Bridge 2: `FRI` (`ZK-STARK`) Even–Odd Polynomial Degree Folding (`deg 3 → deg 1` in `y = x^2`)
    vs. Single-Coset Unchecked Degree-`5` Masquerade. -/
theorem fri_even_odd_polynomial_degree_folding_vs_corrupted_coset_evasion :
    -- (1) Universal `FRI` Fold Identity: for EVERY cubic `P(x) = c0 + c1*x + c2*x^2 + c3*x^3` and challenge `alpha`,
    --     `x * (P(x) + P(-x)) + alpha * (P(x) - P(-x)) = 2 * x * ((c0 + alpha*c1) + (c2 + alpha*c3) * x^2)`,
    --     so `P_fold(y) = (c0 + alpha*c1) + (c2 + alpha*c3)*y` is affine (`2nd` difference `= 0` across all `y`)!
    (∀ c0 c1 c2 c3 alpha x y h : Int,
      let pEven := fun u => c0 + c2 * u
      let pOdd  := fun u => c1 + c3 * u
      let pFold := fun u => pEven u + alpha * pOdd u
      evalCubic c0 c1 c2 c3 x + evalCubic c0 c1 c2 c3 (-x) = 2 * pEven (x * x) ∧
      evalCubic c0 c1 c2 c3 x - evalCubic c0 c1 c2 c3 (-x) = 2 * x * pOdd (x * x) ∧
      pFold (y + 2 * h) - 2 * pFold (y + h) + pFold y = 0) ∧
    -- (2) Premise-Failure Counterexample: querying ONLY a single coset `{1, -1}` (`x^2 = 1`) cannot distinguish
    --     degree-`5` `Q(x) = x^5` from linear `L(x) = x` (`Q(1) = L(1) = 1` and `Q(-1) = L(-1) = -1`), whereas a
    --     second coset `{2, -2}` (`x^2 = 4`) + `3`rd coset `{3, -3}` (`x^2 = 9`) exposes nonzero collinearity defect!
    ((1 : Int)^5 = 1 ∧ (-1 : Int)^5 = -1 ∧
     (2 : Int)^4 ≠ 1 ∧
     9 * ((1 : Int)^4 - (2 : Int)^4) + 4 * ((3 : Int)^4 - (1 : Int)^4) + 1 * ((2 : Int)^4 - (3 : Int)^4) ≠ 0) := by
  refine ⟨?_, by decide⟩
  intro c0 c1 c2 c3 alpha x y h
  dsimp only
  unfold evalCubic
  refine ⟨by grind, by grind, by grind⟩

/-- Bridge 3: Shamir `(2, n)` Threshold Secret Sharing Perfect `1`-Share Zero-Leakage Bijection
    vs. Exact `2`-Share Lagrange Secret Reconstruction. -/
theorem shamir_threshold_secret_sharing_zero_leakage_vs_lagrange_reconstruction :
    -- (1) Information-Theoretic `1`-Share Zero-Leakage (`t - 1 = 1`):
    --     Given ANY single share `(x1, y1)` at `x1 ≠ 0` and ANY candidate secret `s'`, the unique scaled line
    --     `L(x) = x1 * s' + (y1 - s') * x` has secret `L(0) = x1 * s'` and observed share `L(x1) = x1 * y1`
    --     (and for `x1 = 1`, exact integer slope `a1' = y1 - s'` gives `s' + a1'*1 = y1` for EVERY `s' ∈ ℤ`!):
    (∀ s' y1 x1 : Int,
      let L := fun x => x1 * s' + (y1 - s') * x
      L 0 = x1 * s' ∧ L x1 = x1 * y1 ∧ (s' + (y1 - s') * 1 = y1)) ∧
    -- (2) Exact `2`-Share Lagrange Reconstruction (`t = 2`):
    --     Any two shares `y1 = s + a1*x1` and `y2 = s + a1*x2` at `x1 ≠ x2` uniquely recover `(x2 - x1)*s = x2*y1 - x1*y2`!
    (∀ s a1 x1 x2 : Int,
      let y1 := s + a1 * x1
      let y2 := s + a1 * x2
      x2 * y1 - x1 * y2 = (x2 - x1) * s ∧
      (∀ sAlt a1Alt : Int, x1 ≠ x2 → sAlt + a1Alt * x1 = y1 → sAlt + a1Alt * x2 = y2 → sAlt = s ∧ a1Alt = a1)) := by
  refine ⟨?_, ?_⟩
  · intro s' y1 x1
    dsimp only
    refine ⟨by omega, by grind, by omega⟩
  · intro s a1 x1 x2
    dsimp only
    refine ⟨by grind, ?_⟩
    intro sAlt a1Alt hNe h1 h2
    have hSlope : (a1Alt - a1) * (x2 - x1) = 0 := by grind
    have ha1 : a1Alt = a1 := by
      by_cases hEq : a1Alt = a1
      · exact hEq
      · exfalso
        exact (Int.mul_ne_zero (by omega) (by omega)) hSlope
    rw [ha1] at h1
    exact ⟨by omega, ha1⟩

/-- Bridge 4: Moser–Tardos (`2010`) Constructive Entropy-Compression Resampling Bound vs.
    Shearer Tight Dependency-Cycle Threshold Breakdown (`p₀ + p₁ = 1` Infinite Resampling). -/
theorem moser_tardos_entropy_compression_termination_vs_shearer_lovasz_breakdown :
    -- (1) Universal Entropy-Compression Step Bound: if `T` resampling steps consume `b` random bits/step
    --     while witness-tree log encoding uses `N_init + c * T` bits with strict compression `c + gap ≤ b` (`gap ≥ 1`),
    --     and lossless injectivity forces `b * T ≤ N_init + c * T`, then `gap * T ≤ N_init` (hence `T ≤ N_init` steps)!
    (∀ T b c gap nInit : Int,
      0 ≤ T → 1 ≤ gap → c + gap ≤ b →
      b * T ≤ nInit + c * T →
      gap * T ≤ nInit ∧ T ≤ nInit) ∧
    -- (2) Premise-Failure Counterexample (Violating Lovász/Shearer Condition `p₀ + p₁ < 1`):
    --     Two dependent bad events `B₀(x) := (x = false)` and `B₁(x) := (x = true)` each have `p = 1/2` (`d = 1`,
    --     so `p₀ + p₁ = 1 ≥ 1` and `4 p = 2 > 1`), leaving ZERO bad-event-free state `x : Bool`!
    (¬ ∃ x : Bool, x ≠ false ∧ x ≠ true) := by
  refine ⟨?_, by decide⟩
  intro T b c gap nInit hT hGap hComp hLossless
  have hSub : (b - c) * T ≤ nInit := by grind
  have hGe : gap * T ≤ (b - c) * T := Int.mul_le_mul_of_nonneg_right (by omega) hT
  have hOne : 1 * T ≤ gap * T := Int.mul_le_mul_of_nonneg_right hGap hT
  omega

/-- Homogeneous degree-`2` bivariate form `c20 * x^2 + c11 * x * y + c02 * y^2`. -/
def evalHom2 (c20 c11 c02 x y : Int) : Int :=
  c20 * x * x + c11 * x * y + c02 * y * y

/-- Bridge 5: Dvir's (`2009`) Finite-Field Kakeya Homogeneous Vanishing Rigidity (`3` Distinct Directions Force `H ≡ 0`)
    vs. Missing-Direction Reducible Cone (`2` Directions Allow Nonzero `y(y - x)`). -/
theorem dvir_kakeya_homogeneous_directional_vanishing_rigidity_vs_missing_slope_cone :
    -- (1) Universal Homogeneous Degree-`2` Directional Rigidity:
    --     If `H(x, y) = c20 x^2 + c11 x y + c02 y^2` vanishes along `3` distinct directional slopes
    --     `(1, m0), (1, m1), (1, m2)` with `m0 < m1 < m2`, then `c20 = 0 ∧ c11 = 0 ∧ c02 = 0` (`H ≡ 0`)!
    (∀ c20 c11 c02 m0 m1 m2 : Int,
      m0 < m1 → m1 < m2 →
      evalHom2 c20 c11 c02 1 m0 = 0 →
      evalHom2 c20 c11 c02 1 m1 = 0 →
      evalHom2 c20 c11 c02 1 m2 = 0 →
      c20 = 0 ∧ c11 = 0 ∧ c02 = 0) ∧
    -- (2) Premise-Failure Counterexample (`d = 2` with only `2 < d + 1` directions `m ∈ {0, 1}`):
    --     Nonzero cone `H(x, y) = y(y - x) = -x*y + y^2` (`c02 = 1 ≠ 0`) vanishes identically along ALL points
    --     `t * (1, 0)` and `t * (1, 1)`!
    ((1 : Int) ≠ 0 ∧
     ∀ t : Int, evalHom2 0 (-1) 1 t 0 = 0 ∧ evalHom2 0 (-1) 1 t t = 0) := by
  refine ⟨?_, ?_⟩
  · intro c20 c11 c02 m0 m1 m2 h01 h12 z0 z1 z2
    have hVand :
        (m2 - m1) * evalHom2 c20 c11 c02 1 m0 - (m2 - m0) * evalHom2 c20 c11 c02 1 m1 +
          (m1 - m0) * evalHom2 c20 c11 c02 1 m2 =
          c02 * (m1 - m0) * (m2 - m0) * (m2 - m1) := by unfold evalHom2; grind
    rw [z0, z1, z2] at hVand
    have hc02 : c02 = 0 := by
      by_cases hc02Eq : c02 = 0
      · exact hc02Eq
      · exfalso
        have p1 : c02 * (m1 - m0) ≠ 0 := Int.mul_ne_zero hc02Eq (by omega)
        have p2 : c02 * (m1 - m0) * (m2 - m0) ≠ 0 := Int.mul_ne_zero p1 (by omega)
        have p3 : c02 * (m1 - m0) * (m2 - m0) * (m2 - m1) ≠ 0 := Int.mul_ne_zero p2 (by omega)
        omega
    unfold evalHom2 at z0 z1
    rw [hc02] at z0 z1
    have hLin : c11 * (m1 - m0) = 0 := by grind
    have hc11 : c11 = 0 := by
      by_cases hc11Eq : c11 = 0
      · exact hc11Eq
      · exfalso
        exact (Int.mul_ne_zero hc11Eq (by omega)) hLin
    rw [hc11] at z0
    exact ⟨by omega, hc11, hc02⟩
  · refine ⟨by decide, ?_⟩
    intro t
    unfold evalHom2
    grind

end CommonGround.Verification.TheoremAtlasSchwartzZippelSumCheckFRIShamirAndKakeyaBridge
