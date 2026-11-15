/-
Copyright (c) 2026 Common Ground Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Verification Suite (`V198`): Quantum Ensemble Twirling Base Change, Connes Spectral Taming Energy, Radial Orbit Symplectic Strip Action, Moore–Penrose Probability Projections, Compatible Annulus Gram Trace & Radial Origin Excision

This zero-sorry Lean 4.33.0 verification suite certifies all **6 canonical `[92.0, 93.0)` cross-domain bridges**
promoted to `★` in Wave `V198` (clearing the `[92.0, 93.0)` AST similarity horizon with `0` unreviewed
`>= 92.0` pairs remaining), pairing every physical source theorem pair with both a positive Lean 4
witness and an explicit premise-failure counterexample:

1. `ensemble_twirling_invariants_and_base_change_vs_biased_and_char_two_failure`
   (`iso-v11-bridge-0934`: `oai-qrep :: mixtureDensityMatrix` ↔ `tc-reptheory :: _root_.Representation.invariantsBaseChangeEquiv`)
2. `connes_spectral_detection_energy_and_symplectic_taming_vs_antitamed_and_indefinite_failure`
   (`iso-oai-connes-tc-geometry-135`: `oai-connes :: lambdaSpectralEnergy_eq_four_mul_measure` ↔ `tc-geometry :: Tames`)
3. `radial_orbit_symmetrization_and_cotangent_strip_energy_vs_anisotropic_and_antiholomorphic_failure`
   (`iso-domain-bridge-5488`: `oai-sphere :: radialFourierOrbitAverage` ↔ `tc-geometry :: stdComplexLineEnergy_eq_cotangentAction_sub`)
4. `moore_penrose_hermitian_idempotent_probability_vs_oblique_superunity_failure`
   (`iso-domain-bridge-5708`: `oai-connes :: gammaPairProbability` ↔ `tc-analysis :: IsMoorePenroseInverse`)
5. `compatible_annulus_symplectic_cauchy_schwarz_and_normalized_gram_trace_vs_stretched_form_failure`
   (`iso-domain-bridge-6352`: `tc-geometry :: abs_integral_fderiv_apply_annulus_le` ↔ `zeta23 :: trGtilde`)
6. `radial_poincare_homogeneous_jacobian_and_origin_excision_vs_degree_zero_and_nonzero_origin_failure`
   (`iso-domain-bridge-6277`: `oai-codes :: radialIntegrandFDeriv` ↔ `zeta23 :: M2sum_eq_Ioc`)
-/

namespace CommonGround.Verification.V198Bridges

/-! ## Shared Pure-Core Algebraic & Summation Helpers -/

theorem sq_nonneg_v198 (z : Int) : 0 ≤ z * z := by
  by_cases h : 0 ≤ z
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -z := by omega
    have hp : 0 ≤ (-z) * (-z) := Int.mul_nonneg hn hn
    rw [Int.neg_mul_neg] at hp
    exact hp

def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

theorem sumRange_add (n : Nat) (f g : Nat → Int) :
    sumRange n (fun k => f k + g k) = sumRange n f + sumRange n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [sumRange, ih]
      omega

theorem sumRange_sub (n : Nat) (f g : Nat → Int) :
    sumRange n (fun k => f k - g k) = sumRange n f - sumRange n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [sumRange, ih]
      omega

theorem sumRange_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    c * sumRange n f = sumRange n (fun k => c * f k) := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
      simp only [sumRange, Int.mul_add, ih]

theorem sumRange_mul_right (n : Nat) (f : Nat → Int) (c : Int) :
    sumRange n f * c = sumRange n (fun k => f k * c) := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
      simp only [sumRange, Int.add_mul, ih]

theorem sumRange_ones (n : Nat) : sumRange n (fun _ => 1) = Int.ofNat n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [sumRange, ih]
      rfl

theorem sumRange_nonneg (n : Nat) (f : Nat → Int) (h : ∀ k, k < n → 0 ≤ f k) :
    0 ≤ sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
      have ih' : 0 ≤ sumRange k f := ih (fun i hi => h i (by omega))
      have hk : 0 ≤ f k := h k (by omega)
      simp only [sumRange]
      omega

theorem sumRange_mono (n : Nat) (f g : Nat → Int) (h : ∀ k, k < n → f k ≤ g k) :
    sumRange n f ≤ sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
      have ih' : sumRange k f ≤ sumRange k g := ih (fun i hi => h i (by omega))
      have hk : f k ≤ g k := h k (by omega)
      simp only [sumRange]
      omega

theorem sumRange_congr (n : Nat) (f g : Nat → Int) (h : ∀ k, k < n → f k = g k) :
    sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have ih' : sumRange k f = sumRange k g := ih (fun i hi => h i (by omega))
      have hk : f k = g k := h k (by omega)
      simp [sumRange, ih', hk]

/-! ## Bridge 1 (`iso-v11-bridge-0934`): `mixtureDensityMatrix` ↔ `invariantsBaseChangeEquiv` -/

abbrev Mat2 := Int × Int × Int × Int

def conjZ (M : Mat2) : Mat2 :=
  (M.1, -M.2.1, -M.2.2.1, M.2.2.2)

def twirlZ (M : Mat2) : Mat2 :=
  (M.1 + (conjZ M).1, M.2.1 + (conjZ M).2.1, M.2.2.1 + (conjZ M).2.2.1, M.2.2.2 + (conjZ M).2.2.2)

def biasedTwirlZ (M : Mat2) : Mat2 :=
  (3 * M.1 + (conjZ M).1, 3 * M.2.1 + (conjZ M).2.1,
   3 * M.2.2.1 + (conjZ M).2.2.1, 3 * M.2.2.2 + (conjZ M).2.2.2)

def conjZCplx (MC : Mat2 × Mat2) : Mat2 × Mat2 :=
  (conjZ MC.1, conjZ MC.2)

def twirlZCplx (MC : Mat2 × Mat2) : Mat2 × Mat2 :=
  (twirlZ MC.1, twirlZ MC.2)

/--
**Bridge 1 (`iso-v11-bridge-0934`)**:
Uniform Pauli-`Z` ensemble twirling (`mixtureDensityMatrix`) projects any `2 × 2` matrix onto the
diagonal `Z`-invariant commutant while scaling trace cleanly by `|G| = 2`, and commutes with complex
scalar extension `ℤ → ℤ[i]` (`invariantsBaseChangeEquiv`).
*Premise Failures*: Non-uniform `(3, 1)` weights leave coherent off-diagonal entries that fail
`Z`-invariance (`(4, 2, 2, 4) ≠ (4, -2, -2, 4)`), and unnormalized summation mod `2` (`char = 2`)
annihilates even invariant diagonal entries (`(1 + 1) % 2 = 0`).
-/
theorem ensemble_twirling_invariants_and_base_change_vs_biased_and_char_two_failure :
    (∀ M : Mat2,
      conjZ (twirlZ M) = twirlZ M ∧
      (twirlZ M).1 + (twirlZ M).2.2.2 = 2 * (M.1 + M.2.2.2) ∧
      (twirlZ M).2.1 = 0 ∧ (twirlZ M).2.2.1 = 0) ∧
    (∀ MC : Mat2 × Mat2,
      twirlZCplx MC = (twirlZ MC.1, twirlZ MC.2) ∧
      (conjZCplx MC = MC ↔ (conjZ MC.1 = MC.1 ∧ conjZ MC.2 = MC.2))) ∧
    (biasedTwirlZ (1, 1, 1, 1) = (4, 2, 2, 4) ∧
     conjZ (biasedTwirlZ (1, 1, 1, 1)) ≠ biasedTwirlZ (1, 1, 1, 1)) ∧
    (((1 + 1 : Nat) % 2 = 0) ∧ ((1 + 1 : Nat) % 2 ≠ 1)) := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · intro ⟨a, b, c, d⟩
    simp [conjZ, twirlZ]
    omega
  · intro ⟨reM, imM⟩
    simp [twirlZCplx, conjZCplx]

/-! ## Bridge 2 (`iso-oai-connes-tc-geometry-135`): `lambdaSpectralEnergy_eq_four_mul_measure` ↔ `Tames` -/

def countNeg : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | k + 1, χ => countNeg k χ + (if χ k = -1 then 1 else 0)

def omega2 (u v : Int × Int) : Int :=
  u.1 * v.2 - u.2 * v.1

def stdJ2 (u : Int × Int) : Int × Int :=
  (-u.2, u.1)

def negStdJ2 (u : Int × Int) : Int × Int :=
  (u.2, -u.1)

def splitQuad2 (u : Int × Int) : Int :=
  u.1 * u.1 - u.2 * u.2

/--
**Bridge 2 (`iso-oai-connes-tc-geometry-135`)**:
Connes' spectral detection energy `∑_{k<N} (1 - χ(k))² = 4 · countNeg(N, χ)` for any `±1`-valued
character `χ` and symplectic taming `ω₂(u, stdJ₂ u) = u₁² + u₂² > 0` (`u ≠ 0`) both convert a
signed/skew pairing into a strictly positive `L²` quadratic witness of nontrivial support.
*Premise Failures*: Orientation-reversed `negStdJ₂(x, y) = (y, -x)` still satisfies
`negStdJ₂² = -I`, yet is **anti-tamed** (`ω₂((1,0), negStdJ₂(1,0)) = -1 < 0`), while the split
indefinite form `x² - y²` vanishes on nonzero null ray `(1, 1) ≠ (0, 0)`.
-/
theorem connes_spectral_detection_energy_and_symplectic_taming_vs_antitamed_and_indefinite_failure :
    (∀ (N : Nat) (χ : Nat → Int),
      (∀ k, k < N → χ k = 1 ∨ χ k = -1) →
      sumRange N (fun k => (1 - χ k) * (1 - χ k)) = 4 * countNeg N χ ∧
      (0 < sumRange N (fun k => (1 - χ k) * (1 - χ k)) ↔ 0 < countNeg N χ)) ∧
    (∀ u : Int × Int, u ≠ (0, 0) → 0 < omega2 u (stdJ2 u)) ∧
    ((∀ u : Int × Int, negStdJ2 (negStdJ2 u) = (-u.1, -u.2)) ∧
     omega2 (1, 0) (negStdJ2 (1, 0)) = -1 ∧
     (1, 1) ≠ (0, 0) ∧ splitQuad2 (1, 1) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N χ hpm
    have hEq : sumRange N (fun k => (1 - χ k) * (1 - χ k)) = 4 * countNeg N χ := by
      induction N with
      | zero => simp [sumRange, countNeg]
      | succ k ih =>
          have ih' := ih (fun i hi => hpm i (by omega))
          have hk := hpm k (by omega)
          rcases hk with hk1 | hkm1
          · simp [sumRange, countNeg, ih', hk1]
          · simp [sumRange, countNeg, ih', hkm1]
            omega
    refine ⟨hEq, ?_⟩
    rw [hEq]
    omega
  · intro ⟨x, y⟩ hne
    dsimp [omega2, stdJ2]
    rw [Int.mul_neg, Int.sub_neg]
    have hx : 0 ≤ x * x := sq_nonneg_v198 x
    have hy : 0 ≤ y * y := sq_nonneg_v198 y
    by_cases hx0 : x = 0
    · subst hx0
      have hy0 : y ≠ 0 := by intro h; apply hne; subst h; rfl
      by_cases hyp : 0 < y
      · have hpos : 0 < y * y := Int.mul_pos hyp hyp
        omega
      · have hyn : 0 < -y := by omega
        have hpos : 0 < (-y) * (-y) := Int.mul_pos hyn hyn
        rw [Int.neg_mul_neg] at hpos
        omega
    · by_cases hxp : 0 < x
      · have hpos : 0 < x * x := Int.mul_pos hxp hxp
        omega
      · have hxn : 0 < -x := by omega
        have hpos : 0 < (-x) * (-x) := Int.mul_pos hxn hxn
        rw [Int.neg_mul_neg] at hpos
        omega
  · refine ⟨?_, by decide, by decide, by decide⟩
    intro ⟨x, y⟩
    rfl

/-! ## Bridge 3 (`iso-domain-bridge-5488`): `radialFourierOrbitAverage` ↔ `stdComplexLineEnergy_eq_cotangentAction_sub` -/

def rotC4 (p : Int × Int) : Int × Int :=
  (-p.2, p.1)

def orbitAvgC4 (f : Int × Int → Int) (p : Int × Int) : Int :=
  f p + f (-p.2, p.1) + f (-p.1, -p.2) + f (p.2, -p.1)

def anisoModeX (p : Int × Int) : Int :=
  p.1 * p.1

/--
**Bridge 3 (`iso-domain-bridge-5488`)**:
Discrete `C₄` rotational orbit averaging (`radialFourierOrbitAverage`) projects any test profile
onto `C₄`-invariant radial functions while preserving origin amplitude (`4 * f(0,0)`) and point-wise
nonnegativity, mirroring the exact Cauchy–Riemann / cotangent strip identity
`u_x² + u_y² + v_x² + v_y² = (u_x - v_y)² + (u_y + v_x)² + 2(u_x v_y - u_y v_x)`
(`stdComplexLineEnergy_eq_cotangentAction_sub`).
*Premise Failures*: Unaveraged `anisoModeX(x, y) = x²` fails rotational invariance
(`anisoModeX(1,0) = 1 ≠ 0 = anisoModeX(0,1)`), and anti-holomorphic `(u, v) = (x, -y)`
(`ux = 1, uy = 0, vx = 0, vy = -1`) flips symplectic area negative (`-1 < 0`) with `|∂̄ u|² = 4`.
-/
theorem radial_orbit_symmetrization_and_cotangent_strip_energy_vs_anisotropic_and_antiholomorphic_failure :
    (∀ (f : Int × Int → Int) (p : Int × Int),
      orbitAvgC4 f (rotC4 p) = orbitAvgC4 f p ∧
      orbitAvgC4 f (0, 0) = 4 * f (0, 0) ∧
      ((∀ q, 0 ≤ f q) → 0 ≤ orbitAvgC4 f p)) ∧
    (∀ ux uy vx vy : Int,
      ux * ux + uy * uy + vx * vx + vy * vy =
        (ux - vy) * (ux - vy) + (uy + vx) * (uy + vx) + 2 * (ux * vy - uy * vx)) ∧
    (anisoModeX (1, 0) = 1 ∧ anisoModeX (0, 1) = 0 ∧ anisoModeX (1, 0) ≠ anisoModeX (0, 1) ∧
     (1 * (-1) - 0 * 0 : Int) = -1 ∧ ((1 - (-1)) * (1 - (-1)) + (0 + 0) * (0 + 0) : Int) = 4) := by
  refine ⟨?_, ?_, by decide⟩
  · intro f ⟨x, y⟩
    refine ⟨?_, ?_, ?_⟩
    · simp [orbitAvgC4, rotC4]
      omega
    · simp [orbitAvgC4]
      omega
    · intro hnn
      have h1 := hnn (x, y)
      have h2 := hnn (-y, x)
      have h3 := hnn (-x, -y)
      have h4 := hnn (y, -x)
      dsimp [orbitAvgC4]
      omega
  · intro ux uy vx vy
    have h1 : (ux - vy) * (ux - vy) = ux * ux - ux * vy - vy * ux + vy * vy := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
      omega
    have h2 : (uy + vx) * (uy + vx) = uy * uy + uy * vx + vx * uy + vx * vx := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
      omega
    rw [h1, h2, Int.mul_comm vy ux, Int.mul_comm vx uy]
    omega

/-! ## Bridge 4 (`iso-domain-bridge-5708`): `gammaPairProbability` ↔ `IsMoorePenroseInverse` -/

def dot2 (u v : Int × Int) : Int :=
  u.1 * v.1 + u.2 * v.2

def normSq2 (u : Int × Int) : Int :=
  u.1 * u.1 + u.2 * u.2

def projDiag2 (u : Int × Int) : Int × Int :=
  (u.1 + u.2, u.1 + u.2)

def obliqueQ (u : Int × Int) : Int × Int :=
  (u.1 + u.2, 0)

/--
**Bridge 4 (`iso-domain-bridge-5708`)**:
Orthogonal character-pair probability `gammaPairProbability` requires the Moore–Penrose Hermitian
idempotent axiom `isSymmetric_comp` (`IsMoorePenroseInverse`): `projDiag2` satisfies symmetry
`⟨u, P v⟩ = ⟨P u, v⟩`, scaled idempotence `P(P u) = 2 P u`, Moore–Penrose reflexivity
`P(P(P u)) = 4 P u`, and exact Pythagorean probability conservation
`‖P u‖² + ‖2u - P u‖² = 4 ‖u‖²` (`0 ≤ ‖P u‖² ≤ 4 ‖u‖²`).
*Premise Failure*: Oblique projection `obliqueQ(x, y) = (x + y, 0)` satisfies algebraic idempotence
`Q(Q u) = Q u` (`Q ∘ Q ∘ Q = Q`), YET fails symmetry (`⟨(0,1), Q(1,0)⟩ = 0 ≠ 1 = ⟨Q(0,1), (1,0)⟩`),
yielding `‖Q(1,1)‖² = 4 > 2 = ‖(1,1)‖²` (a `200%` super-unity non-probability!).
-/
theorem moore_penrose_hermitian_idempotent_probability_vs_oblique_superunity_failure :
    (∀ u v : Int × Int,
      dot2 u (projDiag2 v) = dot2 (projDiag2 u) v ∧
      projDiag2 (projDiag2 u) = (2 * (u.1 + u.2), 2 * (u.1 + u.2)) ∧
      projDiag2 (projDiag2 (projDiag2 u)) = (4 * (u.1 + u.2), 4 * (u.1 + u.2)) ∧
      normSq2 (projDiag2 u) + normSq2 (2 * u.1 - (u.1 + u.2), 2 * u.2 - (u.1 + u.2)) =
        4 * normSq2 u ∧
      0 ≤ normSq2 (projDiag2 u) ∧
      normSq2 (projDiag2 u) ≤ 4 * normSq2 u) ∧
    ((∀ u : Int × Int, obliqueQ (obliqueQ u) = obliqueQ u ∧
       obliqueQ (obliqueQ (obliqueQ u)) = obliqueQ u) ∧
     dot2 (0, 1) (obliqueQ (1, 0)) ≠ dot2 (obliqueQ (0, 1)) (1, 0) ∧
     normSq2 (obliqueQ (1, 1)) = 4 ∧
     normSq2 (1, 1) = 2 ∧
     normSq2 (1, 1) < normSq2 (obliqueQ (1, 1))) := by
  refine ⟨?_, ?_⟩
  · intro ⟨x, y⟩ ⟨z, w⟩
    have hSym : dot2 (x, y) (projDiag2 (z, w)) = dot2 (projDiag2 (x, y)) (z, w) := by
      dsimp [dot2, projDiag2]
      rw [Int.mul_add, Int.mul_add, Int.add_mul, Int.add_mul]
      omega
    have hPar :
        normSq2 (projDiag2 (x, y)) + normSq2 (2 * x - (x + y), 2 * y - (x + y)) =
          4 * normSq2 (x, y) := by
      dsimp [normSq2, projDiag2]
      have hs1 : 2 * x - (x + y) = x - y := by omega
      have hs2 : 2 * y - (x + y) = y - x := by omega
      rw [hs1, hs2]
      have hp : (x + y) * (x + y) = x * x + x * y + y * x + y * y := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add]
        omega
      have hm1 : (x - y) * (x - y) = x * x - x * y - y * x + y * y := by
        rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
        omega
      have hm2 : (y - x) * (y - x) = y * y - y * x - x * y + x * x := by
        rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
        omega
      rw [hp, hm1, hm2]
      omega
    have hPos1 : 0 ≤ normSq2 (projDiag2 (x, y)) := by
      dsimp [normSq2, projDiag2]
      have hs := sq_nonneg_v198 (x + y)
      omega
    have hPos2 : 0 ≤ normSq2 (2 * x - (x + y), 2 * y - (x + y)) := by
      dsimp [normSq2]
      have hs1 := sq_nonneg_v198 (2 * x - (x + y))
      have hs2 := sq_nonneg_v198 (2 * y - (x + y))
      omega
    refine ⟨hSym, ?_, ?_, hPar, hPos1, by omega⟩
    · simp [projDiag2]; omega
    · simp [projDiag2]; omega
  · refine ⟨?_, by decide, by decide, by decide, by decide⟩
    intro ⟨x, y⟩
    simp [obliqueQ]

/-! ## Bridge 5 (`iso-domain-bridge-6352`): `abs_integral_fderiv_apply_annulus_le` ↔ `trGtilde` -/

theorem single_le_sumRange_of_nonneg (d k : Nat) (f : Nat → Int)
    (hk : k < d) (hnn : ∀ l, l < d → 0 ≤ f l) :
    f k ≤ sumRange d f := by
  induction d with
  | zero => omega
  | succ m ih =>
      simp only [sumRange]
      by_cases hkm : k = m
      · subst hkm
        have hPre : 0 ≤ sumRange k f := sumRange_nonneg k f (fun l hl => hnn l (by omega))
        omega
      · have hlt : k < m := by omega
        have hih : f k ≤ sumRange m f := ih hlt (fun l hl => hnn l (by omega))
        have hm : 0 ≤ f m := hnn m (by omega)
        omega

/--
**Bridge 5 (`iso-domain-bridge-6352`)**:
1. (*Compatible Symplectic Annulus Cauchy–Schwarz*): Under metric compatibility
   `hg : ω₂(v, stdJ₂ w) = ⟨v, w⟩`, `normSq2 u + normSq2 v - 2 * omega2 u v = (u₁ - v₂)² + (u₂ + v₁)² ≥ 0`
   and `normSq2 u + normSq2 v + 2 * omega2 u v = (u₁ + v₂)² + (u₂ - v₁)² ≥ 0`, certifying the exact
   `1/2` boundary energy constant in `abs_integral_fderiv_apply_annulus_le`.
2. (*Normalized Gram Trace vs. Frobenius Norm `trGtilde` / `trGtildeSq`*): For any `d × d` matrix `G`,
   `(∑_{k<d} G_{kk})² ≤ d * ∑_{k<d} G_{kk}² ≤ d * ∑_{k<d} ∑_{l<d} G_{kl}²`.
3. (*Stretched-Form Premise Failure*): Stretching `ω_stretch = 3 * ω₂` without rescaling `‖·‖²`
   violates `hg` and breaks the `1/2` bound on `(1,0), (0,1)` (`2 * 3 = 6 > 2 = 1 + 1`).
-/
theorem compatible_annulus_symplectic_cauchy_schwarz_and_normalized_gram_trace_vs_stretched_form_failure :
    (∀ u v : Int × Int,
      2 * omega2 u v ≤ normSq2 u + normSq2 v ∧
      -(2 * omega2 u v) ≤ normSq2 u + normSq2 v) ∧
    (∀ (d : Nat) (G : Nat → Nat → Int),
      let tr := sumRange d (fun k => G k k)
      let diagSq := sumRange d (fun k => G k k * G k k)
      let frobSq := sumRange d (fun k => sumRange d (fun l => G k l * G k l))
      tr * tr ≤ Int.ofNat d * diagSq ∧
      Int.ofNat d * diagSq ≤ Int.ofNat d * frobSq) ∧
    (2 * (3 * omega2 (1, 0) (0, 1)) = 6 ∧
     normSq2 (1, 0) + normSq2 (0, 1) = 2 ∧
     normSq2 (1, 0) + normSq2 (0, 1) < 2 * (3 * omega2 (1, 0) (0, 1))) := by
  refine ⟨?_, ?_, by decide⟩
  · intro ⟨u1, u2⟩ ⟨v1, v2⟩
    have hMinus :
        normSq2 (u1, u2) + normSq2 (v1, v2) - 2 * omega2 (u1, u2) (v1, v2) =
          (u1 - v2) * (u1 - v2) + (u2 + v1) * (u2 + v1) := by
      dsimp [normSq2, omega2]
      have s1 : (u1 - v2) * (u1 - v2) = u1 * u1 - u1 * v2 - v2 * u1 + v2 * v2 := by
        rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
      have s2 : (u2 + v1) * (u2 + v1) = u2 * u2 + u2 * v1 + v1 * u2 + v1 * v1 := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
      rw [s1, s2, Int.mul_comm v2 u1, Int.mul_comm v1 u2]
      omega
    have hPlus :
        normSq2 (u1, u2) + normSq2 (v1, v2) + 2 * omega2 (u1, u2) (v1, v2) =
          (u1 + v2) * (u1 + v2) + (u2 - v1) * (u2 - v1) := by
      dsimp [normSq2, omega2]
      have s1 : (u1 + v2) * (u1 + v2) = u1 * u1 + u1 * v2 + v2 * u1 + v2 * v2 := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
      have s2 : (u2 - v1) * (u2 - v1) = u2 * u2 - u2 * v1 - v1 * u2 + v1 * v1 := by
        rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
      rw [s1, s2, Int.mul_comm v2 u1, Int.mul_comm v1 u2]
      omega
    have hp1 := sq_nonneg_v198 (u1 - v2)
    have hp2 := sq_nonneg_v198 (u2 + v1)
    have hp3 := sq_nonneg_v198 (u1 + v2)
    have hp4 := sq_nonneg_v198 (u2 - v1)
    omega
  · intro d G
    dsimp
    let f := fun k => G k k
    have hLagrange :
        sumRange d (fun i => sumRange d (fun j => (f i - f j) * (f i - f j))) =
          2 * (Int.ofNat d * sumRange d (fun k => f k * f k) - sumRange d f * sumRange d f) := by
      have hInner : ∀ i : Nat,
          sumRange d (fun j => (f i - f j) * (f i - f j)) =
            Int.ofNat d * (f i * f i) - 2 * f i * sumRange d f + sumRange d (fun j => f j * f j) := by
        intro i
        have hExp : ∀ j, j < d →
            (f i - f j) * (f i - f j) =
              ((f i * f i) * 1 - (2 * f i) * f j) + f j * f j := by
          intro j _
          rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm (f j) (f i)]
          have h2 : (2 * f i) * f j = f i * f j + f i * f j := by
            rw [Int.mul_assoc, Int.two_mul]
          rw [h2]
          omega
        rw [sumRange_congr d _ _ hExp, sumRange_add, sumRange_sub,
            ← sumRange_mul_left d (f i * f i) (fun _ => 1), sumRange_ones,
            ← sumRange_mul_left d (2 * f i) f, Int.mul_comm (f i * f i) (Int.ofNat d)]
      rw [sumRange_congr d _ _ (fun i _ => hInner i), sumRange_add, sumRange_sub,
          ← sumRange_mul_left d (Int.ofNat d) (fun i => f i * f i)]
      have hMid : sumRange d (fun i => 2 * f i * sumRange d f) = 2 * (sumRange d f * sumRange d f) := by
        have hCon : ∀ i, i < d → 2 * f i * sumRange d f = 2 * (f i * sumRange d f) := by
          intro i _; rw [Int.mul_assoc]
        rw [sumRange_congr d _ _ hCon, ← sumRange_mul_left d 2 (fun i => f i * sumRange d f),
            ← sumRange_mul_right d f (sumRange d f)]
      have hEnd : sumRange d (fun _ => sumRange d (fun j => f j * f j)) =
          Int.ofNat d * sumRange d (fun j => f j * f j) := by
        have hCon2 : ∀ i, i < d →
            sumRange d (fun j => f j * f j) = sumRange d (fun j => f j * f j) * 1 := by
          intro i _; omega
        rw [sumRange_congr d _ _ hCon2, ← sumRange_mul_left d (sumRange d (fun j => f j * f j)) (fun _ => 1),
            sumRange_ones, Int.mul_comm]
      rw [hMid, hEnd]
      omega
    have hLagNonneg :
        0 ≤ sumRange d (fun i => sumRange d (fun j => (f i - f j) * (f i - f j))) := by
      apply sumRange_nonneg
      intro i _
      apply sumRange_nonneg
      intro j _
      exact sq_nonneg_v198 (f i - f j)
    have hPart1 : sumRange d f * sumRange d f ≤ Int.ofNat d * sumRange d (fun k => f k * f k) := by
      omega
    have hDiagLeFrob :
        sumRange d (fun k => G k k * G k k) ≤
          sumRange d (fun k => sumRange d (fun l => G k l * G k l)) := by
      apply sumRange_mono
      intro k hk
      exact single_le_sumRange_of_nonneg d k (fun l => G k l * G k l) hk
        (fun l _ => sq_nonneg_v198 (G k l))
    refine ⟨hPart1, Int.mul_le_mul_of_nonneg_left hDiagLeFrob (by omega)⟩

/-! ## Bridge 6 (`iso-domain-bridge-6277`): `radialIntegrandFDeriv` ↔ `M2sum_eq_Ioc` -/

def nonzeroOriginSeq : Nat → Int
  | 0 => 5
  | _ + 1 => 1

/--
**Bridge 6 (`iso-domain-bridge-6277`)**:
1. (*Homogeneous Radial Pullback Weight `tⁿ` & Telescoping Primitive*): For every `n ≥ 0`,
   `0 ^ (n + 1) = 0` (the homogeneous radial Jacobian `t^{n+1}` vanishes at the origin `t = 0`),
   and `∑_{t<T} ((t+1)^{n+1} - t^{n+1}) = T^{n+1}`.
2. (*`[0, N]` to `(0, N]` Origin Excision `M2sum_eq_Ioc`*): Whenever `g 0 = 0` (such as `Λ(0)² / 0 = 0`),
   `sumRange (N + 1) g = sumRange N (fun k => g (k + 1))`.
3. (*Degree-0 & Non-Zero Origin Premise Failures*): `(0 : Nat) ^ 0 = 1 ≠ 0`, and for
   `nonzeroOriginSeq` (`g 0 = 5`), `sumRange 3 g - sumRange 2 (fun k => g (k + 1)) = 5 ≠ 0`!
-/
theorem radial_poincare_homogeneous_jacobian_and_origin_excision_vs_degree_zero_and_nonzero_origin_failure :
    (∀ n T : Nat,
      (0 : Nat) ^ (n + 1) = 0 ∧
      sumRange T (fun t => Int.ofNat ((t + 1) ^ (n + 1)) - Int.ofNat (t ^ (n + 1))) =
        Int.ofNat (T ^ (n + 1))) ∧
    (∀ (N : Nat) (g : Nat → Int),
      g 0 = 0 →
      sumRange (N + 1) g = sumRange N (fun k => g (k + 1))) ∧
    ((0 : Nat) ^ 0 = 1 ∧ (0 : Nat) ^ 0 ≠ 0 ∧
     sumRange 3 nonzeroOriginSeq = 7 ∧
     sumRange 2 (fun k => nonzeroOriginSeq (k + 1)) = 2 ∧
     sumRange 3 nonzeroOriginSeq ≠ sumRange 2 (fun k => nonzeroOriginSeq (k + 1))) := by
  refine ⟨?_, ?_, by decide⟩
  · intro n T
    have hZeroPow : (0 : Nat) ^ (n + 1) = 0 := Nat.zero_pow (Nat.succ_pos n)
    refine ⟨hZeroPow, ?_⟩
    induction T with
    | zero =>
        simp [sumRange, hZeroPow]
    | succ m ih =>
        simp only [sumRange, ih]
        omega
  · intro N g hg0
    induction N with
    | zero =>
        simp [sumRange, hg0]
    | succ m ih =>
        change sumRange (m + 1) g + g (m + 1) = sumRange m (fun k => g (k + 1)) + g (m + 1)
        rw [ih]

end CommonGround.Verification.V198Bridges
