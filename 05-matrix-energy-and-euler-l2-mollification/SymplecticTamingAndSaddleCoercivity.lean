/-
  Discovery 05 · Frontier Synthesis:
  Symplectic Taming, 2D-to-4D Gromov Phase Transition & Asymmetric Saddle-Point Coercivity
  =========================================================================================
  Pure-core Lean 4.33.0 formalization (0 Mathlib imports, 0 sorry) unifying:
  - Folder `05` (`MatrixEnergyVolume.lean`, `LagrangianVolumeStability.lean`: solenoidal zero-trace
    flows conserve volume while carrying pure rotational shear Frobenius energy),
  - Folder `07` & `08` (`OpenAIGame.lean`, `InspectedFoundationsAndFiniteDuality.lean`: bilinear
    saddle-point equilibrium games and contractive fixed-point uniqueness),
  - `TauCeti/Geometry/Symplectic/AlmostComplex.lean` (`AlmostComplexStructure`, `Tames`, `Compatible`).

  Main Kernel-Verified Theorems:
  1. `skew_bilinear_zero_dissipation_and_euler_inflation`:
     Conservative skew-symmetric game dynamics have identically zero quadratic dissipation
     `⟨z, Ω z⟩ = 0`, causing naive forward-Euler updates `q z - p Ω z` to strictly INFLATE
     Euclidean energy `(q² + p² s²) ‖z‖² > q² ‖z‖²` whenever `p ≠ 0, s ≠ 0, ‖z‖² > 0`.
  2. `dim2_almost_complex_trace_zero_det_one` & `dim2_taming_implies_symplectic_compatibility`:
     Dimension-2 Rigidity: EVERY `2 × 2` integer almost-complex structure `J² = -I₂` automatically
     satisfies `tr(J) = 0` and `det(J) = 1`, forcing `ω₂(J u, J v) = ω₂(u, v)` and symmetry
     `ω₂(u, J v) = ω₂(v, J u)` unconditionally (Taming ⟺ Kähler Compatibility in 2D!).
  3. `dim4_sheared_almost_complex_sq_neg_id`, `dim4_sheared_tames_sum_of_squares_and_pos`,
     & `dim4_tamed_not_compatible_and_asymmetric_metric`:
     Dimension-4 Gromov Phase Transition: on `ℤ⁴`, the unipotently sheared operator
     `J₄(x₁, y₁, x₂, y₂) = (-y₁ - y₂, x₁ - x₂, -y₂, x₂)` satisfies `J₄² = -I₄` and strict
     symplectic taming `2 ω₄(v, J₄ v) = x₁² + (x₁ - x₂)² + x₂² + y₁² + (y₁ + y₂)² + y₂² > 0`
     for all `v ≠ 0`, YET `ω₄(J₄ e₂, J₄ e₃) = 1 ≠ 0 = ω₄(e₂, e₃)` and
     `ω₄(e₁, J₄ e₃) = -1 ≠ 0 = ω₄(e₃, J₄ e₁)` (Taming ⇏ Compatibility for `dim ≥ 4`!).
  4. `asymmetric_tamed_operator_discrete_contraction`:
     Universal Asymmetric Taming Contraction Certificate: on `Fin n → Int`, ANY (possibly
     asymmetric, non-Kähler!) tamed operator `M` satisfying `μ ‖z‖² ≤ ⟨z, M z⟩` and
     `‖M z‖² ≤ L₂ ‖z‖²` contracts strictly under discrete Euler `step(z) = q z - p M z`:
       `‖q z - p M z‖² ≤ (q² - 2 p q μ + p² L₂) ‖z‖² < q² ‖z‖²`
     whenever `0 < p`, `p L₂ < 2 q μ`, and `0 < ‖z‖²` — stabilizing min-max games without Riccati
     diagonalization!
-/

namespace CommonGround.Frontier.SymplecticTamingAndSaddleCoercivity

/-! ## Part 1: Skew-Symmetric Saddle Oscillation & Forward-Euler Energy Inflation -/

/-- Canonical 2D Euclidean squared norm `x² + y²`. -/
def normSq2 (z : Int × Int) : Int :=
  z.1 * z.1 + z.2 * z.2

/-- Canonical 2D dot product. -/
def dot2 (u v : Int × Int) : Int :=
  u.1 * v.1 + u.2 * v.2

/-- Skew-symmetric Hamiltonian / bilinear min-max game vector field `Ω_s(x, y) = (-s y, s x)`. -/
def skewGame2 (s : Int) (z : Int × Int) : Int × Int :=
  (-s * z.2, s * z.1)

/-- Scaled discrete forward-Euler update `z⁺ = q z - p Ω_s(z)`. -/
def skewEulerStep2 (q p s : Int) (z : Int × Int) : Int × Int :=
  (q * z.1 - p * (skewGame2 s z).1, q * z.2 - p * (skewGame2 s z).2)

private theorem sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -x := by omega
    have hmul : 0 ≤ (-x) * (-x) := Int.mul_nonneg hn hn
    have heq : (-x) * (-x) = x * x := by
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    omega

private theorem sq_pos_of_ne_zero {x : Int} (hx : x ≠ 0) : 0 < x * x := by
  by_cases h : 0 < x
  · exact Int.mul_pos h h
  · have hn : 0 < -x := by omega
    have hmul : 0 < (-x) * (-x) := Int.mul_pos hn hn
    have heq : (-x) * (-x) = x * x := by
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    omega

/-- **Conservative Skew-Symmetric Zero Dissipation & Forward-Euler Energy Inflation**:
    `⟨z, Ω_s z⟩ = 0` identically, and explicit forward Euler strictly inflates Euclidean energy
    `‖q z - p Ω_s z‖² = (q² + p² s²) ‖z‖² > q² ‖z‖²` whenever `p ≠ 0`, `s ≠ 0`, and `‖z‖² > 0`. -/
theorem skew_bilinear_zero_dissipation_and_euler_inflation
    (q p s : Int) (z : Int × Int) :
    dot2 z (skewGame2 s z) = 0 ∧
    normSq2 (skewEulerStep2 q p s z) = (q * q + (p * s) * (p * s)) * normSq2 z ∧
    (p ≠ 0 → s ≠ 0 → 0 < normSq2 z →
      q * q * normSq2 z < normSq2 (skewEulerStep2 q p s z)) := by
  rcases z with ⟨x, y⟩
  have hDot : x * (-s * y) + y * (s * x) = 0 := by
    have h1 : x * (-s * y) = -(s * (x * y)) := by
      calc
        x * (-s * y) = -(x * (s * y)) := by rw [Int.neg_mul, Int.mul_neg]
      _ = -(s * (x * y)) := by simp only [Int.mul_left_comm]
    have h2 : y * (s * x) = s * (x * y) := by
      simp only [Int.mul_left_comm, Int.mul_comm]
    omega
  have hExpand :
      (q * x - p * (-s * y)) * (q * x - p * (-s * y)) +
        (q * y - p * (s * x)) * (q * y - p * (s * x)) =
      (q * q + (p * s) * (p * s)) * (x * x + y * y) := by
    have hps1 : q * x - p * (-s * y) = q * x + (p * s) * y := by
      have hm : p * (-s * y) = -((p * s) * y) := by
        calc
          p * (-s * y) = -(p * (s * y)) := by rw [Int.neg_mul, Int.mul_neg]
          _ = -((p * s) * y) := by rw [Int.mul_assoc]
      omega
    have hps2 : q * y - p * (s * x) = q * y - (p * s) * x := by
      rw [Int.mul_assoc]
    rw [hps1, hps2]
    let ps := p * s
    calc
      (q * x + ps * y) * (q * x + ps * y) + (q * y - ps * x) * (q * y - ps * x)
          = ((q * x) * (q * x) + (q * x) * (ps * y) + (ps * y) * (q * x) + (ps * y) * (ps * y)) +
            ((q * y) * (q * y) - (q * y) * (ps * x) - (ps * x) * (q * y) + (ps * x) * (ps * x)) := by
            simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
            omega
      _ = q * q * (x * x) + ps * ps * (y * y) + q * q * (y * y) + ps * ps * (x * x) := by
            have hc1 : (q * x) * (ps * y) = (q * y) * (ps * x) := by
              simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
            have hc2 : (ps * y) * (q * x) = (ps * x) * (q * y) := by
              simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
            have hqx : (q * x) * (q * x) = q * q * (x * x) := by
              simp only [Int.mul_left_comm, Int.mul_comm]
            have hqy : (q * y) * (q * y) = q * q * (y * y) := by
              simp only [Int.mul_left_comm, Int.mul_comm]
            have hpx : (ps * x) * (ps * x) = ps * ps * (x * x) := by
              simp only [Int.mul_left_comm, Int.mul_comm]
            have hpy : (ps * y) * (ps * y) = ps * ps * (y * y) := by
              simp only [Int.mul_left_comm, Int.mul_comm]
            omega
      _ = (q * q + ps * ps) * (x * x + y * y) := by
            simp only [Int.add_mul, Int.mul_add]
            omega
  refine ⟨hDot, hExpand, ?_⟩
  intro hp hs hz
  change q * q * (x * x + y * y) <
    (q * x - p * (-s * y)) * (q * x - p * (-s * y)) +
      (q * y - p * (s * x)) * (q * y - p * (s * x))
  rw [hExpand, Int.add_mul]
  have hpsNe : p * s ≠ 0 := by
    intro hZero
    rcases Int.mul_eq_zero.mp hZero with h0 | h0
    · exact hp h0
    · exact hs h0
  have hpsPos : 0 < (p * s) * (p * s) := sq_pos_of_ne_zero hpsNe
  have hProdPos : 0 < (p * s) * (p * s) * (x * x + y * y) := Int.mul_pos hpsPos hz
  omega

/-! ## Part 2: Dimension-2 Rigidity — Every Almost-Complex Structure Is Symplectically Compatible -/

/-- `2 × 2` integer matrix carrier. -/
structure Mat2 where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving DecidableEq, Repr

/-- Matrix-vector action on `ℤ²`. -/
def Mat2.act (J : Mat2) (v : Int × Int) : Int × Int :=
  (J.a * v.1 + J.b * v.2, J.c * v.1 + J.d * v.2)

/-- Standard symplectic form `ω₂(u, v) = u₁ v₂ - u₂ v₁` on `ℤ²`. -/
def omega2 (u v : Int × Int) : Int :=
  u.1 * v.2 - u.2 * v.1

/-- Almost-complex condition `J² = -I₂` in matrix entries. -/
def IsAlmostComplex2 (J : Mat2) : Prop :=
  J.a * J.a + J.b * J.c = -1 ∧
  J.a * J.b + J.b * J.d = 0 ∧
  J.c * J.a + J.d * J.c = 0 ∧
  J.c * J.b + J.d * J.d = -1

/-- **Dimension-2 Almost-Complex Rigidity**:
    Every `2 × 2` integer matrix satisfying `J² = -I₂` automatically has `tr(J) = a + d = 0`
    and `det(J) = a d - b c = 1`. -/
theorem dim2_almost_complex_trace_zero_det_one (J : Mat2) (hJ : IsAlmostComplex2 J) :
    J.a + J.d = 0 ∧ J.a * J.d - J.b * J.c = 1 := by
  rcases hJ with ⟨h11, h12, _, _⟩
  have hbNe : J.b ≠ 0 := by
    intro hb0
    have hsq : 0 ≤ J.a * J.a := sq_nonneg J.a
    rw [hb0, Int.zero_mul] at h11
    omega
  have hProdZero : J.b * (J.a + J.d) = 0 := by
    calc
      J.b * (J.a + J.d) = J.b * J.a + J.b * J.d := Int.mul_add J.b J.a J.d
      _ = J.a * J.b + J.b * J.d := by rw [Int.mul_comm J.b J.a]
      _ = 0 := h12
  have hTr : J.a + J.d = 0 := by
    rcases Int.mul_eq_zero.mp hProdZero with hb0 | had0
    · exact False.elim (hbNe hb0)
    · exact had0
  have hd : J.d = -J.a := by omega
  have hDet : J.a * J.d - J.b * J.c = 1 := by
    rw [hd, Int.mul_neg]
    omega
  exact ⟨hTr, hDet⟩

/-- **2D Taming Implies Automatic Kähler Compatibility**:
    In dimension `2`, `J² = -I₂` forces `ω₂(J u, J v) = ω₂(u, v)` and `ω₂(u, J v) = ω₂(v, J u)`
    for all `u, v ∈ ℤ²`! -/
theorem dim2_taming_implies_symplectic_compatibility
    (J : Mat2) (hJ : IsAlmostComplex2 J) (u v : Int × Int) :
    omega2 (J.act u) (J.act v) = omega2 u v ∧
    omega2 u (J.act v) = omega2 v (J.act u) := by
  rcases dim2_almost_complex_trace_zero_det_one J hJ with ⟨hTr, hDet⟩
  rcases u with ⟨u1, u2⟩
  rcases v with ⟨v1, v2⟩
  have hd : J.d = -J.a := by omega
  have hCompat :
      (J.a * u1 + J.b * u2) * (J.c * v1 + J.d * v2) -
        (J.c * u1 + J.d * u2) * (J.a * v1 + J.b * v2) =
      (J.a * J.d - J.b * J.c) * (u1 * v2 - u2 * v1) := by
    calc
      (J.a * u1 + J.b * u2) * (J.c * v1 + J.d * v2) -
          (J.c * u1 + J.d * u2) * (J.a * v1 + J.b * v2)
          = ((J.a * u1) * (J.c * v1) + (J.a * u1) * (J.d * v2) +
             (J.b * u2) * (J.c * v1) + (J.b * u2) * (J.d * v2)) -
            ((J.c * u1) * (J.a * v1) + (J.c * u1) * (J.b * v2) +
             (J.d * u2) * (J.a * v1) + (J.d * u2) * (J.b * v2)) := by
            simp only [Int.add_mul, Int.mul_add]
            omega
      _ = J.a * J.d * (u1 * v2) - J.a * J.d * (u2 * v1) -
          J.b * J.c * (u1 * v2) + J.b * J.c * (u2 * v1) := by
            have k1 : (J.a * u1) * (J.c * v1) = (J.c * u1) * (J.a * v1) := by
              simp only [Int.mul_left_comm, Int.mul_comm]
            have k2 : (J.b * u2) * (J.d * v2) = (J.d * u2) * (J.b * v2) := by
              simp only [Int.mul_left_comm, Int.mul_comm]
            have k3 : (J.a * u1) * (J.d * v2) = J.a * J.d * (u1 * v2) := by
              simp only [Int.mul_left_comm, Int.mul_comm]
            have k4 : (J.d * u2) * (J.a * v1) = J.a * J.d * (u2 * v1) := by
              simp only [Int.mul_left_comm, Int.mul_comm]
            have k5 : (J.b * u2) * (J.c * v1) = J.b * J.c * (u2 * v1) := by
              simp only [Int.mul_left_comm, Int.mul_comm]
            have k6 : (J.c * u1) * (J.b * v2) = J.b * J.c * (u1 * v2) := by
              simp only [Int.mul_left_comm, Int.mul_comm]
            omega
      _ = (J.a * J.d - J.b * J.c) * (u1 * v2 - u2 * v1) := by
            simp only [Int.sub_mul, Int.mul_sub]
            omega
  have hSym :
      u1 * (J.c * v1 + J.d * v2) - u2 * (J.a * v1 + J.b * v2) =
      v1 * (J.c * u1 + J.d * u2) - v2 * (J.a * u1 + J.b * u2) := by
    rw [hd]
    simp only [Int.mul_add, Int.neg_mul, Int.mul_neg]
    have s1 : u1 * (J.c * v1) = v1 * (J.c * u1) := by
      simp only [Int.mul_left_comm, Int.mul_comm]
    have s2 : u2 * (J.b * v2) = v2 * (J.b * u2) := by
      simp only [Int.mul_left_comm, Int.mul_comm]
    have s3 : u1 * (J.a * v2) = v2 * (J.a * u1) := by
      simp only [Int.mul_left_comm, Int.mul_comm]
    have s4 : u2 * (J.a * v1) = v1 * (J.a * u2) := by
      simp only [Int.mul_left_comm, Int.mul_comm]
    omega
  refine ⟨?_, hSym⟩
  change (J.a * u1 + J.b * u2) * (J.c * v1 + J.d * v2) -
      (J.c * u1 + J.d * u2) * (J.a * v1 + J.b * v2) = u1 * v2 - u2 * v1
  rw [hCompat, hDet, Int.one_mul]

/-! ## Part 3: Dimension-4 Gromov Phase Transition — Taming Strictly Separates from Compatibility -/

/-- `ℤ⁴` vector carrier `(x₁, y₁, x₂, y₂)`. -/
structure Vec4 where
  x1 : Int
  y1 : Int
  x2 : Int
  y2 : Int
  deriving DecidableEq, Repr

def Vec4.neg (v : Vec4) : Vec4 :=
  ⟨-v.x1, -v.y1, -v.x2, -v.y2⟩

def Vec4.zero : Vec4 := ⟨0, 0, 0, 0⟩

/-- Standard symplectic 2-form `ω₄(u, v) = (u.x₁ v.y₁ - u.y₁ v.x₁) + (u.x₂ v.y₂ - u.y₂ v.x₂)`. -/
def omega4 (u v : Vec4) : Int :=
  (u.x1 * v.y1 - u.y1 * v.x1) + (u.x2 * v.y2 - u.y2 * v.x2)

/-- Unipotently sheared 4D almost-complex operator `J₄ = S J₀ S⁻¹`:
    `J₄(x₁, y₁, x₂, y₂) = (-y₁ - y₂, x₁ - x₂, -y₂, x₂)`. -/
def shearedJ4 (v : Vec4) : Vec4 :=
  ⟨-v.y1 - v.y2, v.x1 - v.x2, -v.y2, v.x2⟩

/-- `shearedJ4` is an exact almost-complex structure (`J₄(J₄(v)) = -v`). -/
theorem dim4_sheared_almost_complex_sq_neg_id (v : Vec4) :
    shearedJ4 (shearedJ4 v) = Vec4.neg v := by
  cases v with
  | mk x1 y1 x2 y2 =>
    simp [shearedJ4, Vec4.neg]
    omega

/-- **Strict 4D Symplectic Taming (`ω₄.Tames J₄`)**:
    `2 ω₄(v, J₄ v) = x₁² + (x₁ - x₂)² + x₂² + y₁² + (y₁ + y₂)² + y₂²`, so `ω₄(v, J₄ v) > 0`
    for every non-zero `v ∈ ℤ⁴`. -/
theorem dim4_sheared_tames_sum_of_squares_and_pos (v : Vec4) :
    2 * omega4 v (shearedJ4 v) =
      v.x1 * v.x1 + (v.x1 - v.x2) * (v.x1 - v.x2) + v.x2 * v.x2 +
      v.y1 * v.y1 + (v.y1 + v.y2) * (v.y1 + v.y2) + v.y2 * v.y2 ∧
    (v ≠ Vec4.zero → 0 < omega4 v (shearedJ4 v)) := by
  rcases v with ⟨x1, y1, x2, y2⟩
  have hSOS :
      2 * ((x1 * (x1 - x2) - y1 * (-y1 - y2)) + (x2 * x2 - y2 * (-y2))) =
      x1 * x1 + (x1 - x2) * (x1 - x2) + x2 * x2 +
      y1 * y1 + (y1 + y2) * (y1 + y2) + y2 * y2 := by
    have hL :
        (x1 * (x1 - x2) - y1 * (-y1 - y2)) + (x2 * x2 - y2 * (-y2)) =
        x1 * x1 - x1 * x2 + y1 * y1 + y1 * y2 + x2 * x2 + y2 * y2 := by
      have p1 : y1 * (-y1 - y2) = -(y1 * y1 + y1 * y2) := by
        calc
          y1 * (-y1 - y2) = y1 * (-(y1 + y2)) := by
            have hh : -y1 - y2 = -(y1 + y2) := by omega
            rw [hh]
          _ = -(y1 * (y1 + y2)) := Int.mul_neg y1 (y1 + y2)
          _ = -(y1 * y1 + y1 * y2) := by rw [Int.mul_add]
      have p2 : y2 * (-y2) = -(y2 * y2) := Int.mul_neg y2 y2
      rw [Int.mul_sub, p1, p2]
      omega
    have hR1 : (x1 - x2) * (x1 - x2) = x1 * x1 - x1 * x2 - x2 * x1 + x2 * x2 := by
      simp only [Int.sub_mul, Int.mul_sub]
      omega
    have hR2 : (y1 + y2) * (y1 + y2) = y1 * y1 + y1 * y2 + y2 * y1 + y2 * y2 := by
      simp only [Int.add_mul, Int.mul_add]
      omega
    have hxComm : x2 * x1 = x1 * x2 := Int.mul_comm x2 x1
    have hyComm : y2 * y1 = y1 * y2 := Int.mul_comm y2 y1
    rw [hL, hR1, hR2, hxComm, hyComm]
    omega
  refine ⟨hSOS, ?_⟩
  intro hNe
  have s1 := sq_nonneg x1
  have s2 := sq_nonneg (x1 - x2)
  have s3 := sq_nonneg x2
  have s4 := sq_nonneg y1
  have s5 := sq_nonneg (y1 + y2)
  have s6 := sq_nonneg y2
  have hTwoPos : 0 < 2 * ((x1 * (x1 - x2) - y1 * (-y1 - y2)) + (x2 * x2 - y2 * (-y2))) := by
    rw [hSOS]
    by_cases hx1 : x1 ≠ 0
    · have p := sq_pos_of_ne_zero hx1; omega
    · by_cases hy1 : y1 ≠ 0
      · have p := sq_pos_of_ne_zero hy1; omega
      · by_cases hx2 : x2 ≠ 0
        · have p := sq_pos_of_ne_zero hx2; omega
        · by_cases hy2 : y2 ≠ 0
          · have p := sq_pos_of_ne_zero hy2; omega
          · exfalso
            apply hNe
            have ex1 : x1 = 0 := Decidable.byContradiction hx1
            have ey1 : y1 = 0 := Decidable.byContradiction hy1
            have ex2 : x2 = 0 := Decidable.byContradiction hx2
            have ey2 : y2 = 0 := Decidable.byContradiction hy2
            subst ex1 ey1 ex2 ey2
            rfl
  change 0 < (x1 * (x1 - x2) - y1 * (-y1 - y2)) + (x2 * x2 - y2 * (-y2))
  omega

/-- **4D Separation of Taming vs. Compatibility**:
    `ω₄` strictly tames `shearedJ4`, yet `ω₄(J₄ e₂, J₄ e₃) = 1 ≠ 0 = ω₄(e₂, e₃)` and the twisted
    bilinear tensor `g(u, v) = ω₄(u, J₄ v)` is asymmetric (`g(e₁, e₃) = -1 ≠ 0 = g(e₃, e₁)`). -/
theorem dim4_tamed_not_compatible_and_asymmetric_metric :
    let e1 : Vec4 := ⟨1, 0, 0, 0⟩
    let e2 : Vec4 := ⟨0, 1, 0, 0⟩
    let e3 : Vec4 := ⟨0, 0, 1, 0⟩
    omega4 (shearedJ4 e2) (shearedJ4 e3) = 1 ∧
    omega4 e2 e3 = 0 ∧
    omega4 e1 (shearedJ4 e3) = -1 ∧
    omega4 e3 (shearedJ4 e1) = 0 := by
  decide

/-! ## Part 4: Universal Asymmetric Taming Contraction Certificate on `Fin n → Int` -/

/-- Finite coordinate dot product `∑_{i < n} u_i v_i`. -/
def dotFin : {n : Nat} → (Fin n → Int) → (Fin n → Int) → Int
  | 0, _, _ => 0
  | n + 1, u, v =>
      dotFin (fun i : Fin n => u i.castSucc) (fun i : Fin n => v i.castSucc) +
        u ⟨n, Nat.lt_succ_self n⟩ * v ⟨n, Nat.lt_succ_self n⟩

/-- Squared Euclidean norm `∑_{i < n} z_i²`. -/
def normSqFin {n : Nat} (z : Fin n → Int) : Int :=
  dotFin z z

/-- Exact coordinate quadratic expansion:
    `‖q z - p m‖² = q² ‖z‖² - 2 p q ⟨z, m⟩ + p² ‖m‖²`. -/
theorem normSqFin_scaled_step_eq {n : Nat} (q p : Int) (z m : Fin n → Int) :
    normSqFin (fun i => q * z i - p * m i) =
      q * q * normSqFin z - 2 * p * q * dotFin z m + p * p * normSqFin m := by
  induction n with
  | zero =>
      simp [normSqFin, dotFin]
  | succ n ih =>
      simp only [normSqFin, dotFin] at ih ⊢
      let zInit : Fin n → Int := fun i => z i.castSucc
      let mInit : Fin n → Int := fun i => m i.castSucc
      have hRec := ih zInit mInit
      let zn := z ⟨n, Nat.lt_succ_self n⟩
      let mn := m ⟨n, Nat.lt_succ_self n⟩
      have hCoord :
          (q * zn - p * mn) * (q * zn - p * mn) =
            q * q * (zn * zn) - 2 * p * q * (zn * mn) + p * p * (mn * mn) := by
        calc
          (q * zn - p * mn) * (q * zn - p * mn)
              = (q * zn) * (q * zn) - (q * zn) * (p * mn) - (p * mn) * (q * zn) + (p * mn) * (p * mn) := by
                simp only [Int.sub_mul, Int.mul_sub]
                omega
          _ = q * q * (zn * zn) - 2 * p * q * (zn * mn) + p * p * (mn * mn) := by
                have c1 : (q * zn) * (q * zn) = q * q * (zn * zn) := by
                  calc
                    (q * zn) * (q * zn) = q * (q * (zn * zn)) := by
                      simp only [Int.mul_assoc, Int.mul_left_comm]
                    _ = q * q * (zn * zn) := by rw [← Int.mul_assoc]
                have c2 : (p * mn) * (p * mn) = p * p * (mn * mn) := by
                  calc
                    (p * mn) * (p * mn) = p * (p * (mn * mn)) := by
                      simp only [Int.mul_assoc, Int.mul_left_comm]
                    _ = p * p * (mn * mn) := by rw [← Int.mul_assoc]
                have c3 : (q * zn) * (p * mn) = p * q * (zn * mn) := by
                  calc
                    (q * zn) * (p * mn) = p * (q * (zn * mn)) := by
                      simp only [Int.mul_assoc, Int.mul_left_comm]
                    _ = p * q * (zn * mn) := by rw [← Int.mul_assoc]
                have c4 : (p * mn) * (q * zn) = p * q * (zn * mn) := by
                  calc
                    (p * mn) * (q * zn) = p * (q * (zn * mn)) := by
                      simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
                    _ = p * q * (zn * mn) := by rw [← Int.mul_assoc]
                have c5 : 2 * p * q * (zn * mn) = p * q * (zn * mn) + p * q * (zn * mn) := by
                  have h2 : (2 : Int) * p * q = p * q + p * q := by
                    calc
                      (2 : Int) * p * q = (p + p) * q := by
                        have hp2 : (2 : Int) * p = p + p := by omega
                        rw [hp2]
                      _ = p * q + p * q := Int.add_mul p p q
                  rw [h2, Int.add_mul]
                omega
      change dotFin (fun i : Fin n => q * zInit i - p * mInit i)
          (fun i : Fin n => q * zInit i - p * mInit i) +
          (q * zn - p * mn) * (q * zn - p * mn) =
        q * q * (dotFin zInit zInit + zn * zn) -
          2 * p * q * (dotFin zInit mInit + zn * mn) +
          p * p * (dotFin mInit mInit + mn * mn)
      rw [hRec, hCoord]
      simp only [Int.mul_add]
      omega

/-- **Universal Asymmetric Taming Contraction Certificate**:
    Even when `M` is asymmetric (`g_J ≠ g_J^T`), taming coercivity `μ ‖z‖² ≤ ⟨z, M z⟩` together
    with `‖M z‖² ≤ L₂ ‖z‖²` guarantees
      `‖q z - p M z‖² ≤ (q² - 2 p q μ + p² L₂) ‖z‖²`,
    yielding strict discrete Lyapunov contraction `‖q z - p M z‖² < q² ‖z‖²` whenever
    `0 < p`, `0 ≤ q`, `p L₂ < 2 q μ`, and `0 < ‖z‖²`! -/
theorem asymmetric_tamed_operator_discrete_contraction
    {n : Nat} (M : (Fin n → Int) → (Fin n → Int))
    (z : Fin n → Int) (q p μ L2 : Int)
    (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hTame : μ * normSqFin z ≤ dotFin z (M z))
    (hLip : normSqFin (M z) ≤ L2 * normSqFin z) :
    normSqFin (fun i => q * z i - p * M z i) ≤
      (q * q - 2 * p * q * μ + p * p * L2) * normSqFin z ∧
    (0 < p → p * L2 < 2 * q * μ → 0 < normSqFin z →
      normSqFin (fun i => q * z i - p * M z i) < q * q * normSqFin z) := by
  have hEq := normSqFin_scaled_step_eq q p z (M z)
  have h2pNonneg : 0 ≤ 2 * p := by omega
  have h2pqNonneg : 0 ≤ 2 * p * q := Int.mul_nonneg h2pNonneg hq
  have hppNonneg : 0 ≤ p * p := Int.mul_nonneg hp hp
  have hTameScaled :
      (2 * p * q) * (μ * normSqFin z) ≤ (2 * p * q) * dotFin z (M z) :=
    Int.mul_le_mul_of_nonneg_left hTame h2pqNonneg
  have hLipScaled :
      (p * p) * normSqFin (M z) ≤ (p * p) * (L2 * normSqFin z) :=
    Int.mul_le_mul_of_nonneg_left hLip hppNonneg
  have hAssoc1 : (2 * p * q) * (μ * normSqFin z) = (2 * p * q * μ) * normSqFin z := by
    rw [← Int.mul_assoc]
  have hAssoc2 : (p * p) * (L2 * normSqFin z) = (p * p * L2) * normSqFin z := by
    rw [← Int.mul_assoc]
  have hRhsExpand :
      (q * q - 2 * p * q * μ + p * p * L2) * normSqFin z =
        q * q * normSqFin z - (2 * p * q * μ) * normSqFin z + (p * p * L2) * normSqFin z := by
    simp only [Int.add_mul, Int.sub_mul]
  have hBound :
      normSqFin (fun i => q * z i - p * M z i) ≤
        (q * q - 2 * p * q * μ + p * p * L2) * normSqFin z := by
    rw [hEq, hRhsExpand]
    omega
  refine ⟨hBound, ?_⟩
  intro hpPos hStepCond hzPos
  have hFactorNeg : p * (p * L2 - 2 * q * μ) < 0 := by
    have hNeg : p * L2 - 2 * q * μ < 0 := by omega
    have hPosNeg : 0 < p * (2 * q * μ - p * L2) := Int.mul_pos hpPos (by omega)
    have hDist : p * (2 * q * μ - p * L2) = -(p * (p * L2 - 2 * q * μ)) := by
      simp only [Int.mul_sub]
      omega
    omega
  have hExpandFactor :
      p * (p * L2 - 2 * q * μ) = p * p * L2 - 2 * p * q * μ := by
    rw [Int.mul_sub]
    have f1 : p * (p * L2) = p * p * L2 := by rw [← Int.mul_assoc]
    have f2 : p * (2 * q * μ) = 2 * p * q * μ := by
      calc
        p * (2 * q * μ) = p * (2 * (q * μ)) := by rw [Int.mul_assoc]
        _ = (2 * p) * (q * μ) := by
          rw [← Int.mul_assoc, Int.mul_comm p 2]
        _ = 2 * p * q * μ := by rw [← Int.mul_assoc]
    omega
  have hCoeffLt : q * q - 2 * p * q * μ + p * p * L2 < q * q := by
    omega
  have hStrictMul :
      (q * q - 2 * p * q * μ + p * p * L2) * normSqFin z < q * q * normSqFin z := by
    have hDiffPos : 0 < (q * q - (q * q - 2 * p * q * μ + p * p * L2)) * normSqFin z :=
      Int.mul_pos (by omega) hzPos
    rw [Int.sub_mul] at hDiffPos
    omega
  omega

end CommonGround.Frontier.SymplecticTamingAndSaddleCoercivity
