/-
  LittlewoodPaleyParaproductAndCFLDispersionFrontier.lean
  -------------------------------------------------------
  Pure-core Lean 4.33.0 frontier formalization (0 imports, 0 sorry) unifying
  Folders 02, 05, 06, 09, and 10 around four foundational mechanisms of
  harmonic analysis, nonlinear PDE regularity, and numerical/spectral operators:

  1. Exact Dyadic Littlewood–Paley Shell Orthogonality, Plancherel Partition &
     Bernstein–Poincaré Gradient Diagonalization (`16 ‖D x‖₂² = 2 ‖4 Δ₁ x‖₂² + 4 ‖4 Δ₂ x‖₂²`)
     vs. High-High → DC Aliasing (`(1,-1,1,-1)² = (1,1,1,1)`) and Unweighted `L²` Spike Blowup.
  2. Discrete Calderón / Bony Paraproduct Transport Commutator Cancellation
     (`[D, a·] u = (D a) ⊙ u`, Zero Derivative Loss under Lipschitz Velocity)
     vs. Rough Non-Lipschitz Velocity Derivative Explosion (`16 M²`).
  3. Exact Courant–Friedrichs–Lewy (`CFL`) Upwind Energy-Viscosity Identity
     (`‖U‖₂² + C(S - C) ‖D u‖₂² = S² ‖u‖₂²`) vs. Super-Courant Anti-Diffusive `9×`
     Nyquist Blowup (`ν = 2 > 1`) and Centered Forward-Euler Unconditional Instability
     vs. Skew-Symmetric Crank–Nicolson / Cayley Unitary Conservation (`‖(S-K)u‖₂² = ‖(S+K)u‖₂²`).
  4. Discrete Agmon–Sobolev `L^∞ ↪ H¹` Pointwise Control & `H¹` Banach Multiplication
     Algebra Closure (`‖u ⊙ v‖_{H¹} ≤ C ‖u‖_{H¹} ‖v‖_{H¹}`).
-/

namespace CommonGround.Frontier.LittlewoodPaleyAndCFL

/-- Exact integer squaring helper. -/
def sq4 (x : Int) : Int := x * x

/-- 4-point Euclidean inner product over `ℤ⁴`. -/
def dot4 (x0 x1 x2 x3 y0 y1 y2 y3 : Int) : Int :=
  x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3

/-- 4-point squared `L²` norm `‖x‖₂² = x0² + x1² + x2² + x3²`. -/
def normSq4 (x0 x1 x2 x3 : Int) : Int :=
  sq4 x0 + sq4 x1 + sq4 x2 + sq4 x3

/-- Cyclic forward difference gradient `(D x)_j = x_{(j+1) mod 4} - x_j`. -/
def diff0 (x0 x1 _x2 _x3 : Int) : Int := x1 - x0
def diff1 (_x0 x1 x2 _x3 : Int) : Int := x2 - x1
def diff2 (_x0 _x1 x2 x3 : Int) : Int := x3 - x2
def diff3 (x0 _x1 _x2 x3 : Int) : Int := x0 - x3

/-- Squared `L²` Dirichlet gradient energy `‖D x‖₂²`. -/
def gradSq4 (x0 x1 x2 x3 : Int) : Int :=
  normSq4 (diff0 x0 x1 x2 x3) (diff1 x0 x1 x2 x3) (diff2 x0 x1 x2 x3) (diff3 x0 x1 x2 x3)

/-- Scaled Littlewood–Paley DC projector `4 · P₀ x = (S, S, S, S)` (`k = 0` shell). -/
def lp0_0 (x0 x1 x2 x3 : Int) : Int := x0 + x1 + x2 + x3
def lp0_1 (x0 x1 x2 x3 : Int) : Int := x0 + x1 + x2 + x3
def lp0_2 (x0 x1 x2 x3 : Int) : Int := x0 + x1 + x2 + x3
def lp0_3 (x0 x1 x2 x3 : Int) : Int := x0 + x1 + x2 + x3

/-- Scaled Littlewood–Paley dyadic shell `4 · Δ₁ x` (`k ∈ {1, 3}` medium-frequency shell). -/
def lp1_0 (x0 _x1 x2 _x3 : Int) : Int := 2 * (x0 - x2)
def lp1_1 (_x0 x1 _x2 x3 : Int) : Int := 2 * (x1 - x3)
def lp1_2 (x0 _x1 x2 _x3 : Int) : Int := 2 * (x2 - x0)
def lp1_3 (_x0 x1 _x2 x3 : Int) : Int := 2 * (x3 - x1)

/-- Scaled Littlewood–Paley Nyquist shell `4 · Δ₂ x = (A, -A, A, -A)` (`k = 2` shell). -/
def lp2_0 (x0 x1 x2 x3 : Int) : Int := x0 - x1 + x2 - x3
def lp2_1 (x0 x1 x2 x3 : Int) : Int := -(x0 - x1 + x2 - x3)
def lp2_2 (x0 x1 x2 x3 : Int) : Int := x0 - x1 + x2 - x3
def lp2_3 (x0 x1 x2 x3 : Int) : Int := -(x0 - x1 + x2 - x3)

theorem sq4_nonneg (x : Int) : 0 ≤ sq4 x := by
  unfold sq4
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have hn : x ≤ 0 := Int.le_of_lt (Int.lt_of_not_ge h)
    exact Int.mul_nonneg_of_nonpos_of_nonpos hn hn

theorem normSq4_nonneg (x0 x1 x2 x3 : Int) : 0 ≤ normSq4 x0 x1 x2 x3 := by
  unfold normSq4
  have h0 := sq4_nonneg x0
  have h1 := sq4_nonneg x1
  have h2 := sq4_nonneg x2
  have h3 := sq4_nonneg x3
  omega

theorem gradSq4_nonneg (x0 x1 x2 x3 : Int) : 0 ≤ gradSq4 x0 x1 x2 x3 := by
  unfold gradSq4
  exact normSq4_nonneg _ _ _ _

/-!
## 1. Dyadic Littlewood–Paley Orthogonality, Plancherel & Bernstein–Poincaré vs. Aliasing
-/

/-- **Theorem 1 (Littlewood–Paley Dyadic Shell Orthogonality, Bernstein–Poincaré Gradient
    Diagonalization & High-High → DC Aliasing Counterexample)**:
  1. **Exact Dyadic Identity Resolution & Pairwise `L²` Shell Orthogonality**:
     `4 P₀ + 4 Δ₁ + 4 Δ₂ = 4 I` at all 4 nodes, and `⟨4 P₀ x, 4 Δ₁ y⟩ = ⟨4 P₀ x, 4 Δ₂ y⟩ =
     ⟨4 Δ₁ x, 4 Δ₂ y⟩ = 0` universally for all `x, y ∈ ℤ⁴`.
  2. **Exact Dyadic Plancherel & Gradient Spectral Diagonalization**:
     `‖4 P₀ x‖₂² + ‖4 Δ₁ x‖₂² + ‖4 Δ₂ x‖₂² = 16 ‖x‖₂²` AND
     `16 ‖D x‖₂² = 2 ‖4 Δ₁ x‖₂² + 4 ‖4 Δ₂ x‖₂²`!
  3. **Bernstein Upper Bound & Zero-Mean Poincaré–Wirtinger Spectral Gap (`λ₁ = 2`)**:
     Universally `‖D x‖₂² ≤ 4 ‖x‖₂²`, AND for every zero-mean field (`x0 + x1 + x2 + x3 = 0`),
     `2 ‖x‖₂² ≤ ‖D x‖₂²` — whereas dropping zero-mean (`x = (1, 1, 1, 1)`) gives `‖D x‖₂² = 0 < 8`.
  4. **Bony High-High → DC Aliasing & Unweighted `L²` Non-Closure**:
     Pure Nyquist wave `u = (1, -1, 1, -1)` has `P₀ u = Δ₁ u = 0`, yet its quadratic product
     `u ⊙ u = (1, 1, 1, 1)` aliases 100% into the DC shell (`4 P₀(u ⊙ u) = (16,16,16,16)`,
     `4 Δ₂(u ⊙ u) = 0`), and spike `v_N = (3, 0, 0, 0)` violates `L²` algebra bound `C = 8`
     (`‖v ⊙ v‖₂² = 81 > 8 · 9 = 72`). -/
theorem littlewood_paley_dyadic_orthogonality_and_plancherel_vs_nyquist_dc_aliasing :
    (∀ x0 x1 x2 x3 y0 y1 y2 y3 : Int,
      lp0_0 x0 x1 x2 x3 + lp1_0 x0 x1 x2 x3 + lp2_0 x0 x1 x2 x3 = 4 * x0 ∧
      lp0_1 x0 x1 x2 x3 + lp1_1 x0 x1 x2 x3 + lp2_1 x0 x1 x2 x3 = 4 * x1 ∧
      lp0_2 x0 x1 x2 x3 + lp1_2 x0 x1 x2 x3 + lp2_2 x0 x1 x2 x3 = 4 * x2 ∧
      lp0_3 x0 x1 x2 x3 + lp1_3 x0 x1 x2 x3 + lp2_3 x0 x1 x2 x3 = 4 * x3 ∧
      dot4 (lp0_0 x0 x1 x2 x3) (lp0_1 x0 x1 x2 x3) (lp0_2 x0 x1 x2 x3) (lp0_3 x0 x1 x2 x3)
           (lp1_0 y0 y1 y2 y3) (lp1_1 y0 y1 y2 y3) (lp1_2 y0 y1 y2 y3) (lp1_3 y0 y1 y2 y3) = 0 ∧
      dot4 (lp0_0 x0 x1 x2 x3) (lp0_1 x0 x1 x2 x3) (lp0_2 x0 x1 x2 x3) (lp0_3 x0 x1 x2 x3)
           (lp2_0 y0 y1 y2 y3) (lp2_1 y0 y1 y2 y3) (lp2_2 y0 y1 y2 y3) (lp2_3 y0 y1 y2 y3) = 0 ∧
      dot4 (lp1_0 x0 x1 x2 x3) (lp1_1 x0 x1 x2 x3) (lp1_2 x0 x1 x2 x3) (lp1_3 x0 x1 x2 x3)
           (lp2_0 y0 y1 y2 y3) (lp2_1 y0 y1 y2 y3) (lp2_2 y0 y1 y2 y3) (lp2_3 y0 y1 y2 y3) = 0) ∧
    (∀ x0 x1 x2 x3 : Int,
      normSq4 (lp0_0 x0 x1 x2 x3) (lp0_1 x0 x1 x2 x3) (lp0_2 x0 x1 x2 x3) (lp0_3 x0 x1 x2 x3) +
      normSq4 (lp1_0 x0 x1 x2 x3) (lp1_1 x0 x1 x2 x3) (lp1_2 x0 x1 x2 x3) (lp1_3 x0 x1 x2 x3) +
      normSq4 (lp2_0 x0 x1 x2 x3) (lp2_1 x0 x1 x2 x3) (lp2_2 x0 x1 x2 x3) (lp2_3 x0 x1 x2 x3) =
        16 * normSq4 x0 x1 x2 x3 ∧
      16 * gradSq4 x0 x1 x2 x3 =
        2 * normSq4 (lp1_0 x0 x1 x2 x3) (lp1_1 x0 x1 x2 x3) (lp1_2 x0 x1 x2 x3) (lp1_3 x0 x1 x2 x3) +
        4 * normSq4 (lp2_0 x0 x1 x2 x3) (lp2_1 x0 x1 x2 x3) (lp2_2 x0 x1 x2 x3) (lp2_3 x0 x1 x2 x3)) ∧
    (∀ x0 x1 x2 x3 : Int,
      gradSq4 x0 x1 x2 x3 ≤ 4 * normSq4 x0 x1 x2 x3 ∧
      (x0 + x1 + x2 + x3 = 0 → 2 * normSq4 x0 x1 x2 x3 ≤ gradSq4 x0 x1 x2 x3)) ∧
    (gradSq4 1 1 1 1 = 0 ∧ 2 * normSq4 1 1 1 1 = 8 ∧
      lp0_0 1 (-1) 1 (-1) = 0 ∧ lp1_0 1 (-1) 1 (-1) = 0 ∧ lp2_0 1 (-1) 1 (-1) = 4 ∧
      lp0_0 (1 * 1) ((-1) * (-1)) (1 * 1) ((-1) * (-1)) = 4 ∧
      lp2_0 (1 * 1) ((-1) * (-1)) (1 * 1) ((-1) * (-1)) = 0 ∧
      normSq4 (3 * 3) 0 0 0 > 8 * normSq4 3 0 0 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x0 x1 x2 x3 y0 y1 y2 y3
    unfold dot4 lp0_0 lp0_1 lp0_2 lp0_3 lp1_0 lp1_1 lp1_2 lp1_3 lp2_0 lp2_1 lp2_2 lp2_3
    refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩ <;> grind
  · intro x0 x1 x2 x3
    unfold gradSq4 normSq4 sq4 diff0 diff1 diff2 diff3
      lp0_0 lp0_1 lp0_2 lp0_3 lp1_0 lp1_1 lp1_2 lp1_3 lp2_0 lp2_1 lp2_2 lp2_3
    constructor <;> grind
  · intro x0 x1 x2 x3
    have hP0 := normSq4_nonneg (lp0_0 x0 x1 x2 x3) (lp0_1 x0 x1 x2 x3) (lp0_2 x0 x1 x2 x3) (lp0_3 x0 x1 x2 x3)
    have hP1 := normSq4_nonneg (lp1_0 x0 x1 x2 x3) (lp1_1 x0 x1 x2 x3) (lp1_2 x0 x1 x2 x3) (lp1_3 x0 x1 x2 x3)
    have hP2 := normSq4_nonneg (lp2_0 x0 x1 x2 x3) (lp2_1 x0 x1 x2 x3) (lp2_2 x0 x1 x2 x3) (lp2_3 x0 x1 x2 x3)
    have hPlan :
        normSq4 (lp0_0 x0 x1 x2 x3) (lp0_1 x0 x1 x2 x3) (lp0_2 x0 x1 x2 x3) (lp0_3 x0 x1 x2 x3) +
        normSq4 (lp1_0 x0 x1 x2 x3) (lp1_1 x0 x1 x2 x3) (lp1_2 x0 x1 x2 x3) (lp1_3 x0 x1 x2 x3) +
        normSq4 (lp2_0 x0 x1 x2 x3) (lp2_1 x0 x1 x2 x3) (lp2_2 x0 x1 x2 x3) (lp2_3 x0 x1 x2 x3) =
          16 * normSq4 x0 x1 x2 x3 := by
      unfold normSq4 sq4 lp0_0 lp0_1 lp0_2 lp0_3 lp1_0 lp1_1 lp1_2 lp1_3 lp2_0 lp2_1 lp2_2 lp2_3
      grind
    have hGrad :
        16 * gradSq4 x0 x1 x2 x3 =
          2 * normSq4 (lp1_0 x0 x1 x2 x3) (lp1_1 x0 x1 x2 x3) (lp1_2 x0 x1 x2 x3) (lp1_3 x0 x1 x2 x3) +
          4 * normSq4 (lp2_0 x0 x1 x2 x3) (lp2_1 x0 x1 x2 x3) (lp2_2 x0 x1 x2 x3) (lp2_3 x0 x1 x2 x3) := by
      unfold gradSq4 normSq4 sq4 diff0 diff1 diff2 diff3 lp1_0 lp1_1 lp1_2 lp1_3 lp2_0 lp2_1 lp2_2 lp2_3
      grind
    refine ⟨?_, ?_⟩
    · omega
    · intro hMean
      have hZeroP0 :
          normSq4 (lp0_0 x0 x1 x2 x3) (lp0_1 x0 x1 x2 x3) (lp0_2 x0 x1 x2 x3) (lp0_3 x0 x1 x2 x3) = 0 := by
        unfold normSq4 sq4 lp0_0 lp0_1 lp0_2 lp0_3
        rw [hMean]
        decide
      omega
  · decide

/-!
## 2. Calderón / Bony Transport Commutator Cancellation vs. Rough Velocity Derivative Loss
-/

/-- Transport commutator `[D, a·] u = D(a ⊙ u) - (shift a) ⊙ (D u)` at each cyclic node `0..3`. -/
def calderonComm0 (a0 a1 _a2 _a3 u0 u1 _u2 _u3 : Int) : Int :=
  (a1 * u1 - a0 * u0) - a1 * (u1 - u0)
def calderonComm1 (_a0 a1 a2 _a3 _u0 u1 u2 _u3 : Int) : Int :=
  (a2 * u2 - a1 * u1) - a2 * (u2 - u1)
def calderonComm2 (_a0 _a1 a2 a3 _u0 _u1 u2 u3 : Int) : Int :=
  (a3 * u3 - a2 * u2) - a3 * (u3 - u2)
def calderonComm3 (a0 _a1 _a2 a3 u0 _u1 _u2 u3 : Int) : Int :=
  (a0 * u0 - a3 * u3) - a0 * (u0 - u3)

theorem mul_nonneg_of_sq_le (p q u2 : Int) (hpq : p ≤ q) (hu : 0 ≤ u2) : p * u2 ≤ q * u2 := by
  have hd : 0 ≤ (q - p) * u2 := Int.mul_nonneg (by omega) hu
  have hexp : (q - p) * u2 = q * u2 - p * u2 := by grind
  omega

/-- **Theorem 2 (Calderón Transport Commutator Cancellation vs. Rough Velocity Derivative Loss)**:
  1. **Universal Commutator Cancellation (`[D, a·] u = (D a) ⊙ u`)**:
     Every `D u` derivative cancels identically out of `D(a ⊙ u) - (shift a) ⊙ (D u)`, leaving
     pure zero-order multiplication `(D a)_j · u_j` at all 4 nodes.
  2. **Lipschitz Velocity Taming (`Zero Derivative Loss`)**:
     Whenever velocity gradient satisfies `(D a)_j² ≤ L²`, the commutator obeys
     `‖[D, a·] u‖₂² ≤ L² ‖u‖₂²` independently of how oscillatory `D u` is!
  3. **Premise-Failure Counterexample (Rough Non-Lipschitz Velocity Derivative Explosion)**:
     On smooth constant scalar `u = (1, 1, 1, 1)` (`D u = 0`, `‖u‖₂² = 4`) and rough Nyquist
     velocity `a_M = (M, -M, M, -M)`, `(shift a) ⊙ (D u) = 0` yet `‖[D, a_M·] u‖₂² = 16 M²`! -/
theorem calderon_paraproduct_commutator_taming_vs_rough_velocity_derivative_loss :
    (∀ a0 a1 a2 a3 u0 u1 u2 u3 : Int,
      calderonComm0 a0 a1 a2 a3 u0 u1 u2 u3 = diff0 a0 a1 a2 a3 * u0 ∧
      calderonComm1 a0 a1 a2 a3 u0 u1 u2 u3 = diff1 a0 a1 a2 a3 * u1 ∧
      calderonComm2 a0 a1 a2 a3 u0 u1 u2 u3 = diff2 a0 a1 a2 a3 * u2 ∧
      calderonComm3 a0 a1 a2 a3 u0 u1 u2 u3 = diff3 a0 a1 a2 a3 * u3) ∧
    (∀ a0 a1 a2 a3 u0 u1 u2 u3 L : Int,
      sq4 (diff0 a0 a1 a2 a3) ≤ sq4 L →
      sq4 (diff1 a0 a1 a2 a3) ≤ sq4 L →
      sq4 (diff2 a0 a1 a2 a3) ≤ sq4 L →
      sq4 (diff3 a0 a1 a2 a3) ≤ sq4 L →
      normSq4
        (calderonComm0 a0 a1 a2 a3 u0 u1 u2 u3)
        (calderonComm1 a0 a1 a2 a3 u0 u1 u2 u3)
        (calderonComm2 a0 a1 a2 a3 u0 u1 u2 u3)
        (calderonComm3 a0 a1 a2 a3 u0 u1 u2 u3) ≤ sq4 L * normSq4 u0 u1 u2 u3) ∧
    (∀ M : Int,
      gradSq4 1 1 1 1 = 0 ∧
      normSq4
        (calderonComm0 M (-M) M (-M) 1 1 1 1)
        (calderonComm1 M (-M) M (-M) 1 1 1 1)
        (calderonComm2 M (-M) M (-M) 1 1 1 1)
        (calderonComm3 M (-M) M (-M) 1 1 1 1) = 16 * sq4 M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a0 a1 a2 a3 u0 u1 u2 u3
    unfold calderonComm0 calderonComm1 calderonComm2 calderonComm3 diff0 diff1 diff2 diff3
    refine ⟨?_, ?_, ?_, ?_⟩ <;> grind
  · intro a0 a1 a2 a3 u0 u1 u2 u3 L hd0 hd1 hd2 hd3
    have hc0 : sq4 (calderonComm0 a0 a1 a2 a3 u0 u1 u2 u3) = sq4 (diff0 a0 a1 a2 a3) * sq4 u0 := by
      unfold calderonComm0 diff0 sq4; grind
    have hc1 : sq4 (calderonComm1 a0 a1 a2 a3 u0 u1 u2 u3) = sq4 (diff1 a0 a1 a2 a3) * sq4 u1 := by
      unfold calderonComm1 diff1 sq4; grind
    have hc2 : sq4 (calderonComm2 a0 a1 a2 a3 u0 u1 u2 u3) = sq4 (diff2 a0 a1 a2 a3) * sq4 u2 := by
      unfold calderonComm2 diff2 sq4; grind
    have hc3 : sq4 (calderonComm3 a0 a1 a2 a3 u0 u1 u2 u3) = sq4 (diff3 a0 a1 a2 a3) * sq4 u3 := by
      unfold calderonComm3 diff3 sq4; grind
    have b0 := mul_nonneg_of_sq_le _ _ (sq4 u0) hd0 (sq4_nonneg u0)
    have b1 := mul_nonneg_of_sq_le _ _ (sq4 u1) hd1 (sq4_nonneg u1)
    have b2 := mul_nonneg_of_sq_le _ _ (sq4 u2) hd2 (sq4_nonneg u2)
    have b3 := mul_nonneg_of_sq_le _ _ (sq4 u3) hd3 (sq4_nonneg u3)
    unfold normSq4
    have hsum : sq4 L * (sq4 u0 + sq4 u1 + sq4 u2 + sq4 u3) =
        sq4 L * sq4 u0 + sq4 L * sq4 u1 + sq4 L * sq4 u2 + sq4 L * sq4 u3 := by grind
    omega
  · intro M
    refine ⟨by decide, ?_⟩
    unfold normSq4 sq4 calderonComm0 calderonComm1 calderonComm2 calderonComm3
    grind

/-!
## 3. Exact CFL Upwind Viscosity Identity vs. Super-Courant & Centered Forward-Euler Blowup
-/

/-- 1st-order upwind advection `U_j = (S - C) u_j + C u_{(j-1) mod 4}` (scale `S`, Courant `C`). -/
def upwind0 (S C u0 _u1 _u2 u3 : Int) : Int := (S - C) * u0 + C * u3
def upwind1 (S C u0 u1 _u2 _u3 : Int) : Int := (S - C) * u1 + C * u0
def upwind2 (S C _u0 u1 u2 _u3 : Int) : Int := (S - C) * u2 + C * u1
def upwind3 (S C _u0 _u1 u2 u3 : Int) : Int := (S - C) * u3 + C * u2

/-- Centered skew-symmetric transport operator `(K u)_j = C * (u_{j+1} - u_{j-1})`. -/
def skewAdv0 (C _u0 u1 _u2 u3 : Int) : Int := C * (u1 - u3)
def skewAdv1 (C u0 _u1 u2 _u3 : Int) : Int := C * (u2 - u0)
def skewAdv2 (C _u0 u1 _u2 u3 : Int) : Int := C * (u3 - u1)
def skewAdv3 (C u0 _u1 u2 _u3 : Int) : Int := C * (u0 - u2)

/-- **Theorem 3 (Exact CFL Upwind Viscosity Identity vs. Super-Courant `9×` Nyquist Blowup,
    Centered Forward-Euler Unconditional Instability & Crank–Nicolson Cayley Conservation)**:
  1. **Exact Cyclic CFL Energy-Viscosity Identity & Mass Conservation**:
     `‖upwind(S, C, u)‖₂² + C * (S - C) * ‖D u‖₂² = S² * ‖u‖₂²` and `∑ U_j = S ∑ u_j`.
  2. **CFL Stability Cone (`0 ≤ C ≤ S`, Courant `ν = C/S ∈ [0, 1]`)**:
     `0 ≤ C` and `C ≤ S` imply `‖upwind(S, C, u)‖₂² ≤ S² * ‖u‖₂²` for ALL `u ∈ ℤ⁴`.
  3. **Super-Courant Anti-Diffusive Blowup (`S = 1, C = 2`, Courant `ν = 2 > 1`)**:
     `C * (S - C) = -2 < 0` flips viscosity negative; Nyquist mode `u = (1, -1, 1, -1)` (`‖u‖₂² = 4`)
     blows up in one step to `(-3, 3, -3, 3)` with `‖U‖₂² = 36 = 9 * ‖u‖₂² > 4`!
  4. **Centered Forward-Euler Unconditional Instability vs. Crank–Nicolson Unitary Conservation**:
     Explicit `S u - K u` inflates energy `‖S u - K u‖₂² = S² ‖u‖₂² + ‖K u‖₂²` (strictly `> S² ‖u‖₂²`
     on `u = (1, 0, -1, 0)` for EVERY `C ≠ 0`), whereas Crank–Nicolson `(S + K) u^{n+1} = (S - K) u^n`
     satisfies `‖(S - K) u‖₂² = ‖(S + K) u‖₂²` for ALL `S, C ∈ ℤ`! -/
theorem cfl_upwind_exact_viscosity_dissipation_vs_super_courant_and_centered_euler_blowup :
    (∀ S C u0 u1 u2 u3 : Int,
      normSq4
        (upwind0 S C u0 u1 u2 u3) (upwind1 S C u0 u1 u2 u3)
        (upwind2 S C u0 u1 u2 u3) (upwind3 S C u0 u1 u2 u3) +
      C * (S - C) * gradSq4 u0 u1 u2 u3 = sq4 S * normSq4 u0 u1 u2 u3 ∧
      upwind0 S C u0 u1 u2 u3 + upwind1 S C u0 u1 u2 u3 +
      upwind2 S C u0 u1 u2 u3 + upwind3 S C u0 u1 u2 u3 = S * (u0 + u1 + u2 + u3)) ∧
    (∀ S C u0 u1 u2 u3 : Int,
      0 ≤ C → C ≤ S →
      normSq4
        (upwind0 S C u0 u1 u2 u3) (upwind1 S C u0 u1 u2 u3)
        (upwind2 S C u0 u1 u2 u3) (upwind3 S C u0 u1 u2 u3) ≤ sq4 S * normSq4 u0 u1 u2 u3) ∧
    (normSq4 1 (-1) 1 (-1) = 4 ∧
      normSq4
        (upwind0 1 2 1 (-1) 1 (-1)) (upwind1 1 2 1 (-1) 1 (-1))
        (upwind2 1 2 1 (-1) 1 (-1)) (upwind3 1 2 1 (-1) 1 (-1)) = 36) ∧
    (∀ S C u0 u1 u2 u3 : Int,
      normSq4
        (S * u0 - skewAdv0 C u0 u1 u2 u3) (S * u1 - skewAdv1 C u0 u1 u2 u3)
        (S * u2 - skewAdv2 C u0 u1 u2 u3) (S * u3 - skewAdv3 C u0 u1 u2 u3) =
        sq4 S * normSq4 u0 u1 u2 u3 +
        normSq4 (skewAdv0 C u0 u1 u2 u3) (skewAdv1 C u0 u1 u2 u3)
                (skewAdv2 C u0 u1 u2 u3) (skewAdv3 C u0 u1 u2 u3) ∧
      normSq4
        (S * u0 - skewAdv0 C u0 u1 u2 u3) (S * u1 - skewAdv1 C u0 u1 u2 u3)
        (S * u2 - skewAdv2 C u0 u1 u2 u3) (S * u3 - skewAdv3 C u0 u1 u2 u3) =
      normSq4
        (S * u0 + skewAdv0 C u0 u1 u2 u3) (S * u1 + skewAdv1 C u0 u1 u2 u3)
        (S * u2 + skewAdv2 C u0 u1 u2 u3) (S * u3 + skewAdv3 C u0 u1 u2 u3) ∧
      (C ≠ 0 →
        sq4 S * normSq4 1 0 (-1) 0 <
        normSq4
          (S * 1 - skewAdv0 C 1 0 (-1) 0) (S * 0 - skewAdv1 C 1 0 (-1) 0)
          (S * (-1) - skewAdv2 C 1 0 (-1) 0) (S * 0 - skewAdv3 C 1 0 (-1) 0))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S C u0 u1 u2 u3
    unfold upwind0 upwind1 upwind2 upwind3 gradSq4 normSq4 sq4 diff0 diff1 diff2 diff3
    constructor <;> grind
  · intro S C u0 u1 u2 u3 hC0 hCS
    have hId :
        normSq4
          (upwind0 S C u0 u1 u2 u3) (upwind1 S C u0 u1 u2 u3)
          (upwind2 S C u0 u1 u2 u3) (upwind3 S C u0 u1 u2 u3) +
        C * (S - C) * gradSq4 u0 u1 u2 u3 = sq4 S * normSq4 u0 u1 u2 u3 := by
      unfold upwind0 upwind1 upwind2 upwind3 gradSq4 normSq4 sq4 diff0 diff1 diff2 diff3
      grind
    have hVisc : 0 ≤ C * (S - C) := Int.mul_nonneg hC0 (by omega)
    have hProd : 0 ≤ C * (S - C) * gradSq4 u0 u1 u2 u3 :=
      Int.mul_nonneg hVisc (gradSq4_nonneg u0 u1 u2 u3)
    omega
  · decide
  · intro S C u0 u1 u2 u3
    refine ⟨?_, ?_, ?_⟩
    · unfold normSq4 sq4 skewAdv0 skewAdv1 skewAdv2 skewAdv3; grind
    · unfold normSq4 sq4 skewAdv0 skewAdv1 skewAdv2 skewAdv3; grind
    · intro hC
      have hPos : 0 < sq4 C := by
        unfold sq4
        by_cases hp : 0 < C
        · exact Int.mul_pos hp hp
        · have hn : C < 0 := by omega
          exact Int.mul_pos_of_neg_of_neg hn hn
      have hCalc :
          normSq4
            (S * 1 - skewAdv0 C 1 0 (-1) 0) (S * 0 - skewAdv1 C 1 0 (-1) 0)
            (S * (-1) - skewAdv2 C 1 0 (-1) 0) (S * 0 - skewAdv3 C 1 0 (-1) 0) =
          sq4 S * normSq4 1 0 (-1) 0 + 8 * sq4 C := by
        unfold normSq4 sq4 skewAdv0 skewAdv1 skewAdv2 skewAdv3
        grind
      omega

/-!
## 4. Discrete Agmon–Sobolev Pointwise Embedding & `H¹` Multiplication Algebra Closure
-/

/-- Squared discrete `H¹` Sobolev norm `‖u‖_{H¹}² = ‖u‖₂² + ‖D u‖₂²`. -/
def sobolevH1Sq4 (u0 u1 u2 u3 : Int) : Int :=
  normSq4 u0 u1 u2 u3 + gradSq4 u0 u1 u2 u3

/-- **Theorem 4 (Discrete Agmon–Sobolev Pointwise `L^∞ ↪ H¹` Control & Banach Algebra Closure)**:
  1. **Exact 3-Shell Cauchy–Schwarz SOS Identity**:
     `3 * (a² + b² + c²) - (a + b + c)² = (a - b)² + (a - c)² + (b - c)² ≥ 0`.
  2. **Agmon–Sobolev Pointwise Bound & `H¹` Banach Multiplication Algebra (`C = 2`)**:
     Every nodal value obeys `sq4 u_j ≤ normSq4 u ≤ sobolevH1Sq4 u`, and for ALL `u, v ∈ ℤ⁴`,
     `sobolevH1Sq4 (u ⊙ v) ≤ 2 * sobolevH1Sq4 u * sobolevH1Sq4 v`! -/
theorem agmon_sobolev_pointwise_and_h1_banach_algebra_closure :
    (∀ a b c : Int,
      3 * (sq4 a + sq4 b + sq4 c) - sq4 (a + b + c) =
        sq4 (a - b) + sq4 (a - c) + sq4 (b - c) ∧
      sq4 (a + b + c) ≤ 3 * (sq4 a + sq4 b + sq4 c)) ∧
    (∀ u0 u1 u2 u3 v0 v1 v2 v3 : Int,
      sq4 u0 ≤ sobolevH1Sq4 u0 u1 u2 u3 ∧
      sq4 u1 ≤ sobolevH1Sq4 u0 u1 u2 u3 ∧
      sq4 u2 ≤ sobolevH1Sq4 u0 u1 u2 u3 ∧
      sq4 u3 ≤ sobolevH1Sq4 u0 u1 u2 u3 ∧
      sobolevH1Sq4 (u0 * v0) (u1 * v1) (u2 * v2) (u3 * v3) ≤
        2 * sobolevH1Sq4 u0 u1 u2 u3 * sobolevH1Sq4 v0 v1 v2 v3) := by
  refine ⟨?_, ?_⟩
  · intro a b c
    have hId :
        3 * (sq4 a + sq4 b + sq4 c) - sq4 (a + b + c) =
          sq4 (a - b) + sq4 (a - c) + sq4 (b - c) := by
      unfold sq4; grind
    have h1 := sq4_nonneg (a - b)
    have h2 := sq4_nonneg (a - c)
    have h3 := sq4_nonneg (b - c)
    exact ⟨hId, by omega⟩
  · intro u0 u1 u2 u3 v0 v1 v2 v3
    have hU := normSq4_nonneg u0 u1 u2 u3
    have hGU := gradSq4_nonneg u0 u1 u2 u3
    have hV := normSq4_nonneg v0 v1 v2 v3
    have hGV := gradSq4_nonneg v0 v1 v2 v3
    have hu0 := sq4_nonneg u0; have hu1 := sq4_nonneg u1
    have hu2 := sq4_nonneg u2; have hu3 := sq4_nonneg u3
    have hv0 := sq4_nonneg v0; have hv1 := sq4_nonneg v1
    have hv2 := sq4_nonneg v2; have hv3 := sq4_nonneg v3
    have pu0 : sq4 u0 ≤ normSq4 u0 u1 u2 u3 := by unfold normSq4; omega
    have pu1 : sq4 u1 ≤ normSq4 u0 u1 u2 u3 := by unfold normSq4; omega
    have pu2 : sq4 u2 ≤ normSq4 u0 u1 u2 u3 := by unfold normSq4; omega
    have pu3 : sq4 u3 ≤ normSq4 u0 u1 u2 u3 := by unfold normSq4; omega
    have qv0 : sq4 v0 ≤ normSq4 v0 v1 v2 v3 := by unfold normSq4; omega
    have qv1 : sq4 v1 ≤ normSq4 v0 v1 v2 v3 := by unfold normSq4; omega
    have qv2 : sq4 v2 ≤ normSq4 v0 v1 v2 v3 := by unfold normSq4; omega
    have qv3 : sq4 v3 ≤ normSq4 v0 v1 v2 v3 := by unfold normSq4; omega
    have p0 : sq4 u0 ≤ sobolevH1Sq4 u0 u1 u2 u3 := by unfold sobolevH1Sq4; omega
    have p1 : sq4 u1 ≤ sobolevH1Sq4 u0 u1 u2 u3 := by unfold sobolevH1Sq4; omega
    have p2 : sq4 u2 ≤ sobolevH1Sq4 u0 u1 u2 u3 := by unfold sobolevH1Sq4; omega
    have p3 : sq4 u3 ≤ sobolevH1Sq4 u0 u1 u2 u3 := by unfold sobolevH1Sq4; omega
    have d0 : sq4 (u1 * v1 - u0 * v0) ≤ 2 * (sq4 v1 * sq4 (u1 - u0) + sq4 u0 * sq4 (v1 - v0)) := by
      have hs := sq4_nonneg ((u1 - u0) * v1 - u0 * (v1 - v0))
      have he : 2 * (sq4 v1 * sq4 (u1 - u0) + sq4 u0 * sq4 (v1 - v0)) - sq4 (u1 * v1 - u0 * v0) =
          sq4 ((u1 - u0) * v1 - u0 * (v1 - v0)) := by unfold sq4; grind
      omega
    have d1 : sq4 (u2 * v2 - u1 * v1) ≤ 2 * (sq4 v2 * sq4 (u2 - u1) + sq4 u1 * sq4 (v2 - v1)) := by
      have hs := sq4_nonneg ((u2 - u1) * v2 - u1 * (v2 - v1))
      have he : 2 * (sq4 v2 * sq4 (u2 - u1) + sq4 u1 * sq4 (v2 - v1)) - sq4 (u2 * v2 - u1 * v1) =
          sq4 ((u2 - u1) * v2 - u1 * (v2 - v1)) := by unfold sq4; grind
      omega
    have d2 : sq4 (u3 * v3 - u2 * v2) ≤ 2 * (sq4 v3 * sq4 (u3 - u2) + sq4 u2 * sq4 (v3 - v2)) := by
      have hs := sq4_nonneg ((u3 - u2) * v3 - u2 * (v3 - v2))
      have he : 2 * (sq4 v3 * sq4 (u3 - u2) + sq4 u2 * sq4 (v3 - v2)) - sq4 (u3 * v3 - u2 * v2) =
          sq4 ((u3 - u2) * v3 - u2 * (v3 - v2)) := by unfold sq4; grind
      omega
    have d3 : sq4 (u0 * v0 - u3 * v3) ≤ 2 * (sq4 v0 * sq4 (u0 - u3) + sq4 u3 * sq4 (v0 - v3)) := by
      have hs := sq4_nonneg ((u0 - u3) * v0 - u3 * (v0 - v3))
      have he : 2 * (sq4 v0 * sq4 (u0 - u3) + sq4 u3 * sq4 (v0 - v3)) - sq4 (u0 * v0 - u3 * v3) =
          sq4 ((u0 - u3) * v0 - u3 * (v0 - v3)) := by unfold sq4; grind
      omega
    have m0 := mul_nonneg_of_sq_le _ _ (sq4 u0) qv0 hu0
    have m1 := mul_nonneg_of_sq_le _ _ (sq4 u1) qv1 hu1
    have m2 := mul_nonneg_of_sq_le _ _ (sq4 u2) qv2 hu2
    have m3 := mul_nonneg_of_sq_le _ _ (sq4 u3) qv3 hu3
    have gu0 := mul_nonneg_of_sq_le _ _ (sq4 (u1 - u0)) qv1 (sq4_nonneg (u1 - u0))
    have gu1 := mul_nonneg_of_sq_le _ _ (sq4 (u2 - u1)) qv2 (sq4_nonneg (u2 - u1))
    have gu2 := mul_nonneg_of_sq_le _ _ (sq4 (u3 - u2)) qv3 (sq4_nonneg (u3 - u2))
    have gu3 := mul_nonneg_of_sq_le _ _ (sq4 (u0 - u3)) qv0 (sq4_nonneg (u0 - u3))
    have gv0 := mul_nonneg_of_sq_le _ _ (sq4 (v1 - v0)) pu0 (sq4_nonneg (v1 - v0))
    have gv1 := mul_nonneg_of_sq_le _ _ (sq4 (v2 - v1)) pu1 (sq4_nonneg (v2 - v1))
    have gv2 := mul_nonneg_of_sq_le _ _ (sq4 (v3 - v2)) pu2 (sq4_nonneg (v3 - v2))
    have gv3 := mul_nonneg_of_sq_le _ _ (sq4 (v0 - v3)) pu3 (sq4_nonneg (v0 - v3))
    refine ⟨p0, p1, p2, p3, ?_⟩
    have hUVNorm :
        normSq4 (u0 * v0) (u1 * v1) (u2 * v2) (u3 * v3) ≤
          normSq4 u0 u1 u2 u3 * normSq4 v0 v1 v2 v3 := by
      have hLHS : normSq4 (u0 * v0) (u1 * v1) (u2 * v2) (u3 * v3) =
          sq4 v0 * sq4 u0 + sq4 v1 * sq4 u1 + sq4 v2 * sq4 u2 + sq4 v3 * sq4 u3 := by
        unfold normSq4 sq4; grind
      have hRHS : normSq4 u0 u1 u2 u3 * normSq4 v0 v1 v2 v3 =
          normSq4 v0 v1 v2 v3 * sq4 u0 + normSq4 v0 v1 v2 v3 * sq4 u1 +
          normSq4 v0 v1 v2 v3 * sq4 u2 + normSq4 v0 v1 v2 v3 * sq4 u3 := by
        unfold normSq4; grind
      omega
    have hUVGrad :
        gradSq4 (u0 * v0) (u1 * v1) (u2 * v2) (u3 * v3) ≤
          2 * (gradSq4 u0 u1 u2 u3 * normSq4 v0 v1 v2 v3) +
          2 * (normSq4 u0 u1 u2 u3 * gradSq4 v0 v1 v2 v3) := by
      have hLHS : gradSq4 (u0 * v0) (u1 * v1) (u2 * v2) (u3 * v3) =
          sq4 (u1 * v1 - u0 * v0) + sq4 (u2 * v2 - u1 * v1) +
          sq4 (u3 * v3 - u2 * v2) + sq4 (u0 * v0 - u3 * v3) := by
        unfold gradSq4 normSq4 diff0 diff1 diff2 diff3; rfl
      have hR1 : gradSq4 u0 u1 u2 u3 * normSq4 v0 v1 v2 v3 =
          normSq4 v0 v1 v2 v3 * sq4 (u1 - u0) + normSq4 v0 v1 v2 v3 * sq4 (u2 - u1) +
          normSq4 v0 v1 v2 v3 * sq4 (u3 - u2) + normSq4 v0 v1 v2 v3 * sq4 (u0 - u3) := by
        unfold gradSq4 normSq4 diff0 diff1 diff2 diff3; grind
      have hR2 : normSq4 u0 u1 u2 u3 * gradSq4 v0 v1 v2 v3 =
          normSq4 u0 u1 u2 u3 * sq4 (v1 - v0) + normSq4 u0 u1 u2 u3 * sq4 (v2 - v1) +
          normSq4 u0 u1 u2 u3 * sq4 (v3 - v2) + normSq4 u0 u1 u2 u3 * sq4 (v0 - v3) := by
        unfold gradSq4 normSq4 diff0 diff1 diff2 diff3; grind
      omega
    have hNN : 0 ≤ normSq4 u0 u1 u2 u3 * normSq4 v0 v1 v2 v3 := Int.mul_nonneg hU hV
    have hGG : 0 ≤ gradSq4 u0 u1 u2 u3 * gradSq4 v0 v1 v2 v3 := Int.mul_nonneg hGU hGV
    have hComb :
        2 * sobolevH1Sq4 u0 u1 u2 u3 * sobolevH1Sq4 v0 v1 v2 v3 -
        (normSq4 u0 u1 u2 u3 * normSq4 v0 v1 v2 v3 +
         2 * (gradSq4 u0 u1 u2 u3 * normSq4 v0 v1 v2 v3) +
         2 * (normSq4 u0 u1 u2 u3 * gradSq4 v0 v1 v2 v3)) =
        normSq4 u0 u1 u2 u3 * normSq4 v0 v1 v2 v3 +
        2 * (gradSq4 u0 u1 u2 u3 * gradSq4 v0 v1 v2 v3) := by
      unfold sobolevH1Sq4; grind
    have hDef :
        sobolevH1Sq4 (u0 * v0) (u1 * v1) (u2 * v2) (u3 * v3) =
          normSq4 (u0 * v0) (u1 * v1) (u2 * v2) (u3 * v3) +
          gradSq4 (u0 * v0) (u1 * v1) (u2 * v2) (u3 * v3) := rfl
    omega

end CommonGround.Frontier.LittlewoodPaleyAndCFL
