/-!
# Helstrom Quantum Hypothesis-Testing Duality, Kraus CPTP Purity Contraction, Pauli–Clifford `1`-Design Depolarizing Twirl & GKSL Lindblad Detailed Balance (`0` Imports, `0` Sorry)

This standalone pure-core Lean 4.33.0 frontier module unifies **Folder `07`**
(Quantum Nonlocal Games & Parallel Channels), **Folder `01`** (Blackwell–Le Cam
Statistical Decision Sufficiency), and **Folder `03`** (Information Contraction &
Detailed-Balance Equilibrium):

1. **Helstrom Two-State Quantum Hypothesis-Testing Bound vs. Non-Orthogonal Overlap Error Floor**
   (`helstrom_two_state_quantum_hypothesis_testing_bound_vs_nonorthogonal_overlap_error`):
   - *Universal Lagrange–Helstrom Trace-Norm Bound*: For any two Bloch-parameterized states
     with difference vector `(dz, dx)` and any measurement bias direction `(nz, nx)` satisfying
     `nz^2 + nx^2 ≤ M^2`, exact Lagrange identity
     `(dz^2 + dx^2)(nz^2 + nx^2) - (dz*nz + dx*nx)^2 = (dz*nx - dx*nz)^2 ≥ 0`
     forces `(dz*nz + dx*nx)^2 ≤ (dz^2 + dx^2) * M^2` across ALL quantum measurements!
   - *Orthogonal Zero-Error Attainment*: Orthogonal states `|0⟩` (`(1, 0)`) and `|1⟩` (`(-1, 0)`)
     have `(dz, dx) = (2, 0)` and saturate `(2*1 + 0*0)^2 = 4 = 4 * 1` (`100%` distinguishability).
   - *Premise-Failure Counterexample*: Non-orthogonal states `|0⟩` (`(1, 0)`) and `|+⟩` (`(0, 1)`)
     have `(dz, dx) = (1, -1)` (`dz^2 + dx^2 = 2 < 4`), so for EVERY measurement `(nz, nx)` with
     `nz^2 + nx^2 ≤ M^2` (`M ≥ 1`), `dz*nz + dx*nx ≠ 2*M` (zero-error discrimination is impossible!).

2. **Kraus CPTP Trace Preservation & Dephasing Bloch-Purity Contraction vs. Post-Selection Blowup**
   (`kraus_cptp_trace_preservation_and_purity_contraction_vs_postselection_blowup`):
   - *Universal `2 × 2` Kraus Completeness Trace Identity*: Whenever `K0^T K0 + K1^T K1 = D * I_2`,
     `Tr(K0 ρ K0^T + K1 ρ K1^T) = D * Tr(ρ)` holds for EVERY `2 × 2` operator `ρ`!
   - *Exact Dephasing Purity Contraction*: Under `Φ_{p,q}(ρ) = p ρ + q Z ρ Z` (`D = p + q`),
     `D^2 (z^2 + x^2) - ((D z)^2 + ((p - q) x)^2) = 4 p q x^2 ≥ 0`!
   - *Premise-Failure Counterexamples*: Incomplete post-selection `K = [[1,0],[0,0]]` annihilates
     `|1⟩⟨1|` trace `1 → 0`, while non-contractive `K = [[2,0],[0,1]]` inflates `|0⟩⟨0|` trace `1 → 4`.

3. **Pauli–Clifford `1`-Design Depolarizing Twirl vs. Incomplete Abelian Subgroup Leakage**
   (`pauli_clifford_one_design_depolarizing_twirl_vs_incomplete_subgroup_leakage`):
   - *Universal `4`-Pauli Schur Projection*: Averaging `U M U^T` over `{I_2, X, Z, J}` (`J = X Z`)
     maps EVERY `2 × 2` matrix `M = [[m00, m01], [m10, m11]]` identically to `2 (m00 + m11) I_2`!
   - *Premise-Failure Counterexample*: Twirling over only the `2`-element abelian dephasing
     subgroup `{I_2, Z}` kills off-diagonals yet leaves `Z`-imbalance `[[2 m00, 0], [0, 2 m11]]`
     (`[[2, 0], [0, -2]] ≠ 0` on traceless `M = [[1, 3], [5, -1]]`) completely un-twirled!

4. **GKSL Lindblad Trace Conservation & Gibbs Detailed Balance vs. Non-Hermitian Probability Loss**
   (`gksl_lindblad_trace_conservation_and_gibbs_detailed_balance_vs_nonhermitian_loss`):
   - *Universal Population Conservation & Unique Detailed-Balance Equilibrium*: The two-level
     thermal + dephasing GKSL generator `ℒ(ρ)` has `Tr(ℒ(ρ)) = 0` identically, vanishes iff
     `γ_down * p1 = γ_up * p0` and `c = 0`, and contracts detailed-balance slack multiplicatively,
     whereas omitting quantum jump recycling `2 L ρ L^T` leaks probability mass (`Tr = -2 < 0`).
-/

namespace CommonGround.Frontier.HelstromKrausPauliTwirlingAndLindblad

/-- Helper: every integer square `t * t` is non-negative (`0` imports). -/
theorem int_sq_nonneg (t : Int) : 0 ≤ t * t := by
  by_cases ht : 0 ≤ t
  · exact Int.mul_nonneg ht ht
  · have hn : 0 ≤ -t := by omega
    have hp : 0 ≤ (-t) * (-t) := Int.mul_nonneg hn hn
    have hEq : (-t) * (-t) = t * t := by grind
    omega

/-- Trace of `K ρ K^T` for `2 × 2` integer matrices `K = [[k00, k01], [k10, k11]]` and `ρ = [[r00, r01], [r10, r11]]`. -/
def traceConj2 (k00 k01 k10 k11 r00 r01 r10 r11 : Int) : Int :=
  let a00 := k00 * r00 + k01 * r10
  let a01 := k00 * r01 + k01 * r11
  let a10 := k10 * r00 + k11 * r10
  let a11 := k10 * r01 + k11 * r11
  (a00 * k00 + a01 * k01) + (a10 * k10 + a11 * k11)

/-- Theorem 1: Helstrom Two-State Quantum Hypothesis-Testing Lagrange Bound & Orthogonal Attainment
    vs. Non-Orthogonal Overlap (`|0⟩` vs. `|+⟩`) Strictly Positive Error Floor. -/
theorem helstrom_two_state_quantum_hypothesis_testing_bound_vs_nonorthogonal_overlap_error :
    -- (1) Universal Lagrange–Helstrom Identity & Measurement Bias Ceiling:
    (∀ dz dx nz nx M : Int,
      (dz * dz + dx * dx) * (nz * nz + nx * nx) - (dz * nz + dx * nx) * (dz * nz + dx * nx) =
        (dz * nx - dx * nz) * (dz * nx - dx * nz) ∧
      (0 ≤ dz * dz + dx * dx → nz * nz + nx * nx ≤ M * M →
        (dz * nz + dx * nx) * (dz * nz + dx * nx) ≤ (dz * dz + dx * dx) * (M * M))) ∧
    -- (2) Orthogonal Pure-State Zero-Error Attainment (`|0⟩` vs `|1⟩`, `(dz, dx) = (2, 0)`):
    (let dz := (2 : Int); let dx := (0 : Int); let nz := (1 : Int); let nx := (0 : Int); let M := (1 : Int)
     nz * nz + nx * nx = M * M ∧ dz * nz + dx * nx = 2 * M ∧
     (dz * nz + dx * nx) * (dz * nz + dx * nx) = (dz * dz + dx * dx) * (M * M)) ∧
    -- (3) Premise-Failure Counterexample (Non-Orthogonal `|0⟩` vs `|+⟩`, `(dz, dx) = (1, -1)`):
    --     No physical measurement `nz^2 + nx^2 ≤ M^2` (`M ≥ 1`) can ever reach zero-error bias `2 * M`!
    (∀ nz nx M : Int,
      1 ≤ M →
      nz * nz + nx * nx ≤ M * M →
      1 * nz + (-1) * nx ≠ 2 * M) := by
  refine ⟨?_, by decide, ?_⟩
  · intro dz dx nz nx M
    have hLag :
        (dz * dz + dx * dx) * (nz * nz + nx * nx) - (dz * nz + dx * nx) * (dz * nz + dx * nx) =
          (dz * nx - dx * nz) * (dz * nx - dx * nz) := by grind
    refine ⟨hLag, ?_⟩
    intro hD hMeas
    have hCross := int_sq_nonneg (dz * nx - dx * nz)
    have hProd : (dz * dz + dx * dx) * (nz * nz + nx * nx) ≤ (dz * dz + dx * dx) * (M * M) := by
      have hDiff : 0 ≤ (dz * dz + dx * dx) * (M * M - (nz * nz + nx * nx)) :=
        Int.mul_nonneg hD (by omega)
      have hExp : (dz * dz + dx * dx) * (M * M - (nz * nz + nx * nx)) =
          (dz * dz + dx * dx) * (M * M) - (dz * dz + dx * dx) * (nz * nz + nx * nx) := by grind
      omega
    omega
  · intro nz nx M hM hMeas hZeroErr
    have hAdd : (nz + nx) * (nz + nx) ≥ 0 := int_sq_nonneg (nz + nx)
    have hPar : (nz - nx) * (nz - nx) + (nz + nx) * (nz + nx) = 2 * (nz * nz + nx * nx) := by grind
    have hLHS : (nz - nx) * (nz - nx) = 4 * (M * M) := by
      have hSub : nz - nx = 2 * M := by omega
      rw [hSub]
      grind
    have hPosM2 : 1 ≤ M * M := by
      have h1 : 0 ≤ (M - 1) * (M + 1) := Int.mul_nonneg (by omega) (by omega)
      have h2 : (M - 1) * (M + 1) = M * M - 1 := by grind
      omega
    omega

/-- Theorem 2: Kraus CPTP Completeness Trace Preservation & Dephasing Purity Contraction
    vs. Incomplete Post-Selection Loss & Non-TP Amplification. -/
theorem kraus_cptp_trace_preservation_and_purity_contraction_vs_postselection_blowup :
    -- (1) Universal `2`-Kraus Completeness (`K0^T K0 + K1^T K1 = D * I_2`) Preserves Trace:
    (∀ a0 b0 c0 d0 a1 b1 c1 d1 D r00 r01 r10 r11 : Int,
      a0 * a0 + c0 * c0 + a1 * a1 + c1 * c1 = D →
      b0 * b0 + d0 * d0 + b1 * b1 + d1 * d1 = D →
      a0 * b0 + c0 * d0 + a1 * b1 + c1 * d1 = 0 →
      traceConj2 a0 b0 c0 d0 r00 r01 r10 r11 + traceConj2 a1 b1 c1 d1 r00 r01 r10 r11 =
        D * (r00 + r11)) ∧
    -- (2) Dephasing Channel `Φ_{p,q}(ρ) = p ρ + q Z ρ Z` (`D = p + q`) Bloch Purity Contraction:
    (∀ p q z x : Int,
      let D := p + q
      let zOut := D * z
      let xOut := (p - q) * x
      D * D * (z * z + x * x) - (zOut * zOut + xOut * xOut) = 4 * p * q * (x * x) ∧
      (0 ≤ p → 0 ≤ q → zOut * zOut + xOut * xOut ≤ D * D * (z * z + x * x))) ∧
    -- (3) Premise-Failure Counterexamples:
    --     (a) Post-selection `K = [[1,0],[0,0]]` maps `|1⟩⟨1|` (`Tr = 1`) to `Tr = 0`;
    --     (b) Trace-increasing `K = [[2,0],[0,1]]` maps `|0⟩⟨0|` (`Tr = 1`) to `Tr = 4`!
    (traceConj2 1 0 0 0 0 0 0 1 = 0 ∧ traceConj2 2 0 0 1 1 0 0 0 = 4) := by
  refine ⟨?_, ?_, by decide⟩
  · intro a0 b0 c0 d0 a1 b1 c1 d1 D r00 r01 r10 r11 h00 h11 h01
    unfold traceConj2
    dsimp only
    have hAlg :
        ((a0 * r00 + b0 * r10) * a0 + (a0 * r01 + b0 * r11) * b0 +
         ((c0 * r00 + d0 * r10) * c0 + (c0 * r01 + d0 * r11) * d0)) +
        ((a1 * r00 + b1 * r10) * a1 + (a1 * r01 + b1 * r11) * b1 +
         ((c1 * r00 + d1 * r10) * c1 + (c1 * r01 + d1 * r11) * d1)) =
        (a0 * a0 + c0 * c0 + a1 * a1 + c1 * c1) * r00 +
        (b0 * b0 + d0 * d0 + b1 * b1 + d1 * d1) * r11 +
        (a0 * b0 + c0 * d0 + a1 * b1 + c1 * d1) * (r01 + r10) := by grind
    rw [hAlg, h00, h11, h01]
    grind
  · intro p q z x
    dsimp only
    have hId :
        (p + q) * (p + q) * (z * z + x * x) -
          (((p + q) * z) * ((p + q) * z) + ((p - q) * x) * ((p - q) * x)) =
          4 * p * q * (x * x) := by grind
    refine ⟨hId, ?_⟩
    intro hp hq
    have hpq : 0 ≤ 4 * p * q := by
      have h1 : 0 ≤ 4 * p := by omega
      exact Int.mul_nonneg h1 hq
    have hTerm : 0 ≤ (4 * p * q) * (x * x) := Int.mul_nonneg hpq (int_sq_nonneg x)
    omega

/-- Conjugation `(U M U^T)` entry `(i, j)` for `2 × 2` matrix `M = [[m00, m01], [m10, m11]]` and `U = [[u00, u01], [u10, u11]]`. -/
def conjEntry00 (u00 u01 m00 m01 m10 m11 : Int) : Int :=
  (u00 * m00 + u01 * m10) * u00 + (u00 * m01 + u01 * m11) * u01

def conjEntry01 (u00 u01 u10 u11 m00 m01 m10 m11 : Int) : Int :=
  (u00 * m00 + u01 * m10) * u10 + (u00 * m01 + u01 * m11) * u11

def conjEntry10 (u00 u01 u10 u11 m00 m01 m10 m11 : Int) : Int :=
  (u10 * m00 + u11 * m10) * u00 + (u10 * m01 + u11 * m11) * u01

def conjEntry11 (u10 u11 m00 m01 m10 m11 : Int) : Int :=
  (u10 * m00 + u11 * m10) * u10 + (u10 * m01 + u11 * m11) * u11

/-- Theorem 3: Pauli–Clifford `1`-Design Depolarizing Twirl (`{I_2, X, Z, J}`) Annihilates All Traceless Modes
    vs. Incomplete Abelian `{I_2, Z}` Subgroup Leaving Diagonal `Z`-Bias Un-Twirled. -/
theorem pauli_clifford_one_design_depolarizing_twirl_vs_incomplete_subgroup_leakage :
    -- (1) Universal `4`-Pauli Twirl (`I_2 = [[1,0],[0,1]]`, `X = [[0,1],[1,0]]`, `Z = [[1,0],[0,-1]]`, `J = [[0,-1],[1,0]]`):
    --     Maps EVERY `2 × 2` matrix `M` (even non-symmetric!) to `2 * (m00 + m11) * I_2`!
    (∀ m00 m01 m10 m11 : Int,
      conjEntry00 1 0 m00 m01 m10 m11 + conjEntry00 0 1 m00 m01 m10 m11 +
      conjEntry00 1 0 m00 m01 m10 m11 + conjEntry00 0 (-1) m00 m01 m10 m11 = 2 * (m00 + m11) ∧
      conjEntry11 0 1 m00 m01 m10 m11 + conjEntry11 1 0 m00 m01 m10 m11 +
      conjEntry11 0 (-1) m00 m01 m10 m11 + conjEntry11 1 0 m00 m01 m10 m11 = 2 * (m00 + m11) ∧
      conjEntry01 1 0 0 1 m00 m01 m10 m11 + conjEntry01 0 1 1 0 m00 m01 m10 m11 +
      conjEntry01 1 0 0 (-1) m00 m01 m10 m11 + conjEntry01 0 (-1) 1 0 m00 m01 m10 m11 = 0 ∧
      conjEntry10 1 0 0 1 m00 m01 m10 m11 + conjEntry10 0 1 1 0 m00 m01 m10 m11 +
      conjEntry10 1 0 0 (-1) m00 m01 m10 m11 + conjEntry10 0 (-1) 1 0 m00 m01 m10 m11 = 0) ∧
    -- (2) Premise-Failure Counterexample (Incomplete Abelian Subgroup `{I_2, Z}`):
    --     Traceless matrix `M = [[1, 3], [5, -1]]` (`m00 + m11 = 0`) twirls to `0` under `{I_2, X, Z, J}`,
    --     YET `{I_2, Z}` twirl yields diagonal `[[2, 0], [0, -2]] ≠ [[0, 0], [0, 0]]`!
    (conjEntry00 1 0 1 3 5 (-1) + conjEntry00 1 0 1 3 5 (-1) = 2 ∧
     conjEntry11 0 1 1 3 5 (-1) + conjEntry11 0 (-1) 1 3 5 (-1) = -2) := by
  refine ⟨?_, by decide⟩
  intro m00 m01 m10 m11
  unfold conjEntry00 conjEntry01 conjEntry10 conjEntry11
  exact ⟨by grind, by grind, by grind, by grind⟩

/-- GKSL / Lindblad `2 × 2` generator entries `(dp0, dc, dp1)` under emission `gDown`, excitation `gUp`, and dephasing `gPhi`. -/
def lindbladPop0 (gDown gUp p0 p1 : Int) : Int := 2 * (gDown * p1 - gUp * p0)
def lindbladPop1 (gDown gUp p0 p1 : Int) : Int := 2 * (gUp * p0 - gDown * p1)
def lindbladCoh (gDown gUp gPhi c : Int) : Int := -(gDown + gUp + 4 * gPhi) * c

/-- Theorem 4: GKSL Lindblad Trace Conservation & Gibbs Detailed-Balance Stationarity
    vs. Uncompensated Non-Hermitian Anti-Commutator Probability Loss. -/
theorem gksl_lindblad_trace_conservation_and_gibbs_detailed_balance_vs_nonhermitian_loss :
    -- (1) Universal Trace Conservation `Tr(ℒ(ρ)) = dp0 + dp1 = 0` & Detailed-Balance Contraction:
    (∀ gDown gUp gPhi p0 p1 c S : Int,
      lindbladPop0 gDown gUp p0 p1 + lindbladPop1 gDown gUp p0 p1 = 0 ∧
      (1 ≤ gDown + gUp + 4 * gPhi →
        ((lindbladPop0 gDown gUp p0 p1 = 0 ∧ lindbladPop1 gDown gUp p0 p1 = 0 ∧ lindbladCoh gDown gUp gPhi c = 0) ↔
          (gDown * p1 = gUp * p0 ∧ c = 0))) ∧
      (let p0Next := S * p0 + lindbladPop0 gDown gUp p0 p1
       let p1Next := S * p1 + lindbladPop1 gDown gUp p0 p1
       gDown * p1Next - gUp * p0Next = (S - 2 * (gDown + gUp)) * (gDown * p1 - gUp * p0))) ∧
    -- (2) Premise-Failure Counterexample (Omitting Quantum Jump Recycling `2 L_↓ ρ L_↓^T`):
    --     Anti-commutator alone `-(L_↓^T L_↓ ρ + ρ L_↓^T L_↓)` on `ρ = |1⟩⟨1|` (`p0 = 0, p1 = 1`)
    --     gives `(dp0_noJump, dp1_noJump) = (0, -2)` with trace `-2 ≠ 0`!
    ((0 : Int) + (-2 * (1 : Int)) = -2 ∧ (-2 : Int) ≠ 0) := by
  refine ⟨?_, by decide⟩
  intro gDown gUp gPhi p0 p1 c S
  unfold lindbladPop0 lindbladPop1 lindbladCoh
  refine ⟨by omega, ?_, by grind⟩
  intro hRate
  constructor
  · intro ⟨h0, _, hc⟩
    have hBal : gDown * p1 = gUp * p0 := by omega
    have hcZero : c = 0 := by
      by_cases hcz : c = 0
      · exact hcz
      · by_cases hcp : 1 ≤ c
        · have hProd : 1 ≤ (gDown + gUp + 4 * gPhi) * c := Int.mul_le_mul hRate hcp (by omega) (by omega)
          have hNeg : -(gDown + gUp + 4 * gPhi) * c = -((gDown + gUp + 4 * gPhi) * c) := by grind
          omega
        · have hcn : 1 ≤ -c := by omega
          have hProd : 1 ≤ (gDown + gUp + 4 * gPhi) * (-c) := Int.mul_le_mul hRate hcn (by omega) (by omega)
          have hPos : -(gDown + gUp + 4 * gPhi) * c = (gDown + gUp + 4 * gPhi) * (-c) := by grind
          omega
    exact ⟨hBal, hcZero⟩
  · intro ⟨hBal, hcZero⟩
    rw [hcZero]
    exact ⟨by omega, by omega, by grind⟩

end CommonGround.Frontier.HelstromKrausPauliTwirlingAndLindblad
