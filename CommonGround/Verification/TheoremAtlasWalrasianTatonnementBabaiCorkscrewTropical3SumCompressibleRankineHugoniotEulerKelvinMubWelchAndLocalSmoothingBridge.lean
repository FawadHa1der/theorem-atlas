/-
  Common Ground — Verification Suite #607 (Wave V206)
  Module: CommonGround/Verification/TheoremAtlasWalrasianTatonnementBabaiCorkscrewTropical3SumCompressibleRankineHugoniotEulerKelvinMubWelchAndLocalSmoothingBridge.lean

  Pure-Core Lean 4.33.0 Formalization (`0` imports, `0` sorrys, `0` warnings) certifying positive
  mechanism witnesses AND explicit premise-failure counterexamples across 8 specialized frontier domains:
  1. `econlib`: General `N`-Agent, `G`-Good Walras's Law Orthogonality (`∑_{j<G} p_j Z_j = 0` when every
     agent satisfies budget balance `⟨p, x_a⟩ = ⟨p, ω_a⟩`, forcing `(G - 1)`-market clearing to clear
     the `G`-th market when `p_G > 0`) vs. Budget-Leak Disequilibrium (`δ ≠ 0`).
  2. `oai-gapcvp`: Babai Nearest-Plane Exact CVP Optimality on Orthogonal `2D` Lattices
     (`∀ k₁ k₂ : Int, r₁² + r₂² ≤ (q₁ d₁ + r₁ - k₁ d₁)² + (q₂ d₂ + r₂ - k₂ d₂)²` whenever `2|r_i| ≤ d_i`)
     vs. Sheared Basis Rounding Trap (`b₁ = (10, 0), b₂ = (5, 3), t = (5, 1)`: Babai error `≥ 26 > 4`).
  3. `apsp3sum`: Potential-Invariant `3SUM ↔ Zero-Weight Tripartite Triangle` Reduction
     (`(a + φ_A - φ_B) + (b + φ_B - φ_C) + (c + φ_C - φ_A) = a + b + c`) vs. Sub-Range Modular Hashing
     False-Positive Triangle (`(3 + 4 + 5) % 12 = 0` yet `3 + 4 + 5 = 12 ≠ 0`).
  4. `oai-nscomp`: Compressible Burgers / Navier–Stokes Rankine–Hugoniot Jump & Exact Cubic Lax Shock
     Entropy Dissipation (`4(u_L³ - u_R³) - 3(u_L + u_R)(u_L² - u_R²) = (u_L - u_R)³ > 0` for `u_L > u_R`)
     vs. Unphysical Rarefaction-Shock Entropy Creation (`(u_L - u_R)³ = -8 < 0` for `u_L = -1 < u_R = 1`).
  5. `tc-numtheory`: Dirichlet Convolution Möbius Orthogonal Inversion (`(f * 1) * μ = f` and coprime
     multiplicativity `μ(ab) = μ(a)μ(b)` up to `n = 12`) vs. Non-Squarefree-Annihilating Failure (`n = 4`).
  6. `euler`: Discrete Kelvin Loop Circulation Conservation (`∑_{i<N} (Φ_{i+1 mod N} - Φ_i) = 0` for any
     single-valued Bernoulli potential `Φ`) vs. Baroclinic Density-Pressure Misalignment Torque (`-2 ≠ 0`).
  7. `oai-mub`: `4 × 4` Sylvester–Hadamard Mutually Unbiased Bases Flat Welch Overlap
     (`∀ i j : Fin 4, ⟨E_i, H_j⟩² = 4` and pairwise orthogonality) vs. Block-Aligned Coherence Spike (`16 > 4`).
  8. `oai-smoothing`: Bilinear Dispersive Paraboloid Transversality & Local-Smoothing Jacobian
     (`2(ξ₁² + ξ₂²) - (ξ₁ + ξ₂)² = (ξ₁ - ξ₂)²` and `|det J| = 2|ξ₂ - ξ₁| ≥ 2Δ > 0`) vs. Collinear
     Parallel-Wave Singularity (`ξ₁ = ξ₂ → det J = 0`).
-/

namespace CommonGround.Verification.EightSpecializedFrontiersV206

theorem sq_nonneg_int (x : Int) : 0 ≤ x * x := by
  by_cases hx : 0 ≤ x
  · exact Int.mul_nonneg hx hx
  · have hnx : 0 ≤ -x := by omega
    have hp : 0 ≤ (-x) * (-x) := Int.mul_nonneg hnx hnx
    have heq : (-x) * (-x) = x * x := by simp [Int.neg_mul_neg]
    omega

/-! ## 1. `econlib`: General `N`-Agent, `G`-Good Walras's Law vs. Budget-Leak Disequilibrium -/

def sumNat (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumNat f n + f n

theorem sumNat_zero : ∀ n : Nat, sumNat (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by
      have ih := sumNat_zero n
      simp [sumNat, ih]

theorem sumNat_congr (f g : Nat → Int) :
    ∀ n : Nat, (∀ i : Nat, i < n → f i = g i) → sumNat f n = sumNat g n
  | 0, _ => rfl
  | n + 1, h => by
      have ih := sumNat_congr f g n (fun i hi => h i (by omega))
      have hn := h n (by omega)
      simp [sumNat, ih, hn]

theorem sumNat_add (f g : Nat → Int) :
    ∀ n : Nat, sumNat (fun i => f i + g i) n = sumNat f n + sumNat g n
  | 0 => by simp [sumNat]
  | n + 1 => by
      have ih := sumNat_add f g n
      simp only [sumNat, ih]
      omega

theorem sumNat_mul_const_left (c : Int) (f : Nat → Int) :
    ∀ n : Nat, sumNat (fun i => c * f i) n = c * sumNat f n
  | 0 => by simp [sumNat]
  | n + 1 => by
      have ih := sumNat_mul_const_left c f n
      simp only [sumNat, ih]
      rw [← Int.mul_add]

theorem sumNat_swap (F : Nat → Nat → Int) (N : Nat) :
    ∀ G : Nat, sumNat (fun j => sumNat (fun a => F a j) N) G =
      sumNat (fun a => sumNat (fun j => F a j) G) N
  | 0 => by
      simp only [sumNat]
      exact (sumNat_zero N).symm
  | G + 1 => by
      have ih := sumNat_swap F N G
      have hsplit := sumNat_add (fun a => sumNat (fun j => F a j) G) (fun a => F a G) N
      simp only [sumNat] at hsplit ⊢
      omega

def agentNetValue (G : Nat) (p : Nat → Int) (x ω : Nat → Nat → Int) (a : Nat) : Int :=
  sumNat (fun j => p j * (x a j - ω a j)) G

def marketExcessDemand (N : Nat) (x ω : Nat → Nat → Int) (j : Nat) : Int :=
  sumNat (fun a => x a j - ω a j) N

theorem econlib_walras_law_orthogonality_vs_budget_leak_bridge :
    (∀ (N G : Nat) (p : Nat → Int) (x ω : Nat → Nat → Int),
      (∀ a : Nat, a < N → agentNetValue G p x ω a = 0) →
      sumNat (fun j => p j * marketExcessDemand N x ω j) G = 0) ∧
    (∀ p₁ p₂ z₁ z₂ : Int, p₁ * z₁ + p₂ * z₂ = 0 → z₁ = 0 → 0 < p₂ → z₂ = 0) ∧
    (∃ (p₁ p₂ z₁ z₂ δ : Int), 0 < p₁ ∧ 0 < p₂ ∧ δ ≠ 0 ∧
      p₁ * z₁ + p₂ * z₂ = δ ∧ z₁ = 0 ∧ z₂ ≠ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N G p x ω hbud
    have hpull : sumNat (fun j => p j * marketExcessDemand N x ω j) G =
        sumNat (fun j => sumNat (fun a => p j * (x a j - ω a j)) N) G := by
      apply sumNat_congr
      intro j _
      exact (sumNat_mul_const_left (p j) (fun a => x a j - ω a j) N).symm
    have hsw := sumNat_swap (fun a j => p j * (x a j - ω a j)) N G
    have hzero : sumNat (fun a => agentNetValue G p x ω a) N = sumNat (fun _ => 0) N := by
      apply sumNat_congr
      intro a ha
      exact hbud a ha
    unfold agentNetValue at hzero
    rw [hpull, hsw, hzero, sumNat_zero]
  · intro p₁ p₂ z₁ z₂ hwal hz1 hp2
    have hpz2 : p₂ * z₂ = 0 := by
      subst hz1
      omega
    by_cases hz2 : z₂ = 0
    · exact hz2
    · by_cases hpos : 0 < z₂
      · have hm := Int.mul_pos hp2 hpos
        omega
      · have hneg : 0 < -z₂ := by omega
        have hm := Int.mul_pos hp2 hneg
        have heq : p₂ * (-z₂) = -(p₂ * z₂) := Int.mul_neg p₂ z₂
        omega
  · exact ⟨2, 3, 0, 1, 3, by omega, by omega, by omega, by omega, rfl, by omega⟩

/-! ## 2. `oai-gapcvp`: Babai Nearest-Plane Orthogonal Optimality vs. Sheared Basis Rounding Trap -/

theorem rounded_coord_sq_min (d r m : Int) (hd : 0 < d) (hr_lo : -d ≤ 2 * r) (hr_hi : 2 * r ≤ d) :
    r * r ≤ (r - m * d) * (r - m * d) := by
  by_cases hm0 : m = 0
  · subst hm0
    simp
  · have hdiff : (r - m * d) * (r - m * d) - r * r = m * d * (m * d - 2 * r) := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_sub]
      have hcomm : r * (m * d) = m * d * r := Int.mul_comm _ _
      have htwo : m * d * (2 * r) = 2 * (m * d * r) := by
        rw [← Int.mul_assoc, Int.mul_comm (m * d) 2, Int.mul_assoc]
      omega
    by_cases hmpos : 0 < m
    · have hmd_ge : d ≤ m * d := by
        have hm1 : 0 ≤ m - 1 := by omega
        have hp := Int.mul_nonneg hm1 (show 0 ≤ d by omega)
        rw [Int.sub_mul] at hp
        omega
      have hfac : 0 ≤ m * d * (m * d - 2 * r) :=
        Int.mul_nonneg (by omega) (by omega)
      omega
    · have hmneg : 0 < -m := by omega
      have hmd_ge : d ≤ (-m) * d := by
        have hm1 : 0 ≤ -m - 1 := by omega
        have hp := Int.mul_nonneg hm1 (show 0 ≤ d by omega)
        rw [Int.sub_mul] at hp
        omega
      have hneg_eq : (-m) * d = -(m * d) := Int.neg_mul m d
      have hfac_neg : 0 ≤ (-(m * d)) * (2 * r - m * d) :=
        Int.mul_nonneg (by omega) (by omega)
      have hprod_eq : (-(m * d)) * (2 * r - m * d) = m * d * (m * d - 2 * r) := by
        rw [Int.neg_mul, Int.mul_sub, Int.mul_sub]
        omega
      omega

theorem gapcvp_babai_orthogonal_nearest_plane_vs_sheared_corkscrew_bridge :
    (∀ d₁ d₂ q₁ q₂ r₁ r₂ k₁ k₂ : Int,
      0 < d₁ → 0 < d₂ →
      -d₁ ≤ 2 * r₁ → 2 * r₁ ≤ d₁ →
      -d₂ ≤ 2 * r₂ → 2 * r₂ ≤ d₂ →
      r₁ * r₁ + r₂ * r₂ ≤
        (q₁ * d₁ + r₁ - k₁ * d₁) * (q₁ * d₁ + r₁ - k₁ * d₁) +
        (q₂ * d₂ + r₂ - k₂ * d₂) * (q₂ * d₂ + r₂ - k₂ * d₂)) ∧
    (((5 : Int) - (0 * 10 + 1 * 5)) * ((5 : Int) - (0 * 10 + 1 * 5)) +
      ((1 : Int) - (0 * 0 + 1 * 3)) * ((1 : Int) - (0 * 0 + 1 * 3)) = 4 ∧
     ∀ q₁ : Int,
      26 ≤ (5 - 10 * q₁) * (5 - 10 * q₁) + ((1 : Int) - 0) * ((1 : Int) - 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d₁ d₂ q₁ q₂ r₁ r₂ k₁ k₂ hd1 hd2 hr1l hr1u hr2l hr2u
    have heq1 : q₁ * d₁ + r₁ - k₁ * d₁ = r₁ - (k₁ - q₁) * d₁ := by
      rw [Int.sub_mul]
      omega
    have heq2 : q₂ * d₂ + r₂ - k₂ * d₂ = r₂ - (k₂ - q₂) * d₂ := by
      rw [Int.sub_mul]
      omega
    rw [heq1, heq2]
    have h1 := rounded_coord_sq_min d₁ r₁ (k₁ - q₁) hd1 hr1l hr1u
    have h2 := rounded_coord_sq_min d₂ r₂ (k₂ - q₂) hd2 hr2l hr2u
    omega
  · decide
  · intro q₁
    have hmin := rounded_coord_sq_min 10 5 q₁ (by omega) (by omega) (by omega)
    have hc : q₁ * 10 = 10 * q₁ := Int.mul_comm _ _
    rw [hc] at hmin
    omega

/-! ## 3. `apsp3sum`: Potential-Invariant `3SUM ↔ Zero-Weight Triangle` vs. Modular Hash False Triangle -/

theorem apsp3sum_potential_invariant_zero_triangle_vs_modular_wrap_bridge :
    (∀ a b c φA φB φC : Int,
      ((a + φA - φB) + (b + φB - φC) + (c + φC - φA) = a + b + c) ∧
      (((a + φA - φB) + (b + φB - φC) + (c + φC - φA) = 0) ↔ (a + b + c = 0))) ∧
    ((3 + 4 + 5 : Int) % 12 = 0 ∧ (3 + 4 + 5 : Int) ≠ 0) := by
  refine ⟨?_, ?_⟩
  · intro a b c φA φB φC
    refine ⟨by omega, ?_⟩
    constructor <;> intro h <;> omega
  · decide

/-! ## 4. `oai-nscomp`: Compressible Rankine–Hugoniot Jump & Cubic Lax Entropy vs. Expansion Shock -/

theorem nscomp_rankine_hugoniot_cubic_lax_entropy_vs_rarefaction_shock_bridge :
    (∀ uL uR s : Int,
      2 * s = uL + uR →
      2 * s * (uL - uR) = uL * uL - uR * uR ∧
      4 * (uL * uL * uL - uR * uR * uR) - 3 * (2 * s) * (uL * uL - uR * uR) =
        (uL - uR) * (uL - uR) * (uL - uR)) ∧
    (∀ uL uR : Int, uR < uL → 0 < (uL - uR) * (uL - uR) * (uL - uR)) ∧
    (let uL : Int := -1
     let uR : Int := 1
     let s : Int := 0
     2 * s * (uL - uR) = uL * uL - uR * uR ∧
     (uL - uR) * (uL - uR) * (uL - uR) = -8 ∧ -8 < (0 : Int)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro uL uR s hs
    have hrh : (uL + uR) * (uL - uR) = uL * uL - uR * uR := by
      rw [Int.add_mul, Int.mul_sub, Int.mul_sub]
      have hc : uR * uL = uL * uR := Int.mul_comm _ _
      omega
    have hcub : 4 * (uL * uL * uL - uR * uR * uR) - 3 * (uL + uR) * (uL * uL - uR * uR) =
        (uL - uR) * (uL - uR) * (uL - uR) := by
      have h1 : 3 * (uL + uR) * (uL * uL - uR * uR) =
          3 * (uL * uL * uL) - 3 * (uL * (uR * uR)) + 3 * (uR * (uL * uL)) - 3 * (uR * uR * uR) := by
        simp only [Int.add_mul, Int.mul_add, Int.mul_sub]
        have ha1 : 3 * uL * (uL * uL) = 3 * (uL * uL * uL) := by
          rw [Int.mul_assoc 3 uL (uL * uL), ← Int.mul_assoc uL uL uL]
        have ha2 : 3 * uL * (uR * uR) = 3 * (uL * (uR * uR)) := Int.mul_assoc _ _ _
        have ha3 : 3 * uR * (uL * uL) = 3 * (uR * (uL * uL)) := Int.mul_assoc _ _ _
        have ha4 : 3 * uR * (uR * uR) = 3 * (uR * uR * uR) := by
          rw [Int.mul_assoc 3 uR (uR * uR), ← Int.mul_assoc uR uR uR]
        omega
      have h2 : (uL - uR) * (uL - uR) * (uL - uR) =
          uL * uL * uL - 3 * (uR * (uL * uL)) + 3 * (uL * (uR * uR)) - uR * uR * uR := by
        simp only [Int.sub_mul, Int.mul_sub]
        have hc1 : uL * uR * uL = uR * (uL * uL) := by
          rw [Int.mul_comm uL uR, Int.mul_assoc]
        have hc2 : uR * uL * uL = uR * (uL * uL) := Int.mul_assoc _ _ _
        have hc3 : uL * uL * uR = uR * (uL * uL) := Int.mul_comm (uL * uL) uR
        have hc4 : uR * uR * uL = uL * (uR * uR) := Int.mul_comm _ _
        have hc5 : uR * uL * uR = uL * (uR * uR) := by
          rw [Int.mul_comm uR uL, Int.mul_assoc]
        have hc6 : uL * uR * uR = uL * (uR * uR) := Int.mul_assoc _ _ _
        omega
      have h4 : 4 * (uL * uL * uL - uR * uR * uR) = 4 * (uL * uL * uL) - 4 * (uR * uR * uR) :=
        Int.mul_sub _ _ _
      rw [h4, h1, h2]
      omega
    rw [hs]
    exact ⟨hrh, hcub⟩
  · intro uL uR hlt
    have hd : 0 < uL - uR := by omega
    exact Int.mul_pos (Int.mul_pos hd hd) hd
  · decide

/-! ## 5. `tc-numtheory`: Dirichlet Convolution Möbius Inversion vs. Non-Squarefree Failure -/

def mu12 : Nat → Int
  | 1 => 1
  | 2 => -1
  | 3 => -1
  | 4 => 0
  | 5 => -1
  | 6 => 1
  | 7 => -1
  | 8 => 0
  | 9 => 0
  | 10 => 1
  | 11 => -1
  | 12 => 0
  | _ => 0

def badMu12 (n : Nat) : Int :=
  if n == 4 then 1 else mu12 n

def dirichletConv12 (f g : Nat → Int) (n : Nat) : Int :=
  (List.range 12).foldl
    (fun acc k =>
      let d := k + 1
      if n % d == 0 then acc + f d * g (n / d) else acc)
    0

def zeta1 (_ : Nat) : Int := 1

def sampleArith (n : Nat) : Int := (n * n : Nat) - 3 * (n : Int) + 5

theorem tc_numtheory_dirichlet_mobius_inversion_vs_square_defect_bridge :
    (∀ n : Fin 12,
      dirichletConv12 zeta1 mu12 (n.val + 1) = (if n.val + 1 == 1 then 1 else 0)) ∧
    (∀ n : Fin 12,
      dirichletConv12 (dirichletConv12 sampleArith zeta1) mu12 (n.val + 1) = sampleArith (n.val + 1)) ∧
    (∀ a b : Fin 12,
      (a.val + 1) * (b.val + 1) ≤ 12 → Nat.gcd (a.val + 1) (b.val + 1) = 1 →
      mu12 ((a.val + 1) * (b.val + 1)) = mu12 (a.val + 1) * mu12 (b.val + 1)) ∧
    (dirichletConv12 zeta1 badMu12 4 = 1 ∧
     dirichletConv12 (dirichletConv12 sampleArith zeta1) badMu12 4 ≠ sampleArith 4) := by
  decide

/-! ## 6. `euler`: Discrete Kelvin Loop Circulation Conservation vs. Baroclinic Curl Torque -/

def closedLoopGradSum (Φ : Nat → Int) (N : Nat) : Int :=
  sumNat (fun i => Φ ((i + 1) % (N + 1)) - Φ i) (N + 1)

theorem telescSum (Φ : Nat → Int) : ∀ k : Nat, sumNat (fun i => Φ (i + 1) - Φ i) k = Φ k - Φ 0
  | 0 => by simp [sumNat]
  | k + 1 => by
      have ih := telescSum Φ k
      simp only [sumNat, ih]
      omega

def vec4 (x0 x1 x2 x3 : Int) (k : Fin 4) : Int :=
  match k.val with
  | 0 => x0
  | 1 => x1
  | 2 => x2
  | _ => x3

def baroclinicLoopTorque4 (σ P : Fin 4 → Int) : Int :=
  (σ 0 + σ 1) * (P 1 - P 0) +
  (σ 1 + σ 2) * (P 2 - P 1) +
  (σ 2 + σ 3) * (P 3 - P 2) +
  (σ 3 + σ 0) * (P 0 - P 3)

theorem euler_kelvin_circulation_conservation_vs_baroclinic_torque_bridge :
    (∀ (Φ : Nat → Int) (N : Nat), closedLoopGradSum Φ N = 0) ∧
    (∀ (c : Int) (P : Fin 4 → Int), baroclinicLoopTorque4 (fun _ => c) P = 0) ∧
    (let σ : Fin 4 → Int := vec4 1 2 2 1
     let P : Fin 4 → Int := vec4 0 1 0 (-1)
     baroclinicLoopTorque4 σ P = -2 ∧ baroclinicLoopTorque4 σ P ≠ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Φ N
    unfold closedLoopGradSum
    simp only [sumNat]
    have hcongr : sumNat (fun i => Φ ((i + 1) % (N + 1)) - Φ i) N =
        sumNat (fun i => Φ (i + 1) - Φ i) N := by
      apply sumNat_congr
      intro i hi
      have hmod : (i + 1) % (N + 1) = i + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hmod]
    have hlast : (N + 1) % (N + 1) = 0 := Nat.mod_self (N + 1)
    rw [hcongr, telescSum, hlast]
    omega
  · intro c P
    dsimp [baroclinicLoopTorque4]
    simp only [Int.mul_sub]
    omega
  · decide

/-! ## 7. `oai-mub`: `4 × 4` Sylvester–Hadamard MUB Flat Welch Overlap vs. Aligned Basis Spike -/

def stdBasis4 (i : Fin 4) : Fin 4 → Int :=
  fun k => if i == k then 2 else 0

def hadamardBasis4 (j : Fin 4) : Fin 4 → Int :=
  match j.val with
  | 0 => vec4 1 1 1 1
  | 1 => vec4 1 (-1) 1 (-1)
  | 2 => vec4 1 1 (-1) (-1)
  | _ => vec4 1 (-1) (-1) 1

def alignedBlockBasis4 (j : Fin 4) : Fin 4 → Int :=
  match j.val with
  | 0 => vec4 2 0 0 0
  | 1 => vec4 0 2 0 0
  | 2 => vec4 0 0 2 0
  | _ => vec4 0 0 0 2

def dot4 (u v : Fin 4 → Int) : Int :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3

theorem mub_sylvester_hadamard_flat_welch_overlap_vs_aligned_spike_bridge :
    (∀ i j : Fin 4,
      dot4 (stdBasis4 i) (stdBasis4 j) = (if i == j then 4 else 0) ∧
      dot4 (hadamardBasis4 i) (hadamardBasis4 j) = (if i == j then 4 else 0) ∧
      let ip := dot4 (stdBasis4 i) (hadamardBasis4 j)
      ip * ip = 4) ∧
    (let ipAligned := dot4 (stdBasis4 0) (alignedBlockBasis4 0)
     ipAligned * ipAligned = 16 ∧ 4 < ipAligned * ipAligned) := by
  decide

/-! ## 8. `oai-smoothing`: Bilinear Dispersive Paraboloid Jacobian vs. Collinear Singularity -/

def paraboloidJacobianDet (ξ₁ ξ₂ : Int) : Int :=
  1 * (2 * ξ₂) - 1 * (2 * ξ₁)

theorem smoothing_bilinear_paraboloid_jacobian_vs_collinear_concentration_bridge :
    (∀ ξ₁ ξ₂ Δ : Int,
      2 * (ξ₁ * ξ₁ + ξ₂ * ξ₂) - (ξ₁ + ξ₂) * (ξ₁ + ξ₂) = (ξ₁ - ξ₂) * (ξ₁ - ξ₂) ∧
      paraboloidJacobianDet ξ₁ ξ₂ = 2 * (ξ₂ - ξ₁) ∧
      (0 < Δ → Δ ≤ Int.natAbs (ξ₂ - ξ₁) → 2 * Δ ≤ Int.natAbs (paraboloidJacobianDet ξ₁ ξ₂))) ∧
    (∀ ξ : Int,
      paraboloidJacobianDet ξ ξ = 0 ∧
      2 * (ξ * ξ + ξ * ξ) - (ξ + ξ) * (ξ + ξ) = 0) := by
  refine ⟨?_, ?_⟩
  · intro ξ₁ ξ₂ Δ
    have halg : 2 * (ξ₁ * ξ₁ + ξ₂ * ξ₂) - (ξ₁ + ξ₂) * (ξ₁ + ξ₂) = (ξ₁ - ξ₂) * (ξ₁ - ξ₂) := by
      simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
      have hc : ξ₂ * ξ₁ = ξ₁ * ξ₂ := Int.mul_comm _ _
      omega
    have hjac : paraboloidJacobianDet ξ₁ ξ₂ = 2 * (ξ₂ - ξ₁) := by
      unfold paraboloidJacobianDet
      omega
    refine ⟨halg, hjac, ?_⟩
    intro _ hsep
    rw [hjac]
    have habs : (Int.natAbs (2 * (ξ₂ - ξ₁)) : Int) = 2 * (Int.natAbs (ξ₂ - ξ₁) : Int) := by
      rw [Int.natAbs_mul]
      simp
    omega
  · intro ξ
    refine ⟨by unfold paraboloidJacobianDet; omega, ?_⟩
    simp only [Int.add_mul, Int.mul_add]
    omega

end CommonGround.Verification.EightSpecializedFrontiersV206
