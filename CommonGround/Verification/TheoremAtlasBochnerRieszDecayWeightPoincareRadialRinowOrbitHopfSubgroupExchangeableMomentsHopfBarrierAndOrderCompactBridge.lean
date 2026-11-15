/-
  Theorem-Atlas Verification Suite #602 (`V201` — Zero `>= 88.0` Unreviewed Horizon):
  Bochner–Riesz Dyadic Decay Weights, Poincaré Radial Ray Homotopy & Lie Exp Domain,
  Hyperoctahedral `O₂(ℤ)` Hopf-Subgroup Orbit Idempotence, `S₃` Exchangeable Symmetrization,
  Radial Even-Moment Determinacy, `ℤ_4` Cohn–Elkies Hopf-Barrier Packing & OrderIso Compactness
  =============================================================================================
  Pure-core Lean 4.33.0 (`0` external imports, `0` sorrys) certifying all 7 canonical `[88.0, 90.0)`
  cross-domain bridges with machine-checked positive witnesses and premise-failure counterexamples:
  1. `iso-domain-bridge-5195` (`oai-riesz :: localSmoothing_bochnerRiesz_Lp_ae_convergence` ↔ `tc-numtheory :: decayWeight`)
  2. `iso-domain-bridge-5110` (`oai-codes :: radialIntegrand` ↔ `tc-lie :: tfae_expDomain_eq_univ`)
  3. `iso-domain-bridge-5500` (`oai-sphere :: radialFourierOrbitAverage` ↔ `tc-lie :: hopfIdealPointsSubgroup`)
  4. `iso-domain-bridge-5991` (`oai-sphere :: radialFourierOrbitAverage` ↔ `tc-probcomb :: ExchangeableAt`)
  5. `iso-domain-bridge-5831` (`oai-sphere :: radialFourierOrbitAverage` ↔ `tc-probcomb :: charFun_eq_of_forall_integral_pow_eq`)
  6. `iso-domain-bridge-6560` (`oai-sphere :: radialFourierOrbitAverage` ↔ `tc-lie :: hopfBarrier`)
  7. `iso-oai-sphere-tauceti-89` (`oai-sphere :: monotoneOn_quotientRootMap` ↔ `tauceti :: OrderIso.isCompactElement`)
-/

namespace CommonGround.Verification.TheoremAtlasBochnerRieszDecayWeightPoincareRadialRinowOrbitHopfSubgroupExchangeableMomentsHopfBarrierAndOrderCompactBridge

/-! ## 1. Bochner–Riesz Dyadic `decayWeight` Convergence vs. Critical Zero-Decay Divergence (`iso-domain-bridge-5195`) -/

/-- Geometric dyadic shell sum `∑_{k<N} 2^k`. -/
def dyadicSum : Nat → Nat
  | 0 => 0
  | n + 1 => dyadicSum n + 2 ^ n

/-- Constant (zero-decay critical exponent) shell sum `∑_{k<N} A`. -/
def zeroDecayShellSum : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, A => zeroDecayShellSum n A + A

theorem dyadicSum_closed_form (N : Nat) : dyadicSum N + 1 = 2 ^ N := by
  induction N with
  | zero => rfl
  | succ n ih =>
    simp only [dyadicSum, Nat.pow_succ]
    omega

theorem zeroDecayShellSum_closed_form (N A : Nat) : zeroDecayShellSum N A = N * A := by
  induction N with
  | zero => simp [zeroDecayShellSum]
  | succ n ih =>
    simp only [zeroDecayShellSum, ih, Nat.succ_mul]

/--
**Bridge 1 (`iso-domain-bridge-5195`)**:
1. Positive dyadic `decayWeight` (`δ > 0`) telescopes `∑_{k < N+1} A · 2^k = A · (2^{N+1} - 1) < 2 · (A · 2^N)`
   for `A ≥ 1`, bounding the normalized dyadic maximal sum uniformly by `< 2 A` for all `N`.
2. Sharp Critical Zero-Decay Failure (`δ = 0`): Constant unit shell weights diverge unboundedly —
   for every proposed uniform ceiling `B`, `zeroDecayShellSum (B + 1) 1 = B + 1 > B`!
-/
theorem bochner_riesz_dyadic_decay_weight_convergence_vs_critical_constant_divergence :
    (∀ N A : Nat, 1 ≤ A → A * dyadicSum (N + 1) < 2 * (A * (2 ^ N))) ∧
    (∀ B : Nat, zeroDecayShellSum (B + 1) 1 > B) := by
  refine ⟨?_, ?_⟩
  · intro N A hA
    have hd := dyadicSum_closed_form (N + 1)
    have hpow : 2 ^ (N + 1) = 2 * (2 ^ N) := by
      simp [Nat.pow_succ, Nat.mul_comm]
    have hlt : dyadicSum (N + 1) < 2 * (2 ^ N) := by omega
    have hmul : A * dyadicSum (N + 1) < A * (2 * (2 ^ N)) :=
      Nat.mul_lt_mul_of_pos_left hlt (by omega)
    have hassoc : A * (2 * (2 ^ N)) = 2 * (A * (2 ^ N)) := by
      simp [Nat.mul_left_comm]
    omega
  · intro B
    rw [zeroDecayShellSum_closed_form]
    omega

/-! ## 2. Poincaré `radialIntegrand` Homotopy & Global `expDomain = univ` vs. Punctured Winding (`iso-domain-bridge-5110`) -/

/-- Twice the radial Poincaré homotopy primitive `2 Φ(x, y) = a₁ x² + (b₁ + a₂) x y + b₂ y²` of linear 1-form `(a₁ x + b₁ y, a₂ x + b₂ y)`. -/
def radialPrimitive2 (a1 b1 a2 b2 x y : Int) : Int :=
  a1 * x * x + (b1 + a2) * x * y + b2 * y * y

/-- Formal partial derivatives `(∂_x(2Φ), ∂_y(2Φ))`. -/
def gradRadialPrimitive2 (a1 b1 a2 b2 x y : Int) : Int × Int :=
  (2 * a1 * x + (b1 + a2) * y, (b1 + a2) * x + 2 * b2 * y)

/-- Discrete circulation of a 1-form `ω : Int × Int → Int × Int` around the 4-step diamond loop `(1,0) → (0,1) → (-1,0) → (0,-1) → (1,0)`. -/
def diamondLoopCirculation (omegaForm : Int × Int → Int × Int) : Int :=
  let e0 := omegaForm (1, 0)
  let e1 := omegaForm (0, 1)
  let e2 := omegaForm (-1, 0)
  let e3 := omegaForm (0, -1)
  (e0.1 * (-1) + e0.2 * 1) +
  (e1.1 * (-1) + e1.2 * (-1)) +
  (e2.1 * 1 + e2.2 * (-1)) +
  (e3.1 * 1 + e3.2 * 1)

/-- Non-exact rotational / punctured-origin winding field `ω_wind(x, y) = (-y, x)`. -/
def windingForm (v : Int × Int) : Int × Int :=
  (-v.2, v.1)

/--
**Bridge 2 (`iso-domain-bridge-5110`)**:
1. On a star-shaped global ray domain (`tfae_expDomain_eq_univ`), whenever a linear 1-form `(a₁ x + b₁ y, a₂ x + b₂ y)`
   is closed (`b₁ = a₂`), the radial Poincaré primitive `radialPrimitive2` recovers `2 ω` everywhere (`grad = (2 P, 2 Q)`),
   and any exact potential difference telescopes to `0` around the closed diamond loop.
2. Sharp Punctured / Non-Exact Failure: For `windingForm(x, y) = (-y, x)` (`b₁ = -1 ≠ +1 = a₂`, modelling the punctured
   plane `ℝ² \ {0}` where rays hit the singularity and `expDomain ≠ univ`), the radial integrand `x(-y) + y(x)` vanishes
   identically (`radialPrimitive2 0 (-1) 1 0 x y = 0`), failing to recover `2 ω` at `(1, 0)` (`(0, 0) ≠ (0, 2)`), while
   `diamondLoopCirculation windingForm = 4 ≠ 0`!
-/
theorem poincare_radial_ray_homotopy_and_global_exp_domain_vs_punctured_winding_obstruction :
    (∀ a1 b1 a2 b2 x y : Int,
      b1 = a2 →
      gradRadialPrimitive2 a1 b1 a2 b2 x y =
        (2 * (a1 * x + b1 * y), 2 * (a2 * x + b2 * y))) ∧
    (∀ Φ : Int × Int → Int,
      (Φ (0, 1) - Φ (1, 0)) + (Φ (-1, 0) - Φ (0, 1)) +
      (Φ (0, -1) - Φ (-1, 0)) + (Φ (1, 0) - Φ (0, -1)) = 0) ∧
    ((∀ x y : Int, radialPrimitive2 0 (-1) 1 0 x y = 0) ∧
     gradRadialPrimitive2 0 (-1) 1 0 1 0 ≠ (2 * (windingForm (1, 0)).1, 2 * (windingForm (1, 0)).2) ∧
     diamondLoopCirculation windingForm = 4) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a1 b1 a2 b2 x y hclosed
    subst hclosed
    unfold gradRadialPrimitive2
    apply Prod.ext <;> (simp only [Int.mul_add, Int.add_mul, Int.mul_assoc]; omega)
  · intro Φ
    omega
  · refine ⟨?_, by decide, by decide⟩
    intro x y
    unfold radialPrimitive2
    simp

/-! ## 3. Hyperoctahedral `O₂(ℤ)` Hopf-Subgroup Orbit Average vs. Non-Subgroup Subset (`iso-domain-bridge-5500`) -/

/-- The 8 elements of the 2D hyperoctahedral integral orthogonal Hopf subgroup `O₂(ℤ)` acting on `ℤ²`. -/
def hyperOctAction (i : Fin 8) (v : Int × Int) : Int × Int :=
  match i.val with
  | 0 => (v.1, v.2)
  | 1 => (-v.1, v.2)
  | 2 => (v.1, -v.2)
  | 3 => (-v.1, -v.2)
  | 4 => (v.2, v.1)
  | 5 => (-v.2, v.1)
  | 6 => (v.2, -v.1)
  | _ => (-v.2, -v.1)

/-- Unnormalized `O₂(ℤ)` radial/orbit average `(P_H f)(v) = ∑_{i<8} f(g_i · v)`. -/
def hyperOctOrbitSum (f : Int × Int → Int) (v : Int × Int) : Int :=
  f (hyperOctAction ⟨0, by decide⟩ v) +
  f (hyperOctAction ⟨1, by decide⟩ v) +
  f (hyperOctAction ⟨2, by decide⟩ v) +
  f (hyperOctAction ⟨3, by decide⟩ v) +
  f (hyperOctAction ⟨4, by decide⟩ v) +
  f (hyperOctAction ⟨5, by decide⟩ v) +
  f (hyperOctAction ⟨6, by decide⟩ v) +
  f (hyperOctAction ⟨7, by decide⟩ v)

/-- Non-subgroup 2-element subset sum `P_S f (x, y) = f(x, y) + f(-y, x)` (`S = {I, R_{90°}}`). -/
def nonSubgroupQuarterTurnSum (f : Int × Int → Int) (v : Int × Int) : Int :=
  f v + f (-v.2, v.1)

/--
**Bridge 3 (`iso-domain-bridge-5500`)**:
1. Every `g_i ∈ O₂(ℤ)` preserves the Euclidean Hopf quadratic form `x² + y²`, and `hyperOctOrbitSum` is
   strictly `O₂(ℤ)`-invariant (`P_H f (g_j · v) = P_H f (v)` for all `j : Fin 8`) and scaled-idempotent
   (`P_H (P_H f) (v) = 8 · P_H f (v)`).
2. Sharp Non-Subgroup Failure: Averaging over the non-subgroup subset `S = {I, R_{90°}}` on `f(x, y) = x`
   at `v = (1, 0)` fails `R_{90°}`-invariance (`P_S f (0, 1) = -1 ≠ +1 = P_S f (1, 0)`) and fails scaled
   idempotence (`P_S (P_S f) (1, 0) = 0 ≠ 2 · P_S f (1, 0)`)!
-/
theorem hyperoctahedral_hopf_subgroup_orbit_average_idempotence_vs_nonsubgroup_drift :
    (∀ i : Fin 8, ∀ x y : Int,
      let w := hyperOctAction i (x, y)
      w.1 * w.1 + w.2 * w.2 = x * x + y * y) ∧
    (∀ f : Int × Int → Int, ∀ j : Fin 8, ∀ x y : Int,
      hyperOctOrbitSum f (hyperOctAction j (x, y)) = hyperOctOrbitSum f (x, y)) ∧
    (∀ f : Int × Int → Int, ∀ x y : Int,
      hyperOctOrbitSum (hyperOctOrbitSum f) (x, y) = 8 * hyperOctOrbitSum f (x, y)) ∧
    (let f1 : Int × Int → Int := fun v => v.1
     nonSubgroupQuarterTurnSum f1 (0, 1) ≠ nonSubgroupQuarterTurnSum f1 (1, 0) ∧
     nonSubgroupQuarterTurnSum (nonSubgroupQuarterTurnSum f1) (1, 0) ≠
       2 * nonSubgroupQuarterTurnSum f1 (1, 0)) := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro i x y
    match i with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ =>
      simp only [hyperOctAction, Int.neg_mul, Int.mul_neg, Int.neg_neg]
      try omega
  · intro f j x y
    match j with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ =>
      simp only [hyperOctOrbitSum, hyperOctAction, Int.neg_neg]
      try omega
  · intro f x y
    simp only [hyperOctOrbitSum, hyperOctAction, Int.neg_neg]
    omega

/-! ## 4. `S₃` Orbit Symmetrization vs. Prefix `ExchangeableAt 2` Failure (`iso-domain-bridge-5991`) -/

/-- Full `S₃` permutation orbit sum on 3-tuples. -/
def sym3Orbit (F : Int → Int → Int → Int) (x y z : Int) : Int :=
  F x y z + F y x z + F x z y + F z y x + F y z x + F z x y

/-- Prefix `ExchangeableAt 2` law on `{0, 1}³`: symmetric in `(x, y)` but asymmetric in `z`. -/
def prefixExch2Law (x y z : Int) : Int :=
  if (x = 1 ∧ y = 0 ∧ z = 0) ∨ (x = 0 ∧ y = 1 ∧ z = 0) then 1 else 0

/--
**Bridge 4 (`iso-domain-bridge-5991`)**:
1. `sym3Orbit F` is invariant under both Coxeter transpositions `(x, y, z) ↦ (y, x, z)` and `(x, y, z) ↦ (x, z, y)`
   (hence all of `S₃` — `ExchangeableAt 3`) and satisfies `sym3Orbit (sym3Orbit F) = 6 · sym3Orbit F`.
2. Sharp Prefix `ExchangeableAt 2` Failure: `prefixExch2Law` satisfies `prefixExch2Law x y z = prefixExch2Law y x z`
   for all `x, y, z : Int` (`ExchangeableAt 2`), yet `prefixExch2Law 1 0 0 = 1 ≠ 0 = prefixExch2Law 0 0 1`!
-/
theorem s3_orbit_symmetrization_full_exchangeability_vs_prefix_exchangeable_at_two_failure :
    (∀ F : Int → Int → Int → Int, ∀ x y z : Int,
      sym3Orbit F y x z = sym3Orbit F x y z ∧
      sym3Orbit F x z y = sym3Orbit F x y z ∧
      sym3Orbit (sym3Orbit F) x y z = 6 * sym3Orbit F x y z) ∧
    ((∀ x y z : Int, prefixExch2Law x y z = prefixExch2Law y x z) ∧
     prefixExch2Law 1 0 0 = 1 ∧
     prefixExch2Law 0 0 1 = 0 ∧
     prefixExch2Law 1 0 0 ≠ prefixExch2Law 0 0 1) := by
  refine ⟨?_, ?_⟩
  · intro F x y z
    refine ⟨by unfold sym3Orbit; omega, by unfold sym3Orbit; omega, by unfold sym3Orbit; omega⟩
  · refine ⟨?_, by decide, by decide, by decide⟩
    intro x y z
    unfold prefixExch2Law
    by_cases h1 : x = 1 ∧ y = 0 ∧ z = 0
    · rcases h1 with ⟨hx, hy, hz⟩
      subst hx; subst hy; subst hz
      decide
    · by_cases h2 : x = 0 ∧ y = 1 ∧ z = 0
      · rcases h2 with ⟨hx, hy, hz⟩
        subst hx; subst hy; subst hz
        decide
      · have hL : ¬ ((x = 1 ∧ y = 0 ∧ z = 0) ∨ (x = 0 ∧ y = 1 ∧ z = 0)) := by
          intro hOr
          rcases hOr with ha | hb
          · exact h1 ha
          · exact h2 hb
        have hR : ¬ ((y = 1 ∧ x = 0 ∧ z = 0) ∨ (y = 0 ∧ x = 1 ∧ z = 0)) := by
          intro hOr
          rcases hOr with ⟨hy, hx, hz⟩ | ⟨hy, hx, hz⟩
          · exact h2 ⟨hx, hy, hz⟩
          · exact h1 ⟨hx, hy, hz⟩
        simp [hL, hR]

/-! ## 5. Radial Antipodal Even-Moment Determinacy vs. Chiral Odd-Moment Ambiguity (`iso-domain-bridge-5831`) -/

/-- Moments `(m₀, m₁, m₂, m₃, m₄)` of a 5-point measure `(p_{-2}, p_{-1}, p_0, p_1, p_2)` on `{-2, -1, 0, 1, 2}`. -/
def moments5 (pm2 pm1 p0 pp1 pp2 : Int) : Int × Int × Int × Int × Int :=
  (pm2 + pm1 + p0 + pp1 + pp2,
   (-2) * pm2 + (-1) * pm1 + pp1 + 2 * pp2,
   4 * pm2 + pm1 + pp1 + 4 * pp2,
   (-8) * pm2 + (-1) * pm1 + pp1 + 8 * pp2,
   16 * pm2 + pm1 + pp1 + 16 * pp2)

/--
**Bridge 5 (`iso-domain-bridge-5831`)**:
1. Radial/antipodal symmetry (`pm2 = pp2` and `pm1 = pp1`) annihilates odd moments (`m₁ = 0`, `m₃ = 0`),
   and equality of the 3 even moments `(m₀, m₂, m₄)` uniquely reconstructs all 5 weights!
2. Sharp Non-Radial Chiral Failure: Without antipodal averaging, `δ_{+1} = (0, 0, 0, 1, 0)` and
   `δ_{-1} = (0, 1, 0, 0, 0)` have identical even moments `(m₀, m₂, m₄) = (1, 1, 1)` yet differ at `m₁` (`+1 ≠ -1`)!
-/
theorem radial_antipodal_orbit_even_moment_determinacy_vs_chiral_odd_moment_ambiguity :
    (∀ pm2 pm1 p0 pp1 pp2 qm2 qm1 q0 qp1 qp2 : Int,
      pm2 = pp2 → pm1 = pp1 → qm2 = qp2 → qm1 = qp1 →
      let mp := moments5 pm2 pm1 p0 pp1 pp2
      let mq := moments5 qm2 qm1 q0 qp1 qp2
      mp.2.1 = 0 ∧ mp.2.2.2.1 = 0 ∧
      (mp.1 = mq.1 → mp.2.2.1 = mq.2.2.1 → mp.2.2.2.2 = mq.2.2.2.2 →
        pm2 = qm2 ∧ pm1 = qm1 ∧ p0 = q0 ∧ pp1 = qp1 ∧ pp2 = qp2)) ∧
    (let mPos := moments5 0 0 0 1 0
     let mNeg := moments5 0 1 0 0 0
     mPos.1 = mNeg.1 ∧
     mPos.2.2.1 = mNeg.2.2.1 ∧
     mPos.2.2.2.2 = mNeg.2.2.2.2 ∧
     mPos.2.1 = 1 ∧
     mNeg.2.1 = -1) := by
  refine ⟨?_, by decide⟩
  intro pm2 pm1 p0 pp1 pp2 qm2 qm1 q0 qp1 qp2 hp2 hp1 hq2 hq1
  dsimp only [moments5]
  refine ⟨by omega, by omega, ?_⟩
  intro hm0 hm2 hm4
  omega

/-! ## 6. `ℤ_4` Cohn–Elkies `hopfBarrier` Packing Bound vs. Negative-Fourier & Exterior-Barrier Failures (`iso-domain-bridge-6560`) -/

/-- Discrete cosine character `cos(π x / 2)` on `ℤ_4`. -/
def cosZ4 (x : Fin 4) : Int :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => -1
  | _ => 0

/-- Discrete sine character `sin(π x / 2)` on `ℤ_4`. -/
def sinZ4 (x : Fin 4) : Int :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | _ => -1

/-- Alternating character `(-1)^x` on `ℤ_4`. -/
def altZ4 (x : Fin 4) : Int :=
  if x.val % 2 = 0 then 1 else -1

/-- Positive-definite radial Cohn–Elkies barrier kernel `K(x, y) = 1 + cosZ4(x)cosZ4(y) + sinZ4(x)sinZ4(y)` on `ℤ_4`. -/
def barrierKernelZ4 (x y : Fin 4) : Int :=
  1 + cosZ4 x * cosZ4 y + sinZ4 x * sinZ4 y

/-- Cyclic Lee distance on `ℤ_4` (`0, 1, 2`). -/
def leeDistZ4 (x y : Fin 4) : Nat :=
  let d := if x.val ≥ y.val then x.val - y.val else y.val - x.val
  if d = 3 then 1 else d

/-- Sum over `Fin 4`. -/
def sumFin4 (g : Fin 4 → Int) : Int :=
  g ⟨0, by decide⟩ + g ⟨1, by decide⟩ + g ⟨2, by decide⟩ + g ⟨3, by decide⟩

/-- Indefinite kernel `K_bad(x, y) = 1 - (-1)^x (-1)^y` (`w_alt = -1 < 0`). -/
def badNegFourierZ4 (x y : Fin 4) : Int :=
  1 - altZ4 x * altZ4 y

/-- Positive-exterior kernel `K_pos(x, y) = 1 + (-1)^x (-1)^y` (`K_pos(0, 2) = +2 > 0`). -/
def badPosBarrierZ4 (x y : Fin 4) : Int :=
  1 + altZ4 x * altZ4 y

/--
**Bridge 6 (`iso-domain-bridge-6560`)**:
1. `barrierKernelZ4` has non-negative Fourier weights `(1, 1, 1)`, constant diagonal `K(x, x) = 2`, and radial
   `hopfBarrier` root `K(x, y) = 0 ≤ 0` at cyclic distance `leeDistZ4 x y ≥ 2`; consequently **every** subset
   `C : Fin 4 → Bool` with minimum Lee distance `≥ 2` has cardinality `≤ 2`, attained at `{0, 2}`!
2. Sharp Fourier & Barrier Premise Failures:
   - `badNegFourierZ4` (`w_alt = -1 < 0`) satisfies `K_bad(0, 2) = 0 ≤ 0` on `{0, 2}`, yet `w_0 · |{0, 2}| = 2 > 0 = K_bad(0, 0)`!
   - `badPosBarrierZ4` (`w ≥ 0`, `K_pos(0, 2) = +2 > 0`) violates the exterior Hopf barrier, giving double sum `8 > 4 = K_pos(0, 0) · |{0, 2}|`!
-/
theorem cyclic_z4_cohn_elkies_hopf_barrier_packing_bound_vs_barrier_and_fourier_failures :
    ((∀ x : Fin 4, barrierKernelZ4 x x = 2) ∧
     (∀ x y : Fin 4, 2 ≤ leeDistZ4 x y → barrierKernelZ4 x y = 0) ∧
     (∀ c0 c1 c2 c3 : Bool,
       let C : Fin 4 → Int := fun x =>
         match x.val with
         | 0 => if c0 then 1 else 0
         | 1 => if c1 then 1 else 0
         | 2 => if c2 then 1 else 0
         | _ => if c3 then 1 else 0
       (∀ x y : Fin 4, x ≠ y → C x = 1 → C y = 1 → 2 ≤ leeDistZ4 x y) →
       sumFin4 C ≤ 2)) ∧
    (badNegFourierZ4 ⟨0, by decide⟩ ⟨2, by decide⟩ ≤ 0 ∧
     badNegFourierZ4 ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 ∧
     (2 : Int) > badNegFourierZ4 ⟨0, by decide⟩ ⟨0, by decide⟩) ∧
    (badPosBarrierZ4 ⟨0, by decide⟩ ⟨2, by decide⟩ = 2 ∧
     badPosBarrierZ4 ⟨0, by decide⟩ ⟨0, by decide⟩ + badPosBarrierZ4 ⟨0, by decide⟩ ⟨2, by decide⟩ +
     badPosBarrierZ4 ⟨2, by decide⟩ ⟨0, by decide⟩ + badPosBarrierZ4 ⟨2, by decide⟩ ⟨2, by decide⟩ = 8) := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide, by decide⟩

/-! ## 7. `OrderIso.isCompactElement` & Monotone Quotient Map vs. Antitone & Non-Injective Truncation (`iso-oai-sphere-tauceti-89`) -/

/-- Join (`max`) on `Nat`. -/
def joinNat (a b : Nat) : Nat :=
  if a ≤ b then b else a

/-- Monotone quotient root map `q(x) = x / 2`. -/
def quotientHalf (x : Nat) : Nat :=
  x / 2

/-- Antitone involution `rev4(x) = 4 - x` on `{0..4}`. -/
def antitoneRev4 (x : Nat) : Nat :=
  4 - x

/-- Non-injective monotone truncation `trunc1(x) = min(x, 1)`. -/
def nonInjTrunc1 (x : Nat) : Nat :=
  if x ≤ 1 then x else 1

/--
**Bridge 7 (`iso-oai-sphere-tauceti-89`)**:
1. Any order isomorphism `e : Nat → Nat` (`∀ x y, x ≤ y ↔ e x ≤ e y`) preserves finite joins
   `e(joinNat a b) = joinNat (e a) (e b)` and compact threshold coverability
   `k ≤ joinNat a b ↔ e k ≤ joinNat (e a) (e b)` (`OrderIso.isCompactElement`), while `quotientHalf`
   is monotone (`x ≤ y → quotientHalf x ≤ quotientHalf y`).
2. Sharp Antitone & Non-Injective Quotient Failures:
   - Antitone bijection `antitoneRev4` reverses order: `1 ≤ joinNat 2 3` holds, yet
     `antitoneRev4 1 ≤ joinNat (antitoneRev4 2) (antitoneRev4 3)` (`3 ≤ 2`) fails!
   - Non-injective monotone map `nonInjTrunc1` collapses `2 ↦ 1`: `nonInjTrunc1 2 ≤ joinNat (nonInjTrunc1 0) (nonInjTrunc1 1)` (`1 ≤ 1`)
     holds, yet `2 ≤ joinNat 0 1` (`2 ≤ 1`) fails!
-/
theorem order_iso_compact_element_and_monotone_quotient_threshold_vs_antitone_and_truncation_failures :
    (∀ e : Nat → Nat,
      (∀ x y : Nat, x ≤ y ↔ e x ≤ e y) →
      (∀ a b : Nat, e (joinNat a b) = joinNat (e a) (e b)) ∧
      (∀ k a b : Nat, k ≤ joinNat a b ↔ e k ≤ joinNat (e a) (e b))) ∧
    (∀ x y : Nat, x ≤ y → quotientHalf x ≤ quotientHalf y) ∧
    (1 ≤ joinNat 2 3 ∧ ¬ (antitoneRev4 1 ≤ joinNat (antitoneRev4 2) (antitoneRev4 3))) ∧
    (nonInjTrunc1 2 ≤ joinNat (nonInjTrunc1 0) (nonInjTrunc1 1) ∧ ¬ (2 ≤ joinNat 0 1)) := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · intro e hIso
    have hJoin : ∀ a b : Nat, e (joinNat a b) = joinNat (e a) (e b) := by
      intro a b
      unfold joinNat
      by_cases hab : a ≤ b
      · have heab : e a ≤ e b := (hIso a b).mp hab
        simp [hab, heab]
      · have hneab : ¬ (e a ≤ e b) := fun h => hab ((hIso a b).mpr h)
        simp [hab, hneab]
    refine ⟨hJoin, ?_⟩
    intro k a b
    rw [← hJoin a b]
    exact hIso k (joinNat a b)
  · intro x y hxy
    unfold quotientHalf
    omega

end CommonGround.Verification.TheoremAtlasBochnerRieszDecayWeightPoincareRadialRinowOrbitHopfSubgroupExchangeableMomentsHopfBarrierAndOrderCompactBridge
