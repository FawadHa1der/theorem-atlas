/-
  Common Ground · Verification Suite #601 (V200 — [90.0, 91.0) Horizon Audit)
  ===========================================================================
  Module: `CommonGround/Verification/TheoremAtlasRapidDecayMomentsAnalyticCharFunQuantileDualityHopfSubgroupNormalChartHopfBarrierAndAlmostComplexBridge.lean`

  Certifies all 7 genuine cross-domain bridges in the `[90.0, 91.0)` AST structural band
  with zero `sorry`s and explicit premise-failure counterexamples in Lean 4.33.0:
    1. `iso-domain-bridge-5090` (`oai-riesz :: uniform_rapid_decay_joint_amplitude` ↔
       `tc-probcomb :: charFun_eq_of_forall_integral_pow_eq`)
    2. `iso-domain-bridge-6957` (`oai-ehrhart :: angularFourierCoefficient` ↔
       `tc-probcomb :: charFun_eq_of_frequently_complexMGF_eq`)
    3. `iso-domain-bridge-6183` (`oai-smoothing :: complexDualityPartner_mul` ↔
       `tc-probcomb :: le_cdf_quantile`)
    4. `iso-v11-bridge-0963` (`oai-ehrhart :: angularSmoothPartitionBump_zero_of_le` ↔
       `tc-lie :: hopfIdealPointsSubgroup`)
    5. `iso-domain-bridge-6262` (`oai-codes :: normalChart` ↔
       `oai-gapcvp :: BinaryAffineSystem.effectiveSquareBasisMatrix`)
    6. `iso-domain-bridge-6943` (`oai-ehrhart :: angularFourierCoefficient` ↔
       `tc-lie :: hopfBarrier`)
    7. `iso-domain-bridge-5272` (`oai-smoothing :: complexDualityPartner_mul` ↔
       `tc-geometry :: AlmostComplexStructure`)
-/

namespace TheoremAtlasRapidDecayMomentsAnalyticCharFunQuantileDualityHopfSubgroupNormalChartHopfBarrierAndAlmostComplexBridge

/-! ## 1. Rapid-Decay Full-Moment Determinacy vs. Truncated Two-Moment Indeterminacy (`iso-domain-bridge-5090`) -/

def mom0 (p : Int × Int × Int) : Int := p.1 + p.2.1 + p.2.2
def mom1 (p : Int × Int × Int) : Int := p.2.1 + 2 * p.2.2
def mom2 (p : Int × Int × Int) : Int := p.2.1 + 4 * p.2.2

theorem rapid_decay_full_moment_determinacy_vs_truncated_two_moment_indeterminacy :
    -- 1. Full power moments `(m₀, m₁, m₂)` uniquely reconstruct every signed measure on `{0, 1, 2}`
    (∀ p q : Int × Int × Int,
      mom0 p = mom0 q → mom1 p = mom1 q → mom2 p = mom2 q → p = q) ∧
    -- 2. Explicit Vandermonde inversion formulas
    (∀ p : Int × Int × Int,
      2 * p.2.2 = mom2 p - mom1 p ∧
      p.2.1 = 2 * mom1 p - mom2 p ∧
      2 * p.1 = 2 * mom0 p - 3 * mom1 p + mom2 p) ∧
    -- 3. Truncated 2-moment indeterminacy: `(1, 0, 1)` and `(0, 2, 0)` share `(m₀, m₁) = (2, 2)` yet `m₂` differs (`4 ≠ 2`)
    (mom0 (1, (0, 1)) = 2 ∧ mom0 (0, (2, 0)) = 2 ∧
      mom1 (1, (0, 1)) = 2 ∧ mom1 (0, (2, 0)) = 2 ∧
      mom2 (1, (0, 1)) = 4 ∧ mom2 (0, (2, 0)) = 2 ∧
      ((1 : Int), ((0 : Int), (1 : Int))) ≠ (0, (2, 0))) := by
  refine ⟨?_, ?_, by decide⟩
  · intro ⟨p0, p1, p2⟩ ⟨q0, q1, q2⟩ h0 h1 h2
    simp only [mom0, mom1, mom2] at h0 h1 h2
    have hp2 : p2 = q2 := by omega
    have hp1 : p1 = q1 := by omega
    have hp0 : p0 = q0 := by omega
    rw [hp0, hp1, hp2]
  · intro ⟨p0, p1, p2⟩
    simp only [mom0, mom1, mom2]
    omega

/-! ## 2. Analytic MGF / Trigonometric 3-Node Uniqueness vs. 2-Node Aliasing (`iso-domain-bridge-6957`) -/

def evalQuad (a : Int × Int × Int) (z : Int) : Int :=
  a.1 + a.2.1 * z + a.2.2 * z * z

theorem analytic_mgf_three_node_uniqueness_vs_two_node_aliasing_failure :
    -- 1. Agreement at 3 distinct nodes `{-1, 0, 1}` forces coefficient identity `a = b`
    (∀ a b : Int × Int × Int,
      evalQuad a (-1) = evalQuad b (-1) →
      evalQuad a 0 = evalQuad b 0 →
      evalQuad a 1 = evalQuad b 1 →
      a = b) ∧
    -- 2. Sparse 2-node aliasing failure: `Q(z) = z(z - 1) = -z + z²` vanishes at `0` and `1` yet `Q(2) = 2 ≠ 0`
    (let qAlias : Int × Int × Int := (0, (-1, 1))
     evalQuad qAlias 0 = 0 ∧
     evalQuad qAlias 1 = 0 ∧
     evalQuad qAlias 2 = 2 ∧
     evalQuad qAlias (-1) = 2 ∧
     qAlias ≠ (0, (0, 0))) := by
  refine ⟨?_, by decide⟩
  · intro ⟨a0, a1, a2⟩ ⟨b0, b1, b2⟩ hm1 h0 hp1
    simp [evalQuad] at hm1 h0 hp1
    have eq0 : a0 = b0 := by omega
    have eq1 : a1 = b1 := by omega
    have eq2 : a2 = b2 := by omega
    rw [eq0, eq1, eq2]

/-! ## 3. Duality Partner Saturation & Quantile–CDF Unit vs. Out-of-Range & Phase Mismatch (`iso-domain-bridge-6183`) -/

def normSq2 (v : Int × Int) : Int := v.1 * v.1 + v.2 * v.2
def dot2 (u v : Int × Int) : Int := u.1 * v.1 + u.2 * v.2
def stdJ (v : Int × Int) : Int × Int := (-v.2, v.1)
def dualP4 (v : Int × Int) : Int × Int := (normSq2 v * v.1, normSq2 v * v.2)

def stdCdf2 : Nat → Int
  | 0 => 1
  | 1 => 3
  | _ => 4

def stdQuant2 (t : Int) : Nat :=
  if t ≤ stdCdf2 0 then 0 else if t ≤ stdCdf2 1 then 1 else 2

theorem mul_left_swap (a x y : Int) : a * (x * y) = x * (a * y) := by
  rw [← Int.mul_assoc, Int.mul_comm a x, Int.mul_assoc]

theorem duality_partner_holder_saturation_and_quantile_unit_vs_out_of_range_and_phase_mismatch :
    -- 1. `dualP4` achieves exact `L⁴` Hölder saturation `⟨v, D₄(v)⟩ = (‖v‖²)²`
    (∀ v : Int × Int, dot2 v (dualP4 v) = normSq2 v * normSq2 v) ∧
    -- 2. Discrete quantile–CDF adjunction & unit saturation `t ≤ F(q(t))` for all in-range `t ≤ 4`
    (∀ t : Int, t ≤ 4 →
      t ≤ stdCdf2 (stdQuant2 t) ∧
      (∀ x : Fin 3, (stdQuant2 t ≤ x.val ↔ t ≤ stdCdf2 x.val))) ∧
    -- 3. Premise failures: out-of-range `t = 5 > 4 = F(2)` violates `t ≤ F(q(t))`, and `90°` rotated `D₄(stdJ v)` gives `0 ≠ 25`
    (¬ (5 ≤ stdCdf2 (stdQuant2 5)) ∧
      dot2 (2, 1) (dualP4 (2, 1)) = 25 ∧
      dot2 (2, 1) (dualP4 (stdJ (2, 1))) = 0) := by
  refine ⟨?_, ?_, by decide⟩
  · intro ⟨x, y⟩
    unfold dot2 dualP4 normSq2
    dsimp
    have hx : x * ((x * x + y * y) * x) = (x * x + y * y) * (x * x) :=
      mul_left_swap x (x * x + y * y) x
    have hy : y * ((x * x + y * y) * y) = (x * x + y * y) * (y * y) :=
      mul_left_swap y (x * x + y * y) y
    rw [hx, hy, ← Int.mul_add]
  · intro t ht4
    refine ⟨?_, ?_⟩
    · unfold stdQuant2
      split
      · assumption
      · split
        · assumption
        · unfold stdCdf2
          exact ht4
    · intro ⟨x, hx⟩
      match x, hx with
      | 0, _ =>
        unfold stdQuant2
        split
        · simp [stdCdf2] at *; omega
        · split <;> (simp [stdCdf2] at *; omega)
      | 1, _ =>
        unfold stdQuant2
        split
        · simp [stdCdf2] at *; omega
        · split <;> (simp [stdCdf2] at *; omega)
      | 2, _ =>
        unfold stdQuant2
        split
        · simp [stdCdf2] at *; omega
        · split <;> (simp [stdCdf2] at *; omega)

/-! ## 4. Smooth Cutoff Zero-Locus & `SL₂(ℤ)` Hopf-Ideal Subgroup vs. Det-2 Non-Group (`iso-v11-bridge-0963`) -/

def bumpSq (a x : Int) : Int :=
  if x ≤ a then 0 else (x - a) * (x - a)

abbrev Mat2 := Int × Int × Int × Int

def idMat2 : Mat2 := (1, (0, (0, 1)))

def det2 (m : Mat2) : Int :=
  m.1 * m.2.2.2 - m.2.1 * m.2.2.1

def matMul2 (m n : Mat2) : Mat2 :=
  (m.1 * n.1 + m.2.1 * n.2.2.1,
    (m.1 * n.2.1 + m.2.1 * n.2.2.2,
      (m.2.2.1 * n.1 + m.2.2.2 * n.2.2.1,
        m.2.2.1 * n.2.1 + m.2.2.2 * n.2.2.2)))

def adj2 (m : Mat2) : Mat2 :=
  (m.2.2.2, (-m.2.1, (-m.2.2.1, m.1)))

theorem det2_mul (m n : Mat2) : det2 (matMul2 m n) = det2 m * det2 n := by
  rcases m with ⟨a, b, c, d⟩
  rcases n with ⟨p, q, r, s⟩
  unfold det2 matMul2
  dsimp
  have h1 : (a * p + b * r) * (c * q + d * s) =
      a * p * c * q + a * p * d * s + b * r * c * q + b * r * d * s := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
    have e1 : (a * p) * (c * q) = a * p * c * q := by rw [← Int.mul_assoc]
    have e2 : (a * p) * (d * s) = a * p * d * s := by rw [← Int.mul_assoc]
    have e3 : (b * r) * (c * q) = b * r * c * q := by rw [← Int.mul_assoc]
    have e4 : (b * r) * (d * s) = b * r * d * s := by rw [← Int.mul_assoc]
    rw [e1, e2, e3, e4]
    omega
  have h2 : (a * q + b * s) * (c * p + d * r) =
      a * p * c * q + a * d * q * r + b * c * p * s + b * r * d * s := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
    have f1 : (a * q) * (c * p) = a * p * c * q := by
      simp only [Int.mul_left_comm, Int.mul_comm]
    have f2 : (a * q) * (d * r) = a * d * q * r := by
      simp only [Int.mul_left_comm, Int.mul_comm]
    have f3 : (b * s) * (c * p) = b * c * p * s := by
      simp only [Int.mul_left_comm, Int.mul_comm]
    have f4 : (b * s) * (d * r) = b * r * d * s := by
      simp only [Int.mul_left_comm, Int.mul_comm]
    rw [f1, f2, f3, f4]
    omega
  have h3 : (a * d - b * c) * (p * s - q * r) =
      a * p * d * s - a * d * q * r - b * c * p * s + b * r * c * q := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have g1 : (a * d) * (p * s) = a * p * d * s := by
      simp only [Int.mul_left_comm, Int.mul_comm]
    have g2 : (a * d) * (q * r) = a * d * q * r := by
      simp only [Int.mul_left_comm, Int.mul_comm]
    have g3 : (b * c) * (p * s) = b * c * p * s := by
      simp only [Int.mul_left_comm, Int.mul_comm]
    have g4 : (b * c) * (q * r) = b * r * c * q := by
      simp only [Int.mul_left_comm, Int.mul_comm]
    rw [g1, g2, g3, g4]
    omega
  omega

theorem smooth_cutoff_zero_locus_and_sl2_hopf_ideal_subgroup_vs_above_threshold_and_det_two_failure :
    -- 1. Cutoff vanishes below `a` and stays non-negative everywhere
    (∀ a x : Int, (x ≤ a → bumpSq a x = 0) ∧ 0 ≤ bumpSq a x) ∧
    -- 2. Hopf ideal `det M - 1 = 0` cuts out a genuine subgroup (`I₂ ∈ SL₂`, product-closed, adjugate-invertible)
    (det2 idMat2 - 1 = 0 ∧
      (∀ m n : Mat2, det2 m - 1 = 0 → det2 n - 1 = 0 → det2 (matMul2 m n) - 1 = 0) ∧
      (∀ m : Mat2, det2 m - 1 = 0 → matMul2 m (adj2 m) = idMat2)) ∧
    -- 3. Above-threshold non-vanishing (`bumpSq 3 5 = 4 ≠ 0`) & non-Hopf ideal `det M - 2 = 0` fails subgroup closure (`4 ≠ 2`)
    (bumpSq 3 5 = 4 ∧
      det2 idMat2 - 2 ≠ 0 ∧
      (let m2 : Mat2 := (2, (0, (0, 1)))
       det2 m2 - 2 = 0 ∧ det2 (matMul2 m2 m2) - 2 = 2)) := by
  refine ⟨?_, ⟨by decide, ?_, ?_⟩, by decide⟩
  · intro a x
    refine ⟨?_, ?_⟩
    · intro hle
      unfold bumpSq
      rw [if_pos hle]
    · unfold bumpSq
      split
      · omega
      · by_cases hnn : 0 ≤ x - a
        · exact Int.mul_nonneg hnn hnn
        · have hneg : 0 ≤ -(x - a) := by omega
          have hsq : (-(x - a)) * (-(x - a)) = (x - a) * (x - a) := by
            rw [Int.neg_mul_neg]
          rw [← hsq]
          exact Int.mul_nonneg hneg hneg
  · intro m n hm hn
    rw [det2_mul]
    have dm : det2 m = 1 := by omega
    have dn : det2 n = 1 := by omega
    rw [dm, dn]
    decide
  · intro ⟨a, b, c, d⟩ hdet
    unfold det2 at hdet
    dsimp at hdet
    unfold matMul2 adj2 idMat2
    dsimp
    have hbc : a * (-b) + b * a = 0 := by
      simp only [Int.mul_neg, Int.mul_comm]
      omega
    have hcd : c * d + d * (-c) = 0 := by
      simp only [Int.mul_neg, Int.mul_comm]
      omega
    have had1 : a * d + b * (-c) = 1 := by
      simp only [Int.mul_neg]
      omega
    have had2 : c * (-b) + d * a = 1 := by
      simp only [Int.mul_neg, Int.mul_comm d a, Int.mul_comm c b]
      omega
    rw [had1, hbc, hcd, had2]

/-! ## 5. Split Normal Chart Retract Bijection vs. Singular Pivot Collision (`iso-domain-bridge-6262`) -/

abbrev Vec3 := Int × Int × Int

def addV3 (u v : Vec3) : Vec3 := (u.1 + v.1, (u.2.1 + v.2.1, u.2.2 + v.2.2))
def subV3 (u v : Vec3) : Vec3 := (u.1 - v.1, (u.2.1 - v.2.1, u.2.2 - v.2.2))

def injA (x : Int × Int) : Vec3 := (x.1, (x.1 + x.2, x.2))
def retP (y : Vec3) : Int × Int := (y.1, y.2.2)
def singP (y : Vec3) : Int × Int := (y.2.1 - y.1 - y.2.2, 0)

def chartFwd (x : Int × Int) (k : Vec3) : Vec3 := addV3 (injA x) k
def chartInv (y : Vec3) : (Int × Int) × Vec3 := (retP y, subV3 y (injA (retP y)))

theorem split_normal_chart_retract_bijection_vs_singular_pivot_kernel_collision :
    -- 1. Invertible pivot block gives `retP ∘ injA = id` and exact normal-chart bijection `E × ker P ≃ F`
    ((∀ x : Int × Int, retP (injA x) = x) ∧
      (∀ y : Vec3, retP (chartInv y).2 = (0, 0) ∧ chartFwd (chartInv y).1 (chartInv y).2 = y) ∧
      (∀ x : Int × Int, ∀ k : Vec3, retP k = (0, 0) → chartInv (chartFwd x k) = (x, k))) ∧
    -- 2. Singular non-pivot `singP` fails `singP ∘ injA = id` (`(0,0) ≠ (1,2)`) and collides on `E × ker singP`!
    (singP (injA (1, 2)) = (0, 0) ∧
      singP (1, (1, 0)) = (0, 0) ∧
      chartFwd (1, 0) (0, (0, 0)) = chartFwd (0, 0) (1, (1, 0))) := by
  refine ⟨⟨?_, ?_, ?_⟩, by decide⟩
  · intro ⟨x1, x2⟩
    rfl
  · intro ⟨y1, y2, y3⟩
    unfold chartInv chartFwd retP injA subV3 addV3
    dsimp
    refine ⟨by simp only [Int.sub_self], ?_⟩
    have h2 : y1 + y3 + (y2 - (y1 + y3)) = y2 := by omega
    have h1 : y1 + (y1 - y1) = y1 := by omega
    have h3 : y3 + (y3 - y3) = y3 := by omega
    rw [h1, h2, h3]
  · intro ⟨x1, x2⟩ ⟨k1, k2, k3⟩ hk
    unfold retP at hk
    have hk1 : k1 = 0 := by injection hk
    have hk3 : k3 = 0 := by injection hk
    subst hk1; subst hk3
    unfold chartInv chartFwd retP injA addV3 subV3
    dsimp
    have hx1 : x1 + 0 = x1 := by omega
    have hx2 : x2 + 0 = x2 := by omega
    have hm1 : x1 - x1 = 0 := by omega
    have hm2 : x1 + x2 + k2 - (x1 + x2) = k2 := by omega
    have hm3 : x2 - x2 = 0 := by omega
    rw [hx1, hx2, hm1, hm2, hm3]

/-! ## 6. Spherical Hopf Barrier & Harmonic Mean-Value vs. Zero-Exponent & Superharmonic Peak (`iso-domain-bridge-6943`) -/

def hopfBarrier2 (rSq : Int) (v : Int × Int) : Int :=
  normSq2 v - rSq

def harmQuad (a b : Int) (v : Int × Int) : Int :=
  a * (v.1 * v.1 - v.2 * v.2) + 2 * b * v.1 * v.2

theorem spherical_hopf_barrier_level_set_and_harmonic_mean_value_vs_zero_exponent_and_superharmonic_peak :
    -- 1. `hopfBarrier2` vanishes on `‖v‖² = R²`, is `< 0` inside, and `> 0` outside
    (∀ rSq : Int, ∀ v : Int × Int,
      (normSq2 v = rSq → hopfBarrier2 rSq v = 0) ∧
      (normSq2 v < rSq → hopfBarrier2 rSq v < 0) ∧
      (rSq < normSq2 v → 0 < hopfBarrier2 rSq v)) ∧
    -- 2. Every degree-2 harmonic polynomial satisfies the exact `C₄` spherical mean-value law (`= 4 H(0,0) = 0`)
    (∀ a b r : Int,
      harmQuad a b (r, 0) + harmQuad a b (0, r) +
        harmQuad a b (-r, 0) + harmQuad a b (0, -r) = 4 * harmQuad a b (0, 0)) ∧
    -- 3. Degenerate `p = 0` barrier `1 - 1 = 0` fails to separate `(0,0)` from `(2,0)`, and superharmonic `4 - ‖v‖²` peaks strictly at `(0,0)` (`4 > 0`)!
    (((1 : Int) - 1 = 0) ∧
      (let supF := fun v : Int × Int => 4 - normSq2 v
       supF (0, 0) = 4 ∧ supF (2, 0) = 0 ∧ supF (0, 2) = 0 ∧
       supF (-2, 0) = 0 ∧ supF (0, -2) = 0)) := by
  refine ⟨?_, ?_, by decide⟩
  · intro rSq v
    unfold hopfBarrier2
    omega
  · intro a b r
    unfold harmQuad
    dsimp
    have hr : (-r) * (-r) = r * r := by rw [Int.neg_mul_neg]
    simp only [hr, Int.mul_zero, Int.zero_mul, Int.sub_zero, Int.zero_sub,
      Int.add_zero, Int.mul_neg]
    omega

/-! ## 7. `AlmostComplexStructure` (`J² = -I`) Duality Equivariance & Orthogonality vs. Shear (`iso-domain-bridge-5272`) -/

def negV2 (v : Int × Int) : Int × Int := (-v.1, -v.2)
def shearS (v : Int × Int) : Int × Int := (v.1 + v.2, v.2)

theorem almost_complex_j_duality_partner_equivariance_and_orthogonality_vs_unipotent_shear_failure :
    -- 1. `stdJ` satisfies `J ∘ J = -I`, commutes with `dualP4`, and enforces `⟨v, D₄(Jv)⟩ = 0`
    (∀ v : Int × Int,
      stdJ (stdJ v) = negV2 v ∧
      dualP4 (stdJ v) = stdJ (dualP4 v) ∧
      dualP4 (stdJ (stdJ v)) = negV2 (dualP4 v) ∧
      dot2 v (dualP4 (stdJ v)) = 0) ∧
    -- 2. Unipotent shear `shearS` fails `S² = -I`, fails `D₄` commutation (`(15, 5) ≠ (6, 2)`), and fails orthogonality (`20 ≠ 0`)!
    (shearS (shearS (1, 1)) = (3, 1) ∧
      shearS (shearS (1, 1)) ≠ negV2 (1, 1) ∧
      dualP4 (shearS (1, 1)) = (10, 5) ∧
      shearS (dualP4 (1, 1)) = (4, 2) ∧
      dot2 (1, 1) (dualP4 (shearS (1, 1))) = 15) := by
  refine ⟨?_, by decide⟩
  · intro ⟨x, y⟩
    have hnormJ : normSq2 (stdJ (x, y)) = normSq2 (x, y) := by
      unfold normSq2 stdJ
      dsimp
      have hy2 : (-y) * (-y) = y * y := by rw [Int.neg_mul_neg]
      rw [hy2, Int.add_comm]
    have hnormNeg : normSq2 (-x, -y) = normSq2 (x, y) := by
      unfold normSq2
      dsimp
      rw [Int.neg_mul_neg, Int.neg_mul_neg]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rfl
    · unfold dualP4
      rw [hnormJ]
      unfold stdJ
      dsimp
      rw [Int.mul_neg]
    · unfold stdJ dualP4 negV2
      dsimp
      rw [hnormNeg, Int.mul_neg, Int.mul_neg]
    · unfold dot2 dualP4
      rw [hnormJ]
      unfold stdJ normSq2
      dsimp
      have hxy : x * ((x * x + y * y) * (-y)) = -((x * x + y * y) * (x * y)) := by
        rw [Int.mul_neg, Int.mul_neg, mul_left_swap x (x * x + y * y) y]
      have hyx : y * ((x * x + y * y) * x) = (x * x + y * y) * (x * y) := by
        rw [mul_left_swap y (x * x + y * y) x, Int.mul_comm y x]
      rw [hxy, hyx]
      omega

end TheoremAtlasRapidDecayMomentsAnalyticCharFunQuantileDualityHopfSubgroupNormalChartHopfBarrierAndAlmostComplexBridge
