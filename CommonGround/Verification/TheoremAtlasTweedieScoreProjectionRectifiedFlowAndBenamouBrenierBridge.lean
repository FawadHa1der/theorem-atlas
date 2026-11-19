/-!
# Verification Bridge #637 — Tweedie Score Projection, Rectified Flow Straightening & Benamou–Brenier Dynamic OT (`05` + `03` + `08` + `04`)

Cross-domain verification suite bridging:
- **Folder `05` (`oai-smoothing` / `ns` / `euler`)**: Continuum Eulerian velocity fields & antisymmetric Liouville flux conservation;
- **Folder `03` (`tc-probcomb` / `econlib`)**: Empirical Bayes Tweedie–Miyasawa posterior denoiser & conditional score projection;
- **Folder `08` (`tc-geometry` / `poincare`)**: Monge–Kantorovich cyclic monotonicity & Benamou–Brenier dynamic kinetic action lower bound;
- **Folder `04` (`cslib` / `physlib`)**: Single-step (`NFE = 1`) Euler discretization exactness under `Reflow` vs. independent-coupling midpoint mode collapse (`{-2, +2} → +2` empty hole, `W_2² = 9`).
-/

namespace CommonGround.Verification.TheoremAtlasTweedieScoreProjectionRectifiedFlowAndBenamouBrenierBridge

def finSum : {N : Nat} → (Fin N → Int) → Int
  | 0, _ => 0
  | N + 1, f =>
      f ⟨0, Nat.zero_lt_succ N⟩ +
        finSum (fun i : Fin N => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

theorem finSum_add : {N : Nat} → (f g : Fin N → Int) →
    finSum (fun i => f i + g i) = finSum f + finSum g
  | 0, _, _ => by simp [finSum]
  | N + 1, f, g => by
      simp only [finSum]
      have ih := finSum_add (fun i : Fin N => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
                            (fun i : Fin N => g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      omega

theorem finSum_sub : {N : Nat} → (f g : Fin N → Int) →
    finSum (fun i => f i - g i) = finSum f - finSum g
  | 0, _, _ => by simp [finSum]
  | N + 1, f, g => by
      simp only [finSum]
      have ih := finSum_sub (fun i : Fin N => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
                            (fun i : Fin N => g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      omega

theorem finSum_mul_left : {N : Nat} → (c : Int) → (f : Fin N → Int) →
    finSum (fun i => c * f i) = c * finSum f
  | 0, c, _ => by simp [finSum]
  | N + 1, c, f => by
      simp only [finSum]
      have ih := finSum_mul_left c (fun i : Fin N => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      rw [ih, ← Int.mul_add]

theorem finSum_mul_right : {N : Nat} → (f : Fin N → Int) → (c : Int) →
    finSum (fun i => f i * c) = finSum f * c
  | 0, _, c => by simp [finSum]
  | N + 1, f, c => by
      simp only [finSum]
      have ih := finSum_mul_right (fun i : Fin N => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) c
      rw [ih, ← Int.add_mul]

theorem finSum_const_one : (T : Nat) →
    finSum (fun _ : Fin T => (1 : Int)) = (T : Int)
  | 0 => by simp [finSum]
  | T + 1 => by
      simp only [finSum]
      have ih := finSum_const_one T
      omega

theorem finSum_const_zero : (N : Nat) →
    finSum (fun _ : Fin N => (0 : Int)) = 0
  | 0 => by simp [finSum]
  | N + 1 => by
      simp only [finSum]
      have ih := finSum_const_zero N
      omega

theorem finSum_nonneg : {N : Nat} → (f : Fin N → Int) →
    (∀ i : Fin N, 0 ≤ f i) → 0 ≤ finSum f
  | 0, _, _ => by simp [finSum]
  | N + 1, f, hf => by
      simp only [finSum]
      have h0 : 0 ≤ f ⟨0, Nat.zero_lt_succ N⟩ := hf ⟨0, Nat.zero_lt_succ N⟩
      have htail : 0 ≤ finSum (fun i : Fin N => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) :=
        finSum_nonneg _ (fun i => hf ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      omega

theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have hneg : 0 ≤ -x := by omega
    have hsq : (-x) * (-x) = x * x := by
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    rw [← hsq]
    exact Int.mul_nonneg hneg hneg

theorem weighted_sq_sub_expand (w a b : Int) :
    w * ((a - b) * (a - b)) + 2 * a * (w * b) = w * (a * a) + w * (b * b) := by
  have h1 : (a - b) * (a - b) = a * a - a * b - (a * b - b * b) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm b a]
  have h2 : w * ((a - b) * (a - b)) =
      w * (a * a) - w * (a * b) - (w * (a * b) - w * (b * b)) := by
    rw [h1, Int.mul_sub, Int.mul_sub, Int.mul_sub]
  have h3 : 2 * a * (w * b) = w * (a * b) + w * (a * b) := by
    have ha : a * (w * b) = w * (a * b) := by
      rw [← Int.mul_assoc, Int.mul_comm a w, Int.mul_assoc]
    have htwo : (2 : Int) * a * (w * b) = 2 * (a * (w * b)) := Int.mul_assoc 2 a (w * b)
    rw [htwo, ha]
    omega
  omega

theorem posterior_centered_residual_weighted_sum_zero {M : Nat}
    (w u : Fin M → Int) :
    let W := finSum w
    let U := finSum (fun i => w i * u i)
    finSum (fun i => w i * (W * u i - U)) = 0 := by
  intro W U
  have h_pt : (fun i : Fin M => w i * (W * u i - U)) =
      (fun i : Fin M => W * (w i * u i) - w i * U) := by
    funext i
    rw [Int.mul_sub]
    have hm : w i * (W * u i) = W * (w i * u i) := by
      rw [← Int.mul_assoc, Int.mul_comm (w i) W, Int.mul_assoc]
    rw [hm]
  rw [h_pt, finSum_sub, finSum_mul_left, finSum_mul_right]
  change W * U - W * U = 0
  omega

/-- Master `Fin M` Conditional-to-Marginal Flow-Matching & Tweedie Projection Identity. -/
theorem flow_matching_conditional_to_marginal_pythagorean_identity {M : Nat}
    (w u : Fin M → Int) (vHat : Int) :
    let W := finSum w
    let U := finSum (fun i => w i * u i)
    finSum (fun i => w i * ((W * vHat - W * u i) * (W * vHat - W * u i))) =
      W * ((W * vHat - U) * (W * vHat - U)) +
      finSum (fun i => w i * ((W * u i - U) * (W * u i - U))) := by
  intro W U
  let A : Int := W * vHat - U
  have h_diff : ∀ i : Fin M, W * vHat - W * u i = A - (W * u i - U) := by
    intro i; dsimp [A]; omega
  have h_lhs :
      finSum (fun i => w i * ((W * vHat - W * u i) * (W * vHat - W * u i))) +
      finSum (fun i => 2 * A * (w i * (W * u i - U))) =
      finSum (fun i => w i * (A * A)) +
      finSum (fun i => w i * ((W * u i - U) * (W * u i - U))) := by
    rw [← finSum_add, ← finSum_add]
    have h_fn :
        (fun i : Fin M =>
          w i * ((W * vHat - W * u i) * (W * vHat - W * u i)) +
          2 * A * (w i * (W * u i - U))) =
        (fun i : Fin M =>
          w i * (A * A) + w i * ((W * u i - U) * (W * u i - U))) := by
      funext i
      rw [h_diff i]
      exact weighted_sq_sub_expand (w i) A (W * u i - U)
    rw [h_fn]
  have h_zero : finSum (fun i => 2 * A * (w i * (W * u i - U))) = 0 := by
    rw [finSum_mul_left]
    have hz : finSum (fun i => w i * (W * u i - U)) = 0 :=
      posterior_centered_residual_weighted_sum_zero w u
    rw [hz]
    simp
  have h_constA : finSum (fun i => w i * (A * A)) = W * (A * A) :=
    finSum_mul_right w (A * A)
  dsimp [A] at h_lhs h_zero h_constA
  omega

/-- Universal `Fin T` Benamou–Brenier Dynamic Transport Straightening Identity. -/
theorem benamou_brenier_temporal_straightening_identity {T : Nat}
    (v : Fin T → Int) :
    let T_int : Int := (T : Int)
    let D : Int := finSum v
    (T_int * T_int) * finSum (fun t => v t * v t) =
      T_int * (D * D) + finSum (fun t => (T_int * v t - D) * (T_int * v t - D)) := by
  intro T_int D
  have h_spec :=
    flow_matching_conditional_to_marginal_pythagorean_identity
      (fun _ : Fin T => (1 : Int)) v 0
  dsimp at h_spec
  have hW : finSum (fun _ : Fin T => (1 : Int)) = T_int := finSum_const_one T
  have hU : finSum (fun t : Fin T => (1 : Int) * v t) = D := by
    have h1 : (fun t : Fin T => (1 : Int) * v t) = v := by funext t; simp
    rw [h1]
  rw [hW, hU] at h_spec
  have hL :
      finSum (fun t : Fin T => (1 : Int) * ((T_int * 0 - T_int * v t) * (T_int * 0 - T_int * v t))) =
      (T_int * T_int) * finSum (fun t : Fin T => v t * v t) := by
    have hpt :
        (fun t : Fin T => (1 : Int) * ((T_int * 0 - T_int * v t) * (T_int * 0 - T_int * v t))) =
        (fun t : Fin T => (T_int * T_int) * (v t * v t)) := by
      funext t
      have hz : T_int * 0 - T_int * v t = -(T_int * v t) := by omega
      rw [hz, Int.one_mul, Int.neg_mul, Int.mul_neg, Int.neg_neg]
      rw [← Int.mul_assoc, Int.mul_assoc T_int (v t) T_int, Int.mul_comm (v t) T_int,
          ← Int.mul_assoc, Int.mul_assoc]
    rw [hpt, finSum_mul_left]
  have hR1 : (T_int * 0 - D) * (T_int * 0 - D) = D * D := by
    have hz : T_int * 0 - D = -D := by omega
    rw [hz, Int.neg_mul, Int.mul_neg, Int.neg_neg]
  have hR2 :
      finSum (fun t : Fin T => (1 : Int) * ((T_int * v t - D) * (T_int * v t - D))) =
      finSum (fun t : Fin T => (T_int * v t - D) * (T_int * v t - D)) := by
    have hpt :
        (fun t : Fin T => (1 : Int) * ((T_int * v t - D) * (T_int * v t - D))) =
        (fun t : Fin T => (T_int * v t - D) * (T_int * v t - D)) := by
      funext t; simp
    rw [hpt]
  rw [hL, hR1, hR2] at h_spec
  exact h_spec

/-- Master Positive + Premise-Failure Certificate (`Suite #637`):
    1. Independent-coupling anti-diagonal crossing (`t = 4/10`), `4 E_ind = 68` (`E = 17`), and `NFE = 1`
       Euler midpoint collapse onto empty hole `+2` (`W_2² = 9 > 0`).
    2. Monge / Rectified OT `3.4×` kinetic energy reduction (`68 → 20`, i.e. `17 → 5`) and `NFE = 1`
       exact landing on `{-1, +5}` (`W_2² = 0`).
    3. Curved `(0, 0, 4, 4)` vs. straight `(2, 2, 2, 2)` Benamou–Brenier action (`32 > 16`).
    4. Nonzero divergence `v(x) = -2x` breaks uncompensated `CNF` volume (`20 ≠ 40`). -/
theorem tweedie_rectified_flow_and_benamou_brenier_master_bridge :
    ((-2 : Int) * 10 + 4 * (5 - (-2)) = 8 ∧ (2 : Int) * 10 + 4 * (-1 - 2) = 8) ∧
    (let v0_neg2 := ((5 - (-2)) + (-1 - (-2))) / 2
     let v0_pos2 := ((5 - 2) + (-1 - 2)) / 2
     (-2 + v0_neg2 = 2) ∧ (2 + v0_pos2 = 2) ∧
     ((2 - (-1)) * (2 - (-1)) + (2 - 5) * (2 - 5)) / 2 = 9) ∧
    (let fourE_ind := (5 - (-2)) * (5 - (-2)) + (-1 - (-2)) * (-1 - (-2)) +
                      (5 - 2) * (5 - 2) + (-1 - 2) * (-1 - 2)
     let fourE_ot  := 2 * ((-1 - (-2)) * (-1 - (-2)) + (5 - 2) * (5 - 2))
     fourE_ind = 68 ∧ fourE_ot = 20 ∧ fourE_ind - fourE_ot = 2 * (2 - (-2)) * (5 - (-1)) ∧
     (-2 + (-1 - (-2)) = -1) ∧ (2 + (5 - 2) = 5)) ∧
    ((0 * 0 + 0 * 0 + 4 * 4 + 4 * 4 = 32) ∧ (2 * 2 + 2 * 2 + 2 * 2 + 2 * 2 = 16)) ∧
    ((4 * 10 - 2 * 10) - (4 * 0 - 2 * 0) ≠ 4 * (10 - 0)) := by
  decide

end CommonGround.Verification.TheoremAtlasTweedieScoreProjectionRectifiedFlowAndBenamouBrenierBridge
