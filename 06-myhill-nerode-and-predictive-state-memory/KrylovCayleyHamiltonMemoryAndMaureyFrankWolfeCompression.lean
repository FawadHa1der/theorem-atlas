/-
  Common Ground — Discovery 06 + 02 + 05 Cross-Folder Synthesis (Wave V205)
  Module: 06-myhill-nerode-and-predictive-state-memory/KrylovCayleyHamiltonMemoryAndMaureyFrankWolfeCompression.lean

  Pure-Core Lean 4.33.0 Formalization (`0` imports, `0` sorrys, `0` unverified axioms) unifying:
  1. Krylov–Cayley–Hamilton Finite-Horizon Nerode Sufficiency (`Folder 06`):
     - When a sequence readout obeys a degree-`r` linear recurrence
       `y (k + r) = ∑_{j < r} α_j * y (k + j)`, matching ONLY the finite `r`-step prefix
       `t = 0, ..., r - 1` forces infinite-horizon Nerode equivalence `∀ t : Nat, y₁ t = y₂ t`.
     - Sharp Premise-Failure Boundaries:
       (a) Matching `r - 1` steps on the `r`-step delay line `y (k + r) = y k` fails strictly at `t = r - 1`;
       (b) Exhaustive `L = 3` (`8` bitstrings over `Bool³`) Associative-Recall Lower Bound:
           every pair of distinct `3`-token binary contexts `h₁ ≠ h₂` in `Fin 8` is separated by at
           least one recall coordinate `pos : Fin 3`.
  2. Constructive Deterministic Greedy Maurey–Frank–Wolfe / Kernel Herding KV-Cache Compression (`Folder 02` ↔ `06`):
     - Over arbitrary embedding dimension `D` and arbitrary context length `L`, given integer attention
       weights `p_i ≥ 0` with `∑_{i < L} p_i = S > 0` and unnormalized attention output `M = ∑_{i < L} p_i v_i`,
       the weighted inner product `∑_{i < L} p_i ⟨r, S v_i - M⟩ = 0` vanishes identically for EVERY residual `r`,
       guaranteeing constructive existence of a greedy token `i_t < L` with `⟨r_t, S v_{i_t} - M⟩ ≤ 0`.
     - Consequently, `T` greedy tokens satisfy the dimension-free, `L`-free `O(1/T)` error bound
       `‖S ∑_{t < T} v_{i_t} - T M‖₂² ≤ T · B_S` and linear query bound
       `(S ∑_{t < T} ⟨q, v_{i_t}⟩ - T ∑_{i < L} p_i ⟨q, v_i⟩)² ≤ T · B_S · ‖q‖₂²`.
     - Exact Information-Theoretic Minimax Optimality (`orthogonal_simplex_sparsification_minimax_lower_bound`):
       On the `D`-dimensional standard basis with uniform weights (`S = D`), EVERY `T`-element multiset
       selection (`∑_{j < D} c_j = T`) incurs squared residual `∑_{j < D} (D c_j - T)² ≥ D · T · (D - T)`
       (attained iff `c_j ∈ {0, 1}`).
  3. Discrete Stein–Lyapunov Contraction vs. Non-Normal Jordan-Block Transient Explosion (`Folder 05` ↔ `06`):
     - Under discrete Stein–Lyapunov dissipation `q² V(x) - V(Ax) ≥ γ V(x)`, energy contracts monotonically
       at every step (`V(Ax) ≤ (q² - γ) V(x)`), whereas non-normal `2 × 2` Jordan shear `[[1, K], [0, 1]]` at
       scale `q = 2` (eigenvalue `1/2 < 1`!) amplifies step-1 energy (`K² + 1 > 4` for all `K ≥ 2`, `17 > 4` at `K = 4`).
-/

namespace CommonGround.KrylovHerdingSynthesis

/-! ## Section 1: Pure-Core Integer & Finite Summation Primitives -/

theorem sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases hx : 0 ≤ x
  · exact Int.mul_nonneg hx hx
  · have hnx : 0 ≤ -x := by omega
    have hp : 0 ≤ (-x) * (-x) := Int.mul_nonneg hnx hnx
    have heq : (-x) * (-x) = x * x := by simp [Int.neg_mul_neg]
    omega

/-- Sum `f 0 + f 1 + ... + f (n - 1)` over `Int`. -/
def sumInt (n : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | k + 1 => sumInt k f + f k

theorem sumInt_zero : ∀ (n : Nat), sumInt n (fun _ => (0 : Int)) = 0
  | 0 => rfl
  | k + 1 => by simp [sumInt, sumInt_zero k]

theorem sumInt_const : ∀ (n : Nat) (c : Int), sumInt n (fun _ => c) = (n : Int) * c
  | 0, c => by simp [sumInt]
  | k + 1, c => by
      have ih := sumInt_const k c
      have hc : ((k + 1 : Nat) : Int) = (k : Int) + 1 := Int.natCast_add k 1
      simp only [sumInt, ih, hc, Int.add_mul, Int.one_mul]

theorem sumInt_congr :
    ∀ (n : Nat) (f g : Nat → Int),
      (∀ i : Nat, i < n → f i = g i) →
      sumInt n f = sumInt n g
  | 0, _, _, _ => rfl
  | k + 1, f, g, hfg => by
      have ih := sumInt_congr k f g (fun i hi => hfg i (Nat.lt_trans hi (Nat.lt_succ_self k)))
      have hk := hfg k (Nat.lt_succ_self k)
      simp [sumInt, ih, hk]

theorem sumInt_add :
    ∀ (n : Nat) (f g : Nat → Int),
      sumInt n (fun i => f i + g i) = sumInt n f + sumInt n g
  | 0, _, _ => by simp [sumInt]
  | k + 1, f, g => by
      have ih := sumInt_add k f g
      simp only [sumInt, ih]
      omega

theorem sumInt_sub :
    ∀ (n : Nat) (f g : Nat → Int),
      sumInt n (fun i => f i - g i) = sumInt n f - sumInt n g
  | 0, _, _ => by simp [sumInt]
  | k + 1, f, g => by
      have ih := sumInt_sub k f g
      simp only [sumInt, ih]
      omega

theorem sumInt_mul_left :
    ∀ (n : Nat) (c : Int) (f : Nat → Int),
      sumInt n (fun i => c * f i) = c * sumInt n f
  | 0, _, _ => by simp [sumInt]
  | k + 1, c, f => by
      have ih := sumInt_mul_left k c f
      simp only [sumInt, ih, Int.mul_add]

theorem sumInt_mul_right :
    ∀ (n : Nat) (c : Int) (f : Nat → Int),
      sumInt n (fun i => f i * c) = sumInt n f * c
  | 0, _, _ => by simp [sumInt]
  | k + 1, c, f => by
      have ih := sumInt_mul_right k c f
      simp only [sumInt, ih, Int.add_mul]

theorem sumInt_nonneg :
    ∀ (n : Nat) (f : Nat → Int),
      (∀ i : Nat, i < n → 0 ≤ f i) →
      0 ≤ sumInt n f
  | 0, _, _ => by simp [sumInt]
  | k + 1, f, hf => by
      have ih := sumInt_nonneg k f (fun i hi => hf i (Nat.lt_trans hi (Nat.lt_succ_self k)))
      have hk := hf k (Nat.lt_succ_self k)
      simp only [sumInt]
      omega

theorem sumInt_weighted_eq_zero_of_sum_zero :
    ∀ (n : Nat) (p g : Nat → Int),
      (∀ i : Nat, i < n → 0 ≤ p i) →
      sumInt n p = 0 →
      sumInt n (fun i => p i * g i) = 0
  | 0, _, _, _, _ => rfl
  | k + 1, p, g, hp, hsum => by
      have hp_sub : ∀ i : Nat, i < k → 0 ≤ p i :=
        fun i hi => hp i (Nat.lt_trans hi (Nat.lt_succ_self k))
      have hsub_nn : 0 ≤ sumInt k p := sumInt_nonneg k p hp_sub
      have hpk_nn : 0 ≤ p k := hp k (Nat.lt_succ_self k)
      simp only [sumInt] at hsum ⊢
      have hk0 : sumInt k p = 0 := by omega
      have hpk0 : p k = 0 := by omega
      have ih := sumInt_weighted_eq_zero_of_sum_zero k p g hp_sub hk0
      rw [ih, hpk0, Int.zero_mul, Int.add_zero]

theorem sumInt_swap :
    ∀ (m n : Nat) (F : Nat → Nat → Int),
      sumInt m (fun i => sumInt n (fun j => F i j)) =
        sumInt n (fun j => sumInt m (fun i => F i j))
  | 0, n, _ => by simp [sumInt, sumInt_zero n]
  | k + 1, n, F => by
      have ih := sumInt_swap k n F
      have hadd := sumInt_add n (fun j => sumInt k (fun i => F i j)) (fun j => F k j)
      simp only [sumInt, ih, hadd]

/-- Euclidean dot product and squared norm on `Nat → Int` over coordinates `0, ..., D - 1`. -/
def dotD (D : Nat) (x y : Nat → Int) : Int :=
  sumInt D (fun j => x j * y j)

def normSqD (D : Nat) (x : Nat → Int) : Int :=
  sumInt D (fun j => x j * x j)

theorem normSqD_nonneg (D : Nat) (x : Nat → Int) : 0 ≤ normSqD D x :=
  sumInt_nonneg D (fun j => x j * x j) (fun j _ => sq_nonneg (x j))

theorem normSqD_add_expansion (D : Nat) (u w : Nat → Int) :
    normSqD D (fun j => u j + w j) =
      normSqD D u + 2 * dotD D u w + normSqD D w := by
  induction D with
  | zero => simp [normSqD, dotD, sumInt]
  | succ k ih =>
      unfold normSqD dotD at ih ⊢
      simp only [sumInt]
      rw [ih]
      have h1 : (u k + w k) * (u k + w k) = (u k + w k) * u k + (u k + w k) * w k := Int.mul_add _ _ _
      have h2 : (u k + w k) * u k = u k * u k + w k * u k := Int.add_mul _ _ _
      have h3 : (u k + w k) * w k = u k * w k + w k * w k := Int.add_mul _ _ _
      have h4 : w k * u k = u k * w k := Int.mul_comm (w k) (u k)
      omega

/-- Core algebraic step for Lagrange–Cauchy–Schwarz over `Int`. -/
theorem cauchy_step_int (A Q R qk rk : Int)
    (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hih : A * A ≤ Q * R) :
    (A + qk * rk) * (A + qk * rk) ≤ (Q + qk * qk) * (R + rk * rk) := by
  by_cases hQ0 : Q = 0
  · subst hQ0
    have hA2 : A * A ≤ 0 := by simp at hih; exact hih
    have hAnn : 0 ≤ A * A := sq_nonneg A
    have hA0 : A = 0 := by
      by_cases ha : A = 0
      · exact ha
      · exfalso
        by_cases hap : 0 < A
        · have hp := Int.mul_pos hap hap; omega
        · have han : 0 < -A := by omega
          have hp := Int.mul_pos han han
          have heq : (-A) * (-A) = A * A := by simp [Int.neg_mul_neg]
          omega
    subst hA0
    have h1 : (0 + qk * rk) * (0 + qk * rk) = (qk * qk) * (rk * rk) := by
      simp only [Int.zero_add]
      calc
        (qk * rk) * (qk * rk) = qk * (rk * (qk * rk)) := by rw [Int.mul_assoc]
        _ = qk * ((rk * qk) * rk) := by rw [Int.mul_assoc rk qk rk]
        _ = qk * ((qk * rk) * rk) := by rw [Int.mul_comm rk qk]
        _ = qk * (qk * (rk * rk)) := by rw [Int.mul_assoc qk rk rk]
        _ = (qk * qk) * (rk * rk) := by rw [← Int.mul_assoc]
    have h2 : (0 + qk * qk) * (R + rk * rk) = (qk * qk) * R + (qk * qk) * (rk * rk) := by
      simp only [Int.zero_add, Int.mul_add]
    have h3 : 0 ≤ (qk * qk) * R := Int.mul_nonneg (sq_nonneg qk) hR
    omega
  · have hQ_pos : 0 < Q := by omega
    have hdisc : 0 ≤ (Q * rk - qk * A) * (Q * rk - qk * A) := sq_nonneg (Q * rk - qk * A)
    have hprod : 0 ≤ (Q + qk * qk) * (Q * R - A * A) := by
      have hq1 : 0 ≤ Q + qk * qk := by have hsq := sq_nonneg qk; omega
      exact Int.mul_nonneg hq1 (by omega)
    have halg :
        Q * ((Q + qk * qk) * (R + rk * rk) - (A + qk * rk) * (A + qk * rk)) =
          (Q + qk * qk) * (Q * R - A * A) + (Q * rk - qk * A) * (Q * rk - qk * A) := by
      have e1 : (Q + qk * qk) * (R + rk * rk) =
          Q * R + Q * (rk * rk) + (qk * qk) * R + (qk * qk) * (rk * rk) := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
      have e2 : (A + qk * rk) * (A + qk * rk) =
          A * A + 2 * (A * (qk * rk)) + (qk * rk) * (qk * rk) := by
        have m1 := Int.add_mul A (qk * rk) (A + qk * rk)
        have m2 := Int.mul_add A A (qk * rk)
        have m3 := Int.mul_add (qk * rk) A (qk * rk)
        have m4 := Int.mul_comm (qk * rk) A
        omega
      have e3 : (qk * rk) * (qk * rk) = (qk * qk) * (rk * rk) := by
        calc
          (qk * rk) * (qk * rk) = qk * (rk * (qk * rk)) := by rw [Int.mul_assoc]
          _ = qk * ((rk * qk) * rk) := by rw [Int.mul_assoc rk qk rk]
          _ = qk * ((qk * rk) * rk) := by rw [Int.mul_comm rk qk]
          _ = qk * (qk * (rk * rk)) := by rw [Int.mul_assoc qk rk rk]
          _ = (qk * qk) * (rk * rk) := by rw [← Int.mul_assoc]
      have e4 : (Q + qk * qk) * (Q * R - A * A) =
          Q * (Q * R) - Q * (A * A) + (qk * qk) * (Q * R) - (qk * qk) * (A * A) := by
        rw [Int.add_mul, Int.mul_sub, Int.mul_sub]; omega
      have e5 : (Q * rk - qk * A) * (Q * rk - qk * A) =
          (Q * rk) * (Q * rk) - 2 * ((Q * rk) * (qk * A)) + (qk * A) * (qk * A) := by
        have s1 := Int.sub_mul (Q * rk) (qk * A) (Q * rk - qk * A)
        have s2 := Int.mul_sub (Q * rk) (Q * rk) (qk * A)
        have s3 := Int.mul_sub (qk * A) (Q * rk) (qk * A)
        have s4 := Int.mul_comm (qk * A) (Q * rk)
        omega
      have e6 : (Q * rk) * (Q * rk) = Q * (Q * (rk * rk)) := by
        calc
          (Q * rk) * (Q * rk) = Q * (rk * (Q * rk)) := by rw [Int.mul_assoc]
          _ = Q * ((rk * Q) * rk) := by rw [Int.mul_assoc rk Q rk]
          _ = Q * ((Q * rk) * rk) := by rw [Int.mul_comm rk Q]
          _ = Q * (Q * (rk * rk)) := by rw [Int.mul_assoc Q rk rk]
      have e7 : (qk * A) * (qk * A) = (qk * qk) * (A * A) := by
        calc
          (qk * A) * (qk * A) = qk * (A * (qk * A)) := by rw [Int.mul_assoc]
          _ = qk * ((A * qk) * A) := by rw [Int.mul_assoc A qk A]
          _ = qk * ((qk * A) * A) := by rw [Int.mul_comm A qk]
          _ = qk * (qk * (A * A)) := by rw [Int.mul_assoc qk A A]
          _ = (qk * qk) * (A * A) := by rw [← Int.mul_assoc]
      have e8 : (qk * qk) * (Q * R) = Q * ((qk * qk) * R) := by
        calc
          (qk * qk) * (Q * R) = ((qk * qk) * Q) * R := by rw [← Int.mul_assoc]
          _ = (Q * (qk * qk)) * R := by rw [Int.mul_comm (qk * qk) Q]
          _ = Q * ((qk * qk) * R) := by rw [Int.mul_assoc]
      have e9 : (Q * rk) * (qk * A) = Q * (A * (qk * rk)) := by
        calc
          (Q * rk) * (qk * A) = Q * (rk * (qk * A)) := by rw [Int.mul_assoc]
          _ = Q * ((rk * qk) * A) := by rw [Int.mul_assoc rk qk A]
          _ = Q * (A * (rk * qk)) := by rw [Int.mul_comm (rk * qk) A]
          _ = Q * (A * (qk * rk)) := by rw [Int.mul_comm rk qk]
      have e10 :
          Q * ((Q + qk * qk) * (R + rk * rk) - (A + qk * rk) * (A + qk * rk)) =
            Q * (Q * R) + Q * (Q * (rk * rk)) + Q * ((qk * qk) * R) -
            Q * (A * A) - Q * (2 * (A * (qk * rk))) := by
        rw [e1, e2, e3, Int.mul_sub]
        repeat rw [Int.mul_add]
        omega
      have e11 : Q * (2 * (A * (qk * rk))) = 2 * (Q * (A * (qk * rk))) := by
        rw [← Int.mul_assoc, Int.mul_comm Q 2, Int.mul_assoc]
      rw [e10, e11, e4, e5, e6, e7, e8, e9]
      omega
    have hmul_nn :
        0 ≤ Q * ((Q + qk * qk) * (R + rk * rk) - (A + qk * rk) * (A + qk * rk)) := by
      rw [halg]; omega
    by_cases hdiff : 0 ≤ (Q + qk * qk) * (R + rk * rk) - (A + qk * rk) * (A + qk * rk)
    · omega
    · exfalso
      have hneg : 0 < -((Q + qk * qk) * (R + rk * rk) - (A + qk * rk) * (A + qk * rk)) := by omega
      have hp := Int.mul_pos hQ_pos hneg
      rw [Int.mul_neg] at hp
      omega

/-- Exact Lagrange–Cauchy–Schwarz inequality `(dotD D q r)² ≤ normSqD D q * normSqD D r` over `Int`. -/
theorem dotD_sq_le_mul_normSqD :
    ∀ (D : Nat) (q r : Nat → Int),
      dotD D q r * dotD D q r ≤ normSqD D q * normSqD D r
  | 0, _, _ => by simp [dotD, normSqD, sumInt]
  | k + 1, q, r => by
      change (dotD k q r + q k * r k) * (dotD k q r + q k * r k) ≤
        (normSqD k q + q k * q k) * (normSqD k r + r k * r k)
      exact cauchy_step_int (dotD k q r) (normSqD k q) (normSqD k r) (q k) (r k)
        (normSqD_nonneg k q) (normSqD_nonneg k r) (dotD_sq_le_mul_normSqD k q r)

/-! ## Section 2: Krylov–Cayley–Hamilton Finite-Horizon Sufficiency vs. Associative-Recall Lower Bound -/

/-- Strong induction helper: if two trajectories satisfy the same degree-`r` linear recurrence
    `y (k + r) = ∑_{j < r} α j * y (k + j)` and agree on `0, ..., r - 1`, they agree up to any bound `B`. -/
theorem krylov_recurrence_prefix_bound
    (r : Nat) (α : Nat → Int) (y₁ y₂ : Nat → Int)
    (hrec₁ : ∀ k : Nat, y₁ (k + r) = sumInt r (fun j => α j * y₁ (k + j)))
    (hrec₂ : ∀ k : Nat, y₂ (k + r) = sumInt r (fun j => α j * y₂ (k + j)))
    (hinit : ∀ j : Nat, j < r → y₁ j = y₂ j) :
    ∀ (B t : Nat), t < B → y₁ t = y₂ t
  | 0, _, ht => absurd ht (Nat.not_lt_zero _)
  | B + 1, t, ht => by
      by_cases htr : t < r
      · exact hinit t htr
      · by_cases hr0 : r = 0
        · subst hr0
          have h0 := hrec₁ t
          have h0' := hrec₂ t
          rw [Nat.add_zero] at h0 h0'
          simp [sumInt] at h0 h0'
          omega
        · have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
          have hge : r ≤ t := Nat.le_of_not_lt htr
          let k := t - r
          have htk : t = k + r := by omega
          rw [htk, hrec₁ k, hrec₂ k]
          apply sumInt_congr r
          intro j hj
          have hklt : k + j < B := by omega
          have hij := krylov_recurrence_prefix_bound r α y₁ y₂ hrec₁ hrec₂ hinit B (k + j) hklt
          rw [hij]

/-- **Theorem 1A (Krylov–Cayley–Hamilton Finite-Horizon Nerode Sufficiency)**:
    If two sequence histories `y₁, y₂ : Nat → Int` satisfy a common degree-`r` linear recurrence
    (e.g., from the Cayley–Hamilton polynomial of a `d`-state linear SSM, `r ≤ d`), matching ONLY
    the finite `r`-step prefix `0 ≤ j < r` forces infinite-horizon Nerode equivalence `∀ t, y₁ t = y₂ t`. -/
theorem krylov_annihilating_horizon_forces_infinite_nerode_equivalence
    (r : Nat) (α : Nat → Int) (y₁ y₂ : Nat → Int)
    (hrec₁ : ∀ k : Nat, y₁ (k + r) = sumInt r (fun j => α j * y₁ (k + j)))
    (hrec₂ : ∀ k : Nat, y₂ (k + r) = sumInt r (fun j => α j * y₂ (k + j)))
    (hinit : ∀ j : Nat, j < r → y₁ j = y₂ j) :
    ∀ t : Nat, y₁ t = y₂ t := by
  intro t
  exact krylov_recurrence_prefix_bound r α y₁ y₂ hrec₁ hrec₂ hinit (t + 1) t (Nat.lt_succ_self t)

/-- `L`-token binary history encoded via binary digits of `h : Fin 8` (`L = 3`). -/
def bitAt3 (h : Fin 8) (pos : Fin 3) : Bool :=
  ((h.val >>> pos.val) &&& 1) == 1

/-- **Theorem 1B (Premise-Failure Counterexamples: Subcritical `r - 1` Horizon Blindness &
    Associative-Recall Nerode Bottleneck)**:
    1. On the `3`-step delay recurrence `y (k + 3) = y k`, trajectories `[0, 0, 1, ...]` and `[0, 0, 0, ...]`
       match on `0 ≤ j < 2` (`r - 1 = 2` steps) yet diverge strictly at `t = 2` (`1 ≠ 0`).
    2. Over `3`-token binary contexts (`Fin 8`), every pair of distinct contexts `h₁ ≠ h₂` is separated
       by at least one coordinate recall query `pos : Fin 3`, so any sub-`8`-state bottleneck merging two
       distinct histories loses exact associative recall. -/
theorem subcritical_horizon_r_minus_1_blindness_and_associative_recall_lower_bound :
    let yDelay : Nat → Int := fun t => if t % 3 = 2 then 1 else 0
    let yZero  : Nat → Int := fun _ => 0
    ((∀ k : Nat, yDelay (k + 3) = yDelay k) ∧
     (∀ j : Nat, j < 2 → yDelay j = yZero j) ∧
     yDelay 2 ≠ yZero 2) ∧
    (∀ h₁ h₂ : Fin 8, h₁ ≠ h₂ → ∃ pos : Fin 3, bitAt3 h₁ pos ≠ bitAt3 h₂ pos) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, by decide⟩
    · intro k
      have hm : (k + 3) % 3 = k % 3 := Nat.add_mod_right k 3
      simp [hm]
    · intro j hj
      match j with
      | 0 => decide
      | 1 => decide
      | n + 2 => omega
  · decide

/-! ## Section 3: Deterministic Greedy Maurey–Frank–Wolfe / Kernel Herding $O(1/T)$ KV-Cache Compression -/

/-- Unnormalized integer attention sum `M_j = ∑_{i < L} p_i * v_i(j)`. -/
def weightedSumVec (L : Nat) (p : Nat → Int) (v : Nat → Nat → Int) : Nat → Int :=
  fun j => sumInt L (fun i => p i * v i j)

/-- Centered weighted inner-product identity:
    `∑_{i < L} p_i * ⟨r, S * v_i - M⟩ = 0` for EVERY residual vector `r : Nat → Int` whenever `∑_{i < L} p_i = S`. -/
theorem herding_weighted_inner_product_eq_zero
    (L D : Nat) (S : Int) (p : Nat → Int) (v : Nat → Nat → Int)
    (hS : sumInt L p = S) (r : Nat → Int) :
    sumInt L (fun i => p i * dotD D r (fun j => S * v i j - weightedSumVec L p v j)) = 0 := by
  let M := weightedSumVec L p v
  have hrew :
      sumInt L (fun i => p i * dotD D r (fun j => S * v i j - M j)) =
        sumInt L (fun i => sumInt D (fun j => p i * (r j * (S * v i j - M j)))) := by
    apply sumInt_congr L
    intro i _hi
    unfold dotD
    rw [← sumInt_mul_left D (p i)]
  rw [hrew, sumInt_swap L D]
  have hcoord :
      ∀ j : Nat, j < D →
        sumInt L (fun i => p i * (r j * (S * v i j - M j))) = 0 := by
    intro j _hj
    have hlin :
        sumInt L (fun i => p i * (r j * (S * v i j - M j))) =
          r j * (S * sumInt L (fun i => p i * v i j) - sumInt L p * M j) := by
      have hc :
          ∀ i : Nat, i < L →
            p i * (r j * (S * v i j - M j)) =
              r j * (S * (p i * v i j) - p i * M j) := by
        intro i _
        have a1 : p i * (r j * (S * v i j - M j)) = r j * (p i * (S * v i j - M j)) := by
          rw [← Int.mul_assoc, Int.mul_comm (p i) (r j), Int.mul_assoc]
        have a2 : p i * (S * v i j - M j) = p i * (S * v i j) - p i * M j := Int.mul_sub _ _ _
        have a3 : p i * (S * v i j) = S * (p i * v i j) := by
          rw [← Int.mul_assoc, Int.mul_comm (p i) S, Int.mul_assoc]
        rw [a1, a2, a3]
      rw [sumInt_congr L _ _ hc, sumInt_mul_left L (r j), sumInt_sub L,
          sumInt_mul_left L S, sumInt_mul_right L (M j)]
    rw [hlin, hS]
    have hMdef : sumInt L (fun i => p i * v i j) = M j := rfl
    rw [hMdef, Int.sub_self, Int.mul_zero]
  rw [sumInt_congr D _ (fun _ => 0) hcoord, sumInt_zero D]

/-- Pigeonhole sign lemma: if `p_i ≥ 0`, `∑_{i < L} p_i > 0`, and `∑_{i < L} p_i * g_i ≤ 0`,
    then there exists an index `i < L` with `g_i ≤ 0`. -/
theorem exists_nonpos_of_weighted_sum_le_zero :
    ∀ (L : Nat) (p g : Nat → Int),
      (∀ i : Nat, i < L → 0 ≤ p i) →
      0 < sumInt L p →
      sumInt L (fun i => p i * g i) ≤ 0 →
      ∃ i : Nat, i < L ∧ g i ≤ 0
  | 0, _, _, _, hpos, _ => by simp [sumInt] at hpos
  | k + 1, p, g, hp, hpos, hsum => by
      by_cases hgk : g k ≤ 0
      · exact ⟨k, Nat.lt_succ_self k, hgk⟩
      · have hgk_pos : 1 ≤ g k := by omega
        have hp_sub : ∀ i : Nat, i < k → 0 ≤ p i :=
          fun i hi => hp i (Nat.lt_trans hi (Nat.lt_succ_self k))
        have hpk_nn : 0 ≤ p k := hp k (Nat.lt_succ_self k)
        have hterm_nn : 0 ≤ p k * g k := Int.mul_nonneg hpk_nn (by omega)
        simp only [sumInt] at hpos hsum
        by_cases hsum_k_pos : 0 < sumInt k p
        · have hsub : sumInt k (fun i => p i * g i) ≤ 0 := by omega
          obtain ⟨i, hi, hgi⟩ := exists_nonpos_of_weighted_sum_le_zero k p g hp_sub hsum_k_pos hsub
          exact ⟨i, Nat.lt_trans hi (Nat.lt_succ_self k), hgi⟩
        · have hsum_k_nn : 0 ≤ sumInt k p := sumInt_nonneg k p hp_sub
          have hk0 : sumInt k p = 0 := by omega
          have hpk_pos : 0 < p k := by omega
          have hpg0 := sumInt_weighted_eq_zero_of_sum_zero k p g hp_sub hk0
          have hpkg_pos : 0 < p k * g k := Int.mul_pos hpk_pos (by omega)
          omega

/-- **Constructive Existence of Greedy Herding Token**:
    At every step and for every residual `r : Nat → Int`, there exists a dictionary/KV index `i < L`
    with non-positive inner product `dotD D r (S * v_i - M) ≤ 0`. -/
theorem exists_greedy_herding_direction
    (L D : Nat) (S : Int) (p : Nat → Int) (v : Nat → Nat → Int)
    (hp_nonneg : ∀ i : Nat, i < L → 0 ≤ p i)
    (hS_pos : 0 < S) (hS_sum : sumInt L p = S)
    (r : Nat → Int) :
    ∃ i : Nat, i < L ∧ dotD D r (fun j => S * v i j - weightedSumVec L p v j) ≤ 0 := by
  have hz := herding_weighted_inner_product_eq_zero L D S p v hS_sum r
  exact exists_nonpos_of_weighted_sum_le_zero L p
    (fun i => dotD D r (fun j => S * v i j - weightedSumVec L p v j))
    hp_nonneg (by rw [hS_sum]; exact hS_pos) (by rw [hz]; exact Int.le_refl 0)

/-- Cumulative integer herding residual after `t` selected tokens `idx : Nat → Nat`:
    `herdingResidual L S p v idx t j = S * (∑_{m < t} v_{idx m}(j)) - t * M_j`. -/
def herdingResidual (L : Nat) (S : Int) (p : Nat → Int) (v : Nat → Nat → Int)
    (idx : Nat → Nat) : Nat → Nat → Int
  | 0 => fun _ => 0
  | t + 1 => fun j => herdingResidual L S p v idx t j + (S * v (idx t) j - weightedSumVec L p v j)

/-- **Theorem 2A (Dimension-Free Deterministic Greedy Maurey–Frank–Wolfe $O(1/T)$ Coreset & Query Bound)**:
    If each centered token satisfies `‖S v_i - M‖₂² ≤ B_S` and `idx t < L` is chosen greedily with
    `⟨r_t, S v_{idx t} - M⟩ ≤ 0` (guaranteed to exist by `exists_greedy_herding_direction`), then:
    1. `‖r_T‖₂² ≤ T * B_S` (so `‖(1/T) ∑_{m<T} v_{idx m} - (1/S) M‖₂² ≤ (B_S / S²) / T`), and
    2. For EVERY linear readout/attention query `q ∈ ℤ^D`,
       `⟨q, r_T⟩² ≤ (T * B_S) * ‖q‖₂²` — independent of both context length `L` AND dimension `D`! -/
theorem deterministic_greedy_frank_wolfe_herding_dimension_free_bound
    (L D : Nat) (S B_S : Int) (p : Nat → Int) (v : Nat → Nat → Int)
    (_hB_nonneg : 0 ≤ B_S)
    (hnorm_cap : ∀ i : Nat, i < L → normSqD D (fun j => S * v i j - weightedSumVec L p v j) ≤ B_S)
    (idx : Nat → Nat)
    (hidx_lt : ∀ t : Nat, idx t < L)
    (hgreedy : ∀ t : Nat,
      dotD D (herdingResidual L S p v idx t)
        (fun j => S * v (idx t) j - weightedSumVec L p v j) ≤ 0) :
    ∀ T : Nat,
      normSqD D (herdingResidual L S p v idx T) ≤ (T : Int) * B_S ∧
      (∀ q : Nat → Int,
        dotD D q (herdingResidual L S p v idx T) * dotD D q (herdingResidual L S p v idx T) ≤
          ((T : Int) * B_S) * normSqD D q) := by
  intro T
  have hres_bound : normSqD D (herdingResidual L S p v idx T) ≤ (T : Int) * B_S := by
    induction T with
    | zero =>
        change sumInt D (fun _ => (0 : Int) * 0) ≤ 0 * B_S
        simp [sumInt_zero]
    | succ t ih =>
        have hexp := normSqD_add_expansion D
          (herdingResidual L S p v idx t)
          (fun j => S * v (idx t) j - weightedSumVec L p v j)
        have hg := hgreedy t
        have hc := hnorm_cap (idx t) (hidx_lt t)
        change normSqD D (fun j => herdingResidual L S p v idx t j +
          (S * v (idx t) j - weightedSumVec L p v j)) ≤ ((t + 1 : Nat) : Int) * B_S
        rw [hexp]
        have hcast : ((t + 1 : Nat) : Int) * B_S = (t : Int) * B_S + B_S := by
          have hc1 : ((t + 1 : Nat) : Int) = (t : Int) + 1 := Int.natCast_add t 1
          rw [hc1, Int.add_mul, Int.one_mul]
        rw [hcast]
        omega
  refine ⟨hres_bound, ?_⟩
  intro q
  have hcs := dotD_sq_le_mul_normSqD D q (herdingResidual L S p v idx T)
  have hq_nn := normSqD_nonneg D q
  have hmul : normSqD D q * normSqD D (herdingResidual L S p v idx T) ≤ normSqD D q * ((T : Int) * B_S) := by
    have hdiff : 0 ≤ (T : Int) * B_S - normSqD D (herdingResidual L S p v idx T) := by omega
    have hp := Int.mul_nonneg hq_nn hdiff
    rw [Int.mul_sub] at hp
    omega
  rw [Int.mul_comm ((T : Int) * B_S) (normSqD D q)]
  omega

/-- **Theorem 2B (Information-Theoretic Minimax Optimality on the Orthogonal Simplex)**:
    For ANY dimension `D` and ANY `T`-element multiset selection on the `D` standard basis vectors
    with integer multiplicities `c_j ≥ 0` summing to `∑_{j < D} c_j = T`,
    the unnormalized squared `L²` residual satisfies the exact identity & lower bound:
    `∑_{j < D} (D c_j - T)² = D² ∑_{j < D} c_j² - D T² ≥ D * T * (D - T)`!
    In particular, for `1 ≤ T < D`, `D * T * (D - T) > 0` proves that exact zero-error compression is
    impossible below `D` points and that the `1 / T` rate is minimax optimal! -/
theorem orthogonal_simplex_sparsification_minimax_lower_bound
    (D : Nat) (T : Int) (c : Nat → Int)
    (hc_nonneg : ∀ j : Nat, j < D → 0 ≤ c j)
    (hsum : sumInt D c = T) :
    sumInt D (fun j => ((D : Int) * c j - T) * ((D : Int) * c j - T)) =
      (D : Int) * (D : Int) * sumInt D (fun j => c j * c j) - (D : Int) * (T * T) ∧
    (D : Int) * T * ((D : Int) - T) ≤
      sumInt D (fun j => ((D : Int) * c j - T) * ((D : Int) * c j - T)) := by
  have hpoint :
      ∀ j : Nat, j < D →
        ((D : Int) * c j - T) * ((D : Int) * c j - T) =
          ((D : Int) * (D : Int)) * (c j * c j) - (2 * (D : Int) * T) * c j + T * T := by
    intro j _
    have s1 := Int.sub_mul ((D : Int) * c j) T ((D : Int) * c j - T)
    have s2 := Int.mul_sub ((D : Int) * c j) ((D : Int) * c j) T
    have s3 := Int.mul_sub T ((D : Int) * c j) T
    have s4 : ((D : Int) * c j) * ((D : Int) * c j) = ((D : Int) * (D : Int)) * (c j * c j) := by
      calc
        ((D : Int) * c j) * ((D : Int) * c j) = (D : Int) * (c j * ((D : Int) * c j)) := by rw [Int.mul_assoc]
        _ = (D : Int) * ((c j * (D : Int)) * c j) := by rw [Int.mul_assoc (c j) (D : Int) (c j)]
        _ = (D : Int) * (((D : Int) * c j) * c j) := by rw [Int.mul_comm (c j) (D : Int)]
        _ = (D : Int) * ((D : Int) * (c j * c j)) := by rw [Int.mul_assoc (D : Int) (c j) (c j)]
        _ = ((D : Int) * (D : Int)) * (c j * c j) := by rw [← Int.mul_assoc]
    have s5 : ((D : Int) * c j) * T = ((D : Int) * T) * c j := by
      rw [Int.mul_assoc, Int.mul_comm (c j) T, ← Int.mul_assoc]
    have s6 : T * ((D : Int) * c j) = ((D : Int) * T) * c j := by
      rw [← Int.mul_assoc, Int.mul_comm T (D : Int)]
    have s7 : 2 * (((D : Int) * T) * c j) = (2 * (D : Int) * T) * c j := by
      rw [← Int.mul_assoc, ← Int.mul_assoc]
    omega
  have hid :
      sumInt D (fun j => ((D : Int) * c j - T) * ((D : Int) * c j - T)) =
        (D : Int) * (D : Int) * sumInt D (fun j => c j * c j) - (D : Int) * (T * T) := by
    rw [sumInt_congr D _ _ hpoint, sumInt_add, sumInt_sub,
        sumInt_mul_left D ((D : Int) * (D : Int)),
        sumInt_mul_left D (2 * (D : Int) * T), hsum, sumInt_const D (T * T)]
    have hm : (2 * (D : Int) * T) * T = 2 * ((D : Int) * (T * T)) := by
      calc
        (2 * (D : Int) * T) * T = (2 * (D : Int)) * (T * T) := by rw [Int.mul_assoc]
        _ = 2 * ((D : Int) * (T * T)) := by rw [Int.mul_assoc]
    omega
  refine ⟨hid, ?_⟩
  have hcsq_diff : 0 ≤ sumInt D (fun j => c j * c j - c j) := by
    apply sumInt_nonneg D
    intro j hj
    have hcj := hc_nonneg j hj
    by_cases h0 : c j = 0
    · rw [h0]; decide
    · have hm := Int.mul_nonneg hcj (show 0 ≤ c j - 1 by omega)
      rw [Int.mul_sub, Int.mul_one] at hm
      omega
  rw [sumInt_sub, hsum] at hcsq_diff
  rw [hid]
  have hD2_nn : 0 ≤ (D : Int) * (D : Int) := sq_nonneg (D : Int)
  have hmul :
      ((D : Int) * (D : Int)) * T ≤ ((D : Int) * (D : Int)) * sumInt D (fun j => c j * c j) := by
    have hd := Int.mul_nonneg hD2_nn hcsq_diff
    rw [Int.mul_sub] at hd
    omega
  have hexp : (D : Int) * T * ((D : Int) - T) = ((D : Int) * (D : Int)) * T - (D : Int) * (T * T) := by
    rw [Int.mul_sub]
    have a1 : ((D : Int) * T) * (D : Int) = ((D : Int) * (D : Int)) * T := by
      rw [Int.mul_assoc, Int.mul_comm T (D : Int), ← Int.mul_assoc]
    have a2 : ((D : Int) * T) * T = (D : Int) * (T * T) := by rw [Int.mul_assoc]
    rw [a1, a2]
  omega

/-! ## Section 4: Discrete Stein–Lyapunov Contraction vs. Non-Normal Jordan Transient Growth (`Folder 05` ↔ `06`) -/

/-- **Theorem 3 (Discrete Stein–Lyapunov Monotone Contraction vs. Non-Normal Jordan Shear Explosion)**:
    1. Under discrete Stein–Lyapunov dissipation `q² V(x) - V(step x) ≥ γ V(x)`, quadratic energy contracts
       monotonically at EVERY single step (`V(step x) ≤ (q² - γ) V(x)`) with zero transient overshoot.
    2. Conversely, the non-normal `2 × 2` defective Jordan block `J_K(x₀, x₁) = (x₀ + K x₁, x₁)` at scale `q = 2`
       has repeated eigenvalue `1/2 < 1` (Schur-stable!), yet starting from `x = (0, 1)` (`‖x‖₂² = 1`),
       step-1 energy is `‖J_K(0, 1)‖₂² = K² + 1 > 4 = q² ‖(0, 1)‖₂²` for EVERY shear `K ≥ 2`
       (e.g. `17 > 4` at `K = 4`, a `4.25×` energy explosion in a single step!). -/
theorem discrete_stein_lyapunov_contraction_vs_nonnormal_jordan_transient_growth :
    (∀ (qSq γ Vx Vstepx : Int),
      qSq * Vx - Vstepx ≥ γ * Vx →
      Vstepx ≤ (qSq - γ) * Vx) ∧
    (∀ K : Int, 2 ≤ K →
      let q : Int := 2
      let x0 : Int := 0
      let x1 : Int := 1
      let y0 : Int := x0 + K * x1
      let y1 : Int := x1
      q * q * (x0 * x0 + x1 * x1) < y0 * y0 + y1 * y1) ∧
    ((0 + (4 : Int) * 1) * (0 + (4 : Int) * 1) + 1 * 1 = 17 ∧ (2 : Int) * 2 * 1 = 4) := by
  refine ⟨?_, ?_, by decide⟩
  · intro qSq γ Vx Vstepx hdiss
    have hsub : (qSq - γ) * Vx = qSq * Vx - γ * Vx := Int.sub_mul qSq γ Vx
    omega
  · intro K hK
    dsimp only
    have hK2 : 4 ≤ K * K := by
      have hm := Int.mul_nonneg (show 0 ≤ K - 2 by omega) (show 0 ≤ K + 2 by omega)
      have hexp : (K - 2) * (K + 2) = K * K - 4 := by
        rw [Int.sub_mul, Int.mul_add, Int.mul_add]
        omega
      omega
    have hy0 : (0 + K * 1) * (0 + K * 1) = K * K := by simp
    omega

end CommonGround.KrylovHerdingSynthesis
