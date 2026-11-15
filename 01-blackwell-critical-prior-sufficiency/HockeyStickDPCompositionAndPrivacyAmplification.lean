/-!
# Hockey-Stick `(ε, δ)`-DP Post-Processing, Asymmetric Chain vs. Bi-Hybrid Composition & Tight Subsampling Privacy Amplification

Pure-core Lean 4.33.0 formalization (`0 sorry`, `0` external dependencies) extending Folder `01`
(`QuantitativeCriticalSlack.lean :: weightedValue_eq_hockeyStick`) into a complete, division-free
quantitative calculus for Differential Privacy and Blackwell experiment degradation:

1. **`bayes_max_sum_eq_scaled_hockey_stick` & `hockey_stick_reversal_duality`**:
   - Exact arbitrary-`n` duality between prior-weighted Bayes max-sum value and scaled Hockey-Stick
     divergence `hockeyStickScaled n A B p q = ∑_{i < n} max(A p_i - B q_i, 0)`:
     `∑_{i < n} max(A p_i, B q_i) = B ∑_{i < n} q_i + hockeyStickScaled n A B p q`.
   - Exact reversal duality `H_{A,B}(p ‖ q) - H_{B,A}(q ‖ p) = A ∑ p - B ∑ q`.
2. **`hockey_stick_post_processing_contraction`** (Data-Processing Inequality for `(ε, δ)`-DP):
   For any nonnegative Markov post-processing matrix `M` with constant row sum `∑_{j < m} M_{i,j} = S`,
   `hockeyStickScaled m A B (pushMatrix n p M) (pushMatrix n q M) ≤ S * hockeyStickScaled n A B p q`.
3. **`heterogeneous_hockey_stick_chain_and_bihybrid_composition`** (Chain vs. Bi-Hybrid Composition):
   - Along a single intermediate distribution `p₁` (`p₀ → p₁ → p₂`), for `0 ≤ A₂, B₁`:
     `H_{A₁ A₂, B₁ B₂}(p₀ ‖ p₂) ≤ A₂ · H_{A₁,B₁}(p₀ ‖ p₁) + B₁ · H_{A₂,B₂}(p₁ ‖ p₂)` (`δ₁ + e^{ε₁} δ₂`),
     extending by induction to 3-step heterogeneous chains `A₂ A₃ H₁ + B₁ A₃ H₂ + B₁ B₂ H₃`.
   - When a reverse-order hybrid `q₁` (`(A₂, B₂)` on `p₀ → q₁`, `(A₁, B₁)` on `q₁ → p₂`) also exists,
     `H_{A₁ A₂, B₁ B₂}(p₀ ‖ p₂)` simultaneously satisfies `≤ A₁ · H_{A₂,B₂}(p₀ ‖ q₁) + B₂ · H_{A₁,B₁}(q₁ ‖ p₂)`,
     recovering `min(δ₁ + e^{ε₁} δ₂, δ₂ + e^{ε₂} δ₁)`.
4. **`privacy_amplification_by_subsampling_exact_identity`** (Balle–Barthe–Gaboardi Tight Subsampling Identity):
   For subsampled mixture `pSub_i = (S - λ) r_i + λ p_i` (`0 ≤ λ`) against reference `r` at amplified
   threshold `BSub = (S - λ) A + λ B` (representing `e^{ε'} = 1 + q(e^ε - 1)` with `q = λ / S`),
   `hockeyStickScaled n A BSub pSub r = λ * hockeyStickScaled n A B p r` holds with **exact equality**!
5. **`rare_event_pure_dp_impossibility_and_chain_order_asymmetry`**:
   - Rare-event channel `p = (99, 1), q = (100, 0)` satisfies `(0, 1/100)`-Hockey-Stick (`= 1`) for all `B ≥ 1`,
     yet violates pure `ε`-DP (`δ = 0`) for **every** finite multiplier `B ≥ 1` (`1 * p_1 - B * q_1 = 1 > 0`).
   - Explicit **order-asymmetry separation** for single-chain sequential transitions: on normalized distributions
     `p₀ = (2, 0) → p₁ = (1, 1) → p₂ = (0, 2)` with `(A₁, B₁) = (1, 10)` (`δ₁ = 0`) and `(A₂, B₂) = (1, 1)` (`δ₂ = 1/2`),
     the valid chain bound gives `2 ≤ 1·0 + 10·1 = 10`, whereas the naive swapped formula
     `B₂ H_{1,10}(p₀ ‖ p₁) + A₁ H_{1,1}(p₁ ‖ p₂) = 1·0 + 1·1 = 1 < 2 = H_{1,10}(p₀ ‖ p₂)` **strictly fails**!
-/

namespace CommonGround.BlackwellDP.HockeyStickComposition

/-- Finite integer sum `∑_{i = 0}^{n - 1} f(i)`. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

/-- Integer maximum `max(a, b)`. -/
def maxInt (a b : Int) : Int :=
  if a ≥ b then a else b

/-- Division-free scaled Hockey-Stick divergence `∑_{i < n} max(A p_i - B q_i, 0)`.
    When `p, q` are normalized and `γ = B / A = e^ε`, dividing by `A` recovers `H_{e^ε}(p ‖ q)`. -/
def hockeyStickScaled (n : Nat) (A B : Int) (p q : Nat → Int) : Int :=
  sumRange n (fun i => maxInt (A * p i - B * q i) 0)

/-- Pushforward of weight vector `v` of length `n` through matrix `M : Nat → Nat → Int`. -/
def pushMatrix (n : Nat) (v : Nat → Int) (M : Nat → Nat → Int) (j : Nat) : Int :=
  sumRange n (fun i => v i * M i j)

theorem sumRange_congr (n : Nat) (f g : Nat → Int) (h : ∀ i, i < n → f i = g i) :
    sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumRange]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k)]

theorem sumRange_add (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    simp only [sumRange]
    omega

theorem sumRange_sub (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i - g i) = sumRange n f - sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    simp only [sumRange]
    omega

theorem sumRange_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    simp only [sumRange]
    rw [ih, Int.mul_add]

theorem sumRange_zero (n : Nat) : sumRange n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [sumRange, ih]

theorem sumRange_nonneg (n : Nat) (f : Nat → Int) (hf : ∀ i, i < n → 0 ≤ f i) :
    0 ≤ sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    simp only [sumRange]
    have h1 := ih (fun i hi => hf i (Nat.lt_succ_of_lt hi))
    have h2 := hf k (Nat.lt_succ_self k)
    omega

theorem sumRange_le (n : Nat) (f g : Nat → Int) (h : ∀ i, i < n → f i ≤ g i) :
    sumRange n f ≤ sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
    simp only [sumRange]
    have h1 := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have h2 := h k (Nat.lt_succ_self k)
    omega

theorem sumRange_swap (n m : Nat) (H : Nat → Nat → Int) :
    sumRange n (fun i => sumRange m (fun j => H i j)) =
      sumRange m (fun j => sumRange n (fun i => H i j)) := by
  induction n with
  | zero =>
    simp only [sumRange]
    exact (sumRange_zero m).symm
  | succ k ih =>
    simp only [sumRange]
    rw [ih, ← sumRange_add]

theorem le_maxInt_left (a b : Int) : a ≤ maxInt a b := by
  unfold maxInt
  split <;> omega

theorem le_maxInt_right (a b : Int) : b ≤ maxInt a b := by
  unfold maxInt
  split <;> omega

theorem maxInt_le (a b c : Int) (ha : a ≤ c) (hb : b ≤ c) : maxInt a b ≤ c := by
  unfold maxInt
  split <;> omega

theorem maxInt_eq_right_add_pos_part (u v : Int) :
    maxInt u v = v + maxInt (u - v) 0 := by
  unfold maxInt
  split <;> split <;> omega

theorem maxInt_sub_maxInt_neg (u : Int) :
    maxInt u 0 - maxInt (-u) 0 = u := by
  unfold maxInt
  split <;> split <;> omega

theorem mul_maxInt_zero_nonneg (k u : Int) (hk : 0 ≤ k) :
    maxInt (k * u) 0 = k * maxInt u 0 := by
  by_cases hu : u ≥ 0
  · have hku : 0 ≤ k * u := Int.mul_nonneg hk hu
    simp only [maxInt, hu, ↓reduceIte]
    split <;> omega
  · have hle : u ≤ 0 := by omega
    have hku : k * u ≤ k * 0 := Int.mul_le_mul_of_nonneg_left hle hk
    simp only [Int.mul_zero] at hku
    simp only [maxInt, hu, ↓reduceIte, Int.mul_zero]
    split <;> omega

/-- Theorem 1: Exact Duality Between Prior-Weighted Bayes Max-Sum Value and Scaled Hockey-Stick Divergence,
    paired with Exact Reversal Duality `H_{A,B}(p ‖ q) - H_{B,A}(q ‖ p) = A ∑ p - B ∑ q`. -/
theorem bayes_max_sum_eq_scaled_hockey_stick
    (n : Nat) (A B : Int) (p q : Nat → Int) :
    (sumRange n (fun i => maxInt (A * p i) (B * q i)) =
      B * sumRange n q + hockeyStickScaled n A B p q) ∧
    (hockeyStickScaled n A B p q - hockeyStickScaled n B A q p =
      A * sumRange n p - B * sumRange n q) := by
  constructor
  · unfold hockeyStickScaled
    have hcongr :
        sumRange n (fun i => maxInt (A * p i) (B * q i)) =
          sumRange n (fun i => B * q i + maxInt (A * p i - B * q i) 0) := by
      apply sumRange_congr
      intro i _
      exact maxInt_eq_right_add_pos_part (A * p i) (B * q i)
    rw [hcongr, sumRange_add, sumRange_mul_left]
  · unfold hockeyStickScaled
    rw [← sumRange_sub]
    have hrev :
        sumRange n (fun i => maxInt (A * p i - B * q i) 0 - maxInt (B * q i - A * p i) 0) =
          sumRange n (fun i => A * p i - B * q i) := by
      apply sumRange_congr
      intro i _
      have hneg : B * q i - A * p i = -(A * p i - B * q i) := by omega
      rw [hneg]
      exact maxInt_sub_maxInt_neg (A * p i - B * q i)
    rw [hrev, sumRange_sub, sumRange_mul_left, sumRange_mul_left]

/-- Theorem 2: Exact Data-Processing / Post-Processing Contraction for `(ε, δ)`-Differential Privacy.
    Any nonnegative matrix `M` with constant row sum `∑_{j < m} M(i, j) = S` contracts `hockeyStickScaled`
    by at most the normalization scale `S`. -/
theorem hockey_stick_post_processing_contraction
    (n m : Nat) (A B S : Int) (p q : Nat → Int) (M : Nat → Nat → Int)
    (hNonneg : ∀ i j, i < n → j < m → 0 ≤ M i j)
    (hRowSum : ∀ i, i < n → sumRange m (fun j => M i j) = S) :
    hockeyStickScaled m A B (pushMatrix n p M) (pushMatrix n q M) ≤
      S * hockeyStickScaled n A B p q := by
  unfold hockeyStickScaled
  have hColBound : ∀ j, j < m →
      maxInt (A * pushMatrix n p M j - B * pushMatrix n q M j) 0 ≤
        sumRange n (fun i => maxInt (A * p i - B * q i) 0 * M i j) := by
    intro j hj
    apply maxInt_le
    · unfold pushMatrix
      rw [← sumRange_mul_left, ← sumRange_mul_left, ← sumRange_sub]
      apply sumRange_le
      intro i hi
      have hrewrite :
          A * (p i * M i j) - B * (q i * M i j) = (A * p i - B * q i) * M i j := by
        rw [Int.sub_mul, Int.mul_assoc, Int.mul_assoc]
      rw [hrewrite]
      exact Int.mul_le_mul_of_nonneg_right (le_maxInt_left (A * p i - B * q i) 0) (hNonneg i j hi hj)
    · apply sumRange_nonneg
      intro i hi
      exact Int.mul_nonneg (le_maxInt_right (A * p i - B * q i) 0) (hNonneg i j hi hj)
  have hSumLe :
      sumRange m (fun j => maxInt (A * pushMatrix n p M j - B * pushMatrix n q M j) 0) ≤
        sumRange m (fun j => sumRange n (fun i => maxInt (A * p i - B * q i) 0 * M i j)) :=
    sumRange_le m _ _ hColBound
  rw [← sumRange_swap] at hSumLe
  have hEval :
      sumRange n (fun i => sumRange m (fun j => maxInt (A * p i - B * q i) 0 * M i j)) =
        S * sumRange n (fun i => maxInt (A * p i - B * q i) 0) := by
    have h1 :
        sumRange n (fun i => sumRange m (fun j => maxInt (A * p i - B * q i) 0 * M i j)) =
          sumRange n (fun i => S * maxInt (A * p i - B * q i) 0) := by
      apply sumRange_congr
      intro i hi
      rw [sumRange_mul_left, hRowSum i hi, Int.mul_comm]
    rw [h1, sumRange_mul_left]
  omega

/-- Pointwise triangle-type decomposition for heterogeneous Hockey-Stick composition:
    `(A₁ A₂) x - (B₁ B₂) z = A₂ (A₁ x - B₁ y) + B₁ (A₂ y - B₂ z)`. -/
theorem pointwise_heterogeneous_hockey_stick_le
    (A1 B1 A2 B2 x y z : Int) (hA2 : 0 ≤ A2) (hB1 : 0 ≤ B1) :
    maxInt ((A1 * A2) * x - (B1 * B2) * z) 0 ≤
      A2 * maxInt (A1 * x - B1 * y) 0 + B1 * maxInt (A2 * y - B2 * z) 0 := by
  have hSplit :
      (A1 * A2) * x - (B1 * B2) * z =
        A2 * (A1 * x - B1 * y) + B1 * (A2 * y - B2 * z) := by
    rw [Int.mul_sub, Int.mul_sub]
    have h1 : A2 * (A1 * x) = (A1 * A2) * x := by ac_rfl
    have h2 : A2 * (B1 * y) = B1 * (A2 * y) := by ac_rfl
    have h3 : B1 * (B2 * z) = (B1 * B2) * z := by ac_rfl
    omega
  apply maxInt_le
  · rw [hSplit]
    have t1 : A2 * (A1 * x - B1 * y) ≤ A2 * maxInt (A1 * x - B1 * y) 0 :=
      Int.mul_le_mul_of_nonneg_left (le_maxInt_left _ 0) hA2
    have t2 : B1 * (A2 * y - B2 * z) ≤ B1 * maxInt (A2 * y - B2 * z) 0 :=
      Int.mul_le_mul_of_nonneg_left (le_maxInt_left _ 0) hB1
    omega
  · have n1 : 0 ≤ A2 * maxInt (A1 * x - B1 * y) 0 :=
      Int.mul_nonneg hA2 (le_maxInt_right _ 0)
    have n2 : 0 ≤ B1 * maxInt (A2 * y - B2 * z) 0 :=
      Int.mul_nonneg hB1 (le_maxInt_right _ 0)
    omega

/-- Single-chain 2-step heterogeneous Hockey-Stick composition (`δ₁ + e^{ε₁} δ₂`). -/
theorem heterogeneous_hockey_stick_chain_le
    (n : Nat) (A1 B1 A2 B2 : Int) (p0 p1 p2 : Nat → Int)
    (hA2 : 0 ≤ A2) (hB1 : 0 ≤ B1) :
    hockeyStickScaled n (A1 * A2) (B1 * B2) p0 p2 ≤
      A2 * hockeyStickScaled n A1 B1 p0 p1 + B1 * hockeyStickScaled n A2 B2 p1 p2 := by
  unfold hockeyStickScaled
  rw [← sumRange_mul_left, ← sumRange_mul_left, ← sumRange_add]
  apply sumRange_le
  intro i _
  exact pointwise_heterogeneous_hockey_stick_le A1 B1 A2 B2 (p0 i) (p1 i) (p2 i) hA2 hB1

/-- Theorem 3: Heterogeneous Chain & Bi-Hybrid Hockey-Stick Composition (2-Step, Bi-Hybrid & 3-Step).
    - Along forward hybrid `p₁`: `H_{A₁ A₂, B₁ B₂}(p₀ ‖ p₂) ≤ A₂ H_{A₁,B₁}(p₀ ‖ p₁) + B₁ H_{A₂,B₂}(p₁ ‖ p₂)`.
    - Along reverse-order hybrid `q₁`: `H_{A₁ A₂, B₁ B₂}(p₀ ‖ p₂) ≤ A₁ H_{A₂,B₂}(p₀ ‖ q₁) + B₂ H_{A₁,B₁}(q₁ ‖ p₂)`.
    - Along 3-step chain `p₀ → p₁ → p₂ → p₃`:
      `H_{A₁ A₂ A₃, B₁ B₂ B₃}(p₀ ‖ p₃) ≤ A₂ A₃ H₁ + B₁ A₃ H₂ + B₁ B₂ H₃`. -/
theorem heterogeneous_hockey_stick_chain_and_bihybrid_composition
    (n : Nat) (A1 B1 A2 B2 A3 B3 : Int) (p0 p1 q1 p2 p3 : Nat → Int)
    (hA1 : 0 ≤ A1) (hB1 : 0 ≤ B1) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2) (hA3 : 0 ≤ A3) :
    (hockeyStickScaled n (A1 * A2) (B1 * B2) p0 p2 ≤
      A2 * hockeyStickScaled n A1 B1 p0 p1 + B1 * hockeyStickScaled n A2 B2 p1 p2) ∧
    (hockeyStickScaled n (A1 * A2) (B1 * B2) p0 p2 ≤
      A1 * hockeyStickScaled n A2 B2 p0 q1 + B2 * hockeyStickScaled n A1 B1 q1 p2) ∧
    (hockeyStickScaled n ((A1 * A2) * A3) ((B1 * B2) * B3) p0 p3 ≤
      (A2 * A3) * hockeyStickScaled n A1 B1 p0 p1 +
        (B1 * A3) * hockeyStickScaled n A2 B2 p1 p2 +
        (B1 * B2) * hockeyStickScaled n A3 B3 p2 p3) := by
  refine ⟨?_, ?_, ?_⟩
  · exact heterogeneous_hockey_stick_chain_le n A1 B1 A2 B2 p0 p1 p2 hA2 hB1
  · have hRev := heterogeneous_hockey_stick_chain_le n A2 B2 A1 B1 p0 q1 p2 hA1 hB2
    have hCommA : A2 * A1 = A1 * A2 := Int.mul_comm A2 A1
    have hCommB : B2 * B1 = B1 * B2 := Int.mul_comm B2 B1
    rw [hCommA, hCommB] at hRev
    exact hRev
  · have hStep12 := heterogeneous_hockey_stick_chain_le n A1 B1 A2 B2 p0 p1 p2 hA2 hB1
    have hB12 : 0 ≤ B1 * B2 := Int.mul_nonneg hB1 hB2
    have hStep123 :=
      heterogeneous_hockey_stick_chain_le n (A1 * A2) (B1 * B2) A3 B3 p0 p2 p3 hA3 hB12
    have hMul := Int.mul_le_mul_of_nonneg_left hStep12 hA3
    rw [Int.mul_add] at hMul
    have c1 : A3 * (A2 * hockeyStickScaled n A1 B1 p0 p1) =
        (A2 * A3) * hockeyStickScaled n A1 B1 p0 p1 := by ac_rfl
    have c2 : A3 * (B1 * hockeyStickScaled n A2 B2 p1 p2) =
        (B1 * A3) * hockeyStickScaled n A2 B2 p1 p2 := by ac_rfl
    rw [c1, c2] at hMul
    omega

/-- Theorem 4: Exact Privacy Amplification by Subsampling Identity (Balle–Barthe–Gaboardi).
    For mixture `pSub_i = (S - λ) r_i + λ p_i` (`0 ≤ λ`) against base `r` at amplified threshold
    `BSub = (S - λ) A + λ B`, `hockeyStickScaled n A BSub pSub r = λ * hockeyStickScaled n A B p r`
    holds with **exact equality** (zero relaxation slack!). -/
theorem privacy_amplification_by_subsampling_exact_identity
    (n : Nat) (A B S lam : Int) (p r : Nat → Int) (hLam : 0 ≤ lam) :
    hockeyStickScaled n A ((S - lam) * A + lam * B)
      (fun i => (S - lam) * r i + lam * p i) r =
      lam * hockeyStickScaled n A B p r := by
  unfold hockeyStickScaled
  rw [← sumRange_mul_left]
  apply sumRange_congr
  intro i _
  have hAlg :
      A * ((S - lam) * r i + lam * p i) - ((S - lam) * A + lam * B) * r i =
        lam * (A * p i - B * r i) := by
    rw [Int.mul_add, Int.add_mul, Int.mul_sub]
    have t1 : A * ((S - lam) * r i) = ((S - lam) * A) * r i := by ac_rfl
    have t2 : A * (lam * p i) = lam * (A * p i) := by ac_rfl
    have t3 : (lam * B) * r i = lam * (B * r i) := by ac_rfl
    omega
  rw [hAlg]
  exact mul_maxInt_zero_nonneg lam (A * p i - B * r i) hLam

/-- Rare-event distribution `p = (99, 1)` vs. `q = (100, 0)`. -/
def rareP : Nat → Int
  | 0 => 99
  | 1 => 1
  | _ => 0

def rareQ : Nat → Int
  | 0 => 100
  | 1 => 0
  | _ => 0

/-- Normalized 2-step chain `p₀ = (2, 0) → p₁ = (1, 1) → p₂ = (0, 2)` witnessing
    both tight `(0, δ)`-composition (`2 = 1 + 1`) and strict failure (`2 > 1`) of
    order-swapped coefficients on a single sequential chain. -/
def chainP0 : Nat → Int
  | 0 => 2
  | _ => 0

def chainP1 : Nat → Int
  | 0 => 1
  | 1 => 1
  | _ => 0

def chainP2 : Nat → Int
  | 1 => 2
  | _ => 0

/-- Theorem 5: Sharp Guardrails —
    1. Rare-event `(0, δ)`-DP (`H_{1, B}(rareP ‖ rareQ) = 1` for all `B ≥ 1`) cannot be captured by pure `ε`-DP
       at **any** finite multiplier `B ≥ 1` (`1 * rareP 1 - B * rareQ 1 = 1 > 0`).
    2. Tightness of `2`-step composition: `H_{1,1}(chainP0 ‖ chainP2) = 2 = 1 + 1`.
    3. Strict failure of swapped coefficients on a single sequential chain:
       for `(A₁, B₁) = (1, 10)` and `(A₂, B₂) = (1, 1)` on normalized `chainP0, chainP1, chainP2` (all summing to `2`),
       `H_{1, 10}(chainP0 ‖ chainP2) = 2`, whereas `B₂ H_{1, 10}(chainP0 ‖ chainP1) + A₁ H_{1, 1}(chainP1 ‖ chainP2) = 1 < 2`! -/
theorem rare_event_pure_dp_impossibility_and_chain_order_asymmetry
    (B : Int) (hB : 1 ≤ B) :
    (hockeyStickScaled 2 1 B rareP rareQ = 1 ∧ 1 * rareP 1 - B * rareQ 1 = 1) ∧
    (hockeyStickScaled 2 1 1 chainP0 chainP2 = 2 ∧
      hockeyStickScaled 2 1 1 chainP0 chainP1 + hockeyStickScaled 2 1 1 chainP1 chainP2 = 2) ∧
    (sumRange 2 chainP0 = 2 ∧ sumRange 2 chainP1 = 2 ∧ sumRange 2 chainP2 = 2 ∧
      hockeyStickScaled 2 (1 * 1) (10 * 1) chainP0 chainP2 = 2 ∧
      1 * hockeyStickScaled 2 1 10 chainP0 chainP1 +
        1 * hockeyStickScaled 2 1 1 chainP1 chainP2 = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · simp only [hockeyStickScaled, sumRange, rareP, rareQ, maxInt]
      split <;> omega
    · simp [rareP, rareQ]
  · decide
  · decide

end CommonGround.BlackwellDP.HockeyStickComposition
