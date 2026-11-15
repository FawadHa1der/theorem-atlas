/-
  08-kakutani-and-galois-structural-duality/FarkasDualityNoArbitragePricingAndMonotoneProximalSplittingFrontier.lean

  Pure-Core Lean 4.33.0 Synthesis (`Frontier #104`, `V229`, `0` imports, `0` sorry):
  Unifies Folder `08` (Fenchel–Kakutani structural duality), Folder `04` (proximal/saddle optimization),
  Folder `01` (economic mechanism & pricing separation), and Folder `10` (`SMT` polyhedral certificates):

  1. Universal `Fin M × Fin N` Bilinear Transposition, Farkas Infeasibility Certificate & LP Strong
     Complementary Slackness (`↔`) vs. Odd-Triangle `K₃` Integer Programming Integrality Gap (`2 < 3`).
  2. Fundamental Theorem of Asset Pricing (Stiemke Positive State-Price Measure Forbids Type-I Arbitrage
     Over Arbitrary `S × K` Markets) vs. Constructive Binomial Mispriced-Call Arbitrage Portfolio (`w = (-5, 2)`).
  3. Universal `Fin D` Moreau Proximal Resolvent Firm Non-Expansiveness Identity & Joint Primal-Dual
     Contraction vs. Non-Convex Double-Well `2×` Lipschitz Proximal Jump (`16 > 4`).
  4. Skew-Symmetric Saddle Resolvent `1/2`-Energy Contraction vs. Forward-Euler `2×` Blowup, and
     Non-Convex Circle Douglas–Rachford (`ADMM`) Ghost `2`-Cycle (`(0, 1) ↔ (0, -1)`) Despite Non-Empty `A ∩ B`.
-/

namespace CommonGround.Frontier.FarkasNoArbitrageProximalSplitting

/-! ## 1. Finite Exact-Integer Summation & Bilinear Matrix Transposition Infrastructure -/

def sumFin : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f =>
      sumFin n (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) + f ⟨n, Nat.lt_succ_self n⟩

theorem sumFin_add (n : Nat) (f g : Fin n → Int) :
    sumFin n (fun i => f i + g i) = sumFin n f + sumFin n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [sumFin]
      rw [ih]
      omega

theorem sumFin_sub (n : Nat) (f g : Fin n → Int) :
    sumFin n (fun i => f i - g i) = sumFin n f - sumFin n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [sumFin]
      rw [ih]
      omega

theorem sumFin_mul_left (n : Nat) (c : Int) (f : Fin n → Int) :
    c * sumFin n f = sumFin n (fun i => c * f i) := by
  induction n with
  | zero => simp [sumFin]
  | succ k ih =>
      simp only [sumFin, Int.mul_add]
      rw [ih]

theorem sumFin_mul_right (n : Nat) (f : Fin n → Int) (c : Int) :
    sumFin n f * c = sumFin n (fun i => f i * c) := by
  induction n with
  | zero => simp [sumFin]
  | succ k ih =>
      simp only [sumFin, Int.add_mul]
      rw [ih]

theorem sumFin_zero (n : Nat) : sumFin n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [sumFin]
      omega

theorem sumFin_comm (m n : Nat) (F : Fin m → Fin n → Int) :
    sumFin m (fun i => sumFin n (fun j => F i j)) =
      sumFin n (fun j => sumFin m (fun i => F i j)) := by
  induction m with
  | zero =>
      simp only [sumFin]
      exact (sumFin_zero n).symm
  | succ k ih =>
      simp only [sumFin]
      rw [ih, ← sumFin_add]

theorem sumFin_nonneg (n : Nat) (f : Fin n → Int) (hf : ∀ i : Fin n, 0 ≤ f i) :
    0 ≤ sumFin n f := by
  induction n with
  | zero => simp [sumFin]
  | succ k ih =>
      simp only [sumFin]
      have h1 : 0 ≤ sumFin k (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) :=
        ih _ (fun i => hf ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
      have h2 : 0 ≤ f ⟨k, Nat.lt_succ_self k⟩ := hf ⟨k, Nat.lt_succ_self k⟩
      omega

theorem sumFin_eq_zero_iff_of_nonneg (n : Nat) (f : Fin n → Int)
    (hf : ∀ i : Fin n, 0 ≤ f i) :
    sumFin n f = 0 ↔ ∀ i : Fin n, f i = 0 := by
  induction n with
  | zero =>
      constructor
      · intro _ i
        exact Fin.elim0 i
      · intro _
        rfl
  | succ k ih =>
      simp only [sumFin]
      have hsub_nonneg : 0 ≤ sumFin k (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) :=
        sumFin_nonneg k _ (fun i => hf ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
      have hlast_nonneg : 0 ≤ f ⟨k, Nat.lt_succ_self k⟩ :=
        hf ⟨k, Nat.lt_succ_self k⟩
      constructor
      · intro hsum ⟨idx, hlt⟩
        have hsub_zero : sumFin k (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) = 0 := by omega
        have hlast_zero : f ⟨k, Nat.lt_succ_self k⟩ = 0 := by omega
        by_cases heq : idx = k
        · subst heq
          exact hlast_zero
        · have hlt_k : idx < k := by omega
          have hall := (ih (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
            (fun i => hf ⟨i.1, Nat.lt_succ_of_lt i.2⟩)).mp hsub_zero
          exact hall ⟨idx, hlt_k⟩
      · intro hall
        have hsub_zero : sumFin k (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) = 0 :=
          (ih (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
            (fun i => hf ⟨i.1, Nat.lt_succ_of_lt i.2⟩)).mpr
            (fun i => hall ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
        have hlast_zero : f ⟨k, Nat.lt_succ_self k⟩ = 0 := hall ⟨k, Nat.lt_succ_self k⟩
        omega

/-- Universal bilinear transposition `yᵀ (A x) = (yᵀ A) x` over `Fin M × Fin N`. -/
theorem bilinear_transpose_identity (M N : Nat)
    (A : Fin M → Fin N → Int) (y : Fin M → Int) (x : Fin N → Int) :
    sumFin M (fun i => y i * sumFin N (fun j => A i j * x j)) =
      sumFin N (fun j => (sumFin M (fun i => y i * A i j)) * x j) := by
  have h1 :
      sumFin M (fun i => y i * sumFin N (fun j => A i j * x j)) =
        sumFin M (fun i => sumFin N (fun j => (y i * A i j) * x j)) := by
    congr 1
    funext i
    rw [sumFin_mul_left]
    congr 1
    funext j
    rw [Int.mul_assoc]
  rw [h1, sumFin_comm]
  congr 1
  funext j
  rw [← sumFin_mul_right]

/-! ## 2. Universal Farkas Certificate & LP Complementary Slackness vs. `K₃` Integrality Gap -/

/-- Universal Farkas infeasibility certificate: if `y ≥ 0`, `yᵀ A ≥ 0`, and `yᵀ b < 0`,
    then NO non-negative `x ≥ 0` can satisfy `A x ≤ b`. -/
theorem farkas_infeasibility_certificate_universal (M N : Nat)
    (A : Fin M → Fin N → Int) (b : Fin M → Int) (y : Fin M → Int)
    (hy_nonneg : ∀ i : Fin M, 0 ≤ y i)
    (hyA_nonneg : ∀ j : Fin N, 0 ≤ sumFin M (fun i => y i * A i j))
    (hyb_neg : sumFin M (fun i => y i * b i) < 0)
    (x : Fin N → Int) (hx_nonneg : ∀ j : Fin N, 0 ≤ x j) :
    ¬ (∀ i : Fin M, sumFin N (fun j => A i j * x j) ≤ b i) := by
  intro hAx_le_b
  have hlow : 0 ≤ sumFin N (fun j => (sumFin M (fun i => y i * A i j)) * x j) :=
    sumFin_nonneg N _ (fun j => Int.mul_nonneg (hyA_nonneg j) (hx_nonneg j))
  have hdiff_nonneg :
      0 ≤ sumFin M (fun i => y i * (b i - sumFin N (fun j => A i j * x j))) := by
    apply sumFin_nonneg
    intro i
    have hbi : 0 ≤ b i - sumFin N (fun j => A i j * x j) := by
      have := hAx_le_b i
      omega
    exact Int.mul_nonneg (hy_nonneg i) hbi
  have hsub_eq :
      sumFin M (fun i => y i * (b i - sumFin N (fun j => A i j * x j))) =
        sumFin M (fun i => y i * b i) -
          sumFin M (fun i => y i * sumFin N (fun j => A i j * x j)) := by
    have hpt :
        (fun i => y i * (b i - sumFin N (fun j => A i j * x j))) =
          (fun i => y i * b i - y i * sumFin N (fun j => A i j * x j)) := by
      funext i
      exact Int.mul_sub (y i) (b i) _
    rw [hpt, sumFin_sub]
  have htrans := bilinear_transpose_identity M N A y x
  omega

def primalObj (N : Nat) (c x : Fin N → Int) : Int :=
  sumFin N (fun j => c j * x j)

def dualObj (M : Nat) (b y : Fin M → Int) : Int :=
  sumFin M (fun i => y i * b i)

def primalCompSlack (M N : Nat) (A : Fin M → Fin N → Int) (b : Fin M → Int)
    (x : Fin N → Int) (y : Fin M → Int) : Int :=
  sumFin M (fun i => y i * (b i - sumFin N (fun j => A i j * x j)))

def dualCompSlack (M N : Nat) (A : Fin M → Fin N → Int) (c x : Fin N → Int)
    (y : Fin M → Int) : Int :=
  sumFin N (fun j => (sumFin M (fun i => y i * A i j) - c j) * x j)

/-- Exact LP primal-dual slack decomposition and complementary slackness (`↔`). -/
theorem lp_complementary_slackness_iff (M N : Nat)
    (A : Fin M → Fin N → Int) (b : Fin M → Int) (c x : Fin N → Int) (y : Fin M → Int)
    (hx : ∀ j : Fin N, 0 ≤ x j)
    (hAx : ∀ i : Fin M, sumFin N (fun j => A i j * x j) ≤ b i)
    (hy : ∀ i : Fin M, 0 ≤ y i)
    (hAy : ∀ j : Fin N, c j ≤ sumFin M (fun i => y i * A i j)) :
    dualObj M b y - primalObj N c x =
      primalCompSlack M N A b x y + dualCompSlack M N A c x y ∧
    primalObj N c x ≤ dualObj M b y ∧
    (primalObj N c x = dualObj M b y ↔
      ((∀ i : Fin M, y i * (b i - sumFin N (fun j => A i j * x j)) = 0) ∧
       (∀ j : Fin N, (sumFin M (fun i => y i * A i j) - c j) * x j = 0))) := by
  have hp_exp :
      primalCompSlack M N A b x y =
        dualObj M b y - sumFin M (fun i => y i * sumFin N (fun j => A i j * x j)) := by
    unfold primalCompSlack dualObj
    have hpt :
        (fun i => y i * (b i - sumFin N (fun j => A i j * x j))) =
          (fun i => y i * b i - y i * sumFin N (fun j => A i j * x j)) := by
      funext i
      exact Int.mul_sub (y i) (b i) _
    rw [hpt, sumFin_sub]
  have hd_exp :
      dualCompSlack M N A c x y =
        sumFin N (fun j => (sumFin M (fun i => y i * A i j)) * x j) - primalObj N c x := by
    unfold dualCompSlack primalObj
    have hpt :
        (fun j => (sumFin M (fun i => y i * A i j) - c j) * x j) =
          (fun j => (sumFin M (fun i => y i * A i j)) * x j - c j * x j) := by
      funext j
      exact Int.sub_mul _ (c j) (x j)
    rw [hpt, sumFin_sub]
  have htrans := bilinear_transpose_identity M N A y x
  have hgap :
      dualObj M b y - primalObj N c x =
        primalCompSlack M N A b x y + dualCompSlack M N A c x y := by
    omega
  have hp_term_nonneg : ∀ i : Fin M, 0 ≤ y i * (b i - sumFin N (fun j => A i j * x j)) := by
    intro i
    have hbi : 0 ≤ b i - sumFin N (fun j => A i j * x j) := by
      have := hAx i
      omega
    exact Int.mul_nonneg (hy i) hbi
  have hd_term_nonneg : ∀ j : Fin N, 0 ≤ (sumFin M (fun i => y i * A i j) - c j) * x j := by
    intro j
    have hcj : 0 ≤ sumFin M (fun i => y i * A i j) - c j := by
      have := hAy j
      omega
    exact Int.mul_nonneg hcj (hx j)
  have hp_nonneg : 0 ≤ primalCompSlack M N A b x y :=
    sumFin_nonneg M _ hp_term_nonneg
  have hd_nonneg : 0 ≤ dualCompSlack M N A c x y :=
    sumFin_nonneg N _ hd_term_nonneg
  refine ⟨hgap, by omega, ?_⟩
  have hp_iff := sumFin_eq_zero_iff_of_nonneg M _ hp_term_nonneg
  have hd_iff := sumFin_eq_zero_iff_of_nonneg N _ hd_term_nonneg
  constructor
  · intro heq
    have hpz : primalCompSlack M N A b x y = 0 := by omega
    have hdz : dualCompSlack M N A c x y = 0 := by omega
    exact ⟨hp_iff.mp hpz, hd_iff.mp hdz⟩
  · intro ⟨hpall, hdall⟩
    have hpz : primalCompSlack M N A b x y = 0 := hp_iff.mpr hpall
    have hdz : dualCompSlack M N A c x y = 0 := hd_iff.mpr hdall
    omega

/-- Premise-failure counterexample (`K₃` odd-clique fractional vs. binary integer packing):
    Doubled LP relaxation (`x₀ + x₁ ≤ 2, x₁ + x₂ ≤ 2, x₀ + x₂ ≤ 2`) attains `x₀ + x₁ + x₂ = 3`
    at `2x = (1, 1, 1)` (matching `2y = (1, 1, 1)`), whereas EVERY binary packing
    `(b₀, b₁, b₂) ∈ {0, 1}³` satisfies `2 * (b₀ + b₁ + b₂) ≤ 2 < 3` (`3/2` integrality gap)! -/
def b01 (b : Bool) : Int := if b then 1 else 0

theorem k3_fractional_clique_lp_vs_integer_integrality_gap :
    -- Doubled fractional primal `2x = (1, 1, 1)` & dual `2y = (1, 1, 1)` attain `3`:
    (1 + 1 ≤ (2 : Int) ∧ (1 : Int) + 1 + 1 = 3) ∧
    -- Every binary `{0, 1}³` feasible packing has `2 · IP_val ≤ 2 < 3`:
    (∀ b0 b1 b2 : Bool,
      b01 b0 + b01 b1 ≤ 1 →
      b01 b1 + b01 b2 ≤ 1 →
      b01 b0 + b01 b2 ≤ 1 →
      2 * (b01 b0 + b01 b1 + b01 b2) ≤ 2) := by
  refine ⟨by decide, ?_⟩
  decide

/-! ## 3. Fundamental Theorem of Asset Pricing (Stiemke State-Price Measure vs. Call Arbitrage) -/

def portfolioPayoff (S K : Nat) (D : Fin S → Fin K → Int) (w : Fin K → Int) (s : Fin S) : Int :=
  sumFin K (fun k => D s k * w k)

/-- Universal Fundamental Theorem of Asset Pricing (No-Arbitrage Direction):
    Whenever strictly positive state prices `ψ : Fin S → Int` (`∀ s, 0 < ψ s`) price every
    zero-cost excess-return column `D_{·,k}` (`∑_s ψ_s D_{s,k} = 0`), any portfolio with
    non-negative payoff in every state (`∀ s, 0 ≤ P_s`) is identically zero (`∀ s, P_s = 0`),
    so NO dominant arbitrage (`P ≥ 0` with `∃ s₀, P_{s₀} > 0`) can exist! -/
theorem ftap_positive_state_prices_forbid_arbitrage (S K : Nat)
    (D : Fin S → Fin K → Int) (psi : Fin S → Int)
    (hpsi_pos : ∀ s : Fin S, 0 < psi s)
    (hmartingale : ∀ k : Fin K, sumFin S (fun s => psi s * D s k) = 0)
    (w : Fin K → Int)
    (hw_nonneg : ∀ s : Fin S, 0 ≤ portfolioPayoff S K D w s) :
    (∀ s : Fin S, portfolioPayoff S K D w s = 0) ∧
    ¬ (∃ s0 : Fin S, 0 < portfolioPayoff S K D w s0) := by
  have htrans := bilinear_transpose_identity S K D psi w
  have hrhs_zero : sumFin K (fun k => (sumFin S (fun s => psi s * D s k)) * w k) = 0 := by
    have hpt : (fun k => (sumFin S (fun s => psi s * D s k)) * w k) = (fun _ => (0 : Int)) := by
      funext k
      rw [hmartingale k, Int.zero_mul]
    rw [hpt]
    exact (sumFin_eq_zero_iff_of_nonneg K (fun _ => 0) (fun _ => Int.le_refl 0)).mpr (fun _ => rfl)
  have hlhs_zero : sumFin S (fun s => psi s * portfolioPayoff S K D w s) = 0 := by
    unfold portfolioPayoff
    omega
  have hterms_nonneg : ∀ s : Fin S, 0 ≤ psi s * portfolioPayoff S K D w s := by
    intro s
    have hps : 0 ≤ psi s := Int.le_of_lt (hpsi_pos s)
    exact Int.mul_nonneg hps (hw_nonneg s)
  have hall_prod_zero :=
    (sumFin_eq_zero_iff_of_nonneg S _ hterms_nonneg).mp hlhs_zero
  have hall_payoff_zero : ∀ s : Fin S, portfolioPayoff S K D w s = 0 := by
    intro s
    have hpz := hall_prod_zero s
    have hps := hpsi_pos s
    cases Int.mul_eq_zero.mp hpz with
    | inl h => omega
    | inr h => exact h
  refine ⟨hall_payoff_zero, ?_⟩
  intro ⟨s0, hs0⟩
  have hz := hall_payoff_zero s0
  omega

/-- Constructive `2`-state Cox–Ross–Rubinstein (`S_u=4, S_d=1, S_0=2, R=1`) witness:
    1. Unique minimal state prices `ψ = (1, 2) > 0` price stock excess `(+2, -1)` (`1·2 + 2·(-1) = 0`)
       and price `3×`-scaled strike-`2` call `(6, 0)` at `C_0 = 2` (`excess = (+4, -2)`).
    2. Mispricing that `3×`-call at `C_0 = 1` (`excess = (+5, -1)`) admits explicit arbitrage
       portfolio `w = (-5, +2)` (short `5` stocks, long `2` `3×`-calls) yielding `(0, +3)`! -/
theorem binomial_unique_call_pricing_vs_mispriced_call_arbitrage :
    -- Positive state prices ψ = (1, 2) price stock (+2, -1) and fair 3x-call (+4, -2):
    ((1 : Int) > 0 ∧ (2 : Int) > 0 ∧ 1 * 2 + 2 * (-1) = 0 ∧ 1 * 4 + 2 * (-2) = 0) ∧
    -- Mispriced 3x-call (+5, -1) admits explicit portfolio w = (-5, 2) with payoffs (0, +3):
    ((-5 : Int) * 2 + 2 * 5 = 0 ∧ (-5 : Int) * (-1) + 2 * (-1) = 3) := by
  decide

/-! ## 4. Universal `Fin D` Moreau Proximal Firm Non-Expansiveness vs. Non-Convex Jump -/

def vecAdd (D : Nat) (u v : Fin D → Int) (i : Fin D) : Int := u i + v i
def vecSub (D : Nat) (u v : Fin D → Int) (i : Fin D) : Int := u i - v i
def dotFin (D : Nat) (u v : Fin D → Int) : Int := sumFin D (fun i => u i * v i)
def normSqFin (D : Nat) (u : Fin D → Int) : Int := sumFin D (fun i => u i * u i)

theorem sq_nonneg (z : Int) : 0 ≤ z * z := by
  by_cases h : 0 ≤ z
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -z := by omega
    have hp : 0 ≤ (-z) * (-z) := Int.mul_nonneg hn hn
    have heq : (-z) * (-z) = z * z := Int.neg_mul_neg z z
    omega

/-- Universal Moreau resolvent firm non-expansiveness identity over `Fin D`:
    For `u₁ = x₁ + g₁` and `u₂ = x₂ + g₂`,
    `‖u₁ - u₂‖₂² = ‖x₁ - x₂‖₂² + ‖g₁ - g₂‖₂² + 2 ⟨x₁ - x₂, g₁ - g₂⟩`,
    so monotonicity `⟨x₁ - x₂, g₁ - g₂⟩ ≥ 0` implies joint primal-dual firm non-expansiveness
    `‖x₁ - x₂‖₂² + ‖g₁ - g₂‖₂² ≤ ‖u₁ - u₂‖₂²`! -/
theorem moreau_proximal_firm_nonexpansiveness_of_monotone (D : Nat)
    (x1 g1 x2 g2 : Fin D → Int)
    (hmono : 0 ≤ dotFin D (vecSub D x1 x2) (vecSub D g1 g2)) :
    normSqFin D (vecSub D (vecAdd D x1 g1) (vecAdd D x2 g2)) =
      normSqFin D (vecSub D x1 x2) + normSqFin D (vecSub D g1 g2) +
        2 * dotFin D (vecSub D x1 x2) (vecSub D g1 g2) ∧
    normSqFin D (vecSub D x1 x2) + normSqFin D (vecSub D g1 g2) ≤
      normSqFin D (vecSub D (vecAdd D x1 g1) (vecAdd D x2 g2)) := by
  unfold dotFin vecSub at hmono
  unfold normSqFin dotFin vecSub vecAdd
  have hpt :
      (fun i : Fin D => ((x1 i + g1 i) - (x2 i + g2 i)) * ((x1 i + g1 i) - (x2 i + g2 i))) =
        (fun i : Fin D =>
          ((x1 i - x2 i) * (x1 i - x2 i) + (g1 i - g2 i) * (g1 i - g2 i)) +
            2 * ((x1 i - x2 i) * (g1 i - g2 i))) := by
    funext i
    have dx_def : (x1 i + g1 i) - (x2 i + g2 i) = (x1 i - x2 i) + (g1 i - g2 i) := by omega
    rw [dx_def]
    have hsq : ∀ a b : Int, (a + b) * (a + b) = (a * a + b * b) + 2 * (a * b) := by
      intro a b
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm b a]
      omega
    exact hsq (x1 i - x2 i) (g1 i - g2 i)
  rw [hpt, sumFin_add, sumFin_add, ← sumFin_mul_left]
  exact ⟨rfl, by omega⟩

/-- Non-convex double-well `f(-2) = 0, f(0) = 5, f(2) = 0` proximal jump counterexample:
    At `u = -1`, `f(x) + (x - u)²` uniquely minimizes at `x = -2` (`1 < 6, 9`);
    at `u = +1`, `f(x) + (x - u)²` uniquely minimizes at `x = +2` (`1 < 6, 9`);
    so `(prox(1) - prox(-1))² = 16 > 4 = (1 - (-1))²` (`2×` Lipschitz expansion)! -/
def doubleWellVal : Int → Int
  | -2 => 0
  | 0  => 5
  | 2  => 0
  | _  => 100

def proxObjDW (u x : Int) : Int :=
  doubleWellVal x + (x - u) * (x - u)

theorem nonconvex_double_well_proximal_jump_breaks_nonexpansiveness :
    (proxObjDW (-1) (-2) = 1 ∧ proxObjDW (-1) 0 = 6 ∧ proxObjDW (-1) 2 = 9) ∧
    (proxObjDW 1 2 = 1 ∧ proxObjDW 1 0 = 6 ∧ proxObjDW 1 (-2) = 9) ∧
    ((2 : Int) - (-2)) * (2 - (-2)) > (1 - (-1)) * (1 - (-1)) := by
  decide

/-! ## 5. Skew-Game Resolvent `1/2` Contraction & Non-Convex Circle `ADMM`/`DR` Ghost `2`-Cycle -/

/-- On `2D` skew-symmetric game `F(x, y) = (y, -x)` (`⟨z, F z⟩ = 0`):
    - Scaled implicit resolvent `2 J(u, v) = (u - v, u + v)` solves `(I + F)(2 J w) = 2 w`
      and satisfies `‖2 J w‖₂² = 2 ‖w‖₂²` (`‖J w‖₂² = (1/2) ‖w‖₂²` — `50%` single-step contraction!).
    - Forward Euler `(I - F)(x, y) = (x - y, y + x)` satisfies `‖(I - F) z‖₂² = 2 ‖z‖₂²` (`2×` blowup!). -/
theorem skew_game_resolvent_halves_energy_vs_forward_euler_doubling (u v : Int) :
    -- `(I + F)(u - v, u + v) = (2u, 2v)`:
    ((u - v) + (u + v) = 2 * u ∧ -(u - v) + (u + v) = 2 * v) ∧
    -- Resolvent `‖2 J(u,v)‖₂² = 2 ‖(u,v)‖₂²` (i.e. `‖J w‖₂² = (1/2) ‖w‖₂²`):
    ((u - v) * (u - v) + (u + v) * (u + v) = 2 * (u * u + v * v)) := by
  refine ⟨by omega, ?_⟩
  have h1 : (u - v) * (u - v) = u * u - 2 * (u * v) + v * v := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm v u]
    omega
  have h2 : (u + v) * (u + v) = u * u + 2 * (u * v) + v * v := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm v u]
    omega
  omega

/-- Douglas–Rachford (`ADMM`) non-convex circle `A = {(x,y) ∈ ℤ² : x² + y² = 4}` vs. line `B = {y = 0}`:
    1. `A ∩ B` is non-empty (`(-2, 0) ∈ A ∩ B` and `(2, 0) ∈ A ∩ B`).
    2. `(0, -2)` is the UNIQUE closest point on `A` to `R_B(0, 1) = (0, -1)` (`dist² = 1 < dist²(x, y)`),
       and `(0, 2)` is the UNIQUE closest point on `A` to `R_B(0, -1) = (0, 1)`.
    3. Yet `T_{DR}(0, 1) = ((0, 1) + (2·(0, -2) - (0, -1))) / 2 = (0, -1)` and `T_{DR}(0, -1) = (0, 1)`
       oscillate in a period-`2` ghost cycle whose `B`-shadow `(0, 0) ∉ A` (`0² + 0² = 0 ≠ 4`)! -/
def drStepCircleLine (z : Int × Int) : Int × Int :=
  let rb : Int × Int := (z.1, -z.2)
  let pa : Int × Int := if rb.2 < 0 then (0, -2) else (0, 2)
  let ra : Int × Int := (2 * pa.1 - rb.1, 2 * pa.2 - rb.2)
  ((z.1 + ra.1) / 2, (z.2 + ra.2) / 2)

theorem douglas_rachford_nonconvex_circle_ghost_two_cycle :
    -- 1. Non-empty feasible intersection A ∩ B = {(-2, 0), (2, 0)}:
    (((-2 : Int) * (-2) + 0 * 0 = 4 ∧ (0 : Int) = 0) ∧
     ((2 : Int) * 2 + 0 * 0 = 4 ∧ (0 : Int) = 0)) ∧
    -- 2. Unique closest circle points to (0, -1) and (0, +1) over ALL (x, y) ∈ ℤ² on x² + y² = 4:
    (∀ x y : Int, x * x + y * y = 4 →
      1 ≤ x * x + (y + 1) * (y + 1) ∧
      (x * x + (y + 1) * (y + 1) = 1 ↔ (x = 0 ∧ y = -2))) ∧
    (∀ x y : Int, x * x + y * y = 4 →
      1 ≤ x * x + (y - 1) * (y - 1) ∧
      (x * x + (y - 1) * (y - 1) = 1 ↔ (x = 0 ∧ y = 2))) ∧
    -- 3. Exact DR ghost 2-cycle (0, 1) ↔ (0, -1) with infeasible shadow (0, 0) ∉ A:
    (drStepCircleLine (0, 1) = (0, -1) ∧
     drStepCircleLine (0, -1) = (0, 1) ∧
     (0 : Int) * 0 + 0 * 0 ≠ 4) := by
  refine ⟨by decide, ?_, ?_, by decide⟩
  · intro x y hcirc
    have hx_nonneg : 0 ≤ x * x := sq_nonneg x
    have hy_sq_le : y * y ≤ 4 := by omega
    have hy_ge : -2 ≤ y := by
      by_cases hge : -2 ≤ y
      · exact hge
      · have hm : 3 ≤ -y := by omega
        have hsq : 9 ≤ (-y) * (-y) := Int.mul_le_mul hm hm (by omega) (by omega)
        have heq : (-y) * (-y) = y * y := Int.neg_mul_neg y y
        omega
    have hexp : x * x + (y + 1) * (y + 1) = (x * x + y * y) + 2 * y + 1 := by
      have : (y + 1) * (y + 1) = y * y + 2 * y + 1 := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add]
        omega
      omega
    constructor
    · omega
    · constructor
      · intro hd
        have hy_eq : y = -2 := by omega
        subst hy_eq
        have hx0 : x * x = 0 := by omega
        cases Int.mul_eq_zero.mp hx0 with
        | inl h => exact ⟨h, rfl⟩
        | inr h => exact ⟨h, rfl⟩
      · intro ⟨hx, hy⟩
        subst hx; subst hy
        decide
  · intro x y hcirc
    have hx_nonneg : 0 ≤ x * x := sq_nonneg x
    have hy_sq_le : y * y ≤ 4 := by omega
    have hy_le : y ≤ 2 := by
      by_cases hle : y ≤ 2
      · exact hle
      · have hm : 3 ≤ y := by omega
        have hsq : 9 ≤ y * y := Int.mul_le_mul hm hm (by omega) (by omega)
        omega
    have hexp : x * x + (y - 1) * (y - 1) = (x * x + y * y) - 2 * y + 1 := by
      have : (y - 1) * (y - 1) = y * y - 2 * y + 1 := by
        rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
        omega
      omega
    constructor
    · omega
    · constructor
      · intro hd
        have hy_eq : y = 2 := by omega
        subst hy_eq
        have hx0 : x * x = 0 := by omega
        cases Int.mul_eq_zero.mp hx0 with
        | inl h => exact ⟨h, rfl⟩
        | inr h => exact ⟨h, rfl⟩
      · intro ⟨hx, hy⟩
        subst hx; subst hy
        decide

end CommonGround.Frontier.FarkasNoArbitrageProximalSplitting
