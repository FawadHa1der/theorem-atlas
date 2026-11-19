/-
  01-blackwell-critical-prior-sufficiency/AumannNoTradeKellyLogGrowthAndShapleyEfficiencyFrontier.lean

  Milestone Wave V259 (Historic 200 Promising Research Leads Milestone!) · Frontier #134:
  Aumann Agreement & Milgrom–Stokey Common-Prior No-Trade Theorem, Kelly Criterion Exact
  Multiplicative Growth Dominance vs. `2f*` Overbetting Gambler's Ruin, and Shapley Value
  Universal Permutation Telescoping vs. Leave-One-Out (`LOO`) Redundant-Feature Blindness
  & Unnormalized Banzhaf Budget Imbalance.

  Toolchain: `leanprover/lean4:v4.33.0` — zero `sorry`, zero `admit`, zero external axioms.
-/

namespace CommonGround.Frontier.AumannNoTradeKellyLogGrowthAndShapleyEfficiency

/-! ## Part I: Aumann / Milgrom–Stokey Common-Prior No-Trade Theorem -/

/-- Prefix sum `∑_{i=0}^{n-1} f(i)` over `Int`. -/
def intPrefixSum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | k + 1, f => intPrefixSum k f + f k

theorem intPrefixSum_nonneg (n : Nat) (f : Nat → Int) (hGe : ∀ i, i < n → 0 ≤ f i) :
    0 ≤ intPrefixSum n f := by
  induction n with
  | zero => dsimp [intPrefixSum]; decide
  | succ k ih =>
    unfold intPrefixSum
    have hSub : 0 ≤ intPrefixSum k f := ih (fun i hi => hGe i (by omega))
    have hLast : 0 ≤ f k := hGe k (by omega)
    omega

theorem intPrefixSum_eq_zero_imp_all_zero (n : Nat) (f : Nat → Int)
    (hGe : ∀ i, i < n → 0 ≤ f i) (hZero : intPrefixSum n f = 0) :
    ∀ i, i < n → f i = 0 := by
  induction n with
  | zero =>
    intro _ hi
    omega
  | succ k ih =>
    unfold intPrefixSum at hZero
    have hSubNonneg : 0 ≤ intPrefixSum k f := intPrefixSum_nonneg k f (fun j hj => hGe j (by omega))
    have hLastNonneg : 0 ≤ f k := hGe k (by omega)
    have hSubZero : intPrefixSum k f = 0 := by omega
    have hLastZero : f k = 0 := by omega
    intro i hi
    by_cases hEq : i = k
    · subst hEq; exact hLastZero
    · exact ih (fun j hj => hGe j (by omega)) hSubZero i (by omega)

/-- **Universal Common-Prior Zero-Sum Conservation**:
    Under ANY shared prior distribution `μ : Nat → Int` across `Ω` states, Trader `A`'s ex-ante
    expected trade payoff `∑ μ(ω) X(ω)` and Trader `B`'s counterparty payoff `∑ μ(ω) (-X(ω))`
    sum identically to zero. -/
theorem common_prior_state_sum_zero_sum_universal (Ω : Nat) (μ X : Nat → Int) :
    intPrefixSum Ω (fun ω => μ ω * X ω) + intPrefixSum Ω (fun ω => μ ω * (-X ω)) = 0 := by
  induction Ω with
  | zero => rfl
  | succ k ih =>
    dsimp [intPrefixSum]
    have hTerm : μ k * X k + μ k * (-X k) = 0 := by
      rw [Int.mul_neg]
      omega
    omega

/-- **Universal Milgrom–Stokey / Aumann Common-Prior No-Trade Theorem**:
    Across ANY `K`-cell information partition of Trader `A` (`gainA`) and ANY `M`-cell information
    partition of Trader `B` (`gainB`), if the trade is ex-ante zero-sum under a common prior
    (`∑ gainA + ∑ gainB = 0`) and common knowledge of individual rationality holds in every cell
    (`∀ i < K, 0 ≤ gainA i` and `∀ j < M, 0 ≤ gainB j`), then EVERY conditional cell gain of BOTH
    traders is identically `0` — ruling out any strictly profitable speculative bet! -/
theorem common_prior_partition_no_strict_speculative_trade_universal
    (K M : Nat) (gainA gainB : Nat → Int)
    (hZeroSum : intPrefixSum K gainA + intPrefixSum M gainB = 0)
    (hRatA : ∀ i, i < K → 0 ≤ gainA i)
    (hRatB : ∀ j, j < M → 0 ≤ gainB j) :
    (∀ i, i < K → gainA i = 0) ∧ (∀ j, j < M → gainB j = 0) := by
  have hSumANonneg : 0 ≤ intPrefixSum K gainA := intPrefixSum_nonneg K gainA hRatA
  have hSumBNonneg : 0 ≤ intPrefixSum M gainB := intPrefixSum_nonneg M gainB hRatB
  have hSumAZero : intPrefixSum K gainA = 0 := by omega
  have hSumBZero : intPrefixSum M gainB = 0 := by omega
  exact ⟨intPrefixSum_eq_zero_imp_all_zero K gainA hRatA hSumAZero,
         intPrefixSum_eq_zero_imp_all_zero M gainB hRatB hSumBZero⟩

/-- **Premise-Failure Counterexample (Heterogeneous / Misspecified Priors Speculative Bubble)**:
    Drop the Common-Prior hypothesis: Trader `A` holds prior `(3, 1)` on `{ω₀, ω₁}`, Trader `B`
    holds prior `(1, 3)`, and they trade zero-sum contract `X = (+2, -2)`. Both traders perceive
    strictly positive expected profit (`+4 > 0` AND `+4 > 0`) simultaneously! -/
theorem heterogeneous_prior_mutually_bullish_speculative_bubble :
    let muA0 : Int := 3; let muA1 : Int := 1
    let muB0 : Int := 1; let muB1 : Int := 3
    let x0 : Int := 2;   let x1 : Int := -2
    (x0 + (-x0) = 0 ∧ x1 + (-x1) = 0) ∧
    (muA0 * x0 + muA1 * x1 = 4 ∧ 0 < muA0 * x0 + muA1 * x1) ∧
    (muB0 * (-x0) + muB1 * (-x1) = 4 ∧ 0 < muB0 * (-x0) + muB1 * (-x1)) := by
  decide

/-! ## Part II: Kelly Criterion Multiplicative Dominance vs. `2f*` Overbetting Ruin -/

private theorem int_diff_of_squares (S f : Int) :
    (S + f) * (S - f) = S * S - f * f := by
  rw [Int.add_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm f S]
  omega

/-- **Universal Symmetric Volatility Drag Identity**:
    For every positive stake `f > 0` on capital scale `S`, one `+f` win followed by one `-f` loss
    multiplies capital by `(S + f)(S - f) = S² - f² < S²` (strictly negative log-wealth drag!). -/
theorem volatility_drag_product_lt_square_universal (S f : Int) (hf : 0 < f) :
    (S + f) * (S - f) = S * S - f * f ∧ (S + f) * (S - f) < S * S := by
  have hId := int_diff_of_squares S f
  have hPos : 0 < f * f := Int.mul_pos hf hf
  exact ⟨hId, by omega⟩

/-- Exact `5`-round (`3` wins, `2` losses, `p = 3/5, q = 2/5`) multiplicative wealth on `10^5 = 100,000`
    initial capital for tenths stake `f ∈ {0..10}`. -/
def kellyCycleWealth10 (f : Nat) : Nat :=
  ((10 + f) ^ 3) * ((10 - f) ^ 2)

/-- Arithmetic `5`-round expected return `3*(+f) + 2*(-f) = +f` (monotone increasing in `f`!). -/
def arithmeticDrift5 (f : Int) : Int :=
  3 * f - 2 * f

/-- **Kelly Optimal (`f* = 2/10`) Strict Global Dominance vs. `2f* = 4/10` Overbetting Ruin & `10/10` Bankruptcy**:
    1. Across ALL `11` stakes `f ∈ Fin 11`, Kelly `f* = p - q = 2/10` (`110,592`) is the strictly
       unique global maximizer (strictly beating Half-Kelly `107,811` and Cash `100,000`);
    2. Double-Kelly `2f* = 4/10` has **twice** the arithmetic single-step expected gain (`4 > 2`),
       YET shrinks `5`-round multiplicative wealth to `98,784 < 100,000` (`-1.216%` decay per cycle!);
    3. All-in betting `f = 10/10` hits absorbing `0` (`bankruptcy`) despite maximizing arithmetic drift! -/
theorem kelly_optimal_dominates_half_kelly_cash_and_double_kelly_ruin :
    kellyCycleWealth10 2 = 110592 ∧
    kellyCycleWealth10 1 = 107811 ∧
    kellyCycleWealth10 0 = 100000 ∧
    (∀ f : Fin 11, f.val ≠ 2 → kellyCycleWealth10 f.val < kellyCycleWealth10 2) ∧
    (arithmeticDrift5 4 = 2 * arithmeticDrift5 2 ∧ kellyCycleWealth10 4 = 98784 ∧
     kellyCycleWealth10 4 < kellyCycleWealth10 0) ∧
    kellyCycleWealth10 10 = 0 := by
  refine ⟨by decide, by decide, by decide, ?_, ⟨by decide, by decide, by decide⟩, by decide⟩
  decide

/-! ## Part III: Shapley Value Universal Telescoping vs. `LOO` Blindness & Banzhaf Deficit -/

/-- Sum of marginal contributions `∑_{k=0}^{n-1} (chain(k+1) - chain(k))` along any arrival order. -/
def marginalChainSum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | k + 1, chain => marginalChainSum k chain + (chain (k + 1) - chain k)

/-- **Universal `n`-Player Shapley Permutation Marginal Telescoping**:
    Along ANY permutation of `n` players and ANY coalition value trajectory `chain`, the sum of
    sequential marginal contributions telescopes identically to `chain n - chain 0` (`= v(N) - v(∅)`). -/
theorem shapley_marginal_chain_telescoping_universal (n : Nat) (chain : Nat → Int) :
    marginalChainSum n chain = chain n - chain 0 := by
  induction n with
  | zero => dsimp [marginalChainSum]; omega
  | succ k ih =>
    unfold marginalChainSum
    rw [ih]
    omega

/-- Asymmetric 3-player Left-Right Glove Game (`0` holds Left glove; `1, 2` hold Right gloves;
    any pair with `0` and `{1 or 2}` produces `6` units). Bitmask `S ∈ Fin 8`. -/
def gloveValue3 (mask : Nat) : Nat :=
  if (mask &&& 1 != 0) && ((mask &&& 2 != 0) || (mask &&& 4 != 0)) then 6 else 0

/-- Exact 6-permutation Shapley payout `(4, 1, 1)` on `gloveValue3`. -/
def gloveShapley3 : Fin 3 → Nat
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1

/-- Unnormalized Banzhaf swing count across the `4` coalitions not containing `i` (quarter-scaled). -/
def gloveBanzhafQuarterScaled : Fin 3 → Nat
  | ⟨0, _⟩ => 18
  | ⟨1, _⟩ => 6
  | ⟨2, _⟩ => 6

/-- Redundant 2-sensor game (`v(∅)=0, v({0})=6, v({1})=6, v({0,1})=6`). -/
def redundantSensor2 (has0 has1 : Bool) : Nat :=
  if has0 || has1 then 6 else 0

/-- **Shapley Efficiency (`4 + 1 + 1 = 6` & `3 + 3 = 6`) vs. Banzhaf `25%` Budget Deficit & `LOO` `(0, 0)` Erasure**:
    1. On the 3-player Glove Game, Shapley allocates `(4, 1, 1)` summing to `6 = v(N)`, whereas
       unnormalized Banzhaf (`18/4 + 6/4 + 6/4 = 30/4 > 24/4`) overshoots total value by `25%`!
    2. On the 2-sensor Redundant Feature Game (`v({0}) = v({1}) = v({0,1}) = 6`), Leave-One-Out
       (`LOO`) ablation assigns `(6 - 6, 6 - 6) = (0, 0)` (`100%` value erasure!), whereas
       Shapley assigns `(3, 3)` (`3 + 3 = 6 = v({0,1})`)! -/
theorem shapley_efficiency_vs_banzhaf_imbalance_and_loo_duplicate_blindness :
    (gloveShapley3 ⟨0, by omega⟩ + gloveShapley3 ⟨1, by omega⟩ + gloveShapley3 ⟨2, by omega⟩ = gloveValue3 7) ∧
    (gloveBanzhafQuarterScaled ⟨0, by omega⟩ + gloveBanzhafQuarterScaled ⟨1, by omega⟩ +
      gloveBanzhafQuarterScaled ⟨2, by omega⟩ = 30 ∧ 4 * gloveValue3 7 = 24) ∧
    (redundantSensor2 true true - redundantSensor2 false true = 0 ∧
     redundantSensor2 true true - redundantSensor2 true false = 0) ∧
    (((redundantSensor2 true false - redundantSensor2 false false) +
      (redundantSensor2 true true - redundantSensor2 false true)) / 2 = 3 ∧
     3 + 3 = redundantSensor2 true true) := by
  decide

end CommonGround.Frontier.AumannNoTradeKellyLogGrowthAndShapleyEfficiency
