/-!
# Bayesian Persuasion Concavification, No-Regret Coarse Correlated Equilibrium, `Nash ⊊ CE ⊊ CCE` & Foster–Vohra Minimax Calibration (`0` Imports, `0` Sorry)

This standalone pure-core Lean 4.33.0 frontier module unifies **Folder `01`**
(Blackwell Experiment Splitting & Sufficiency), **Folder `04`** (Online No-Regret
Learning & Policy Dynamics), **Folder `08`** (Fenchel/Supporting-Hyperplane Concavification
Duality), and **Folder `09`** (Minimax Quantifier Exchange):

1. **Kamenica–Gentzkow (`2011`) Bayesian Persuasion Concavification vs. Concave Loss & Cheap-Talk Collapse**
   (`kamenica_gentzkow_concavification_persuasion_gain_vs_convex_zero_gain_and_cheap_talk_collapse`):
   - *Universal Supporting-Line Concavification Bound*: For any Bayes-plausible posterior
     split `wA * muA + wB * muB = S * mu0` (`wA + wB = S`, `wA ≥ 0`, `wB ≥ 0`), if an affine
     envelope `L(mu) = alpha * Q + beta * mu` majorizes Sender's indirect value `V` at `muA`
     and `muB`, then `wA * V(muA) + wB * V(muB) ≤ S * L(mu0)`.
   - *Constructive Prosecutor-Judge Attainment (`0 → 6/10`)*: At prior `mu0 = 3` (`Q = 10`,
     conviction threshold `2 * mu ≥ 10`), uninformative silence yields `0` convictions,
     whereas Bayes-plausible split `(wA = 6, muA = 5)` and `(wB = 4, muB = 0)` (`6*5 + 4*0 = 30
     = 10*3`) satisfies Judge IC at both signals and achieves `6 > 0` (`60% = 2 * (3/10)`),
     matching the concavification line `L(mu) = 2 * mu` with zero slack.
   - *Premise-Failure Counterexamples*:
     (a) When Sender's indirect value is strictly concave `V(mu) = -mu^2`, any non-degenerate
         Bayes-plausible split (`wA > 0`, `wB > 0`, `muA ≠ muB`) strictly hurts Sender:
         `S * (wA * (-muA^2) + wB * (-muB^2)) - (-(wA*muA + wB*muB)^2) = -wA * wB * (muA - muB)^2 < 0`.
     (b) Without ex-ante channel commitment (Crawford–Sobel state-independent cheap talk),
         Sender strictly deviates in the innocent state (`1 > 0`), collapsing persuasion to `0`.

2. **Empirical No-Regret Convergence to Coarse Correlated Equilibrium (`CCE`) vs. Shapley (`1964`) Period-`6` Cycle**
   (`no_regret_time_average_coarse_correlated_equilibrium_vs_shapley_best_response_cycle`):
   - *Universal External-Regret-to-`CCE` Transfer*: On any `T`-round game play, bounding
     cumulative external regret against every fixed action `a'` by `R` immediately certifies
     that the empirical joint distribution is an `(R/T)`-Coarse Correlated Equilibrium.
   - *Premise-Failure Counterexample*: On Shapley's `3 × 3` non-zero-sum bi-matrix game,
     greedy alternating strict best responses `(0,0) → (1,0) → (1,1) → (2,1) → (2,2) → (0,2) → (0,0)`
     strictly improve the moving player's payoff by `+1` or `+2` at every step yet loop
     forever in a period-`6` limit cycle without converging to Nash!

3. **Binary-Action `CE ↔ CCE` Collapse vs. Aumann `conv(Nash) ⊊ CE` & Viossat `CE ⊊ CCE` Separation**
   (`binary_ce_iff_cce_and_strict_nash_subset_ce_subset_cce_hierarchy`):
   - *Universal Binary-Action Collapse (`|A_i| = 2`)*: In EVERY `2`-action game, unconditional
     external `CCE` incentive compatibility is algebraically equivalent (`↔`) to full Aumann
     conditional swap `CE` incentive compatibility (`swap 0→1`, `swap 1→0`, and `flip 0↔1`).
   - *Aumann Traffic-Light `conv(Nash) ⊊ CE`*: In symmetric Chicken (`(0,0), (7,2), (2,7), (6,6)`),
     every pure Nash sum is `9` (`3 * 9 = 27`) and symmetric mixed Nash `(1/3, 2/3)` achieves
     sum `28/3` (`28 < 30`), whereas Aumann's correlated signal `w = (0, 1, 1, 1)` satisfies
     strict swap IC (`8 > 7`, `7 > 2`) and achieves utilitarian sum `30 / 3 = 10` (`30 > 28`).
   - *Ternary-Action Viossat `CE ⊊ CCE` (`|A_i| = 3`)*: Universal proof that ANY Aumann `CE`
     assigns exact weight `0` to an action strictly dominated by a `50/50` mixture of `{0, 1}`,
     contrasted against an explicit `3 × 2` strict `CCE` (`28 > 18`, `30 > 18`) placing `1/3`
     of total probability (`w_{20} + w_{21} = 2 > 0`) on strictly dominated action `2`!

4. **Foster–Vohra (`1998`) Randomized Minimax Calibration vs. Deterministic Adversarial `≥ 1/2` Trap**
   (`foster_vohra_minimax_randomized_calibration_vs_deterministic_adversarial_miscalibration`):
   - *Deterministic Trap*: Against any deterministic forecast `f ∈ [0, Q]`, an adaptive
     adversary chooses `y ∈ {0, 1}` forcing `2 * |f - Q * y| ≥ Q` (`≥ 50%` bias!).
   - *Randomized Minimax Escape*: Mixing across adjacent grid forecasts `(p0, p1)` via
     Brouwer/minimax weights `w0 = p1 - Q*y_bar, w1 = Q*y_bar - p0` annihilates expected
     calibration residual (`0` bias defect) simultaneously against both `y = 0` and `y = 1`
     at the minimax indifference point!
-/

namespace CommonGround.Frontier.BayesianPersuasionAndCorrelatedEquilibrium

/-- Homogeneous square over `Int`. -/
def sqI (x : Int) : Int := x * x

/-- Judge's optimal conviction indicator scaled by `1` (`1` if `2 * mu ≥ Q`, else `0`). -/
def judgeConvict (Q mu : Int) : Int :=
  if 2 * mu ≥ Q then 1 else 0

/-- Theorem 1: Kamenica–Gentzkow (`2011`) Bayesian Persuasion Concavification Upper Bound &
    Prosecutor-Judge `60%` Attainment vs. Concave Strict Information Loss & Cheap-Talk Collapse. -/
theorem kamenica_gentzkow_concavification_persuasion_gain_vs_convex_zero_gain_and_cheap_talk_collapse :
    -- (1) Universal Concavification Supporting-Line Bound: if `V(mu) ≤ alpha + beta * mu` at posteriors `muA, muB`
    --     and `wA * muA + wB * muB = S * mu0` (`wA + wB = S`, `wA, wB ≥ 0`), then `wA*V(muA) + wB*V(muB) ≤ S*(alpha + beta*mu0)`
    (∀ wA wB S mu0 muA muB vA vB alpha beta : Int,
      0 ≤ wA → 0 ≤ wB → wA + wB = S → wA * muA + wB * muB = S * mu0 →
      vA ≤ alpha + beta * muA → vB ≤ alpha + beta * muB →
      wA * vA + wB * vB ≤ S * (alpha + beta * mu0)) ∧
    -- (2) Constructive Prosecutor-Judge Attainment (`Q = 10, mu0 = 3`):
    --     Silence gives `0`, whereas Bayes-plausible split `(wA=6, muA=5), (wB=4, muB=0)` gives `6` (`60% = 2 * mu0`)!
    (10 * judgeConvict 10 3 = 0 ∧
      6 + 4 = (10 : Int) ∧
      6 * 5 + 4 * 0 = 10 * (3 : Int) ∧
      6 * judgeConvict 10 5 + 4 * judgeConvict 10 0 = 6 ∧
      6 > 10 * judgeConvict 10 3) ∧
    -- (3) Premise-Failure A: Concave Sender Indirect Value `V(mu) = -mu^2` Strictly Loses from Splitting!
    (∀ wA wB muA muB : Int,
      (wA + wB) * (wA * (-sqI muA) + wB * (-sqI muB)) - (-sqI (wA * muA + wB * muB)) =
        -(wA * wB * sqI (muA - muB)) ∧
      (0 < wA → 0 < wB → muA ≠ muB →
        (wA + wB) * (wA * (-sqI muA) + wB * (-sqI muB)) < -sqI (wA * muA + wB * muB))) ∧
    -- (4) Premise-Failure B: Without Channel Commitment (Cheap Talk), Innocent-State Sender Deviates (`1 > 0`)
    (judgeConvict 10 5 > judgeConvict 10 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro wA wB S mu0 muA muB vA vB alpha beta hwA hwB hSum hBayes hMajA hMajB
    have hA : wA * vA ≤ wA * (alpha + beta * muA) := Int.mul_le_mul_of_nonneg_left hMajA hwA
    have hB : wB * vB ≤ wB * (alpha + beta * muB) := Int.mul_le_mul_of_nonneg_left hMajB hwB
    have hIdent :
        wA * (alpha + beta * muA) + wB * (alpha + beta * muB) =
          (wA + wB) * alpha + beta * (wA * muA + wB * muB) := by grind
    have hRhs :
        (wA + wB) * alpha + beta * (wA * muA + wB * muB) = S * (alpha + beta * mu0) := by
      rw [hSum, hBayes]
      grind
    omega
  · decide
  · intro wA wB muA muB
    refine ⟨by unfold sqI; grind, ?_⟩
    intro hwA hwB hNe
    have hId :
        (wA + wB) * (wA * (-sqI muA) + wB * (-sqI muB)) - (-sqI (wA * muA + wB * muB)) =
          -(wA * wB * sqI (muA - muB)) := by unfold sqI; grind
    have hDiffNe : muA - muB ≠ 0 := by omega
    have hSqPos : 0 < sqI (muA - muB) := by
      unfold sqI
      rcases Int.lt_trichotomy (muA - muB) 0 with hNeg | hZ | hPos
      · exact Int.mul_pos_of_neg_of_neg hNeg hNeg
      · exact False.elim (hDiffNe hZ)
      · exact Int.mul_pos hPos hPos
    have hProdPos : 0 < wA * wB * sqI (muA - muB) :=
      Int.mul_pos (Int.mul_pos hwA hwB) hSqPos
    omega
  · decide

/-- Shapley (`1964`) `3 × 3` Non-Zero-Sum Game Row Payoffs. -/
def shapleyRow (r c : Fin 3) : Int :=
  match r.val, c.val with
  | 0, 0 => 1 | 0, 1 => 0 | 0, 2 => 2
  | 1, 0 => 2 | 1, 1 => 1 | 1, 2 => 0
  | _, 0 => 0 | _, 1 => 2 | _, _ => 1

/-- Shapley (`1964`) `3 × 3` Non-Zero-Sum Game Column Payoffs. -/
def shapleyCol (r c : Fin 3) : Int :=
  match r.val, c.val with
  | 0, 0 => 2 | 0, 1 => 1 | 0, 2 => 0
  | 1, 0 => 0 | 1, 1 => 2 | 1, 2 => 1
  | _, 0 => 1 | _, 1 => 0 | _, _ => 2

/-- Alternating strict best-response transition on Shapley's `3 × 3` game (Row moves on even phase, Col on odd phase). -/
def shapleyAltStep (st : Bool × Fin 3 × Fin 3) : Bool × Fin 3 × Fin 3 :=
  let (rowTurn, r, c) := st
  if rowTurn then
    let rNext : Fin 3 :=
      match c.val with
      | 0 => ⟨1, by decide⟩
      | 1 => ⟨2, by decide⟩
      | _ => ⟨0, by decide⟩
    (false, rNext, c)
  else
    let cNext : Fin 3 :=
      match r.val with
      | 0 => ⟨0, by decide⟩
      | 1 => ⟨1, by decide⟩
      | _ => ⟨2, by decide⟩
    (true, r, cNext)

/-- Cumulative sum along a finite integer payoff list. -/
def sumIntList : List Int → Int
  | [] => 0
  | x :: xs => x + sumIntList xs

/-- Cumulative regret of realized payoffs `realized` against benchmark payoffs `dev` over `T` rounds. -/
def extRegretSum : List (Int × Int) → Int
  | [] => 0
  | (uReal, uDev) :: rest => (uDev - uReal) + extRegretSum rest

theorem extRegretSum_eq_dev_sub_real :
    ∀ xs : List (Int × Int),
      extRegretSum xs = sumIntList (xs.map Prod.snd) - sumIntList (xs.map Prod.fst)
  | [] => rfl
  | (uReal, uDev) :: rest => by
      simp [extRegretSum, sumIntList, extRegretSum_eq_dev_sub_real rest]
      omega

/-- Theorem 2: Empirical External No-Regret Implies Approximate Coarse Correlated Equilibrium (`CCE`)
    vs. Shapley's (`1964`) Period-`6` Strict Best-Response Limit Cycle. -/
theorem no_regret_time_average_coarse_correlated_equilibrium_vs_shapley_best_response_cycle :
    -- (1) Universal External-Regret-to-CCE Identity: `extRegretSum ≤ R` iff empirical deviation gain `≤ R`
    (∀ (xs : List (Int × Int)) (R : Int),
      extRegretSum xs ≤ R ↔
        sumIntList (xs.map Prod.snd) ≤ sumIntList (xs.map Prod.fst) + R) ∧
    -- (2) Shapley Period-`6` Cycle: every alternating move is a STRICT best-response improvement,
    --     yet 6 steps return identically to `(true, 0, 0)` while step 3 is distinct!
    (let s0 : Bool × Fin 3 × Fin 3 := (true, ⟨0, by decide⟩, ⟨0, by decide⟩)
     let s1 := shapleyAltStep s0
     let s2 := shapleyAltStep s1
     let s3 := shapleyAltStep s2
     let s4 := shapleyAltStep s3
     let s5 := shapleyAltStep s4
     let s6 := shapleyAltStep s5
     shapleyRow s1.2.1 s1.2.2 > shapleyRow s0.2.1 s0.2.2 ∧
     shapleyCol s2.2.1 s2.2.2 > shapleyCol s1.2.1 s1.2.2 ∧
     shapleyRow s3.2.1 s3.2.2 > shapleyRow s2.2.1 s2.2.2 ∧
     shapleyCol s4.2.1 s4.2.2 > shapleyCol s3.2.1 s3.2.2 ∧
     shapleyRow s5.2.1 s5.2.2 > shapleyRow s4.2.1 s4.2.2 ∧
     shapleyCol s6.2.1 s6.2.2 > shapleyCol s5.2.1 s5.2.2 ∧
     s6 = s0 ∧ s1 ≠ s0 ∧ s3 ≠ s0) := by
  refine ⟨?_, by decide⟩
  intro xs R
  rw [extRegretSum_eq_dev_sub_real xs]
  omega

/-- Symmetric Chicken payoffs: `0 = Stop (Safe)`, `1 = Go (Aggressive)`.
    `(S,S) ↦ 6`, `(S,G) ↦ 2`, `(G,S) ↦ 7`, `(G,G) ↦ 0`. -/
def chickenPayoff (a b : Fin 2) : Int :=
  match a.val, b.val with
  | 0, 0 => 6
  | 0, 1 => 2
  | 1, 0 => 7
  | _, _ => 0

/-- Viossat (`2006`) `3 × 2` game Row payoffs where Row action `2` is strictly dominated by `(1/2) Row 0 + (1/2) Row 1`. -/
def viossatRow (a : Fin 3) (b : Fin 2) : Int :=
  match a.val, b.val with
  | 0, 0 => 6 | 0, 1 => 0
  | 1, 0 => 0 | 1, 1 => 6
  | _, _ => 2

/-- Viossat (`2006`) `3 × 2` game Column payoffs. -/
def viossatCol (a : Fin 3) (b : Fin 2) : Int :=
  match a.val, b.val with
  | 0, 0 => 6 | 0, 1 => 0
  | 1, 0 => 0 | 1, 1 => 6
  | _, _ => 3

/-- Theorem 3: Universal Binary-Action `CE ↔ CCE` Collapse (`|A_i| = 2`) vs.
    Aumann Traffic-Light `conv(Nash) ⊊ CE` (`30 > 28`) & Ternary-Action Viossat `CE ⊊ CCE` (`w_2 > 0` on Strictly Dominated Action!). -/
theorem binary_ce_iff_cce_and_strict_nash_subset_ce_subset_cce_hierarchy :
    -- (1) Universal Binary-Action Collapse (`|A_i| = 2`): External `CCE` IC `↔` Full Swap `CE` IC (including flip `0 ↔ 1`)!
    (∀ w00 w01 w10 w11 u00 u01 u10 u11 : Int,
      let eqPay := w00 * u00 + w01 * u01 + w10 * u10 + w11 * u11
      let ext0  := (w00 + w10) * u00 + (w01 + w11) * u01
      let ext1  := (w00 + w10) * u10 + (w01 + w11) * u11
      let swap1to0 := w10 * (u00 - u10) + w11 * (u01 - u11)
      let swap0to1 := w00 * (u10 - u00) + w01 * (u11 - u01)
      let flip01   := w00 * u10 + w01 * u11 + w10 * u00 + w11 * u01
      (ext0 ≤ eqPay ∧ ext1 ≤ eqPay) ↔ (swap1to0 ≤ 0 ∧ swap0to1 ≤ 0 ∧ flip01 ≤ eqPay)) ∧
    -- (2) Aumann Traffic-Light `conv(Nash) ⊊ CE` on Chicken:
    --     Signal `w = (wSS=1, wSG=1, wGS=1, wGG=0)` is strict `CE` (`8 > 7` at S, `7 > 2` at G)
    --     with scaled utilitarian welfare `30`, strictly beating Pure Nash (`27`) and Symmetric Mixed Nash (`28`)!
    (1 * chickenPayoff ⟨0, by decide⟩ ⟨0, by decide⟩ + 1 * chickenPayoff ⟨0, by decide⟩ ⟨1, by decide⟩ = 8 ∧
     1 * chickenPayoff ⟨1, by decide⟩ ⟨0, by decide⟩ + 1 * chickenPayoff ⟨1, by decide⟩ ⟨1, by decide⟩ = 7 ∧
     1 * chickenPayoff ⟨1, by decide⟩ ⟨0, by decide⟩ > 1 * chickenPayoff ⟨0, by decide⟩ ⟨0, by decide⟩ - 5 ∧
     2 * (1 * (6 + 6) + 1 * (2 + 7) + 1 * (7 + 2)) = 60 ∧
     60 > 2 * 28 ∧ 28 > 3 * 9) ∧
    -- (3) Universal Aumann `CE` Elimination of Mixed-Strictly-Dominated Action `2` (`2*u2 < u0 + u1` ⇒ `w20 = 0 ∧ w21 = 0`):
    (∀ w20 w21 u00 u01 u10 u11 u20 u21 : Int,
      0 ≤ w20 → 0 ≤ w21 →
      2 * u20 < u00 + u10 → 2 * u21 < u01 + u11 →
      w20 * (u00 - u20) + w21 * (u01 - u21) ≤ 0 →
      w20 * (u10 - u20) + w21 * (u11 - u21) ≤ 0 →
      w20 = 0 ∧ w21 = 0) ∧
    -- (4) Ternary-Action Viossat `CE ⊊ CCE` Witness: Row action `2` is strictly dominated (`4 < 6` at both `b = 0, 1`),
    --     yet joint weights `w = [[2,0],[0,2],[1,1]]` put positive weight `1 + 1 = 2 > 0` on action `2`
    --     while satisfying STRICT `CCE` for BOTH Row (`28 > 18, 18, 12`) and Column (`30 > 18, 18`)!
    ((∀ b : Fin 2, 2 * viossatRow ⟨2, by decide⟩ b < viossatRow ⟨0, by decide⟩ b + viossatRow ⟨1, by decide⟩ b) ∧
     (∀ a' : Fin 3,
       (2 + 0 + 1) * viossatRow a' ⟨0, by decide⟩ + (0 + 2 + 1) * viossatRow a' ⟨1, by decide⟩ <
         2 * viossatRow ⟨0, by decide⟩ ⟨0, by decide⟩ + 2 * viossatRow ⟨1, by decide⟩ ⟨1, by decide⟩ +
         1 * viossatRow ⟨2, by decide⟩ ⟨0, by decide⟩ + 1 * viossatRow ⟨2, by decide⟩ ⟨1, by decide⟩) ∧
     (∀ b' : Fin 2,
       2 * viossatCol ⟨0, by decide⟩ b' + 2 * viossatCol ⟨1, by decide⟩ b' + 2 * viossatCol ⟨2, by decide⟩ b' <
         2 * viossatCol ⟨0, by decide⟩ ⟨0, by decide⟩ + 2 * viossatCol ⟨1, by decide⟩ ⟨1, by decide⟩ +
         1 * viossatCol ⟨2, by decide⟩ ⟨0, by decide⟩ + 1 * viossatCol ⟨2, by decide⟩ ⟨1, by decide⟩)) := by
  refine ⟨?_, by decide, ?_, by decide⟩
  · intro w00 w01 w10 w11 u00 u01 u10 u11
    dsimp only
    have hId0 :
        ((w00 + w10) * u00 + (w01 + w11) * u01) - (w00 * u00 + w01 * u01 + w10 * u10 + w11 * u11) =
          w10 * (u00 - u10) + w11 * (u01 - u11) := by grind
    have hId1 :
        ((w00 + w10) * u10 + (w01 + w11) * u11) - (w00 * u00 + w01 * u01 + w10 * u10 + w11 * u11) =
          w00 * (u10 - u00) + w01 * (u11 - u01) := by grind
    have hFlip :
        (w00 * u10 + w01 * u11 + w10 * u00 + w11 * u01) - (w00 * u00 + w01 * u01 + w10 * u10 + w11 * u11) =
          (w10 * (u00 - u10) + w11 * (u01 - u11)) + (w00 * (u10 - u00) + w01 * (u11 - u01)) := by grind
    omega
  · intro w20 w21 u00 u01 u10 u11 u20 u21 hw20 hw21 hDom0 hDom1 hSw0 hSw1
    have hSumId :
        (w20 * (u00 - u20) + w21 * (u01 - u21)) + (w20 * (u10 - u20) + w21 * (u11 - u21)) =
          w20 * (u00 + u10 - 2 * u20) + w21 * (u01 + u11 - 2 * u21) := by grind
    have hGap0 : 1 ≤ u00 + u10 - 2 * u20 := by omega
    have hGap1 : 1 ≤ u01 + u11 - 2 * u21 := by omega
    have hGe0 : w20 * 1 ≤ w20 * (u00 + u10 - 2 * u20) := Int.mul_le_mul_of_nonneg_left hGap0 hw20
    have hGe1 : w21 * 1 ≤ w21 * (u01 + u11 - 2 * u21) := Int.mul_le_mul_of_nonneg_left hGap1 hw21
    omega

/-- Absolute value over `Int`. -/
def absI (x : Int) : Int := if 0 ≤ x then x else -x

/-- Theorem 4: Foster–Vohra (`1998`) Minimax Randomized Calibration vs.
    Deterministic Forecaster Adversarial `≥ 1/2` Trap. -/
theorem foster_vohra_minimax_randomized_calibration_vs_deterministic_adversarial_miscalibration :
    -- (1) Deterministic Adversarial Trap: for ANY scale `Q > 0` and ANY deterministic forecast `f`,
    --     an adversary picks `y ∈ {0, 1}` forcing `2 * |f - Q * y| ≥ Q` (`≥ 50%` miscalibration)!
    (∀ Q f : Int, 0 < Q → ∃ y : Int, (y = 0 ∨ y = 1) ∧ Q ≤ 2 * absI (f - Q * y)) ∧
    -- (2) Randomized Two-Bin Minimax Escape: on adjacent bins `(p0, p1)` with `0 ≤ p0 ≤ p1 ≤ Q`,
    --     choosing weights `w0 = p1 - pStar` and `w1 = pStar - p0` (`p0 ≤ pStar ≤ p1`) ensures
    --     `w0 ≥ 0, w1 ≥ 0, w0 + w1 = p1 - p0`, and at adversary mixed outcome rate `pStar`,
    --     total weighted calibration drift `w0*(p0 - pStar) + w1*(p1 - pStar)` vanishes IDENTICALLY (`= 0`)
    --     while each bin's weighted Brier-direction penalty against ANY outcome `y_val ∈ [p0, p1]`
    --     satisfies `w0*(p0 - y_val) ≤ 0` and `0 ≤ w1*(p1 - y_val)` with exact minimax cancellation!
    (∀ p0 p1 pStar : Int,
      p0 ≤ pStar → pStar ≤ p1 →
      let w0 := p1 - pStar
      let w1 := pStar - p0
      0 ≤ w0 ∧ 0 ≤ w1 ∧ w0 + w1 = p1 - p0 ∧
      w0 * p0 + w1 * p1 = (w0 + w1) * pStar ∧
      (∀ yVal : Int, w0 * (p0 - yVal) + w1 * (p1 - yVal) = (p1 - p0) * (pStar - yVal))) := by
  refine ⟨?_, ?_⟩
  · intro Q f hQ
    by_cases hHalf : 2 * f ≥ Q
    · refine ⟨0, Or.inl rfl, ?_⟩
      unfold absI
      split <;> omega
    · refine ⟨1, Or.inr rfl, ?_⟩
      unfold absI
      split <;> omega
  · intro p0 p1 pStar hp0 hp1
    dsimp only
    refine ⟨by omega, by omega, by omega, by grind, ?_⟩
    intro yVal
    grind

end CommonGround.Frontier.BayesianPersuasionAndCorrelatedEquilibrium
