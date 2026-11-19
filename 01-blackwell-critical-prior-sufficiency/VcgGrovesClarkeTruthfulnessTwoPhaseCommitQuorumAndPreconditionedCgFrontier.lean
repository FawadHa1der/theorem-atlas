/-
  01-blackwell-critical-prior-sufficiency/VcgGrovesClarkeTruthfulnessTwoPhaseCommitQuorumAndPreconditionedCgFrontier.lean

  Frontier #128: Vickrey–Clarke–Groves (VCG) Dominant-Strategy Truthfulness vs. Collusion &
  Budget Deficit, Distributed Two-Phase Commit (2PC) Uncertainty Blocking vs. Quorum Intersection,
  and Spectral Preconditioning (κ(P⁻¹A) = 1) vs. Ill-Conditioned Gradient-Descent Zig-Zagging.

  Zero `sorry`, zero `admit`, zero custom axioms — pure Lean 4.33.0 core.
-/

namespace VcgGrovesClarkeTwoPhaseCommitAndPreconditionedCgFrontier

/-!
## Part I: Vickrey–Clarke–Groves (VCG) Clarke-Pivot Dominant-Strategy Truthfulness
vs. Two-Bidder Collusion & Green–Laffont Public-Good Budget Deficit
-/

/-- Clarke pivot payment charged to bidder `i` at chosen outcome `k`:
    `p_i(k) = M_others - W_others(k)`, where `M_others` is the best welfare achievable
    by the remaining agents without `i` (independent of `i`'s report). -/
def clarkePayment {K : Nat} (M_others : Int) (W_others : Fin K → Int) (k : Fin K) : Int :=
  M_others - W_others k

/-- Quasilinear utility of bidder `i` with true valuation `v_i` under Clarke payment. -/
def vcgUtility {K : Nat} (v_i : Fin K → Int) (M_others : Int) (W_others : Fin K → Int) (k : Fin K) : Int :=
  v_i k - clarkePayment M_others W_others k

/-- **Theorem 1a (Universal VCG / Clarke-Pivot Dominant-Strategy Truthfulness)**:
    Because `vcgUtility v_i M_others W_others k = (v_i k + W_others k) - M_others` aligns
    individual payoff up to the report-independent constant `-M_others` with total social
    surplus, any surplus-maximizing outcome `k_truth` chosen under truthful reporting `v_i`
    weakly dominates *every* outcome `k_mis` achievable by any strategic misreport `b_i`. -/
theorem vcg_clarke_dominant_strategy_truthfulness
    {K : Nat} (v_i W_others : Fin K → Int) (M_others : Int)
    (k_truth k_mis : Fin K)
    (hEfficient : v_i k_mis + W_others k_mis ≤ v_i k_truth + W_others k_truth) :
    vcgUtility v_i M_others W_others k_mis ≤ vcgUtility v_i M_others W_others k_truth := by
  unfold vcgUtility clarkePayment
  omega

/-- Second-price (Vickrey) single-item auction for 3 bidders with deterministic tie-breaking
    toward lower index: returns `(winnerIdx, pricePaid)`. -/
def vickreyAuction3 (b0 b1 b2 : Int) : Nat × Int :=
  if b0 ≥ b1 ∧ b0 ≥ b2 then
    (0, if b1 ≥ b2 then b1 else b2)
  else if b1 ≥ b2 then
    (1, if b0 ≥ b2 then b0 else b2)
  else
    (2, if b0 ≥ b1 then b0 else b1)

/-- Joint utility of coalition `{0, 1}` with true values `(v0, v1)` under outcome `(winner, price)`. -/
def coalition01Utility (v0 v1 : Int) (out : Nat × Int) : Int :=
  if out.1 = 0 then v0 - out.2
  else if out.1 = 1 then v1 - out.2
  else 0

/-- **Premise-Failure Counterexample 1b (VCG Vulnerability to Two-Bidder Bidding-Ring Collusion)**:
    With true valuations `(v0, v1, v2) = (10, 9, 2)`, truthful bidding `(10, 9, 2)` awards the item
    to bidder `0` at Clarke price `9`, yielding coalition `{0, 1}` utility `10 - 9 = 1`.
    When bidders `0` and `1` collude via `(10, 0, 2)` (bidder `1` suppresses its bid), bidder `0`
    still wins while Clarke price collapses to `2`, jumping coalition `{0, 1}` utility `1 → 8`! -/
theorem vcg_two_bidder_collusion_breaks_group_strategyproofness :
    vickreyAuction3 10 9 2 = (0, 9) ∧
    coalition01Utility 10 9 (vickreyAuction3 10 9 2) = 1 ∧
    vickreyAuction3 10 0 2 = (0, 2) ∧
    coalition01Utility 10 9 (vickreyAuction3 10 0 2) = 8 ∧
    coalition01Utility 10 9 (vickreyAuction3 10 0 2) >
      coalition01Utility 10 9 (vickreyAuction3 10 9 2) := by
  decide

/-- Clarke pivotal tax for a binary public project of cost `cost` with two bidders `(b0, b1)`:
    built iff `b0 + b1 ≥ cost`; bidder `i` pays `max(0, cost - b_{-i})` when built. -/
def publicGoodClarkeTaxes (cost b0 b1 : Int) : Bool × Int × Int :=
  if b0 + b1 ≥ cost then
    let t0 := if cost - b1 > 0 then cost - b1 else 0
    let t1 := if cost - b0 > 0 then cost - b0 else 0
    (true, t0, t1)
  else
    (false, 0, 0)

/-- **Premise-Failure Counterexample 1c (Green–Laffont Public-Good VCG Budget Deficit)**:
    For a public project of cost `C = 10` with true valuations `(v0, v1) = (7, 7)` (`14 > 10`),
    VCG efficiently builds the project (`true`), charges each pivotal agent `10 - 7 = 3`,
    and collects total tax `3 + 3 = 6 < 10` — leaving an uncovered `-4` budget deficit! -/
theorem vcg_public_good_green_laffont_budget_deficit :
    publicGoodClarkeTaxes 10 7 7 = (true, 3, 3) ∧
    (3 + 3 : Int) < 10 := by
  decide

/-!
## Part II: Distributed Two-Phase Commit (2PC) Coordinator-Crash Blocking Impossibility
vs. Majority Quorum Pigeonhole Intersection (`2|Q₁| > N ∧ 2|Q₂| > N ⟹ Q₁ ∩ Q₂ ≠ ∅`)
-/

/-- **Theorem 2a (Universal Pigeonhole Quorum Intersection Law)**:
    On `N` replicas, if quorum `Q₁` has size `q1` (`2 * q1 > N`), quorum `Q₂` has size `q2`
    (`2 * q2 > N`), and inclusion-exclusion bounds `q1 + q2 ≤ N + qInter`, then their
    intersection size `qInter` is strictly positive (`qInter ≥ 1`). -/
theorem majority_quorum_pigeonhole_intersection
    (N q1 q2 qInter : Nat)
    (hMaj1 : 2 * q1 > N)
    (hMaj2 : 2 * q2 > N)
    (hIncExc : q1 + q2 ≤ N + qInter) :
    qInter ≥ 1 := by
  omega

/-- Subset popcount for a 5-bit mask `m : Fin 32` representing `Q ⊆ Fin 5`. -/
def maskPopcount5 (m : Fin 32) : Nat :=
  let v := m.val
  (v % 2) + ((v / 2) % 2) + ((v / 4) % 2) + ((v / 8) % 2) + ((v / 16) % 2)

/-- Exhaustive check over all `32 × 32 = 1,024` subset pairs of `Fin 5`: every pair of
    majority quorums (`popcount ≥ 3`) shares at least one replica (`(m1 &&& m2) ≠ 0`). -/
def allFiveNodeMajoritiesIntersect : Bool :=
  (List.finRange 32).all fun m1 =>
    (List.finRange 32).all fun m2 =>
      if maskPopcount5 m1 ≥ 3 ∧ maskPopcount5 m2 ≥ 3 then
        decide ((m1.val &&& m2.val) > 0)
      else
        true

theorem five_replica_majority_quorums_all_intersect :
    allFiveNodeMajoritiesIntersect = true := by
  decide

/-- `2PC` global scenario `(vote0, vote1, coordinatorCrashedAfterLogging)` where cohort `1` voted
    `Yes` (`true`) and observed a timeout before receiving `Commit`/`Abort`. -/
structure TwoPcTimeoutWorld where
  vote0 : Bool
  vote1 : Bool
  globalDecision : Bool

def worldCommitCrash : TwoPcTimeoutWorld :=
  { vote0 := true, vote1 := true, globalDecision := true }

def worldAbortCrash : TwoPcTimeoutWorld :=
  { vote0 := false, vote1 := true, globalDecision := false }

/-- Cohort `1`'s local view upon coordinator + cohort `0` crash: only `vote1` is observable. -/
def cohort1LocalView (w : TwoPcTimeoutWorld) : Bool := w.vote1

/-- **Premise-Failure Theorem 2b (Skeen's 2PC Uncertainty-Window Blocking Impossibility)**:
    Cohort `1` has the *exact same* local view (`true`) in `worldCommitCrash` (where `vote0 = true`
    and the coordinator logged `Commit` before crashing) and `worldAbortCrash` (where `vote0 = false`
    and the coordinator logged `Abort` before crashing). Consequently, *no* non-blocking local timeout
    function `f : Bool → Bool` can agree with `globalDecision` in both worlds! -/
theorem two_phase_commit_uncertainty_window_blocking_impossibility :
    cohort1LocalView worldCommitCrash = cohort1LocalView worldAbortCrash ∧
    ∀ (f : Bool → Bool),
      ¬ (f (cohort1LocalView worldCommitCrash) = worldCommitCrash.globalDecision ∧
         f (cohort1LocalView worldAbortCrash) = worldAbortCrash.globalDecision) := by
  refine ⟨rfl, ?_⟩
  intro f ⟨hC, hA⟩
  have hEq : f true = true ∧ f true = false := ⟨hC, hA⟩
  cases h : f true
  · rw [h] at hEq
    exact Bool.noConfusion hEq.1
  · rw [h] at hEq
    exact Bool.noConfusion hEq.2

/-!
## Part III: Spectral Condition-Number Collapse (`κ(P⁻¹A) = 1`) vs. Ill-Conditioned
Gradient-Descent Zig-Zagging (`ρ = (κ-1)/(κ+1) = 49/50`) & Oversize-Step Divergence
-/

/-- Anisotropic quadratic objective `2·E(x,y) = λ₁ x² + λ₂ y²` with `λ₁ = 1, λ₂ = 99` (`κ = 99`). -/
def quadEnergy1_99 (p : Int × Int) : Int :=
  1 * p.1 * p.1 + 99 * p.2 * p.2

/-- Exact integer-scaled gradient descent step with optimal scalar step `α* = 2/(1+99) = 1/50`
    evaluated on `50`-divisible grid points: `(x, y) ↦ (x - (2·1·x)/100, y - (2·99·y)/100)`. -/
def optimalScalarGdStep50 (p : Int × Int) : Int × Int :=
  (p.1 - (1 * p.1) / 50, p.2 - (99 * p.2) / 50)

/-- Oversize scalar step `α = 1/40 > 2/(1+99) = 1/50` evaluated on `40`-divisible grid points. -/
def oversizeScalarGdStep40 (p : Int × Int) : Int × Int :=
  (p.1 - (1 * p.1) / 40, p.2 - (99 * p.2) / 40)

/-- Diagonal / Newton-Jacobi preconditioned step `p_{t+1} = p_t - P⁻¹ ∇E(p_t)` where
    `P = diag(λ₁, λ₂)` cancels anisotropic curvature `(λ₁ x / λ₁, λ₂ y / λ₂) = (x, y)` (`κ(P⁻¹A) = 1`). -/
def preconditionedJacobiNewtonStep (lam1 lam2 : Int) (_h1 : lam1 ≠ 0) (_h2 : lam2 ≠ 0) (p : Int × Int) : Int × Int :=
  (p.1 - (lam1 * p.1) / lam1, p.2 - (lam2 * p.2) / lam2)

/-- **Theorem 3a (Universal 1-Step Exact Convergence of Metric-Preconditioned Descent)**:
    For every nonzero curvature pair `(lam1, lam2)` and *every* initial state `(x0, y0) ∈ ℤ²`,
    metric preconditioning `P = diag(lam1, lam2)` collapses `κ(P⁻¹A) = 1` and lands at the
    exact global minimizer `(0, 0)` in a single step! -/
theorem preconditioned_jacobi_newton_one_step_universal
    (lam1 lam2 : Int) (h1 : lam1 ≠ 0) (h2 : lam2 ≠ 0) (p : Int × Int) :
    preconditionedJacobiNewtonStep lam1 lam2 h1 h2 p = (0, 0) := by
  unfold preconditionedJacobiNewtonStep
  rw [Int.mul_ediv_cancel_left _ h1, Int.mul_ediv_cancel_left _ h2]
  simp [Int.sub_self]

/-- **Premise-Failure Theorem 3b (Ill-Conditioned `κ = 99` GD `49/50` Crawl & `α = 1/40` Explosion)**:
    1. Under optimal scalar step `α* = 1/50`, `(50, 50) ↦ (49, -49)`: stiff axis flips sign and
       retains `49/50 = 98%` amplitude (`quadEnergy1_99 (49, -49) = 240,100` vs `0` preconditioned!).
    2. Slightly increasing step size to `α = 1/40 > 1/50` maps `(40, 40) ↦ (39, -59)`, strictly
       *amplifying* stiff error `|-59| = 59 > 40` and blowing up energy `160,000 → 346,140`! -/
theorem ill_conditioned_gd_zigzag_and_oversize_step_explosion :
    optimalScalarGdStep50 (50, 50) = (49, -49) ∧
    quadEnergy1_99 (50, 50) = 250000 ∧
    quadEnergy1_99 (optimalScalarGdStep50 (50, 50)) = 240100 ∧
    oversizeScalarGdStep40 (40, 40) = (39, -59) ∧
    quadEnergy1_99 (40, 40) = 160000 ∧
    quadEnergy1_99 (oversizeScalarGdStep40 (40, 40)) = 346140 ∧
    quadEnergy1_99 (oversizeScalarGdStep40 (40, 40)) > quadEnergy1_99 (40, 40) := by
  decide

/-- **Master Frontier #128 Synthesis Theorem** -/
theorem master_vcg_truthfulness_twopc_quorum_and_preconditioned_cg_frontier :
    vickreyAuction3 10 9 2 = (0, 9) ∧
    vickreyAuction3 10 0 2 = (0, 2) ∧
    publicGoodClarkeTaxes 10 7 7 = (true, 3, 3) ∧
    allFiveNodeMajoritiesIntersect = true ∧
    cohort1LocalView worldCommitCrash = cohort1LocalView worldAbortCrash ∧
    optimalScalarGdStep50 (50, 50) = (49, -49) ∧
    oversizeScalarGdStep40 (40, 40) = (39, -59) ∧
    preconditionedJacobiNewtonStep 1 99 (by decide) (by decide) (50, 50) = (0, 0) := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, by decide, by decide, ?_⟩
  exact preconditioned_jacobi_newton_one_step_universal 1 99 (by decide) (by decide) (50, 50)

end VcgGrovesClarkeTwoPhaseCommitAndPreconditionedCgFrontier
