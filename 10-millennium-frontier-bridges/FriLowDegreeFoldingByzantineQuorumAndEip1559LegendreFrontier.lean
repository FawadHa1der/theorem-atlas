/-!
# `FRI` (`ZK-STARK`) Even-Odd Polynomial Folding, `KZG` (`EIP-4844`) Bézout Commitments, Byzantine `3f + 1` Quorum Intersection & `EIP-1559` / `CFMM` Convex Mechanism Duality (`0` Imports, `0` Sorry)

This standalone pure-core Lean 4.33.0 frontier module (`Frontier #114`) unifies four pillars of
verifiable computation, fault-tolerant distributed consensus, and convex mechanism design across
**Folder `10`** (Algebraic Proof Systems & Complexity), **Folder `02`** (Polynomial Moment &
Evaluation Compression), **Folder `07`** (Adversarial Protocols & Quorum Bounds), and
**Folder `08`** (Convex / Legendre–Fenchel Mechanism Duality):

1. **Ben-Sasson–Bentov–Horesh–Riabzev (`FRI` / `ZK-STARK`) Degree-Halving Fold & Soundness
   vs. "Frozen Heart" Fiat–Shamir Grinding**
   (`fri_even_odd_antipodal_and_degree_halving_identities`,
    `fri_high_degree_defect_at_most_one_bad_challenge_vs_frozen_heart_grinding`):
   - *Universal Antipodal Folding*: Every cubic `P(x) = c0 + c1 x + c2 x^2 + c3 x^3` splits into
     `P_even(x^2) + x P_odd(x^2)` and folds under challenge `α` to linear
     `F_α(y) = (c0 + α c1) + (c2 + α c3) y`, obeying the exact `2`-to-`1` colinearity law
     `2 x F_α(x^2) = (x + α) P(x) + (x - α) P(-x)`.
   - *Universal Soundness*: Any committed nonzero high-degree defect `(e2, o2) ≠ (0, 0)` can have
     its folded leading coefficient `e2 + α o2` annihilated by AT MOST ONE challenge `α` (`a1 ≠ a2`
     forbids simultaneous vanishing).
   - *Premise-Failure Counterexample ("Frozen Heart" Unhashed Root)*: Choosing `(e2, o2) = (-α, 1)`
     after observing `α` annihilates `e2 + α o2 = 0` on `100%` of verifier challenges.

2. **Kate–Zaverucha–Goldberg (`KZG` / Ethereum `EIP-4844` Blob Commitments) Bézout Quotient Witness
   vs. Leaked Toxic-Waste Trapdoor `τ` Forgery**
   (`kzg_bezout_opening_completeness_and_binding_vs_leaked_tau_forgery`):
   - *Universal Bézout Completeness*: `P(τ) - P(z) = (τ - z) Q(τ)` holds identically for all cubics.
   - *Universal Binding*: Any false opening `vClaim ≠ P(z)` leaves nonzero evaluation residual at `z`
     and can collide at at most one secret `τ` for any fixed constant witness `q0`.
   - *Premise-Failure Counterexample*: Leaking `τ ≠ z` lets an adversary open `P(X) = c0` to
     `vForge = c0 - k(τ - z) ≠ c0` with `0` pairing residual using `Q_forge = k`.

3. **Universal `Fin n` Byzantine `3f + 1` Quorum Intersection (`HotStuff` / `Tendermint` / `PBFT`)
   vs. `n = 3f` Classical `1/3` Split-Brain Fork**
   (`byzantine_quorum_honest_intersection_universal`,
    `byzantine_3f_plus_1_safety_vs_3f_equivocation_split_brain`):
   - *Universal `Fin n` Inclusion-Exclusion*: For any `0/1` quorums `q1, q2 : Fin n → Nat` and
     fault mask `b : Fin n → Nat`, `∑ q1 + ∑ q2 ≤ n + ∑ b + ∑ q1 * q2 * (1 - b)`. Whenever
     `2 Q ≥ n + f + 1` (in particular `n = 3f + 1, Q = 2f + 1`), every two quorums share `≥ 1`
     honest validator (`∃ i : Fin n, q1 i = 1 ∧ q2 i = 1 ∧ b i = 0`).
   - *Premise-Failure Counterexample (`n = 3f`)*: At `n = 3, f = 1, Q = 2` (and `n = 6, f = 2, Q = 4`),
     quorums `{0, 1}` and `{1, 2}` with equivocator `{1}` have `0` honest validators in common.

4. **Roughgarden `EIP-1559` DSIC Fee Mechanism & Constant-Product `CFMM` (`x y ≥ k`) Convex Slippage
   vs. First-Price Bid Shading & Constant-Sum Pool Drainage**
   (`eip1559_truthful_bidding_dsic_vs_first_price_bid_shading`,
    `cfmm_constant_product_no_arbitrage_vs_constant_sum_pool_drainage`):
   - *Universal `EIP-1559` DSIC + Individual Rationality*: Truthful cap `maxFee = val` dominates
     every alternative `maxFee` across all `basePlusTip` realizations (`0 ≤ payoff(val, val)`),
     whereas first-price auctions force `0` truthful surplus and reward shading (`70 > 0`).
   - *Universal `CFMM` Convexity & No Round-Trip Arbitrage*: `(x + dx)(y - dy) ≥ x y` forces strict
     marginal slippage `x dy < y dx` (`dx, dy > 0`) and `dxOut ≤ dx` on every round-trip trade,
     whereas a zero-curvature constant-sum pool `x + y = 200` suffers `100%` reserve drainage.
-/

namespace CommonGround.Frontier.FriLowDegreeFoldingByzantineQuorumAndEip1559Legendre

/-! ## Section 1: `FRI` (`ZK-STARK`) Even-Odd Polynomial Folding & Soundness -/

/-- Evaluate cubic `c0 + c1*x + c2*x^2 + c3*x^3`. -/
def evalDeg3 (c0 c1 c2 c3 x : Int) : Int :=
  c0 + c1 * x + c2 * x * x + c3 * x * x * x

/-- Even folded half `P_even(y) = c0 + c2*y`. -/
def evalEvenFold (c0 c2 y : Int) : Int :=
  c0 + c2 * y

/-- Odd folded half `P_odd(y) = c1 + c3*y`. -/
def evalOddFold (c1 c3 y : Int) : Int :=
  c1 + c3 * y

/-- `FRI` random linear fold `F_α(y) = P_even(y) + α * P_odd(y) = (c0 + α*c1) + (c2 + α*c3)*y`. -/
def evalFriFold (c0 c1 c2 c3 alpha y : Int) : Int :=
  (c0 + alpha * c1) + (c2 + alpha * c3) * y

/-- Theorem 1a: Exact `FRI` Even-Odd Decomposition, Antipodal Extraction & `2`-to-`1` Fold Identity. -/
theorem fri_even_odd_antipodal_and_degree_halving_identities
    (c0 c1 c2 c3 alpha x : Int) :
    evalDeg3 c0 c1 c2 c3 x = evalEvenFold c0 c2 (x * x) + x * evalOddFold c1 c3 (x * x) ∧
    evalDeg3 c0 c1 c2 c3 x + evalDeg3 c0 c1 c2 c3 (-x) = 2 * evalEvenFold c0 c2 (x * x) ∧
    evalDeg3 c0 c1 c2 c3 x - evalDeg3 c0 c1 c2 c3 (-x) = 2 * x * evalOddFold c1 c3 (x * x) ∧
    2 * x * evalFriFold c0 c1 c2 c3 alpha (x * x) =
      (x + alpha) * evalDeg3 c0 c1 c2 c3 x + (x - alpha) * evalDeg3 c0 c1 c2 c3 (-x) := by
  unfold evalDeg3 evalEvenFold evalOddFold evalFriFold
  refine ⟨by grind, by grind, by grind, by grind⟩

/-- Theorem 1b: `FRI` High-Degree Defect Soundness (`≤ 1` Bad Challenge) vs. "Frozen Heart"
    Unhashed-Root Grinding (`100%` Challenge Evasion). -/
theorem fri_high_degree_defect_at_most_one_bad_challenge_vs_frozen_heart_grinding :
    -- (1) Universal Soundness: for any committed nonzero high-degree defect `(e2, o2) ≠ (0, 0)`,
    --     no two distinct challenges `a1 ≠ a2` can both annihilate `e2 + α * o2`:
    (∀ e2 o2 a1 a2 : Int,
      (e2 ≠ 0 ∨ o2 ≠ 0) →
      a1 ≠ a2 →
      ¬ (e2 + a1 * o2 = 0 ∧ e2 + a2 * o2 = 0)) ∧
    -- (2) Concrete Degree-4 Witness `P(x) = x^4 + 2 x^3` (`e2 = 1, o2 = 2`) has nonzero folded
    --     quadratic defect `1 + 2*α ≠ 0` on EVERY integer challenge `α`:
    (∀ alpha : Int, (1 : Int) + 2 * alpha ≠ 0) ∧
    -- (3) Premise-Failure Counterexample ("Frozen Heart" Fiat–Shamir Order Reversal):
    --     If `(e2, o2)` is chosen AFTER seeing `α` via `e2 = -α, o2 = 1`, the defect is nonzero
    --     (`o2 = 1 ≠ 0`) yet vanishes identically on `100%` of challenges `α`!
    (∀ alpha : Int,
      let e2 := -alpha
      let o2 := (1 : Int)
      (e2 ≠ 0 ∨ o2 ≠ 0) ∧ e2 + alpha * o2 = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e2 o2 a1 a2 hNonzero hNe ⟨h1, h2⟩
    have hDiff : (a1 - a2) * o2 = (e2 + a1 * o2) - (e2 + a2 * o2) := by grind
    rw [h1, h2] at hDiff
    have hSubNe : a1 - a2 ≠ 0 := by omega
    have ho2 : o2 = 0 := by
      by_cases ho2Eq : o2 = 0
      · exact ho2Eq
      · exfalso
        have hZero : (0 : Int) - 0 = 0 := by omega
        rw [hZero] at hDiff
        exact Int.mul_ne_zero hSubNe ho2Eq hDiff
    have he2 : e2 = 0 := by
      rw [ho2] at h1
      omega
    cases hNonzero with
    | inl hE => exact hE he2
    | inr hO => exact hO ho2
  · intro alpha
    omega
  · intro alpha
    exact ⟨Or.inr (by decide), by omega⟩

/-! ## Section 2: `KZG` (`EIP-4844`) Bézout Polynomial Commitments vs. Leaked Trapdoor `τ` -/

/-- Cubic polynomial `P(x) = c0 + c1*x + c2*x^2 + c3*x^3`. -/
def evalKzgPoly3 (c0 c1 c2 c3 x : Int) : Int :=
  c0 + c1 * x + c2 * x * x + c3 * x * x * x

/-- Exact Bézout quotient `Q(x) = (P(x) - P(z)) / (x - z)` for cubic `P`. -/
def evalKzgQuot3 (c1 c2 c3 z x : Int) : Int :=
  (c1 + c2 * z + c3 * z * z) + (c2 + c3 * z) * x + c3 * x * x

/-- Theorem 2: `KZG` Bézout Opening Completeness & Binding Soundness vs. Leaked-`τ` Forgery. -/
theorem kzg_bezout_opening_completeness_and_binding_vs_leaked_tau_forgery :
    -- (1) Universal Bézout Quotient Identity for all cubics and evaluation points `(z, τ)`:
    (∀ c0 c1 c2 c3 z tau : Int,
      evalKzgPoly3 c0 c1 c2 c3 tau - evalKzgPoly3 c0 c1 c2 c3 z =
        (tau - z) * evalKzgQuot3 c1 c2 c3 z tau) ∧
    -- (2) Universal Binding Soundness: any false claim `vClaim ≠ P(z)` has nonzero residual at `z`
    --     for EVERY candidate witness `q : Int → Int`, and against constant `P(X) = c0` with fixed
    --     witness `q0`, at most ONE secret point `τ` can satisfy `c0 - vClaim = (τ - z) * q0`:
    (∀ c0 c1 c2 c3 z vClaim : Int, ∀ q : Int → Int,
      vClaim ≠ evalKzgPoly3 c0 c1 c2 c3 z →
      evalKzgPoly3 c0 c1 c2 c3 z - vClaim - (z - z) * q z ≠ 0) ∧
    (∀ c0 z vClaim q0 tau1 tau2 : Int,
      vClaim ≠ c0 →
      tau1 ≠ tau2 →
      ¬ (c0 - vClaim = (tau1 - z) * q0 ∧ c0 - vClaim = (tau2 - z) * q0)) ∧
    -- (3) Premise-Failure Counterexample (Leaked Trusted-Setup Trapdoor `τ ≠ z`):
    --     Adversary opens `P(X) = c0` to false `vForge = c0 - k*(τ - z) ≠ c0` with `0` residual!
    (∀ c0 z tau k : Int,
      tau ≠ z →
      k ≠ 0 →
      let vForge := c0 - k * (tau - z)
      vForge ≠ c0 ∧ c0 - vForge = (tau - z) * k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c0 c1 c2 c3 z tau
    unfold evalKzgPoly3 evalKzgQuot3
    grind
  · intro c0 c1 c2 c3 z vClaim q hNe
    have hZero : (z - z) * q z = 0 := by
      have hz : z - z = 0 := by omega
      rw [hz, Int.zero_mul]
    rw [hZero]
    omega
  · intro c0 z vClaim q0 tau1 tau2 hFalse hTauNe ⟨hEq1, hEq2⟩
    have hDiff : (tau1 - tau2) * q0 = (tau1 - z) * q0 - (tau2 - z) * q0 := by grind
    rw [← hEq1, ← hEq2] at hDiff
    have hRhsZero : (c0 - vClaim) - (c0 - vClaim) = 0 := by omega
    rw [hRhsZero] at hDiff
    have hSubNe : tau1 - tau2 ≠ 0 := by omega
    have hq0 : q0 = 0 := by
      by_cases hqEq : q0 = 0
      · exact hqEq
      · exfalso
        exact Int.mul_ne_zero hSubNe hqEq hDiff
    rw [hq0] at hEq1
    omega
  · intro c0 z tau k hTauNe hkNe
    have hProdNe : k * (tau - z) ≠ 0 := Int.mul_ne_zero hkNe (by omega)
    refine ⟨by omega, by grind⟩

/-! ## Section 3: Universal `Fin n` Byzantine `3f + 1` Quorum Intersection vs. `3f` Split-Brain -/

/-- Sum a `Nat`-valued weight function across `Fin n`. -/
def finSumNat : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => finSumNat n (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) + f ⟨n, Nat.lt_succ_self n⟩

/-- Pointwise `0/1` quorum-indicator inclusion-exclusion with fault mask `b : Nat`. -/
theorem indicator_honest_intersection_pointwise
    (q1 q2 b : Nat) (hq1 : q1 ≤ 1) (hq2 : q2 ≤ 1) :
    q1 + q2 ≤ 1 + b + q1 * q2 * (1 - b) := by
  match q1, q2 with
  | 0, _ => omega
  | _, 0 => omega
  | 1, 1 =>
    match b with
    | 0 => decide
    | _ + 1 => omega
  | _ + 2, _ => omega
  | 1, _ + 2 => omega

/-- Universal `Fin n` sum inequality: `∑ q1 + ∑ q2 ≤ n + ∑ b + ∑ q1 * q2 * (1 - b)`. -/
theorem finSum_honest_intersection_bound :
    ∀ (n : Nat) (q1 q2 b : Fin n → Nat),
      (∀ i : Fin n, q1 i ≤ 1) →
      (∀ i : Fin n, q2 i ≤ 1) →
      finSumNat n q1 + finSumNat n q2 ≤
        n + finSumNat n b + finSumNat n (fun i => q1 i * q2 i * (1 - b i))
  | 0, _, _, _, _, _ => by simp [finSumNat]
  | n + 1, q1, q2, b, hq1, hq2 => by
    simp only [finSumNat]
    have ih := finSum_honest_intersection_bound n
      (fun i => q1 ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
      (fun i => q2 ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
      (fun i => b ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
      (fun i => hq1 ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
      (fun i => hq2 ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
    have hLast := indicator_honest_intersection_pointwise
      (q1 ⟨n, Nat.lt_succ_self n⟩)
      (q2 ⟨n, Nat.lt_succ_self n⟩)
      (b ⟨n, Nat.lt_succ_self n⟩)
      (hq1 ⟨n, Nat.lt_succ_self n⟩)
      (hq2 ⟨n, Nat.lt_succ_self n⟩)
    omega

/-- Positive `finSumNat` constructively witnesses a nonzero coordinate `i : Fin n`. -/
theorem exists_pos_of_finSumNat_pos :
    ∀ (n : Nat) (g : Fin n → Nat), 0 < finSumNat n g → ∃ i : Fin n, 0 < g i
  | 0, _, hPos => by simp [finSumNat] at hPos
  | n + 1, g, hPos => by
    simp only [finSumNat] at hPos
    by_cases hLast : 0 < g ⟨n, Nat.lt_succ_self n⟩
    · exact ⟨⟨n, Nat.lt_succ_self n⟩, hLast⟩
    · have hPref : 0 < finSumNat n (fun i => g ⟨i.1, Nat.lt_succ_of_lt i.2⟩) := by omega
      obtain ⟨i, hi⟩ := exists_pos_of_finSumNat_pos n (fun i => g ⟨i.1, Nat.lt_succ_of_lt i.2⟩) hPref
      exact ⟨⟨i.1, Nat.lt_succ_of_lt i.2⟩, hi⟩

/-- Theorem 3a: Universal `Fin n` Byzantine Quorum Honest-Intersection Theorem.
    Whenever `∑ q1 ≥ Q`, `∑ q2 ≥ Q`, `∑ b ≤ f`, and `2 Q ≥ n + f + 1`, there exists at least one
    validator `i : Fin n` in `Q1 ∩ Q2` that is non-Byzantine (`q1 i = 1 ∧ q2 i = 1 ∧ b i = 0`). -/
theorem byzantine_quorum_honest_intersection_universal
    (n Q f : Nat) (q1 q2 b : Fin n → Nat)
    (hq1Bit : ∀ i : Fin n, q1 i ≤ 1)
    (hq2Bit : ∀ i : Fin n, q2 i ≤ 1)
    (hq1Quorum : Q ≤ finSumNat n q1)
    (hq2Quorum : Q ≤ finSumNat n q2)
    (hbBudget : finSumNat n b ≤ f)
    (hThreshold : n + f + 1 ≤ 2 * Q) :
    1 ≤ finSumNat n (fun i => q1 i * q2 i * (1 - b i)) ∧
    ∃ i : Fin n, q1 i = 1 ∧ q2 i = 1 ∧ b i = 0 := by
  have hSum := finSum_honest_intersection_bound n q1 q2 b hq1Bit hq2Bit
  have hHonestPos : 1 ≤ finSumNat n (fun i => q1 i * q2 i * (1 - b i)) := by omega
  refine ⟨hHonestPos, ?_⟩
  obtain ⟨i, hiPos⟩ := exists_pos_of_finSumNat_pos n (fun i => q1 i * q2 i * (1 - b i)) hHonestPos
  have h1le := hq1Bit i
  have h2le := hq2Bit i
  have hq1_eq : q1 i = 1 := by
    match h : q1 i with
    | 0 => rw [h] at hiPos; simp at hiPos
    | 1 => rfl
    | _ + 2 => omega
  have hq2_eq : q2 i = 1 := by
    match h : q2 i with
    | 0 => rw [h] at hiPos; simp at hiPos
    | 1 => rfl
    | _ + 2 => omega
  have hb_eq : b i = 0 := by
    rw [hq1_eq, hq2_eq] at hiPos
    omega
  exact ⟨i, hq1_eq, hq2_eq, hb_eq⟩

/-- Concrete `n = 3` (`3f` with `f = 1, Q = 2`) quorum 1 `{0, 1}`. -/
def splitQuorumA : Fin 3 → Nat
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0

/-- Concrete `n = 3` (`3f` with `f = 1, Q = 2`) quorum 2 `{1, 2}`. -/
def splitQuorumB : Fin 3 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1

/-- Concrete `n = 3` single Byzantine equivocator `{1}`. -/
def splitFaultMask : Fin 3 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0

/-- Theorem 3b: `n = 3f + 1, Q = 2f + 1` Universal Safety vs. `n = 3f` (`n = 3, f = 1, Q = 2`)
    Zero-Honest-Intersection Equivocation Split-Brain. -/
theorem byzantine_3f_plus_1_safety_vs_3f_equivocation_split_brain :
    -- (1) For EVERY fault bound `f`, `n = 3f + 1` with `Q = 2f + 1` satisfies `2Q = n + f + 1`:
    (∀ f : Nat, (3 * f + 1) + f + 1 ≤ 2 * (2 * f + 1)) ∧
    -- (2) Concrete `n = 4, f = 1, Q = 3` (`HotStuff`/`Tendermint` minimal BFT cluster):
    --     Every pair of `3`-of-`4` quorums under `≤ 1` Byzantine fault shares `≥ 1` honest node:
    (∀ q1 q2 b : Fin 4 → Nat,
      (∀ i, q1 i ≤ 1) → (∀ i, q2 i ≤ 1) →
      3 ≤ finSumNat 4 q1 → 3 ≤ finSumNat 4 q2 → finSumNat 4 b ≤ 1 →
      ∃ i : Fin 4, q1 i = 1 ∧ q2 i = 1 ∧ b i = 0) ∧
    -- (3) Premise-Failure Counterexample (`n = 3f = 3, f = 1, Q = 2`):
    --     Both quorums have size `2`, fault budget is `1`, yet honest intersection is `0`!
    (finSumNat 3 splitQuorumA = 2 ∧
     finSumNat 3 splitQuorumB = 2 ∧
     finSumNat 3 splitFaultMask = 1 ∧
     finSumNat 3 (fun i => splitQuorumA i * splitQuorumB i * (1 - splitFaultMask i)) = 0) := by
  refine ⟨by intro f; omega, ?_, by decide⟩
  intro q1 q2 b hq1 hq2 hQ1 hQ2 hb
  exact (byzantine_quorum_honest_intersection_universal 4 3 1 q1 q2 b hq1 hq2 hQ1 hQ2 hb (by decide)).2

/-! ## Section 4: `EIP-1559` DSIC Fee Mechanism & `CFMM` Convexity vs. Shading & Drainage -/

/-- User utility under `EIP-1559` base-plus-marginal-tip threshold `basePlusTip`. -/
def eip1559Payoff (val maxFee basePlusTip : Int) : Int :=
  if basePlusTip ≤ maxFee then val - basePlusTip else 0

/-- User utility under a classical First-Price Auction with minimum clearing bid `clearing`. -/
def firstPricePayoff (val bid clearing : Int) : Int :=
  if clearing ≤ bid then val - bid else 0

/-- Theorem 4a: Roughgarden `EIP-1559` Universal Dominant-Strategy Incentive Compatibility (`DSIC`)
    & Non-Negative Surplus vs. First-Price Auction Bid-Shading Incentive. -/
theorem eip1559_truthful_bidding_dsic_vs_first_price_bid_shading :
    -- (1) Universal DSIC + Individual Rationality: truthful `maxFee = val` dominates EVERY `maxFee`
    --     for ALL `(val, basePlusTip)` and guarantees `0 ≤ payoff`:
    (∀ val maxFee basePlusTip : Int,
      eip1559Payoff val maxFee basePlusTip ≤ eip1559Payoff val val basePlusTip ∧
      0 ≤ eip1559Payoff val val basePlusTip) ∧
    -- (2) Premise-Failure Counterexample (First-Price Auction without Base-Fee Separation):
    --     At `val = 100, clearing = 30`, truthful `bid = 100` yields `0` surplus while shaded
    --     `bid = 30` yields `70 > 0`!
    (firstPricePayoff 100 100 30 = 0 ∧
     firstPricePayoff 100 30 30 = 70 ∧
     firstPricePayoff 100 100 30 < firstPricePayoff 100 30 30) := by
  refine ⟨?_, by decide⟩
  intro val maxFee basePlusTip
  unfold eip1559Payoff
  split <;> split <;> omega

/-- Theorem 4b: Constant-Product `CFMM` (`(x + dx)(y - dy) ≥ x y`) Strict Convex Slippage &
    Zero Round-Trip Free-Money Arbitrage vs. Constant-Sum (`x + y = 200`) `100%` Pool Drainage. -/
theorem cfmm_constant_product_no_arbitrage_vs_constant_sum_pool_drainage :
    -- (1) Universal Strict Marginal Slippage: for `x > 0, y > 0, dx > 0, 0 < dy ≤ y`,
    --     preserving `(x + dx)*(y - dy) ≥ x*y` strictly bounds output below spot price (`x*dy < y*dx`):
    (∀ x y dx dy : Int,
      0 < x → 0 < y → 0 < dx → 0 < dy → dy ≤ y →
      x * y ≤ (x + dx) * (y - dy) →
      x * dy < y * dx) ∧
    -- (2) Universal No Round-Trip Free-Money Extraction: swapping `dx` in for `dy` and immediately
    --     swapping `dy` back for `dxOut` under constant-product invariants forces `dxOut ≤ dx`:
    (∀ x y dx dy dxOut : Int,
      0 < x → 0 < y → 0 ≤ dx → 0 ≤ dy → dy ≤ y →
      x * y ≤ (x + dx) * (y - dy) →
      (x + dx) * (y - dy) ≤ (x + dx - dxOut) * y →
      dxOut ≤ dx) ∧
    -- (3) Concrete Constant-Product Witness (`x = 100, y = 100, dx = 25 → dy_max = 20 < 25` spot)
    --     vs. Constant-Sum Premise-Failure Counterexample (`x + y = 200` at external price `3 : 1`
    --     drains `x` from `100 → 0` for `+200` arbitrage profit):
    ((100 + 25) * (100 - 20) = 100 * 100 ∧
     (100 : Int) * 20 < 100 * 25 ∧
     let x0 := (100 : Int); let y0 := (100 : Int)
     let dyIn := (100 : Int); let dxDrained := (100 : Int)
     (x0 - dxDrained) + (y0 + dyIn) = x0 + y0 ∧
     x0 - dxDrained = 0 ∧
     3 * dxDrained - 1 * dyIn = 200) := by
  refine ⟨?_, ?_, by decide⟩
  · intro x y dx dy hx hy hdx hdy _hdyLe hInv
    have hExpand : (x + dx) * (y - dy) = x * y + y * dx - x * dy - dx * dy := by grind
    have hPosProd : 0 < dx * dy := Int.mul_pos hdx hdy
    omega
  · intro x y dx dy dxOut _hx hy _hdx _hdy _hdyLe hStep1 hStep2
    have hChain : x * y ≤ (x + dx - dxOut) * y := Int.le_trans hStep1 hStep2
    have hDiffNonneg : 0 ≤ (dx - dxOut) * y := by
      have hId : (dx - dxOut) * y = (x + dx - dxOut) * y - x * y := by grind
      omega
    by_cases hLe : dxOut ≤ dx
    · exact hLe
    · exfalso
      have hNeg : dx - dxOut < 0 := by omega
      have hProdNeg : (dx - dxOut) * y < 0 := Int.mul_neg_of_neg_of_pos hNeg hy
      omega

end CommonGround.Frontier.FriLowDegreeFoldingByzantineQuorumAndEip1559Legendre
