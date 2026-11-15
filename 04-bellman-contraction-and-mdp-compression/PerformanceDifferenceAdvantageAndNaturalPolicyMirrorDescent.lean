/-!
# Kakade–Langford Performance-Difference Identity, Advantage Baseline Invariance & Mirror-Descent Regret

Pure-core Lean 4.33.0 (`0` imports, `0` sorrys) frontier formalization in Folder `04`
(`04-bellman-contraction-and-mdp-compression`), unifying:
1. **Exact Arbitrary-Horizon Homogeneous Kakade–Langford Performance-Difference Theorem**:
   For any horizon `H : Nat`, finite state count `S : Nat`, action count `A : Nat`, transition kernel `P`,
   and policies `π, π'` normalized to common row-sum `M`, homogeneous integer scaling (`M^H K^{H-1}`)
   eliminates all rational denominators and yields the exact identity
   `J_H(π') - J_H(π) = ∑_{k < H} ∑_{s < S} d_k^{π'}(s) ∑_{a < A} (π'(s,a) - π(s,a)) Q_{H-1-k}^π(s,a)`.
2. **State-Baseline Control-Variate Invariance (Actor-Critic / PPO / GRPO Advantage Centering) &
   Howard Policy-Improvement Monotonicity**, paired with two explicit premise-failure counterexamples:
   - **Unnormalized Policy Bias**: Dropping `∑_a π'(s,a) = ∑_a π(s,a)` makes baseline subtraction bias the
     advantage inner product (`-10 ≠ 0`).
   - **Off-Policy Occupancy Mismatch (The Trust-Region Barrier)**: Evaluating advantages under the old
     occupancy `d_k^π` instead of `d_k^{π'}` on a 2-state `CliffTrap` MDP predicts `+1 > 0` local improvement
     while true performance `J_2(π') - J_2(π)` crashes to `-99 < 0`.
3. **Bregman / Online Mirror-Descent Three-Point Regret Telescoping vs. Unregularized Greedy Oscillation**:
   Proves the exact arbitrary-dimension `(T, A)` three-point identity
   `2 η ∑_{t<T} ⟨u - π_t, g_t⟩ = ‖u - π_0‖₂² - ‖u - π_T‖₂² + η² ∑_{t<T} ‖g_t‖₂²`,
   contrasted against unregularized greedy "chase-yesterday's-winner" oscillation on alternating rewards.
-/

namespace CommonGround.Frontier.PerformanceDifferenceAndMirrorDescent

/-! ## 1. Finite Integer Summation Infrastructure (`0` Imports) -/

def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

theorem sumRange_zero_fn (n : Nat) : sumRange n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih => simp [sumRange, ih]

theorem sumRange_congr {n : Nat} {f g : Nat → Int} (h : ∀ k, k < n → f k = g k) :
    sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [sumRange]
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h m (Nat.lt_succ_self m)]

theorem sumRange_add (n : Nat) (f g : Nat → Int) :
    sumRange n (fun k => f k + g k) = sumRange n f + sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih =>
    simp only [sumRange, ih]
    omega

theorem sumRange_sub (n : Nat) (f g : Nat → Int) :
    sumRange n (fun k => f k - g k) = sumRange n f - sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih =>
    simp only [sumRange, ih]
    omega

theorem sumRange_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun k => c * f k) = c * sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih =>
    simp only [sumRange, ih, Int.mul_add]

theorem sumRange_mul_right (n : Nat) (f : Nat → Int) (c : Int) :
    sumRange n (fun k => f k * c) = sumRange n f * c := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih =>
    simp only [sumRange, ih, Int.add_mul]

theorem sumRange_comm (m n : Nat) (f : Nat → Nat → Int) :
    sumRange m (fun i => sumRange n (fun j => f i j)) =
      sumRange n (fun j => sumRange m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [sumRange]
    exact (sumRange_zero_fn n).symm
  | succ m' ih =>
    simp only [sumRange, ih]
    exact (sumRange_add n (fun j => sumRange m' (fun i => f i j)) (fun j => f m' j)).symm

theorem sumRange_nonneg {n : Nat} {f : Nat → Int} (h : ∀ k, k < n → 0 ≤ f k) :
    0 ≤ sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih =>
    simp only [sumRange]
    have h1 : 0 ≤ sumRange m f := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have h2 : 0 ≤ f m := h m (Nat.lt_succ_self m)
    omega

theorem sumRange_succ_head (m : Nat) (f : Nat → Int) :
    f 0 + sumRange m (fun k => f (k + 1)) = sumRange (m + 1) f := by
  induction m with
  | zero =>
    simp only [sumRange]
    omega
  | succ m' ih =>
    have step1 : f 0 + (sumRange m' (fun k => f (k + 1)) + f (m' + 1)) =
        (f 0 + sumRange m' (fun k => f (k + 1))) + f (m' + 1) := by omega
    change f 0 + (sumRange m' (fun k => f (k + 1)) + f (m' + 1)) = sumRange (m' + 1) f + f (m' + 1)
    rw [step1, ih]

theorem sq_nonneg_int (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -x := by omega
    have hsq : (-x) * (-x) = x * x := by
      rw [Int.neg_mul_neg]
    rw [← hsq]
    exact Int.mul_nonneg hn hn

/-! ## 2. Homogeneous Finite-Horizon Value, Action-Value & Occupancy Dynamics -/

/-- Homogeneous integer-scaled `t`-step state value `V_t^π(s)` (scale `M^t K^{t-1}`). -/
def policyV (S A : Nat) (M K : Int) (R : Nat → Nat → Int) (P : Nat → Nat → Nat → Int)
    (π : Nat → Nat → Int) : Nat → Nat → Int
  | 0, _ => 0
  | t + 1, s =>
      sumRange A (fun a =>
        π s a * (((M * K) ^ t) * R s a + sumRange S (fun s' => P s a s' * policyV S A M K R P π t s')))

/-- Homogeneous integer-scaled `(t+1)`-step state-action value `Q_t^π(s, a)` (scale `(M K)^t`). -/
def policyQ (S A : Nat) (M K : Int) (R : Nat → Nat → Int) (P : Nat → Nat → Nat → Int)
    (π : Nat → Nat → Int) (t : Nat) (s a : Nat) : Int :=
  ((M * K) ^ t) * R s a + sumRange S (fun s' => P s a s' * policyV S A M K R P π t s')

theorem policyV_succ_eq (S A : Nat) (M K : Int) (R : Nat → Nat → Int) (P : Nat → Nat → Nat → Int)
    (π : Nat → Nat → Int) (t : Nat) (s : Nat) :
    policyV S A M K R P π (t + 1) s = sumRange A (fun a => π s a * policyQ S A M K R P π t s a) := rfl

/-- One-step occupancy pushforward `d' (s') = ∑_{s < S} d(s) ∑_{a < A} π'(s,a) P(s,a,s')`. -/
def stepOcc (S A : Nat) (P : Nat → Nat → Nat → Int) (π' : Nat → Nat → Int)
    (d : Nat → Int) (s' : Nat) : Int :=
  sumRange S (fun s => d s * sumRange A (fun a => π' s a * P s a s'))

/-- `k`-step state-occupancy distribution `d_k^{π'}` starting from initial distribution `d`. -/
def iterOcc (S A : Nat) (P : Nat → Nat → Nat → Int) (π' : Nat → Nat → Int) :
    Nat → (Nat → Int) → (Nat → Int)
  | 0, d => d
  | k + 1, d => iterOcc S A P π' k (stepOcc S A P π' d)

/-- Expected `H`-step return `J_H(π) = ∑_{s < S} d(s) V_H^π(s)`. -/
def expectedReturn (S A : Nat) (M K : Int) (R : Nat → Nat → Int) (P : Nat → Nat → Nat → Int)
    (d : Nat → Int) (π : Nat → Nat → Int) (H : Nat) : Int :=
  sumRange S (fun s => d s * policyV S A M K R P π H s)

theorem policyQ_sub_eq (S A : Nat) (M K : Int) (R : Nat → Nat → Int) (P : Nat → Nat → Nat → Int)
    (π π' : Nat → Nat → Int) (t s a : Nat) :
    policyQ S A M K R P π' t s a - policyQ S A M K R P π t s a =
      sumRange S (fun s' => P s a s' * (policyV S A M K R P π' t s' - policyV S A M K R P π t s')) := by
  unfold policyQ
  have hcancel :
      (((M * K) ^ t) * R s a + sumRange S (fun s' => P s a s' * policyV S A M K R P π' t s')) -
      (((M * K) ^ t) * R s a + sumRange S (fun s' => P s a s' * policyV S A M K R P π t s')) =
      sumRange S (fun s' => P s a s' * policyV S A M K R P π' t s') -
      sumRange S (fun s' => P s a s' * policyV S A M K R P π t s') := by omega
  rw [hcancel, ← sumRange_sub]
  apply sumRange_congr
  intro s' _
  rw [Int.mul_sub]

theorem policyV_succ_sub (S A : Nat) (M K : Int) (R : Nat → Nat → Int) (P : Nat → Nat → Nat → Int)
    (π π' : Nat → Nat → Int) (t s : Nat) :
    policyV S A M K R P π' (t + 1) s - policyV S A M K R P π (t + 1) s =
      sumRange A (fun a => (π' s a - π s a) * policyQ S A M K R P π t s a) +
      sumRange A (fun a => π' s a *
        sumRange S (fun s' => P s a s' * (policyV S A M K R P π' t s' - policyV S A M K R P π t s'))) := by
  rw [policyV_succ_eq, policyV_succ_eq, ← sumRange_sub]
  have hsplit :
      sumRange A (fun a => π' s a * policyQ S A M K R P π' t s a - π s a * policyQ S A M K R P π t s a) =
      sumRange A (fun a =>
        (π' s a - π s a) * policyQ S A M K R P π t s a +
        π' s a * (policyQ S A M K R P π' t s a - policyQ S A M K R P π t s a)) := by
    apply sumRange_congr
    intro a _
    rw [Int.sub_mul, Int.mul_sub]
    omega
  rw [hsplit, sumRange_add]
  have hQ :
      sumRange A (fun a => π' s a * (policyQ S A M K R P π' t s a - policyQ S A M K R P π t s a)) =
      sumRange A (fun a => π' s a *
        sumRange S (fun s' => P s a s' * (policyV S A M K R P π' t s' - policyV S A M K R P π t s'))) := by
    apply sumRange_congr
    intro a _
    rw [policyQ_sub_eq]
  rw [hQ]

theorem stepOcc_duality (S A : Nat) (P : Nat → Nat → Nat → Int) (π' : Nat → Nat → Int)
    (d Δ : Nat → Int) :
    sumRange S (fun s => d s * sumRange A (fun a => π' s a * sumRange S (fun s' => P s a s' * Δ s'))) =
      sumRange S (fun s' => stepOcc S A P π' d s' * Δ s') := by
  have h1 :
      sumRange S (fun s => d s * sumRange A (fun a => π' s a * sumRange S (fun s' => P s a s' * Δ s'))) =
      sumRange S (fun s => sumRange S (fun s' => d s * (sumRange A (fun a => π' s a * P s a s') * Δ s'))) := by
    apply sumRange_congr
    intro s _
    have ha :
        sumRange A (fun a => π' s a * sumRange S (fun s' => P s a s' * Δ s')) =
        sumRange S (fun s' => sumRange A (fun a => π' s a * P s a s') * Δ s') := by
      have ha1 :
          sumRange A (fun a => π' s a * sumRange S (fun s' => P s a s' * Δ s')) =
          sumRange A (fun a => sumRange S (fun s' => (π' s a * P s a s') * Δ s')) := by
        apply sumRange_congr
        intro a _
        rw [← sumRange_mul_left]
        apply sumRange_congr
        intro s' _
        rw [Int.mul_assoc]
      rw [ha1, sumRange_comm]
      apply sumRange_congr
      intro s' _
      exact sumRange_mul_right A (fun a => π' s a * P s a s') (Δ s')
    rw [ha, ← sumRange_mul_left]
  rw [h1, sumRange_comm]
  apply sumRange_congr
  intro s' _
  unfold stepOcc
  have h2 :
      sumRange S (fun s => d s * (sumRange A (fun a => π' s a * P s a s') * Δ s')) =
      sumRange S (fun s => (d s * sumRange A (fun a => π' s a * P s a s')) * Δ s') := by
    apply sumRange_congr
    intro s _
    rw [Int.mul_assoc]
  rw [h2, sumRange_mul_right]

/-- **Exact Arbitrary-Horizon Kakade–Langford Performance-Difference Identity**:
    `J_H(π') - J_H(π) = ∑_{k < H} ∑_{s < S} d_k^{π'}(s) ∑_{a < A} (π'(s,a) - π(s,a)) Q_{H-1-k}^π(s,a)`. -/
theorem kakade_langford_performance_difference (S A : Nat) (M K : Int)
    (R : Nat → Nat → Int) (P : Nat → Nat → Nat → Int)
    (π π' : Nat → Nat → Int) (H : Nat) (d : Nat → Int) :
    expectedReturn S A M K R P d π' H - expectedReturn S A M K R P d π H =
      sumRange H (fun k =>
        sumRange S (fun s =>
          iterOcc S A P π' k d s *
            sumRange A (fun a => (π' s a - π s a) * policyQ S A M K R P π (H - 1 - k) s a))) := by
  induction H generalizing d with
  | zero =>
    unfold expectedReturn policyV
    simp only [sumRange, Int.mul_zero]
    rw [sumRange_zero_fn]
    rfl
  | succ m ih =>
    unfold expectedReturn
    rw [← sumRange_sub]
    have hstep :
        sumRange S (fun s => d s * policyV S A M K R P π' (m + 1) s - d s * policyV S A M K R P π (m + 1) s) =
        sumRange S (fun s => d s * sumRange A (fun a => (π' s a - π s a) * policyQ S A M K R P π m s a)) +
        sumRange S (fun s => d s * sumRange A (fun a => π' s a *
          sumRange S (fun s' => P s a s' * (policyV S A M K R P π' m s' - policyV S A M K R P π m s')))) := by
      rw [← sumRange_add]
      apply sumRange_congr
      intro s _
      rw [← Int.mul_sub, policyV_succ_sub, Int.mul_add]
    rw [hstep, stepOcc_duality]
    have hrec :
        sumRange S (fun s' => stepOcc S A P π' d s' * (policyV S A M K R P π' m s' - policyV S A M K R P π m s')) =
        expectedReturn S A M K R P (stepOcc S A P π' d) π' m -
        expectedReturn S A M K R P (stepOcc S A P π' d) π m := by
      unfold expectedReturn
      rw [← sumRange_sub]
      apply sumRange_congr
      intro s' _
      rw [Int.mul_sub]
    rw [hrec, ih (stepOcc S A P π' d)]
    let f : Nat → Int := fun k =>
      sumRange S (fun s =>
        iterOcc S A P π' k d s *
          sumRange A (fun a => (π' s a - π s a) * policyQ S A M K R P π (m - k) s a))
    have hhead :
        sumRange S (fun s => d s * sumRange A (fun a => (π' s a - π s a) * policyQ S A M K R P π m s a)) = f 0 := rfl
    have htail :
        sumRange m (fun k =>
          sumRange S (fun s =>
            iterOcc S A P π' k (stepOcc S A P π' d) s *
              sumRange A (fun a => (π' s a - π s a) * policyQ S A M K R P π (m - 1 - k) s a))) =
        sumRange m (fun k => f (k + 1)) := by
      apply sumRange_congr
      intro k hk
      have hidx : m - 1 - k = m - (k + 1) := by omega
      have hocc : iterOcc S A P π' k (stepOcc S A P π' d) = iterOcc S A P π' (k + 1) d := rfl
      dsimp [f]
      rw [hocc, hidx]
    rw [hhead, htail, sumRange_succ_head]
    rfl

/-- **Baseline Control-Variate Invariance**: When `∑_{a < A} π'(s,a) = ∑_{a < A} π(s,a)`, subtracting ANY
    action-independent state baseline `B(k, s)` (such as the value baseline in Actor-Critic / PPO / GRPO)
    leaves the advantage inner product identically invariant. -/
theorem advantage_baseline_invariance (A : Nat) (p q Q : Nat → Int) (B : Int)
    (hMass : sumRange A p = sumRange A q) :
    sumRange A (fun a => (p a - q a) * (Q a - B)) = sumRange A (fun a => (p a - q a) * Q a) := by
  have hexp :
      sumRange A (fun a => (p a - q a) * (Q a - B)) =
      sumRange A (fun a => (p a - q a) * Q a) - sumRange A (fun a => (p a - q a) * B) := by
    rw [← sumRange_sub]
    apply sumRange_congr
    intro a _
    rw [Int.mul_sub]
  rw [hexp, sumRange_mul_right, sumRange_sub, hMass]
  omega

/-- Nonnegativity of propagated occupancy `d_k^{π'}` under nonnegative initial law, policy, and kernel. -/
theorem iterOcc_nonneg (S A : Nat) (P : Nat → Nat → Nat → Int) (π' : Nat → Nat → Int)
    (hP : ∀ s a s', s < S → a < A → s' < S → 0 ≤ P s a s')
    (hπ' : ∀ s a, s < S → a < A → 0 ≤ π' s a) :
    ∀ (k : Nat) (d : Nat → Int), (∀ s, s < S → 0 ≤ d s) → ∀ s, s < S → 0 ≤ iterOcc S A P π' k d s := by
  intro k
  induction k with
  | zero =>
    intro d hd s hs
    exact hd s hs
  | succ m ih =>
    intro d hd s hs
    apply ih (stepOcc S A P π' d)
    · intro s' hs'
      unfold stepOcc
      apply sumRange_nonneg
      intro s0 hs0
      apply Int.mul_nonneg (hd s0 hs0)
      apply sumRange_nonneg
      intro a ha
      exact Int.mul_nonneg (hπ' s0 a hs0 ha) (hP s0 a s' hs0 ha hs')
    · exact hs

/-- **Howard Policy-Improvement Monotonicity**: Nonnegative statewise advantage against `Q^π`
    certifies `J_H(π) ≤ J_H(π')` unconditionally across any horizon `H`. -/
theorem howard_policy_improvement_monotonicity (S A : Nat) (M K : Int)
    (R : Nat → Nat → Int) (P : Nat → Nat → Nat → Int)
    (d : Nat → Int) (π π' : Nat → Nat → Int) (H : Nat)
    (hd : ∀ s, s < S → 0 ≤ d s)
    (hP : ∀ s a s', s < S → a < A → s' < S → 0 ≤ P s a s')
    (hπ' : ∀ s a, s < S → a < A → 0 ≤ π' s a)
    (hAdv : ∀ k s, k < H → s < S →
      0 ≤ sumRange A (fun a => (π' s a - π s a) * policyQ S A M K R P π (H - 1 - k) s a)) :
    expectedReturn S A M K R P d π H ≤ expectedReturn S A M K R P d π' H := by
  have hdiff := kakade_langford_performance_difference S A M K R P π π' H d
  have hpos :
      0 ≤ sumRange H (fun k =>
        sumRange S (fun s =>
          iterOcc S A P π' k d s *
            sumRange A (fun a => (π' s a - π s a) * policyQ S A M K R P π (H - 1 - k) s a))) := by
    apply sumRange_nonneg
    intro k hk
    apply sumRange_nonneg
    intro s hs
    exact Int.mul_nonneg (iterOcc_nonneg S A P π' hP hπ' k d hd s hs) (hAdv k s hk hs)
  omega

/-! ## 3. Premise-Failure Counterexamples: Unnormalized Policy Bias & Off-Policy CliffTrap Collapse -/

/-- `CliffTrap` 2-state, 2-action MDP (`H = 2`, deterministic `M = 1, K = 1`):
    - At `s = 0` (safe start): `a = 0` stays at `s = 0` with reward `0`; `a = 1` gives `+1` immediate
      reward (`Q_1^π(0, 1) = +1 > 0 = Q_1^π(0, 0)` when `π` plays `a = 0` at `s = 1`!) YET transitions
      to `s = 1` (`cliff`).
    - At `s = 1` (`cliff`): `a = 0` (played by old policy `π`) gives `0`, while `a = 1` (played by aggressive
      new policy `π'`) plunges off the cliff for `-100`!
    - Under old occupancy `d^π` (`d_0^π = (1, 0)`, `d_1^π = (1, 0)` because `π` never visits `s = 1`),
      the first-order local surrogate `L_π(π')` weights `s = 1` by `d_1^π(1) = 0` and predicts `+2 > 0`
      (`+1` at each step at `s = 0`), whereas true `J_2(π') - J_2(π)` evaluates `d_1^{π'}(1) = 1` and crashes to `-99 < 0`! -/
def cliffR (s a : Nat) : Int :=
  if s == 0 then (if a == 1 then 1 else 0)
  else (if a == 1 then -100 else 0)

def cliffP (s a s' : Nat) : Int :=
  if s == 0 then
    if a == 0 then (if s' == 0 then 1 else 0)
    else (if s' == 1 then 1 else 0)
  else (if s' == 1 then 1 else 0)

def cliffPiOld (_s a : Nat) : Int := if a == 0 then 1 else 0
def cliffPiNew (_s a : Nat) : Int := if a == 1 then 1 else 0
def cliffInit (s : Nat) : Int := if s == 0 then 1 else 0

/-- First-order off-policy surrogate `L_π(π')` replacing `d_k^{π'}` by the old occupancy `d_k^π`. -/
def localOldOccupancySurrogate (S A : Nat) (M K : Int)
    (R : Nat → Nat → Int) (P : Nat → Nat → Nat → Int)
    (d : Nat → Int) (π π' : Nat → Nat → Int) (H : Nat) : Int :=
  sumRange H (fun k =>
    sumRange S (fun s =>
      iterOcc S A P π k d s *
        sumRange A (fun a => (π' s a - π s a) * policyQ S A M K R P π (H - 1 - k) s a)))

/-- **Master Theorem 1 (Kakade–Langford, Baseline Centering & Trust-Region Occupancy Barrier)**:
    Unifies exact multi-step performance difference + baseline invariance with explicit counterexamples
    when either (a) equal policy mass `∑ π' = ∑ π` or (b) true new-policy occupancy `d_k^{π'}` is dropped. -/
theorem kakade_langford_and_baseline_invariance_vs_unnormalized_and_offpolicy_cliff_failure :
    (let p : Nat → Int := fun a => if a == 0 then 2 else 0
     let q : Nat → Int := fun a => if a == 0 then 1 else 0
     let Q : Nat → Int := fun _ => 5
     sumRange 2 (fun a => (p a - q a) * (Q a - 10)) ≠ sumRange 2 (fun a => (p a - q a) * Q a)) ∧
    localOldOccupancySurrogate 2 2 1 1 cliffR cliffP cliffInit cliffPiOld cliffPiNew 2 = 2 ∧
    expectedReturn 2 2 1 1 cliffR cliffP cliffInit cliffPiNew 2 -
      expectedReturn 2 2 1 1 cliffR cliffP cliffInit cliffPiOld 2 = -99 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## 4. Online Mirror-Descent Three-Point Regret Telescoping vs. Unregularized Greedy Oscillation -/

/-- Squared Euclidean potential `‖u - π‖₂² = ∑_{a < A} (u_a - π_a)²`. -/
def sqDistVec (A : Nat) (u v : Nat → Int) : Int :=
  sumRange A (fun a => (u a - v a) * (u a - v a))

/-- Online gradient / Euclidean mirror-descent trajectory `π_{t+1}(a) = π_t(a) + η g_t(a)`. -/
def omdPolicy (η : Int) (π₀ : Nat → Int) (g : Nat → Nat → Int) : Nat → Nat → Int
  | 0, a => π₀ a
  | t + 1, a => omdPolicy η π₀ g t a + η * g t a

/-- Exact one-step three-point identity:
    `2 η ⟨u - π, g⟩ = ‖u - π‖₂² - ‖u - (π + η g)‖₂² + η² ‖g‖₂²`. -/
theorem three_point_omd_step (A : Nat) (η : Int) (u π g : Nat → Int) :
    2 * η * sumRange A (fun a => (u a - π a) * g a) =
      sqDistVec A u π - sqDistVec A u (fun a => π a + η * g a) +
        (η * η) * sumRange A (fun a => g a * g a) := by
  unfold sqDistVec
  rw [← sumRange_mul_left, ← sumRange_mul_left, ← sumRange_sub, ← sumRange_add]
  apply sumRange_congr
  intro a _
  have hscalar (d w : Int) :
      2 * η * (d * w) = d * d - (d - η * w) * (d - η * w) + (η * η) * (w * w) := by
    have expand : (d - η * w) * (d - η * w) = d * d - d * (η * w) - (η * w) * d + (η * w) * (η * w) := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
      omega
    have hc1 : d * (η * w) = η * (d * w) := by
      rw [← Int.mul_assoc, Int.mul_comm d η, Int.mul_assoc]
    have hc2 : (η * w) * d = η * (d * w) := by
      rw [Int.mul_assoc, Int.mul_comm w d]
    have hc3 : (η * w) * (η * w) = (η * η) * (w * w) := by
      rw [Int.mul_assoc, ← Int.mul_assoc w η w, Int.mul_comm w η, Int.mul_assoc, ← Int.mul_assoc]
    rw [expand, hc1, hc2, hc3]
    have htwo : η * (d * w) + η * (d * w) = 2 * η * (d * w) := by
      have : (1 + 1) * (η * (d * w)) = 2 * η * (d * w) := by
        rw [← Int.mul_assoc]
        rfl
      rw [Int.add_mul, Int.one_mul] at this
      exact this
    omega
  have hd : u a - (π a + η * g a) = (u a - π a) - η * g a := by omega
  rw [hd]
  exact hscalar (u a - π a) (g a)

/-- **Master Theorem 2 (Arbitrary-Horizon Online Mirror-Descent Regret Telescoping & Upper Bound)**:
    `2 η ∑_{t < T} ⟨u - π_t, g_t⟩ = ‖u - π_0‖₂² - ‖u - π_T‖₂² + η² ∑_{t < T} ‖g_t‖₂²`,
    implying `2 η ∑_{t < T} ⟨u - π_t, g_t⟩ ≤ ‖u - π_0‖₂² + η² ∑_{t < T} ‖g_t‖₂²`. -/
theorem mirror_descent_regret_telescoping_and_bound (T A : Nat) (η : Int)
    (u π₀ : Nat → Int) (g : Nat → Nat → Int) :
    (2 * η * sumRange T (fun t => sumRange A (fun a => (u a - omdPolicy η π₀ g t a) * g t a)) =
      sqDistVec A u π₀ - sqDistVec A u (omdPolicy η π₀ g T) +
        (η * η) * sumRange T (fun t => sumRange A (fun a => g t a * g t a))) ∧
    (2 * η * sumRange T (fun t => sumRange A (fun a => (u a - omdPolicy η π₀ g t a) * g t a)) ≤
      sqDistVec A u π₀ + (η * η) * sumRange T (fun t => sumRange A (fun a => g t a * g t a))) := by
  have htel :
      2 * η * sumRange T (fun t => sumRange A (fun a => (u a - omdPolicy η π₀ g t a) * g t a)) =
      sqDistVec A u π₀ - sqDistVec A u (omdPolicy η π₀ g T) +
        (η * η) * sumRange T (fun t => sumRange A (fun a => g t a * g t a)) := by
    induction T with
    | zero =>
      simp [sumRange, omdPolicy]
    | succ m ih =>
      simp only [sumRange, Int.mul_add]
      rw [ih, three_point_omd_step A η u (omdPolicy η π₀ g m) (g m)]
      have hstep : (fun a => omdPolicy η π₀ g m a + η * g m a) = omdPolicy η π₀ g (m + 1) := rfl
      rw [hstep]
      omega
  refine ⟨htel, ?_⟩
  have hpos : 0 ≤ sqDistVec A u (omdPolicy η π₀ g T) := by
    unfold sqDistVec
    apply sumRange_nonneg
    intro a _
    exact sq_nonneg_int (u a - omdPolicy η π₀ g T a)
  omega

def advPayoff4 : Nat → Nat → Int
  | 0, a => if a == 0 then 1 else 0
  | 1, a => if a == 1 then 2 else 0
  | 2, a => if a == 0 then 2 else 0
  | _, a => if a == 1 then 2 else 0

/-- Unregularized Follow-The-Leader chooses action `0` at `t = 0`, and thereafter picks `0` iff
    cumulative past payoff of `0` is ≥ cumulative past payoff of `1`. -/
def unregularizedFTLAction (t : Nat) : Nat :=
  if sumRange t (fun s => advPayoff4 s 1) ≤ sumRange t (fun s => advPayoff4 s 0) then 0 else 1

theorem unregularized_ftl_chases_yesterday_and_suffers_oscillation_regret :
    unregularizedFTLAction 0 = 0 ∧
    unregularizedFTLAction 1 = 0 ∧
    unregularizedFTLAction 2 = 1 ∧
    unregularizedFTLAction 3 = 0 ∧
    sumRange 4 (fun t => advPayoff4 t (unregularizedFTLAction t)) = 1 ∧
    sumRange 4 (fun t => advPayoff4 t 1) -
      sumRange 4 (fun t => advPayoff4 t (unregularizedFTLAction t)) = 3 := by
  decide

end CommonGround.Frontier.PerformanceDifferenceAndMirrorDescent
