/-
  01-blackwell-critical-prior-sufficiency/PerformativeHockeyStickCvarAndControlBarrierFrontier.lean

  Frontier #106 (`V231`, `0` imports, `0` sorry):
  Grand Tri-Domain Duality & Safe Deployment Synthesis across Statistical Machine Learning (`Folder 01` & `03`),
  Convex / Superquantile Operations Research (`Folder 08`), and Nonlinear Control-Barrier Stability (`Folder 04`):
  1. Universal `Fin M` Hockey-Stick–Rockafellar CVaR Master Variational Inequality:
       `∑_x q_x ℓ_x ≤ (∑_x q_x) τ + γ ∑_x p_x (ℓ_x - τ)_+ + (L - τ) ∑_x (q_x - γ p_x)_+`
     unifying Rockafellar–Uryasev Superquantile (`CVaR_{1-1/γ}`) Duality (`E_γ = 0`), Quantile-Truncated
     Total-Variation Shift Certificates (`γ = 1`), and Differential-Privacy Hockey-Stick Envelopes, with
     Exact Tightness (`34 = 34` at critical quantile `τ* = 4`) vs. Unbounded-Loss Tail Blowup.
  2. Universal `Fin M` Shifted Split-Conformal Coverage Transfer (`L = 1` binary indicator specialization)
     vs. `90% → 60%` Clinical Triage Coverage Collapse under Unadjusted Covariate/Performative Shift.
  3. Universal `T`-Round Performative Retraining Banach Contraction (`|θ_T - θ*| · S^T ≤ κ^T |θ_0 - θ*|`)
     vs. Critical-Gain `2`-Cycle Oscillation (`κ = S`) and Positive-Feedback Runaway (`κ > S`).
  4. Universal Non-Stationary Distributionally Robust Control Barrier Function (`DR-CBF`) Forward Safety
     Invariance (`h_t ≥ h_min` for all `t` across arbitrary non-stationary Hockey-Stick shift sequences)
     vs. Naive Nominal-Mean Barrier Crash (`h_1 = -18 < 0`).
-/

namespace CommonGround.Frontier.PerformativeHockeyStickCvarAndControlBarrier

/-! ## Section 1: Universal `Fin M` Hockey-Stick–Rockafellar CVaR Master Variational Inequality -/

def sumFinNat : (M : Nat) → (Fin M → Nat) → Nat
  | 0, _ => 0
  | n + 1, f =>
      sumFinNat n (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) + f ⟨n, Nat.lt_succ_self n⟩

theorem sumFinNat_add (M : Nat) (f g : Fin M → Nat) :
    sumFinNat M (fun i => f i + g i) = sumFinNat M f + sumFinNat M g := by
  induction M with
  | zero => rfl
  | succ n ih =>
      simp [sumFinNat, ih]
      omega

theorem sumFinNat_scale (M : Nat) (c : Nat) (f : Fin M → Nat) :
    sumFinNat M (fun i => c * f i) = c * sumFinNat M f := by
  induction M with
  | zero => simp [sumFinNat]
  | succ n ih =>
      simp [sumFinNat, ih, Nat.mul_add]

theorem sumFinNat_scale_right (M : Nat) (c : Nat) (f : Fin M → Nat) :
    sumFinNat M (fun i => f i * c) = sumFinNat M f * c := by
  induction M with
  | zero => simp [sumFinNat]
  | succ n ih =>
      simp [sumFinNat, ih, Nat.add_mul]

theorem sumFinNat_le (M : Nat) (f g : Fin M → Nat) (hfg : ∀ i : Fin M, f i ≤ g i) :
    sumFinNat M f ≤ sumFinNat M g := by
  induction M with
  | zero => simp [sumFinNat]
  | succ n ih =>
      have h1 :
          sumFinNat n (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) ≤
          sumFinNat n (fun i => g ⟨i.1, Nat.lt_succ_of_lt i.2⟩) :=
        ih _ _ (fun i => hfg ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
      have h2 : f ⟨n, Nat.lt_succ_self n⟩ ≤ g ⟨n, Nat.lt_succ_self n⟩ :=
        hfg ⟨n, Nat.lt_succ_self n⟩
      simp [sumFinNat]
      omega

/-- Hockey-Stick divergence excess `E_γ(q ‖ p) = ∑_x (q_x - γ p_x)_+` in exact `Nat` truncated subtraction. -/
def hockeyStickExcess (M : Nat) (gamma : Nat) (q p : Fin M → Nat) : Nat :=
  sumFinNat M (fun x => q x - gamma * p x)

/-- Rockafellar–Uryasev Hinge / Superquantile tail sum `∑_x p_x (ℓ_x - τ)_+`. -/
def cvarHingeTail (M : Nat) (p ell : Fin M → Nat) (tau : Nat) : Nat :=
  sumFinNat M (fun x => p x * (ell x - tau))

/-- Rockafellar–Hockey-Stick Distributionally Robust Envelope at threshold `τ`:
    `Env(Z, γ, B, τ) = Z · τ + γ · ∑_x p_x (ℓ_x - τ)_+ + (L - τ) · B`. -/
def drCvarHockeyStickEnvelope
    (M : Nat) (Z gamma L tau budgetB : Nat) (p ell : Fin M → Nat) : Nat :=
  Z * tau + gamma * cvarHingeTail M p ell tau + (L - tau) * budgetB

/-- Master Pointwise Decomposition:
    For every `q, p, γ, ℓ ≤ L, τ ≤ L`,
    `q · ℓ ≤ q · τ + γ · p · (ℓ - τ)_+ + (L - τ) · (q - γ · p)_+`. -/
theorem hockey_stick_cvar_pointwise_master
    (q p gamma ell tau L : Nat) (hell : ell ≤ L) :
    q * ell ≤ q * tau + gamma * (p * (ell - tau)) + (L - tau) * (q - gamma * p) := by
  by_cases hlt : ell ≤ tau
  · have hmul : q * ell ≤ q * tau := Nat.mul_le_mul_left q hlt
    omega
  · have hsplit_ell : ell = tau + (ell - tau) := by omega
    by_cases hqp : q ≤ gamma * p
    · have h1 : q * (ell - tau) ≤ (gamma * p) * (ell - tau) :=
        Nat.mul_le_mul_right (ell - tau) hqp
      have h2 : (gamma * p) * (ell - tau) = gamma * (p * (ell - tau)) :=
        Nat.mul_assoc gamma p (ell - tau)
      calc
        q * ell = q * (tau + (ell - tau)) := by rw [← hsplit_ell]
        _ = q * tau + q * (ell - tau) := Nat.mul_add q tau (ell - tau)
        _ ≤ q * tau + gamma * (p * (ell - tau)) := by omega
        _ ≤ q * tau + gamma * (p * (ell - tau)) + (L - tau) * (q - gamma * p) :=
            Nat.le_add_right _ _
    · have hsplit_q : q = gamma * p + (q - gamma * p) := by omega
      have hrem : ell - tau ≤ L - tau := by omega
      have h3 : (q - gamma * p) * (ell - tau) ≤ (q - gamma * p) * (L - tau) :=
        Nat.mul_le_mul_left (q - gamma * p) hrem
      have h3c : (q - gamma * p) * (L - tau) = (L - tau) * (q - gamma * p) :=
        Nat.mul_comm (q - gamma * p) (L - tau)
      have h2 : (gamma * p) * (ell - tau) = gamma * (p * (ell - tau)) :=
        Nat.mul_assoc gamma p (ell - tau)
      calc
        q * ell = q * (tau + (ell - tau)) := by rw [← hsplit_ell]
        _ = q * tau + q * (ell - tau) := Nat.mul_add q tau (ell - tau)
        _ = q * tau + (gamma * p + (q - gamma * p)) * (ell - tau) := by rw [← hsplit_q]
        _ = q * tau + ((gamma * p) * (ell - tau) + (q - gamma * p) * (ell - tau)) := by
            rw [Nat.add_mul]
        _ ≤ q * tau + (gamma * (p * (ell - tau)) + (L - tau) * (q - gamma * p)) := by omega
        _ = q * tau + gamma * (p * (ell - tau)) + (L - tau) * (q - gamma * p) := by omega

/-- Theorem 1 (Universal `Fin M` Hockey-Stick–Rockafellar CVaR Master Duality):
    For EVERY finite state space `Fin M`, nominal weights `p`, shifted weights `q` with `∑ q_x ≤ Z`,
    losses `ℓ_x ≤ L`, slope `γ`, threshold `τ`, and Hockey-Stick budget `E_γ(q ‖ p) ≤ B`:
    `∑_x q_x ℓ_x ≤ Z · τ + γ · ∑_x p_x (ℓ_x - τ)_+ + (L - τ) · B`. -/
theorem hockey_stick_cvar_variational_duality_universal
    (M Z gamma L tau budgetB : Nat)
    (q p ell : Fin M → Nat)
    (hqZ : sumFinNat M q ≤ Z)
    (hell : ∀ x : Fin M, ell x ≤ L)
    (hB : hockeyStickExcess M gamma q p ≤ budgetB) :
    sumFinNat M (fun x => q x * ell x) ≤
      drCvarHockeyStickEnvelope M Z gamma L tau budgetB p ell := by
  have hpt :
      sumFinNat M (fun x => q x * ell x) ≤
        sumFinNat M (fun x =>
          (q x * tau + gamma * (p x * (ell x - tau))) + (L - tau) * (q x - gamma * p x)) := by
    apply sumFinNat_le
    intro x
    have hm := hockey_stick_cvar_pointwise_master (q x) (p x) gamma (ell x) tau L (hell x)
    omega
  have hsum1 :
      sumFinNat M (fun x =>
        (q x * tau + gamma * (p x * (ell x - tau))) + (L - tau) * (q x - gamma * p x))
      = sumFinNat M (fun x => q x * tau + gamma * (p x * (ell x - tau))) +
        sumFinNat M (fun x => (L - tau) * (q x - gamma * p x)) :=
    sumFinNat_add M _ _
  have hsum2 :
      sumFinNat M (fun x => q x * tau + gamma * (p x * (ell x - tau)))
      = sumFinNat M (fun x => q x * tau) +
        sumFinNat M (fun x => gamma * (p x * (ell x - tau))) :=
    sumFinNat_add M _ _
  have hq_tau : sumFinNat M (fun x => q x * tau) = sumFinNat M q * tau :=
    sumFinNat_scale_right M tau q
  have h_hinge :
      sumFinNat M (fun x => gamma * (p x * (ell x - tau))) =
        gamma * cvarHingeTail M p ell tau :=
    sumFinNat_scale M gamma (fun x => p x * (ell x - tau))
  have h_hs :
      sumFinNat M (fun x => (L - tau) * (q x - gamma * p x)) =
        (L - tau) * hockeyStickExcess M gamma q p :=
    sumFinNat_scale M (L - tau) (fun x => q x - gamma * p x)
  have hZ_mul : sumFinNat M q * tau ≤ Z * tau := Nat.mul_le_mul_right tau hqZ
  have hB_mul : (L - tau) * hockeyStickExcess M gamma q p ≤ (L - tau) * budgetB :=
    Nat.mul_le_mul_left (L - tau) hB
  unfold drCvarHockeyStickEnvelope
  omega

theorem sumFinNat_zero (M : Nat) : sumFinNat M (fun _ => 0) = 0 := by
  induction M with
  | zero => rfl
  | succ n ih => simp [sumFinNat, ih]

/-- Pure Rockafellar–Uryasev `CVaR_{1-1/γ}` Specialization (`E_γ(q ‖ p) = 0`, i.e., `q_x ≤ γ p_x` pointwise):
    The Hockey-Stick tail penalty vanishes identically, yielding `∑ q_x ℓ_x ≤ Z · τ + γ · ∑ p_x (ℓ_x - τ)_+`. -/
theorem pure_cvar_rockafellar_uryasev_reduction
    (M Z gamma L tau : Nat) (q p ell : Fin M → Nat)
    (hqZ : sumFinNat M q ≤ Z)
    (hell : ∀ x : Fin M, ell x ≤ L)
    (hSlope : ∀ x : Fin M, q x ≤ gamma * p x) :
    sumFinNat M (fun x => q x * ell x) ≤ Z * tau + gamma * cvarHingeTail M p ell tau := by
  have hB0 : hockeyStickExcess M gamma q p ≤ 0 := by
    unfold hockeyStickExcess
    have hle : sumFinNat M (fun x => q x - gamma * p x) ≤ sumFinNat M (fun _ => 0) := by
      apply sumFinNat_le
      intro x
      have hsx := hSlope x
      omega
    have hz := sumFinNat_zero M
    omega
  have hmain := hockey_stick_cvar_variational_duality_universal M Z gamma L tau 0 q p ell hqZ hell hB0
  unfold drCvarHockeyStickEnvelope at hmain
  omega

/-- Explicit `4`-State Exact Tightness Witness vs. Dropped-Bound Tail Blowup:
    `p = (1,1,1,1)` (`Z = 4`), `ℓ = (0,2,4,10)` (`L = 10`), `γ = 2`, `q** = (0,0,1,3)` (`E_2 = 1`).
    - Shifted risk `∑ q**_x ℓ_x = 34`.
    - At critical quantile `τ* = 4`, `drCvarHockeyStickEnvelope = 34` (EXACT EQUALITY `34 = 34`!).
    - Saves `15%` (`6 / 40`) over worst-case box bound `40`, whereas `τ = 0` gives `42` and naive mean gives `16 < 34`.
    - Dropping the bounded-loss cap (`ℓ_3 = 100` while certifying with `L_assumed = 10`) breaks the bound (`304 > 34`). -/
def pUniform4 : Fin 4 → Nat
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1

def lossProfile4 : Fin 4 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 4
  | ⟨3, _⟩ => 10

def qAdversarial4 : Fin 4 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 3

def lossUnboundedSpike4 : Fin 4 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 4
  | ⟨3, _⟩ => 100

theorem exact_cvar_hockey_stick_attainment_vs_dropped_cap_blowup :
    (sumFinNat 4 qAdversarial4 = 4) ∧
    (hockeyStickExcess 4 2 qAdversarial4 pUniform4 = 1) ∧
    (sumFinNat 4 (fun x => qAdversarial4 x * lossProfile4 x) = 34) ∧
    (drCvarHockeyStickEnvelope 4 4 2 10 4 1 pUniform4 lossProfile4 = 34) ∧
    (drCvarHockeyStickEnvelope 4 4 2 10 0 1 pUniform4 lossProfile4 = 42) ∧
    (sumFinNat 4 (fun x => pUniform4 x * lossProfile4 x) = 16 ∧ 16 < 34) ∧
    (sumFinNat 4 (fun x => qAdversarial4 x * lossUnboundedSpike4 x) = 304 ∧
      304 > drCvarHockeyStickEnvelope 4 4 2 10 4 1 pUniform4 lossProfile4) := by
  decide

/-! ## Section 2: Universal `Fin M` Shifted Split-Conformal Coverage Transfer (`L = 1`) -/

/-- Theorem 2 (Universal Shifted Conformal Miscoverage Bound):
    Specializing Theorem 1 to binary miscoverage indicators `err : Fin M → Bool` (`L = 1, τ = 0`):
    Shifted miscoverage count `∑_x q_x · 1[err_x]` is bounded by `γ · (∑_x p_x · 1[err_x]) + E_γ(q ‖ p)`. -/
theorem shifted_conformal_miscoverage_hockey_stick_universal
    (M gamma kNom budgetB : Nat)
    (q p : Fin M → Nat)
    (err : Fin M → Bool)
    (hNom : sumFinNat M (fun x => p x * (if err x then 1 else 0)) ≤ kNom)
    (hB : hockeyStickExcess M gamma q p ≤ budgetB) :
    sumFinNat M (fun x => q x * (if err x then 1 else 0)) ≤ gamma * kNom + budgetB := by
  let ind : Fin M → Nat := fun x => if err x then 1 else 0
  have hell1 : ∀ x : Fin M, ind x ≤ 1 := by
    intro x
    dsimp [ind]
    cases err x <;> decide
  have hmain :=
    hockey_stick_cvar_variational_duality_universal
      M (sumFinNat M q) gamma 1 0 budgetB q p ind (Nat.le_refl _) hell1 hB
  unfold drCvarHockeyStickEnvelope cvarHingeTail at hmain
  have htail : sumFinNat M (fun x => p x * (ind x - 0)) = sumFinNat M (fun x => p x * ind x) := rfl
  rw [htail] at hmain
  have hmul : gamma * sumFinNat M (fun x => p x * ind x) ≤ gamma * kNom :=
    Nat.mul_le_mul_left gamma hNom
  dsimp [ind] at hmain hmul
  omega

/-- Clinical Conformal Triage Witness (`Z = 10`):
    Nominal `p = (9, 1)` on `(benign_score ≤ τ_nom, severe_score > τ_nom)` has `1 / 10` (`10%`) miscoverage.
    Under hospital case-mix shift `q = (6, 4)` (`E_1(q ‖ p) = 3`), unadjusted `τ_nom` suffers `4 / 10` (`40%`)
    miscoverage (`60%` coverage collapse!), whereas widening the conformal threshold so nominal tail is `0`
    under `γ = 1, B = 1` or `err_recal = false` restores guaranteed coverage! -/
theorem clinical_conformal_shift_collapse_witness :
    let p2 : Fin 2 → Nat := fun i => if i.1 = 0 then 9 else 1
    let q2 : Fin 2 → Nat := fun i => if i.1 = 0 then 6 else 4
    let errUnadjusted : Fin 2 → Bool := fun i => decide (i.1 = 1)
    let errRecalibrated : Fin 2 → Bool := fun _ => false
    (sumFinNat 2 (fun x => p2 x * (if errUnadjusted x then 1 else 0)) = 1) ∧
    (hockeyStickExcess 2 1 q2 p2 = 3) ∧
    (sumFinNat 2 (fun x => q2 x * (if errUnadjusted x then 1 else 0)) = 4) ∧
    (sumFinNat 2 (fun x => q2 x * (if errRecalibrated x then 1 else 0)) = 0) := by
  decide

/-! ## Section 3: Performative Retraining Contraction vs. Feedback-Loop Oscillation -/

def natPow (b : Nat) : Nat → Nat
  | 0 => 1
  | t + 1 => natPow b t * b

/-- Theorem 3 (Universal `T`-Step Performative Fixed-Point Contraction):
    If closed-loop performative retraining error `e_t = |θ_t - θ*|` satisfies scaled contraction
    `e_{t+1} · S ≤ κ · e_t` at each deployment round, then across EVERY horizon `T : Nat`,
    `e_T · S^T ≤ κ^T · e_0`. -/
theorem performative_contraction_geometric_convergence_universal
    (S kappa : Nat) (errSeq : Nat → Nat)
    (hStep : ∀ t : Nat, errSeq (t + 1) * S ≤ errSeq t * kappa) :
    ∀ T : Nat, errSeq T * natPow S T ≤ errSeq 0 * natPow kappa T := by
  intro T
  induction T with
  | zero =>
      simp [natPow]
  | succ t ih =>
      have h1 : (errSeq (t + 1) * S) * natPow S t ≤ (errSeq t * kappa) * natPow S t :=
        Nat.mul_le_mul_right (natPow S t) (hStep t)
      have h2 : (errSeq t * natPow S t) * kappa ≤ (errSeq 0 * natPow kappa t) * kappa :=
        Nat.mul_le_mul_right kappa ih
      have eqL : errSeq (t + 1) * natPow S (t + 1) = (errSeq (t + 1) * S) * natPow S t := by
        simp [natPow, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have eqM : (errSeq t * kappa) * natPow S t = (errSeq t * natPow S t) * kappa := by
        simp [Nat.mul_assoc, Nat.mul_comm]
      have eqR : (errSeq 0 * natPow kappa t) * kappa = errSeq 0 * natPow kappa (t + 1) := by
        simp [natPow, Nat.mul_assoc]
      omega

/-- Dropped-Coercivity Counterexample (`κ ≥ S`):
    1. At critical unit gain `κ = S` (`G(θ) = -θ`, `θ* = 0`), retraining starting at `θ_0 = 5` oscillates
       in a perpetual `2`-cycle `5, -5, 5, -5, ...` with constant nonzero error `|θ_t| = 5` forever.
    2. Above unit gain (`G(θ) = 2 θ`), error doubles every deployment round (`5 → 10 → 20 → 40`). -/
def oscPolicy : Nat → Int
  | 0 => 5
  | t + 1 => -(oscPolicy t)

def runawayErr : Nat → Nat
  | 0 => 5
  | t + 1 => 2 * runawayErr t

theorem performative_positive_feedback_oscillation_and_blowup_counterexample :
    (∀ t : Nat, Int.natAbs (oscPolicy t) = 5) ∧
    (oscPolicy 0 = 5 ∧ oscPolicy 1 = -5 ∧ oscPolicy 2 = 5) ∧
    (runawayErr 3 = 40 ∧ runawayErr 3 > runawayErr 0) := by
  refine ⟨?_, by decide, by decide⟩
  intro t
  induction t with
  | zero => rfl
  | succ k ih =>
      simp [oscPolicy, Int.natAbs_neg, ih]

/-! ## Section 4: Non-Stationary Distributionally Robust Control Barrier (`DR-CBF`) Forward Invariance -/

/-- Theorem 4 (Universal Non-Stationary `DR-CBF` Forward Safety Invariance):
    Let `h : Nat → Int` be a discrete-time Control Barrier trajectory under arbitrary non-stationary
    shifted disturbance laws `qSeq : Nat → Fin M → Nat` satisfying `∑_w qSeq t w ≤ Z` and
    `E_γ(qSeq t ‖ p) ≤ B` for all `t`, with bounded disturbance profile `d_w ≤ L`.
    If step dynamics satisfy scaled barrier update
      `S · h(t + 1) ≥ (S - α) · h(t) + M_ctrl - ∑_w qSeq t w · d_w`
    with `0 < S`, `α ≤ S`, and `M_ctrl` certified via the Rockafellar–Hockey-Stick envelope
      `drCvarHockeyStickEnvelope M Z γ L τ B p d + α · h_min ≤ M_ctrl`,
    then `h(0) ≥ h_min ⟹ ∀ T, h(T) ≥ h_min` (100% forward safety invariance!). -/
theorem dr_cbf_nonstationary_forward_invariance_universal
    (M Z gamma L tau budgetB S alpha Mctrl hMin : Nat)
    (p d : Fin M → Nat)
    (qSeq : Nat → Fin M → Nat)
    (h : Nat → Int)
    (hS : 0 < S)
    (hAlpha : alpha ≤ S)
    (hqZ : ∀ t : Nat, sumFinNat M (qSeq t) ≤ Z)
    (hdL : ∀ w : Fin M, d w ≤ L)
    (hTube : ∀ t : Nat, hockeyStickExcess M gamma (qSeq t) p ≤ budgetB)
    (hCert : drCvarHockeyStickEnvelope M Z gamma L tau budgetB p d + alpha * hMin ≤ Mctrl)
    (hDyn : ∀ t : Nat,
      ((S - alpha : Nat) : Int) * h t + (Mctrl : Int) -
        (sumFinNat M (fun w => qSeq t w * d w) : Int) ≤ (S : Int) * h (t + 1))
    (hInit : (hMin : Int) ≤ h 0) :
    ∀ T : Nat, (hMin : Int) ≤ h T := by
  intro T
  induction T with
  | zero => exact hInit
  | succ t ih =>
      have hDist :
          sumFinNat M (fun w => qSeq t w * d w) ≤
            drCvarHockeyStickEnvelope M Z gamma L tau budgetB p d :=
        hockey_stick_cvar_variational_duality_universal
          M Z gamma L tau budgetB (qSeq t) p d (hqZ t) hdL (hTube t)
      have hSubNonneg : 0 ≤ ((S - alpha : Nat) : Int) := by omega
      have hMono :
          ((S - alpha : Nat) : Int) * (hMin : Int) ≤ ((S - alpha : Nat) : Int) * h t :=
        Int.mul_le_mul_of_nonneg_left ih hSubNonneg
      have hStep := hDyn t
      have hnat : (S - alpha) * hMin + alpha * hMin = S * hMin := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hAlpha]
      have hCert2 : drCvarHockeyStickEnvelope M Z gamma L tau budgetB p d + (S - alpha) * hMin + alpha * hMin ≤ Mctrl + (S - alpha) * hMin := by
        omega
      rw [Nat.add_assoc, hnat] at hCert2
      have hRhs : (S : Int) * (hMin : Int) ≤ (S : Int) * h (t + 1) := by omega
      by_cases hlt : (hMin : Int) ≤ h (t + 1)
      · exact hlt
      · have hlt' : h (t + 1) + 1 ≤ (hMin : Int) := by omega
        have hmul' : (S : Int) * (h (t + 1) + 1) ≤ (S : Int) * (hMin : Int) :=
          Int.mul_le_mul_of_nonneg_left hlt' (by omega)
        have hexp : (S : Int) * (h (t + 1) + 1) = (S : Int) * h (t + 1) + (S : Int) * 1 :=
          Int.mul_add (S : Int) (h (t + 1)) 1
        omega

/-- Naive Mean-Calibrated CBF Crash Counterexample vs. Certified `DR-CBF` Survival:
    Initial barrier `h_0 = 0`, `S = 1, α = 1`, `p = (1,1,1,1)`, `d = (0,2,4,10)`, `q** = (0,0,1,3)`.
    - Naive controller sets `M_naive = ∑ p_w d_w = 16` → next state crashes to `h_1 = 16 - 34 = -18 < 0`!
    - Exact `DR-CBF` controller at `τ* = 4` sets `M_DR = 34` → next state maintains `h_1 = 34 - 34 = 0 ≥ 0`! -/
theorem naive_mean_calibrated_cbf_crashes_under_hockey_stick_shift :
    let disturbanceRealized : Int := (sumFinNat 4 (fun w => qAdversarial4 w * lossProfile4 w) : Int)
    let mNaive : Int := (sumFinNat 4 (fun w => pUniform4 w * lossProfile4 w) : Int)
    let mDrExact : Int := (drCvarHockeyStickEnvelope 4 4 2 10 4 1 pUniform4 lossProfile4 : Int)
    (mNaive - disturbanceRealized = -18 ∧ mNaive - disturbanceRealized < 0) ∧
    (mDrExact - disturbanceRealized = 0 ∧ 0 ≤ mDrExact - disturbanceRealized) := by
  decide

end CommonGround.Frontier.PerformativeHockeyStickCvarAndControlBarrier
