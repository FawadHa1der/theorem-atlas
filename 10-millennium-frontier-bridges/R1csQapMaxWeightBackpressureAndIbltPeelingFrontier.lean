/-
Copyright (c) 2026 Common Ground Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace CommonGround.Frontier.R1csQapMaxWeightBackpressureAndIbltPeeling

/-!
# Wave V243 Frontier (#118): `zkSNARK` `R1CS`/`QAP` Soundness & Frozen-Heart Guard, `MaxWeight` Backpressure Lyapunov Drift & `IBLT` Homomorphic Set Reconciliation

Unifies **Succinct Zero-Knowledge Proof Systems (`10`+`02`)**, **Stochastic Network Queue Control
(`04`+`08`)**, and **Algebraic Sketch Set Reconciliation (`09`+`02`)** under a single mathematical
mechanism: **certifying global system state from compressed linear/polynomial projections while
guarding exact algebraic premise-failure boundaries (`under-constrained gates`, `unhashed Fiat–Shamir
public inputs`, `queue-blind priority starvation`, and `checksum-free XOR phantom collisions`)**.
-/

/-- Pure-core finite sum over `Fin n` valued in `Int`. -/
def finSumInt : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f =>
      finSumInt n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) +
        f ⟨n, Nat.lt_succ_self n⟩

/-- Pure-core finite sum over `Fin n` valued in `Nat`. -/
def finSumNat : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f =>
      finSumNat n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) +
        f ⟨n, Nat.lt_succ_self n⟩

theorem finSumInt_add (n : Nat) (f g : Fin n → Int) :
    finSumInt n (fun i => f i + g i) = finSumInt n f + finSumInt n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [finSumInt]
      rw [ih]
      omega

theorem finSumInt_mul_const (n : Nat) (f : Fin n → Int) (c : Int) :
    finSumInt n (fun i => f i * c) = finSumInt n f * c := by
  induction n with
  | zero => simp [finSumInt]
  | succ k ih =>
      simp only [finSumInt]
      rw [ih, Int.add_mul]

theorem finSumInt_mul_left (n : Nat) (c : Int) (f : Fin n → Int) :
    finSumInt n (fun i => c * f i) = c * finSumInt n f := by
  induction n with
  | zero => simp [finSumInt]
  | succ k ih =>
      simp only [finSumInt]
      rw [ih, Int.mul_add]

theorem finSumInt_le_finSumInt (n : Nat) (f g : Fin n → Int)
    (h : ∀ i : Fin n, f i ≤ g i) :
    finSumInt n f ≤ finSumInt n g := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ k ih =>
      simp only [finSumInt]
      have h1 := ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                    (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                    (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      have h2 := h ⟨k, Nat.lt_succ_self k⟩
      omega

/-! ## Part I: `zkSNARK` `R1CS`-to-`QAP` Vanishing Equivalence & Schwartz–Zippel Soundness vs. Under-Constrained & Frozen-Heart Forgeries (`10`+`02`) -/

/-- Gate `0` (`r₀ = 1` over `𝔽₁₇`): boolean witness constraint `b · (1 - b) ≡ 0 (mod 17)`. -/
def r1csBooleanGate17 (b : Fin 17) : Fin 17 :=
  ⟨(b.val * ((18 - b.val) % 17)) % 17, Nat.mod_lt _ (by decide)⟩

/-- Gate `1` (`r₁ = 2` over `𝔽₁₇`): guarded payout constraint `b · 10 - out ≡ 0 (mod 17)`. -/
def r1csPayoutGate17 (b out : Fin 17) : Fin 17 :=
  ⟨(b.val * 10 + 17 - out.val) % 17, Nat.mod_lt _ (by decide)⟩

/-- Interpolated degree-`≤ 1` `QAP` gate-error polynomial `E_{b,out}(τ)` through `(1, e₀)` and `(2, e₁)`:
    `E(τ) = e₀ · (2 - τ) + e₁ · (τ - 1) mod 17`. -/
def qapErrorPoly17 (b out tau : Fin 17) : Fin 17 :=
  let e0 := (r1csBooleanGate17 b).val
  let e1 := (r1csPayoutGate17 b out).val
  let t0 := (e0 * ((19 - tau.val) % 17)) % 17
  let t1 := (e1 * ((tau.val + 16) % 17)) % 17
  ⟨(t0 + t1) % 17, Nat.mod_lt _ (by decide)⟩

/-- Number of verifier challenges `τ ∈ Fin 17` that detect a non-zero `QAP` error `E(τ) ≠ 0`. -/
def qapDetectCount17 (b out : Fin 17) : Nat :=
  finSumNat 17 (fun tau => if (qapErrorPoly17 b out tau).val != 0 then 1 else 0)

/-- Multiplicative inverse lookup table in `𝔽₁₇×` (`a · modInv17(a) ≡ 1 mod 17` for `1 ≤ a ≤ 16`). -/
def modInv17 (a : Nat) : Nat :=
  [0, 1, 9, 6, 13, 7, 3, 5, 15, 2, 12, 14, 10, 4, 11, 8, 16].getD (a % 17) 0

/-- **Positive Witness 1 (`r1cs_qap_vanishing_equivalence_and_schwartz_zippel_soundness_17`)**:
    1. Across ALL `289` witness pairs `(b, out) ∈ 𝔽₁₇²`, `E_{b,out}(τ) = 0` identically iff BOTH
       `R1CS` gates vanish (`(b, out) ∈ {(0, 0), (1, 10)}`).
    2. For ANY invalid witness `(b, out)` violating at least one gate (such as forged `5×` payout
       `b = 5, out = 16`), at least **`16` out of `17` challenges (`94.1%`)** detect `E(τ) ≠ 0`! -/
theorem r1cs_qap_vanishing_equivalence_and_schwartz_zippel_soundness_17 :
    (∀ b out : Fin 17,
      (∀ tau : Fin 17, qapErrorPoly17 b out tau = ⟨0, by decide⟩) ↔
        (r1csBooleanGate17 b = ⟨0, by decide⟩ ∧ r1csPayoutGate17 b out = ⟨0, by decide⟩)) ∧
    (∀ b out : Fin 17,
      ¬ (r1csBooleanGate17 b = ⟨0, by decide⟩ ∧ r1csPayoutGate17 b out = ⟨0, by decide⟩) →
        16 ≤ qapDetectCount17 b out) := by
  decide

/-- **Premise-Failure Counterexample 1A (`under_constrained_r1cs_allows_5x_mint_forgery`)**:
    Omitting the boolean gate `b · (1 - b) = 0` allows non-boolean witness `b = 5, out = 16`
    (`5 · 10 = 50 ≡ 16 mod 17`) to satisfy `r1csPayoutGate17` (`0`), whereas the full `2`-gate `QAP`
    catches it on `16 / 17` (`100%` of out-of-domain `τ ∉ {1, 2}`) challenges! -/
theorem under_constrained_r1cs_allows_5x_mint_forgery :
    r1csPayoutGate17 ⟨5, by decide⟩ ⟨16, by decide⟩ = ⟨0, by decide⟩ ∧
    r1csBooleanGate17 ⟨5, by decide⟩ = ⟨14, by decide⟩ ∧
    qapDetectCount17 ⟨5, by decide⟩ ⟨16, by decide⟩ = 16 := by
  decide

/-- **Premise-Failure Counterexample 1B (`frozen_heart_unhashed_public_input_universal_forgery_17`)**:
    In Fiat–Shamir Schnorr/Plonk linear verification `(R + c · Y) mod 17 = S`, if weak Fiat–Shamir
    hashes ONLY commitment `R` (`c = H(R) ≠ 0`) and omits public statement/key `Y`, then for EVERY
    `R, S ∈ 𝔽₁₇` and nonzero `c ∈ 𝔽₁₇×`, a keyless attacker computes `Y_forge = (S - R) · c⁻¹ mod 17`
    so verification succeeds with **`100%` (`4,624 / 4,624`) probability** without knowing any secret witness! -/
def frozenHeartForgeY17 (R c S : Fin 17) : Fin 17 :=
  ⟨(((S.val + 17 - R.val) % 17) * modInv17 c.val) % 17, Nat.mod_lt _ (by decide)⟩

theorem frozen_heart_unhashed_public_input_universal_forgery_17 :
    ∀ R c S : Fin 17, c.val ≠ 0 →
      (R.val + c.val * (frozenHeartForgeY17 R c S).val) % 17 = S.val := by
  decide

/-! ## Part II: `MaxWeight` Backpressure Quadratic Lyapunov Drift vs. Queue-Blind Priority Starvation (`04`+`08`) -/

/-- Quadratic queue Lyapunov energy `L₂(Q) = ∑_{i=0}^{K-1} Q(i)²`. -/
def queueLyapunovSq (K : Nat) (Q : Fin K → Int) : Int :=
  finSumInt K (fun i => Q i * Q i)

/-- Exact universal `Fin K` quadratic queue-evolution identity:
    `∑_i (Q_i + Δ_i)² = ∑_i Q_i² + ∑_i Δ_i² + 2 · ∑_i Q_i Δ_i`. -/
theorem quadratic_queue_drift_exact_identity (K : Nat) (Q Δ : Fin K → Int) :
    queueLyapunovSq K (fun i => Q i + Δ i) =
      queueLyapunovSq K Q + queueLyapunovSq K Δ +
        2 * finSumInt K (fun i => Q i * Δ i) := by
  induction K with
  | zero => rfl
  | succ m ih =>
      unfold queueLyapunovSq at *
      simp only [finSumInt]
      rw [ih (fun i => Q ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
             (fun i => Δ ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)]
      have hpt :
          (Q ⟨m, Nat.lt_succ_self m⟩ + Δ ⟨m, Nat.lt_succ_self m⟩) *
            (Q ⟨m, Nat.lt_succ_self m⟩ + Δ ⟨m, Nat.lt_succ_self m⟩) =
          Q ⟨m, Nat.lt_succ_self m⟩ * Q ⟨m, Nat.lt_succ_self m⟩ +
            Δ ⟨m, Nat.lt_succ_self m⟩ * Δ ⟨m, Nat.lt_succ_self m⟩ +
            2 * (Q ⟨m, Nat.lt_succ_self m⟩ * Δ ⟨m, Nat.lt_succ_self m⟩) := by
        grind
      omega

/-- **Universal `Fin K` `MaxWeight` Negative Quadratic Lyapunov Drift (`maxweight_negative_lyapunov_drift_bound`)**:
    Whenever `Q ≥ 0`, arrivals `A` have interior capacity slack `ε` (`A_i + ε ≤ S_feas(i)`),
    `MaxWeight` maximizes queue-weighted service `∑ Q_i S_feas(i) ≤ ∑ Q_i S_i`, and burst energy
    satisfies `∑ (A_i - S_i)² ≤ B`, one-step Lyapunov drift is bounded above by `B - 2 ε ∑ Q_i`
    (strictly negative as soon as total backlog `∑ Q_i > B / (2 ε)`)! -/
theorem maxweight_negative_lyapunov_drift_bound (K : Nat)
    (Q A S S_feas : Fin K → Int) (B ε : Int)
    (hNonnegQ : ∀ i : Fin K, 0 ≤ Q i)
    (hSlack : ∀ i : Fin K, A i + ε ≤ S_feas i)
    (hMaxWeight : finSumInt K (fun i => Q i * S_feas i) ≤ finSumInt K (fun i => Q i * S i))
    (hBurst : queueLyapunovSq K (fun i => A i - S i) ≤ B) :
    queueLyapunovSq K (fun i => Q i + (A i - S i)) - queueLyapunovSq K Q ≤
      B - 2 * ε * finSumInt K Q := by
  have hId := quadratic_queue_drift_exact_identity K Q (fun i => A i - S i)
  have hPoint : ∀ i : Fin K,
      Q i * (A i - S i) + Q i * ε ≤ Q i * S_feas i - Q i * S i := by
    intro i
    have hMul : Q i * (A i + ε) ≤ Q i * S_feas i :=
      Int.mul_le_mul_of_nonneg_left (hSlack i) (hNonnegQ i)
    have hDist : Q i * (A i + ε) = Q i * A i + Q i * ε := Int.mul_add (Q i) (A i) ε
    have hSub : Q i * (A i - S i) = Q i * A i - Q i * S i := Int.mul_sub (Q i) (A i) (S i)
    omega
  have hSumLe := finSumInt_le_finSumInt K
    (fun i => Q i * (A i - S i) + Q i * ε)
    (fun i => Q i * S_feas i - Q i * S i) hPoint
  rw [finSumInt_add] at hSumLe
  rw [finSumInt_mul_const K Q ε] at hSumLe
  have hSubSplit :
      finSumInt K (fun i => Q i * S_feas i - Q i * S i) =
        finSumInt K (fun i => Q i * S_feas i) - finSumInt K (fun i => Q i * S i) := by
    have hfn : (fun i : Fin K => Q i * S_feas i) =
        (fun i : Fin K => (Q i * S_feas i - Q i * S i) + Q i * S i) := by
      funext i; omega
    have hAdd := finSumInt_add K (fun i => Q i * S_feas i - Q i * S i) (fun i => Q i * S i)
    rw [← hfn] at hAdd
    omega
  rw [hSubSplit] at hSumLe
  have hComm : finSumInt K Q * ε = ε * finSumInt K Q := Int.mul_comm (finSumInt K Q) ε
  have hAssoc : 2 * ε * finSumInt K Q = 2 * (ε * finSumInt K Q) := Int.mul_assoc 2 ε (finSumInt K Q)
  omega

/-- Concrete `2`-queue contrast (`Q = (0, 10)`, `A = (2, 1)`, capacity `4`):
    - `MaxWeight` serves `(0, 4)` (`Q' = (2, 7)`), dropping `L₂` from `100` to `53` (`ΔL₂ = -47 < 0`)!
    - Static Queue-`0` priority wastes service on `Q₀ = 0` (`S_eff = (2, 0)`, `Q' = (0, 11)`),
      pushing `L₂` from `100` up to `121` (`ΔL₂ = +21 > 0`, linear starvation `Q₁(T) = 10 + T → ∞`)! -/
theorem maxweight_vs_static_priority_starvation_witness :
    let Q : Fin 2 → Int := fun i => if i.val == 0 then 0 else 10
    let Q_mw : Fin 2 → Int := fun i => if i.val == 0 then 2 else 7
    let Q_prio : Fin 2 → Int := fun i => if i.val == 0 then 0 else 11
    queueLyapunovSq 2 Q = 100 ∧
    queueLyapunovSq 2 Q_mw = 53 ∧
    queueLyapunovSq 2 Q_prio = 121 := by
  decide

/-! ## Part III: Invertible Bloom Lookup Table (`IBLT`) Homomorphic Set Reconciliation vs. Collision `2`-Core & Missing-Checksum Phantom Key (`09`+`02`) -/

/-- `4`-bit key/checksum XOR on `Fin 16` and nonlinear bucket integrity hash `H(k) = (k² + 3) mod 16`. -/
def xor16 (a b : Fin 16) : Fin 16 :=
  ⟨Nat.xor a.val b.val, by
    have ha := a.isLt
    have hb := b.isLt
    revert a b ha hb
    decide⟩

def ibltHash16 (k : Fin 16) : Fin 16 :=
  ⟨(k.val * k.val + 3) % 16, Nat.mod_lt _ (by decide)⟩

structure IbltCell where
  count : Int
  keyXor : Fin 16
  hashXor : Fin 16
  deriving DecidableEq, Repr

def ibltInsert (c : IbltCell) (k : Fin 16) : IbltCell :=
  { count := c.count + 1
  , keyXor := xor16 c.keyXor k
  , hashXor := xor16 c.hashXor (ibltHash16 k) }

def ibltDiff (cA cB : IbltCell) : IbltCell :=
  { count := cA.count - cB.count
  , keyXor := xor16 cA.keyXor cB.keyXor
  , hashXor := xor16 cA.hashXor cB.hashXor }

/-- Pure-cell test WITH nonlinear `hashXor` integrity check vs. naive count-only pure test. -/
def isPureVerified (c : IbltCell) : Bool :=
  (c.count == 1 || c.count == -1) && (ibltHash16 c.keyXor == c.hashXor)

def isPureCountOnly (c : IbltCell) : Bool :=
  c.count == 1 || c.count == -1

theorem xor16_cancel_right :
    ∀ a b k : Fin 16, xor16 (xor16 a k) (xor16 b k) = xor16 a b := by
  decide

/-- **Universal Shared-Key Cancellation (`iblt_shared_key_cancels_identically`)**:
    Inserting ANY shared key `k` into both Alice's cell `cA` and Bob's cell `cB` leaves the
    difference cell `ibltDiff` **100% invariant** regardless of `cA.count` (`|S_A ∩ S_B| = 10⁹`)! -/
theorem iblt_shared_key_cancels_identically (cA cB : IbltCell) (k : Fin 16) :
    ibltDiff (ibltInsert cA k) (ibltInsert cB k) = ibltDiff cA cB := by
  unfold ibltDiff ibltInsert
  have hc : (cA.count + 1) - (cB.count + 1) = cA.count - cB.count := by omega
  have hk := xor16_cancel_right cA.keyXor cB.keyXor k
  have hh := xor16_cancel_right cA.hashXor cB.hashXor (ibltHash16 k)
  rw [hc, hk, hh]

/-- **Positive Witness & Dual Premise-Failure Counterexamples (`iblt_peeling_vs_2core_and_phantom_key_counterexamples`)**:
    1. Singleton difference cell (`+5` on Alice) is certified pure (`isPureVerified = true`) and recovers `k = 5`.
    2. **Collision `2`-Core Stopping Set**: `+5` (Alice) and `-9` (Bob) colliding in the same bucket
       yield `Δcount = 0` while `ΔkeyXor = 12 ≠ 0` (`isPureVerified = false`, `0` peelable cells).
    3. **Missing-Checksum Phantom Key Corruption**: `+5` (Alice), `-9` (Bob), and `+14` (Alice)
       colliding in one bucket yield `Δcount = +1` (`isPureCountOnly = true`!) and phantom key
       `5 ⊕ 9 ⊕ 14 = 2 ∉ {5, 9, 14}`, which `isPureVerified` REJECTS (`ibltHash16(2) = 7 ≠ 15`)! -/
def emptyCell : IbltCell := ⟨0, ⟨0, by decide⟩, ⟨0, by decide⟩⟩

theorem iblt_peeling_vs_2core_and_phantom_key_counterexamples :
    let k5 : Fin 16 := ⟨5, by decide⟩
    let k9 : Fin 16 := ⟨9, by decide⟩
    let k14 : Fin 16 := ⟨14, by decide⟩
    let pure5 := ibltDiff (ibltInsert emptyCell k5) emptyCell
    let col2Core := ibltDiff (ibltInsert emptyCell k5) (ibltInsert emptyCell k9)
    let phantom3 := ibltDiff (ibltInsert (ibltInsert emptyCell k5) k14) (ibltInsert emptyCell k9)
    (isPureVerified pure5 = true ∧ pure5.keyXor = k5) ∧
    (col2Core.count = 0 ∧ col2Core.keyXor = ⟨12, by decide⟩ ∧ isPureVerified col2Core = false) ∧
    (phantom3.count = 1 ∧ phantom3.keyXor = ⟨2, by decide⟩ ∧
     isPureCountOnly phantom3 = true ∧ isPureVerified phantom3 = false) := by
  decide

end CommonGround.Frontier.R1csQapMaxWeightBackpressureAndIbltPeeling
