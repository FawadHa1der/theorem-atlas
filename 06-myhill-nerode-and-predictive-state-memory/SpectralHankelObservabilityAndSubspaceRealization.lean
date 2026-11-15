/-!
# Spectral Hankel Observability, Ho–Kalman Observable Operators & Horizon-Truncation Barriers

Pure-core Lean 4.33.0 formalization (`0 sorry`, `0` external dependencies) extending Folder `06`
(`Ending01.lean` and `PredictiveStateSufficiency.lean`) from discrete set-cardinality Myhill–Nerode
bounds (`|W| ≤ |M|`) to **linear/spectral Predictive State Representations (PSRs), Ho–Kalman subspace
identification, Hsu–Kakade–Zhang observable operators, and State-Space Sequence Models (SSMs)**:

1. **`hankel_bilinear_factorization_and_core_span_inheritance`**:
   - For any rank-`r` factored history-future Hankel pairing `H(h, z) = ∑_{k < r} φ_k(h) ψ_k(z)`:
     (a) Latent state equality across `k < r` implies universal future Nerode equivalence `∀ z, H(h₁, z) = H(h₂, z)`.
     (b) Whenever a future test functional decomposes in the span of `m` core tests `ψ(zNew, k) = ∑_{j < m} c_j ψ(zCore_j, k)`,
         its Hankel prediction inherits the exact same linear combination `H(h, zNew) = ∑_{j < m} c_j H(h, zCore_j)`.
2. **`observable_core_tests_and_ho_kalman_observable_operator_update`**:
   - Suppose `r` core tests `zCore_0, ..., zCore_{r-1}` form a full-rank observability matrix `O_{j, k} = ψ(zCore_j, k)`
     with integer left-inverse `OInv` at determinant scale `D ≠ 0` (`OInv · O = D · I_r`).
   - **Latent recovery & finite-core Nerode sufficiency**: `∑_{j < r} OInv_{i,j} H(h, zCore_j) = D · φ_i(h)`, so matching
     only the `r` finite core tests `H(h₁, zCore_j) = H(h₂, zCore_j)` (`j < r`) forces `H(h₁, z) = H(h₂, z)` for **all** `z`!
   - **Ho–Kalman / Spectral PSR Observable Operator Law**: Under linear state transitions `φ(step(h, a)) = T_a · φ(h)`,
     the observable core-test vector updates purely in observation space via `BScaled_a = O · T_a · OInv`:
     `D * H(step h a, zCore_i) = ∑_{j < r} BScaled_a(i, j) * H(h, zCore_j)` — requiring **zero** access to latent `φ`!
3. **`gauge_similarity_invariance_of_hankel_predictions`**:
   - Transforming latent states by `φ'(h) = S · φ(h)` and dual tests by `ψ'(z) = SInvᵀ · ψ(z)` (`SInvᵀ · S = D · I_r`)
     scales every Hankel entry uniformly by `D`, with an explicit `2×2` shear witness (`D = 1`) shifting neuron coordinate-0
     (`5 ≠ 2`) while leaving every observable prediction `H'(0, z) = H(0, z)` strictly unchanged.
4. **`unobservable_phantom_mode_and_short_horizon_blindness_counterexamples`**:
   - **Kalman Unobservable Phantom Mode (`ker(O) ≠ 0`)**: Distinct 2D hidden states `(3, 0)` vs `(3, 99)` (`0 ≠ 99`) produce
     identical Hankel payoffs across all future tests `z` when coordinate-1 lies in `ker(O)`, proving latent state dimension
     strictly overestimates minimal Nerode/Hankel rank without observability.
   - **Length-`≤ 1` Horizon Blindness (Delayed-Carry / `Ending01` Shift Register)**: Explicit rank-`3` system where two
     histories `(1, 0, 1)` and `(1, 0, 0)` match identically on length-`0` (`1 = 1`) and length-`1` (`0 = 0`) core tests,
     yet strictly diverge at horizon depth `2` (`1 ≠ 0`) — proving 1-step autoregressive / truncated-window core tests fail
     to recover minimal predictive state rank on delayed dependencies.
-/

namespace CommonGround.PredictiveStateMemory.SpectralHankelObservability

/-- Finite integer sum `∑_{k = 0}^{n - 1} f(k)`. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

/-- Rank-`r` integer inner product `∑_{k < r} u_k v_k`. -/
def dotProd (r : Nat) (u v : Nat → Int) : Int :=
  sumRange r (fun k => u k * v k)

/-- Factored rank-`r` history-future Hankel evaluation `H(h, z) = ⟨φ(h), ψ(z)⟩`. -/
def hankel (r : Nat) (φ ψ : Nat → Nat → Int) (h z : Nat) : Int :=
  dotProd r (φ h) (ψ z)

theorem sumRange_congr (n : Nat) (f g : Nat → Int) (h : ∀ k, k < n → f k = g k) :
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
    simp only [sumRange]
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

theorem sumRange_swap (m n : Nat) (F : Nat → Nat → Int) :
    sumRange m (fun i => sumRange n (fun j => F i j)) =
      sumRange n (fun j => sumRange m (fun i => F i j)) := by
  induction m with
  | zero =>
    have hZero : sumRange n (fun _ => (0 : Int)) = 0 := by
      induction n with
      | zero => rfl
      | succ k ihk => simp [sumRange, ihk]
    simp [sumRange, hZero]
  | succ m' ih =>
    simp only [sumRange]
    rw [ih, ← sumRange_add]

theorem sumRange_zero_of_forall_zero (n : Nat) (f : Nat → Int)
    (h : ∀ k, k < n → f k = 0) :
    sumRange n f = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [sumRange]
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h m (Nat.lt_succ_self m)]
    omega

/-- Kronecker-delta extraction `∑_{k < r} (if i = k then D * g(k) else 0) = D * g(i)` for `i < r`. -/
theorem sumRange_ite_eq_left (r i : Nat) (f : Nat → Int) (hi : i < r) :
    sumRange r (fun k => if i = k then f k else 0) = f i := by
  induction r with
  | zero => cases hi
  | succ m ih =>
    simp only [sumRange]
    by_cases him : i = m
    · subst him
      have hz : sumRange i (fun k => if i = k then f k else 0) = 0 := by
        apply sumRange_zero_of_forall_zero
        intro k hk
        have hne : i ≠ k := Nat.ne_of_gt hk
        simp [hne]
      simp [hz]
    · have hlt : i < m := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) him
      rw [ih hlt]
      simp [him]

/-- Theorem 1 (Hankel Factorization Sufficiency & Core-Test Span Linearity):
    (1) Equal rank-`r` latent states force identical Hankel expectations across all future tests `z`.
    (2) Any future test `zNew` lying in the integer linear span of `m` core tests `zCore_0, ..., zCore_{m-1}`
        has its Hankel value uniquely determined by those `m` observable core predictions. -/
theorem hankel_bilinear_factorization_and_core_span_inheritance
    (r m : Nat) (φ ψ : Nat → Nat → Int) (zCore : Nat → Nat) (c : Nat → Int) (zNew : Nat)
    (hSpan : ∀ k, k < r → ψ zNew k = sumRange m (fun j => c j * ψ (zCore j) k)) :
    ((∀ h₁ h₂ : Nat, (∀ k, k < r → φ h₁ k = φ h₂ k) →
        ∀ z : Nat, hankel r φ ψ h₁ z = hankel r φ ψ h₂ z) ∧
     (∀ h : Nat,
        hankel r φ ψ h zNew = sumRange m (fun j => c j * hankel r φ ψ h (zCore j)))) := by
  constructor
  · intro h₁ h₂ hEq z
    unfold hankel dotProd
    apply sumRange_congr
    intro k hk
    rw [hEq k hk]
  · intro h
    unfold hankel dotProd
    have h1 :
        sumRange r (fun k => φ h k * ψ zNew k) =
          sumRange r (fun k => sumRange m (fun j => c j * (φ h k * ψ (zCore j) k))) := by
      apply sumRange_congr
      intro k hk
      rw [hSpan k hk, ← sumRange_mul_left]
      apply sumRange_congr
      intro j _
      rw [← Int.mul_assoc, Int.mul_comm (φ h k) (c j), Int.mul_assoc]
    rw [h1, sumRange_swap]
    apply sumRange_congr
    intro j _
    rw [sumRange_mul_left]

/-- Scaled Ho–Kalman / Hsu–Kakade–Zhang observable transition operator `BScaled_a = O · T_a · OInv`. -/
def observableOperatorScaled
    (r : Nat) (ψ : Nat → Nat → Int) (zCore : Nat → Nat)
    (Ta OInv : Nat → Nat → Int) (i j : Nat) : Int :=
  sumRange r (fun k => ψ (zCore i) k * sumRange r (fun l => Ta k l * OInv l j))

/-- Theorem 2 (Observable Core-Test Sufficiency & Ho–Kalman Observable Operator Recursion):
    When `r` core tests `zCore` have left-invertible observability matrix `OInv · O = D · I_r`:
    (1) `∑_{j < r} OInv_{i,j} H(h, zCore_j) = D * φ(h, i)` recovers every latent coordinate up to `D`.
    (2) When `D ≠ 0`, matching only the `r` core tests `H(h₁, zCore_j) = H(h₂, zCore_j)` implies
        full infinite-horizon Nerode equivalence `∀ z, H(h₁, z) = H(h₂, z)`.
    (3) Under linear state dynamics `φ(step(h, a)) = T_a · φ(h)`, observable core predictions evolve
        directly via `D * H(step h a, zCore_i) = ∑_{j < r} BScaled_a(i, j) * H(h, zCore_j)`. -/
theorem observable_core_tests_and_ho_kalman_observable_operator_update
    (r : Nat) (D : Int) (φ ψ : Nat → Nat → Int) (zCore : Nat → Nat)
    (OInv : Nat → Nat → Int)
    (step : Nat → Nat → Nat) (a : Nat) (Ta : Nat → Nat → Int)
    (hObs : ∀ i k, i < r → k < r →
      sumRange r (fun j => OInv i j * ψ (zCore j) k) = if i = k then D else 0)
    (hStep : ∀ h k, k < r → φ (step h a) k = sumRange r (fun l => Ta k l * φ h l)) :
    ((∀ h i, i < r →
        sumRange r (fun j => OInv i j * hankel r φ ψ h (zCore j)) = D * φ h i) ∧
     (D ≠ 0 → ∀ h₁ h₂ : Nat,
        (∀ j, j < r → hankel r φ ψ h₁ (zCore j) = hankel r φ ψ h₂ (zCore j)) →
        ∀ z : Nat, hankel r φ ψ h₁ z = hankel r φ ψ h₂ z) ∧
     (∀ h i, i < r →
        D * hankel r φ ψ (step h a) (zCore i) =
          sumRange r (fun j =>
            observableOperatorScaled r ψ zCore Ta OInv i j * hankel r φ ψ h (zCore j)))) := by
  have hRecover : ∀ h i, i < r →
      sumRange r (fun j => OInv i j * hankel r φ ψ h (zCore j)) = D * φ h i := by
    intro h i hi
    unfold hankel dotProd
    have hL :
        sumRange r (fun j => OInv i j * sumRange r (fun k => φ h k * ψ (zCore j) k)) =
          sumRange r (fun j => sumRange r (fun k => (OInv i j * ψ (zCore j) k) * φ h k)) := by
      apply sumRange_congr
      intro j _
      rw [← sumRange_mul_left]
      apply sumRange_congr
      intro k _
      rw [← Int.mul_assoc, Int.mul_comm (OInv i j) (φ h k), Int.mul_assoc, Int.mul_comm (φ h k)]
    rw [hL, sumRange_swap]
    have hDelta :
        sumRange r (fun k => sumRange r (fun j => (OInv i j * ψ (zCore j) k) * φ h k)) =
          sumRange r (fun k => if i = k then D * φ h k else 0) := by
      apply sumRange_congr
      intro k hk
      rw [sumRange_mul_right, hObs i k hi hk]
      by_cases hik : i = k <;> simp [hik]
    rw [hDelta, sumRange_ite_eq_left r i (fun k => D * φ h k) hi]
  refine ⟨hRecover, ?_, ?_⟩
  · intro hD h₁ h₂ hCore z
    unfold hankel dotProd
    apply sumRange_congr
    intro k hk
    have hRec1 := hRecover h₁ k hk
    have hRec2 := hRecover h₂ k hk
    have hSumEq :
        sumRange r (fun j => OInv k j * hankel r φ ψ h₁ (zCore j)) =
          sumRange r (fun j => OInv k j * hankel r φ ψ h₂ (zCore j)) := by
      apply sumRange_congr
      intro j hj
      rw [hCore j hj]
    have hMulEq : D * φ h₁ k = D * φ h₂ k := by
      rw [← hRec1, ← hRec2, hSumEq]
    have hPhiEq : φ h₁ k = φ h₂ k := Int.eq_of_mul_eq_mul_left hD hMulEq
    rw [hPhiEq]
  · intro h i _
    have hRHS :
        sumRange r (fun j =>
          observableOperatorScaled r ψ zCore Ta OInv i j * hankel r φ ψ h (zCore j)) =
          sumRange r (fun k =>
            ψ (zCore i) k *
              sumRange r (fun l =>
                Ta k l * sumRange r (fun j => OInv l j * hankel r φ ψ h (zCore j)))) := by
      unfold observableOperatorScaled
      have stepA :
          sumRange r (fun j =>
            sumRange r (fun k => ψ (zCore i) k * sumRange r (fun l => Ta k l * OInv l j)) *
              hankel r φ ψ h (zCore j)) =
            sumRange r (fun j =>
              sumRange r (fun k =>
                ψ (zCore i) k *
                  sumRange r (fun l => Ta k l * (OInv l j * hankel r φ ψ h (zCore j))))) := by
        apply sumRange_congr
        intro j _
        rw [← sumRange_mul_right]
        apply sumRange_congr
        intro k _
        rw [Int.mul_assoc, ← sumRange_mul_right]
        apply congrArg (fun x => ψ (zCore i) k * x)
        apply sumRange_congr
        intro l _
        rw [Int.mul_assoc]
      rw [stepA, sumRange_swap]
      apply sumRange_congr
      intro k _
      rw [sumRange_mul_left]
      apply congrArg (fun x => ψ (zCore i) k * x)
      rw [sumRange_swap]
      apply sumRange_congr
      intro l _
      rw [sumRange_mul_left]
    rw [hRHS]
    have hSubRec :
        sumRange r (fun k =>
          ψ (zCore i) k *
            sumRange r (fun l =>
              Ta k l * sumRange r (fun j => OInv l j * hankel r φ ψ h (zCore j)))) =
          sumRange r (fun k => D * (φ (step h a) k * ψ (zCore i) k)) := by
      apply sumRange_congr
      intro k hk
      have hInner :
          sumRange r (fun l =>
            Ta k l * sumRange r (fun j => OInv l j * hankel r φ ψ h (zCore j))) =
            D * sumRange r (fun l => Ta k l * φ h l) := by
        rw [← sumRange_mul_left]
        apply sumRange_congr
        intro l hl
        rw [hRecover h l hl, ← Int.mul_assoc, Int.mul_comm (Ta k l) D, Int.mul_assoc]
      rw [hInner, ← hStep h k hk]
      rw [← Int.mul_assoc, Int.mul_comm (ψ (zCore i) k) D, Int.mul_assoc, Int.mul_comm (ψ (zCore i) k)]
    rw [hSubRec, sumRange_mul_left]
    rfl

/-- Shear gauge matrix `S = [[1, 1], [0, 1]]` and transpose-inverse `SInv = [[1, 0], [-1, 1]]`. -/
def shearS (j k : Nat) : Int :=
  if j = 0 ∧ k = 0 then 1
  else if j = 0 ∧ k = 1 then 1
  else if j = 1 ∧ k = 1 then 1
  else 0

def shearSInv (j i : Nat) : Int :=
  if j = 0 ∧ i = 0 then 1
  else if j = 1 ∧ i = 0 then -1
  else if j = 1 ∧ i = 1 then 1
  else 0

/-- Theorem 3 (Gauge Similarity Invariance of Hankel Predictions vs. Coordinate Non-Identifiability):
    Any gauge pair `(S, SInv)` with `SInvᵀ · S = D · I_r` scales all Hankel predictions by `D`,
    while an explicit `2×2` shear gauge (`D = 1`) alters neuron coordinate-0 (`5 ≠ 2`) yet preserves
    every observable Hankel entry `H'(0, z) = H(0, z)`. -/
theorem gauge_similarity_invariance_of_hankel_predictions
    (r : Nat) (D : Int) (φ ψ : Nat → Nat → Int) (S SInv : Nat → Nat → Int)
    (hGauge : ∀ i k, i < r → k < r →
      sumRange r (fun j => SInv j i * S j k) = if i = k then D else 0) :
    let φGauge := fun h j => sumRange r (fun k => S j k * φ h k)
    let ψGauge := fun z j => sumRange r (fun i => SInv j i * ψ z i)
    (∀ h z : Nat, hankel r φGauge ψGauge h z = D * hankel r φ ψ h z) ∧
    (let φ0 : Nat → Nat → Int := fun _ k => if k = 0 then 2 else 3
     let ψ0 : Nat → Nat → Int := fun z i => if i = 0 then Int.ofNat z + 1 else 2 * Int.ofNat z - 1
     let φ0Gauge := fun h j => sumRange 2 (fun k => shearS j k * φ0 h k)
     let ψ0Gauge := fun z j => sumRange 2 (fun i => shearSInv j i * ψ0 z i)
     φ0Gauge 0 0 = 5 ∧ φ0 0 0 = 2 ∧ φ0Gauge 0 0 ≠ φ0 0 0 ∧
     ∀ z : Nat, hankel 2 φ0Gauge ψ0Gauge 0 z = hankel 2 φ0 ψ0 0 z) := by
  intro φGauge ψGauge
  constructor
  · intro h z
    unfold hankel dotProd
    have hExpand :
        sumRange r (fun j => φGauge h j * ψGauge z j) =
          sumRange r (fun j =>
            sumRange r (fun k =>
              sumRange r (fun i => (SInv j i * S j k) * (φ h k * ψ z i)))) := by
      apply sumRange_congr
      intro j _
      dsimp [φGauge, ψGauge]
      rw [← sumRange_mul_right]
      apply sumRange_congr
      intro k _
      rw [← sumRange_mul_left]
      apply sumRange_congr
      intro i _
      have hComm :
          (S j k * φ h k) * (SInv j i * ψ z i) =
            (SInv j i * S j k) * (φ h k * ψ z i) := by
        rw [Int.mul_assoc, ← Int.mul_assoc (φ h k) (SInv j i) (ψ z i),
            Int.mul_comm (φ h k) (SInv j i), Int.mul_assoc (SInv j i) (φ h k) (ψ z i),
            ← Int.mul_assoc (S j k) (SInv j i), Int.mul_comm (S j k) (SInv j i), Int.mul_assoc]
      exact hComm
    rw [hExpand, sumRange_swap]
    have hSwapInner :
        sumRange r (fun k =>
          sumRange r (fun j =>
            sumRange r (fun i => (SInv j i * S j k) * (φ h k * ψ z i)))) =
          sumRange r (fun k =>
            sumRange r (fun i =>
              sumRange r (fun j => (SInv j i * S j k) * (φ h k * ψ z i)))) := by
      apply sumRange_congr
      intro k _
      exact sumRange_swap r r (fun j i => (SInv j i * S j k) * (φ h k * ψ z i))
    rw [hSwapInner]
    have hCollapse :
        sumRange r (fun k =>
          sumRange r (fun i =>
            sumRange r (fun j => (SInv j i * S j k) * (φ h k * ψ z i)))) =
          sumRange r (fun k => D * (φ h k * ψ z k)) := by
      apply sumRange_congr
      intro k hk
      have hInnerI :
          sumRange r (fun i =>
            sumRange r (fun j => (SInv j i * S j k) * (φ h k * ψ z i))) =
            sumRange r (fun i => if k = i then D * (φ h k * ψ z i) else 0) := by
        apply sumRange_congr
        intro i hi
        rw [sumRange_mul_right, hGauge i k hi hk]
        by_cases hki : k = i
        · subst hki; simp
        · have hik : i ≠ k := fun hEq => hki hEq.symm
          simp [hki, hik]
      rw [hInnerI, sumRange_ite_eq_left r k (fun i => D * (φ h k * ψ z i)) hk]
    rw [hCollapse, sumRange_mul_left]
  · refine ⟨by decide, by decide, by decide, ?_⟩
    intro z
    simp [hankel, dotProd, sumRange, shearS, shearSInv]
    omega

/-- Phantom-mode latent vectors `(3, 0)` vs `(3, 99)` with unobservable second coordinate. -/
def φPhantom (h k : Nat) : Int :=
  if k = 0 then 3 else if h = 0 then 0 else 99

def ψPhantom (z k : Nat) : Int :=
  if k = 0 then Int.ofNat z + 1 else 0

/-- Delayed-carry 3-state representations `(1, 0, 1)` vs `(1, 0, 0)` indistinguishable at depth `≤ 1`. -/
def φDelay (h k : Nat) : Int :=
  if k = 0 then 1
  else if k = 1 then 0
  else if h = 0 then 1 else 0

def ψDelay (z k : Nat) : Int :=
  if z = 0 then (if k = 0 then 1 else 0)
  else if z = 1 then (if k = 1 then 1 else 0)
  else (if k = 2 then 1 else 0)

/-- Theorem 4 (Premise-Failure Counterexamples: Unobservable Phantom Modes & Horizon-`≤ 1` Blindness):
    (1) When `ker(O) ≠ 0`, distinct latent states (`0 ≠ 99`) yield identical infinite-horizon Hankel
        predictions `∀ z, H(0, z) = H(1, z)`.
    (2) Truncating core tests to horizon `≤ 1` (`z ∈ {0, 1}`) merges two histories that strictly
        diverge at horizon `z = 2` (`1 ≠ 0`), breaking minimal predictive rank recovery. -/
theorem unobservable_phantom_mode_and_short_horizon_blindness_counterexamples :
    (φPhantom 0 1 ≠ φPhantom 1 1 ∧
     ∀ z : Nat, hankel 2 φPhantom ψPhantom 0 z = hankel 2 φPhantom ψPhantom 1 z) ∧
    (hankel 3 φDelay ψDelay 0 0 = hankel 3 φDelay ψDelay 1 0 ∧
     hankel 3 φDelay ψDelay 0 1 = hankel 3 φDelay ψDelay 1 1 ∧
     hankel 3 φDelay ψDelay 0 2 = 1 ∧
     hankel 3 φDelay ψDelay 1 2 = 0 ∧
     hankel 3 φDelay ψDelay 0 2 ≠ hankel 3 φDelay ψDelay 1 2) := by
  refine ⟨⟨by decide, ?_⟩, by decide, by decide, by decide, by decide, by decide⟩
  intro z
  simp [hankel, dotProd, sumRange, φPhantom, ψPhantom]

end CommonGround.PredictiveStateMemory.SpectralHankelObservability
