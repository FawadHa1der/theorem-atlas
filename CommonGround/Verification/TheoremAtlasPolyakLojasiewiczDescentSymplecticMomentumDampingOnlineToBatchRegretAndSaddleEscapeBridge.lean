/-
Copyright (c) 2026 Common Ground Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Verification Bridge Suite #611: Overparameterized Polyak–Łojasiewicz Descent, Heavy-Ball Symplectic Momentum, Online-to-Batch Averaging, Negative-Curvature Saddle Escape, Discrete Grönwall Dissipation & Frank–Wolfe Duality Certificates

Cross-domain Lean 4.33.0 bridge suite (`0` imports, `0` `sorry`) connecting
`econlib`, `cslib`, `tc-analysis`, `physlib`, `tc-geometry`, `euler`, `oai-extremal`, and `tauceti`:

1. `econlib_cslib_overparameterized_pl_dominance_vs_quartic_saddle_trap_bridge`:
   Overparameterized rank-deficient regression `L(u, v) = (u + v - y)^2` (`det H = 0` along flat
   gauge fiber `(t, -t)`) satisfies global PŁ gradient dominance `‖∇L‖₂² = 8 L` and reaches the
   exact minimum manifold in 1 step `(u - (u+v-y)/2, v - (u+v-y)/2)`, contrasted with quartic
   strict saddle `W(x) = (x^2 - 1)^2` where `W'(0) = 0` freezes deterministic gradient descent at
   `W(0) = 1 > 0`.
2. `analysis_physlib_heavy_ball_kappa9_acceleration_vs_undamped_six_cycle_bridge`:
   Critically damped Polyak Heavy-Ball (`α = 1/4, β = 1/4`) on `κ = 9` (`λ₁ = 1, λ₂ = 9`) places
   double roots at `±1/2` (`1/4 < 16/25`, cross-multiplied `25 < 64` vs. optimal scalar GD),
   contrasted with undamped symplectic momentum (`β = 1`) looping in a periodic `6`-cycle.
3. `cslib_econlib_online_to_batch_variance_drop_vs_nonconvex_rebasin_barrier_bridge`:
   Exact convex quadratic variance drop `2((w₁ - y)^2 + (w₂ - y)^2) - (w₁ + w₂ - 2y)^2 = (w₁ - w₂)^2 ≥ 0`
   contrasted with sign-symmetric non-convex `W(w) = (w^2 - 1)^2`, where zero-loss solutions
   `w₁ = -1, w₂ = +1` average to barrier `W(0) = 1 > 0` unless permutation-aligned (`w₂' = -w₂ = -1`).
4. `geometry_physlib_strict_saddle_negative_curvature_escape_vs_zero_gradient_stall_bridge`:
   Jin–Ge–Netrapalli–Kakade–Jordan negative-curvature saddle escape on `S(x, y) = x^2 - 2 y^2`:
   at `(0, 0)`, `∇S(0, 0) = (0, 0)` stalls pure first-order GD (`S(0, 0) = 0`), whereas stepping
   along negative Hessian eigenvector `e_y = (0, 1)` (`λ_min = -4 < 0`) strictly decreases energy
   `S(0, δ) = -2 δ^2 < 0` for every nonzero perturbation `δ ≠ 0`!
5. `euler_analysis_discrete_gronwall_dissipative_decay_vs_anti_dissipative_blowup_bridge`:
   Discrete dissipative Grönwall contraction `E_{t+1} ≤ E_t` (`2 E_{t+1} = E_t` decays `2^T E_T = E_0`)
   contrasted with anti-dissipative pumping `E_{t+1} = 2 E_t` (`E_T = 2^T E_0` exponential blowup).
6. `extremal_tauceti_frank_wolfe_duality_gap_certificate_vs_unbounded_domain_failure_bridge`:
   Jaggi Frank–Wolfe linear-oracle duality gap `g_FW(x) = max_{s ∈ [-1, 1]} f'(x)(x - s)` upper-bounds
   unknown suboptimality `f(x) - f(x*)` for convex `f(x) = x^2` (`2|x| + x^2 ≥ x^2`? Even sharper:
   `f'(x)(x - s) ≥ f(x) - f(s)` with exact Bregman slack `(x - s)^2 ≥ 0`!), contrasted with
   unbounded `s ∈ ℤ` where `f'(1)(1 - (-M)) = 2(1 + M) → +∞` even at finite suboptimality `1`.
-/

namespace CommonGround.Verification.TheoremAtlasPolyakLojasiewiczDescentSymplecticMomentumDampingOnlineToBatchRegretAndSaddleEscapeBridge

/-! ## Helper Nonnegativity Lemma (`0` Imports) -/

theorem int_sq_nonneg (z : Int) : 0 ≤ z * z := by
  by_cases hz : 0 ≤ z
  · exact Int.mul_nonneg hz hz
  · have hneg : 0 ≤ -z := by omega
    have hnn : 0 ≤ (-z) * (-z) := Int.mul_nonneg hneg hneg
    have hsq : (-z) * (-z) = z * z := by rw [Int.neg_mul_neg]
    rw [← hsq]
    exact hnn

/-! ## Bridge 1 (`econlib` ↔ `cslib`): Overparameterized PŁ Dominance vs. Quartic Saddle Trap -/

def overparamLoss (u v y : Int) : Int :=
  (u + v - y) * (u + v - y)

def overparamGradNormSq (u v y : Int) : Int :=
  4 * ((u + v - y) * (u + v - y)) + 4 * ((u + v - y) * (u + v - y))

def quarticWell (x : Int) : Int :=
  (x * x - 1) * (x * x - 1)

def quarticWellGrad (x : Int) : Int :=
  4 * x * (x * x - 1)

theorem econlib_cslib_overparameterized_pl_dominance_vs_quartic_saddle_trap_bridge :
    -- Singular Hessian det([[2,2],[2,2]]) = 0 & gauge invariance along (t, -t)
    (2 * 2 - 2 * 2 = (0 : Int)) ∧
    (∀ u v y t : Int, overparamLoss (u + t) (v - t) y = overparamLoss u v y) ∧
    -- Exact global PŁ gradient dominance ‖∇L‖₂² = 8 L
    (∀ u v y : Int, overparamGradNormSq u v y = 8 * overparamLoss u v y) ∧
    -- Quartic saddle trap at x = 0: gradient vanishes while suboptimality is 1 > 0
    (quarticWellGrad 0 = 0 ∧ quarticWell 0 = 1 ∧ quarticWell 1 = 0 ∧
      ∀ eta : Int, 0 - eta * quarticWellGrad 0 = 0) := by
  refine ⟨by decide, ?_, ?_, ⟨by decide, by decide, by decide, ?_⟩⟩
  · intro u v y t
    dsimp [overparamLoss]
    have h : (u + t) + (v - t) - y = u + v - y := by omega
    rw [h]
  · intro u v y
    dsimp [overparamGradNormSq, overparamLoss]
    omega
  · intro eta
    dsimp [quarticWellGrad]
    simp

/-! ## Bridge 2 (`tc-analysis` ↔ `physlib`): Heavy-Ball `κ = 9` Acceleration vs. Undamped `6`-Cycle -/

def hbCharPoly4 (lam p q : Int) : Int :=
  4 * (p * p) - (5 - lam) * (p * q) + q * q

structure PhasePt where
  cur : Int
  prev : Int
  deriving DecidableEq, Repr

def undampedMomentum (s : PhasePt) : PhasePt :=
  ⟨s.cur - s.prev, s.cur⟩

def iterPhase : Nat → PhasePt → PhasePt
  | 0, s => s
  | n + 1, s => iterPhase n (undampedMomentum s)

theorem analysis_physlib_heavy_ball_kappa9_acceleration_vs_undamped_six_cycle_bridge :
    (∀ p q : Int,
      hbCharPoly4 1 p q = (2 * p - q) * (2 * p - q) ∧
      hbCharPoly4 9 p q = (2 * p + q) * (2 * p + q)) ∧
    -- Squared contraction comparison at κ = 9: Heavy-Ball 1/4 < 16/25 Optimal Scalar GD
    (25 * 1 < 4 * 16) ∧
    -- Undamped β = 1 momentum has exact period 6 and never damps ⟨1, 0⟩ to ⟨0, 0⟩
    (∀ s : PhasePt, iterPhase 6 s = s) ∧
    iterPhase 3 ⟨1, 0⟩ = ⟨-1, 0⟩ := by
  refine ⟨?_, by decide, ?_, by decide⟩
  · intro p q
    have hpp : (2 * p) * (2 * p) = 4 * (p * p) := by
      calc
        (2 * p) * (2 * p) = 2 * (p * (2 * p)) := Int.mul_assoc 2 p (2 * p)
        _ = 2 * (2 * (p * p)) := by
          rw [← Int.mul_assoc p 2 p, Int.mul_comm p 2, Int.mul_assoc 2 p p]
        _ = 4 * (p * p) := by rw [← Int.mul_assoc 2 2 (p * p)]; rfl
    have hpq1 : (2 * p) * q = 2 * (p * q) := Int.mul_assoc 2 p q
    have hpq2 : q * (2 * p) = 2 * (p * q) := by
      rw [Int.mul_comm q (2 * p), Int.mul_assoc 2 p q]
    constructor
    · dsimp [hbCharPoly4]
      have hsub : (2 * p - q) * (2 * p - q) = 4 * (p * p) - 4 * (p * q) + q * q := by
        calc
          (2 * p - q) * (2 * p - q)
              = (2 * p) * (2 * p - q) - q * (2 * p - q) := Int.sub_mul (2 * p) q (2 * p - q)
          _ = ((2 * p) * (2 * p) - (2 * p) * q) - (q * (2 * p) - q * q) := by
              rw [Int.mul_sub (2 * p) (2 * p) q, Int.mul_sub q (2 * p) q]
          _ = (4 * (p * p) - 2 * (p * q)) - (2 * (p * q) - q * q) := by rw [hpp, hpq1, hpq2]
          _ = 4 * (p * p) - 4 * (p * q) + q * q := by omega
      omega
    · dsimp [hbCharPoly4]
      have hadd : (2 * p + q) * (2 * p + q) = 4 * (p * p) + 4 * (p * q) + q * q := by
        calc
          (2 * p + q) * (2 * p + q)
              = (2 * p) * (2 * p + q) + q * (2 * p + q) := Int.add_mul (2 * p) q (2 * p + q)
          _ = ((2 * p) * (2 * p) + (2 * p) * q) + (q * (2 * p) + q * q) := by
              rw [Int.mul_add (2 * p) (2 * p) q, Int.mul_add q (2 * p) q]
          _ = (4 * (p * p) + 2 * (p * q)) + (2 * (p * q) + q * q) := by rw [hpp, hpq1, hpq2]
          _ = 4 * (p * p) + 4 * (p * q) + q * q := by omega
      omega
  · intro s
    cases s with
    | mk c p =>
      dsimp [iterPhase, undampedMomentum]
      congr 1 <;> omega

/-! ## Bridge 3 (`cslib` ↔ `econlib`): Online-to-Batch Variance Drop vs. Non-Convex Re-Basin Barrier -/

def o2bDrop (w1 w2 y : Int) : Int :=
  2 * ((w1 - y) * (w1 - y) + (w2 - y) * (w2 - y)) - (w1 + w2 - 2 * y) * (w1 + w2 - 2 * y)

theorem cslib_econlib_online_to_batch_variance_drop_vs_nonconvex_rebasin_barrier_bridge :
    (∀ w1 w2 y : Int, o2bDrop w1 w2 y = (w1 - w2) * (w1 - w2) ∧ 0 ≤ o2bDrop w1 w2 y) ∧
    -- Naive midpoint average of symmetric modes (-1, +1) hits barrier W(0) = 1 > 0,
    -- whereas sign-aligned ("Re-Basin") average of (-1, -(+1)) = (-1, -1) preserves W(-1) = 0!
    (quarticWell (-1) = 0 ∧ quarticWell 1 = 0 ∧
      quarticWell (((-1 : Int) + 1) / 2) = 1 ∧
      quarticWell (((-1 : Int) + (-1)) / 2) = 0) := by
  refine ⟨?_, ⟨by decide, by decide, by decide, by decide⟩⟩
  intro w1 w2 y
  have hQuad : ∀ a b : Int, 2 * (a * a + b * b) - (a + b) * (a + b) = (a - b) * (a - b) := by
    intro a b
    have hA : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
      calc
        (a + b) * (a + b) = a * (a + b) + b * (a + b) := Int.add_mul a b (a + b)
        _ = (a * a + a * b) + (b * a + b * b) := by rw [Int.mul_add a a b, Int.mul_add b a b]
        _ = (a * a + a * b) + (a * b + b * b) := by rw [Int.mul_comm b a]
        _ = a * a + 2 * (a * b) + b * b := by omega
    have hS : (a - b) * (a - b) = a * a - 2 * (a * b) + b * b := by
      calc
        (a - b) * (a - b) = a * (a - b) - b * (a - b) := Int.sub_mul a b (a - b)
        _ = (a * a - a * b) - (b * a - b * b) := by rw [Int.mul_sub a a b, Int.mul_sub b a b]
        _ = (a * a - a * b) - (a * b - b * b) := by rw [Int.mul_comm b a]
        _ = a * a - 2 * (a * b) + b * b := by omega
    rw [hA, hS]
    omega
  have hid : o2bDrop w1 w2 y = (w1 - w2) * (w1 - w2) := by
    dsimp [o2bDrop]
    have hs : w1 + w2 - 2 * y = (w1 - y) + (w2 - y) := by omega
    have hd : w1 - w2 = (w1 - y) - (w2 - y) := by omega
    rw [hs, hd]
    exact hQuad (w1 - y) (w2 - y)
  exact ⟨hid, hid ▸ int_sq_nonneg (w1 - w2)⟩

/-! ## Bridge 4 (`tc-geometry` ↔ `physlib`): Negative-Curvature Strict-Saddle Escape vs. Zero-Gradient Stall -/

def morseSaddle (x y : Int) : Int :=
  x * x - 2 * (y * y)

def morseGradX (x : Int) : Int := 2 * x
def morseGradY (y : Int) : Int := -4 * y

theorem geometry_physlib_strict_saddle_negative_curvature_escape_vs_zero_gradient_stall_bridge :
    -- At origin (0, 0), gradient vanishes (stalling pure GD), yet Hessian y-eigenvalue is -4 < 0
    (morseGradX 0 = 0 ∧ morseGradY 0 = 0 ∧ morseSaddle 0 0 = 0) ∧
    -- Stepping along negative-curvature eigenvector (0, δ) strictly lowers energy for every δ ≠ 0!
    (∀ delta : Int, delta ≠ 0 → morseSaddle 0 delta < morseSaddle 0 0) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  intro delta hne
  dsimp [morseSaddle]
  have hpos : 0 < delta * delta := by
    by_cases hd : 0 < delta
    · exact Int.mul_pos hd hd
    · have hnd : 0 < -delta := by omega
      have hp : 0 < (-delta) * (-delta) := Int.mul_pos hnd hnd
      rw [Int.neg_mul_neg] at hp
      exact hp
  omega

/-! ## Bridge 5 (`euler` ↔ `tc-analysis`): Discrete Grönwall Dissipative Decay vs. Anti-Dissipative Blowup -/

def pow2Nat : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * pow2Nat n

def doubleIter : Nat → Nat → Nat
  | 0, e0 => e0
  | n + 1, e0 => 2 * doubleIter n e0

theorem euler_analysis_discrete_gronwall_dissipative_decay_vs_anti_dissipative_blowup_bridge :
    -- Dissipative step 2 * E(t+1) ≤ E(t) implies 2^T * E(T) ≤ E(0) for all T : Nat
    (∀ (E : Nat → Nat), (∀ t : Nat, 2 * E (t + 1) ≤ E t) → ∀ T : Nat, pow2Nat T * E T ≤ E 0) ∧
    -- Anti-dissipative pumping E(t+1) = 2 * E(t) blows up exponentially E(T) = 2^T * E(0)
    (∀ T e0 : Nat, doubleIter T e0 = pow2Nat T * e0) ∧
    doubleIter 6 1 = 64 := by
  refine ⟨?_, ?_, by decide⟩
  · intro E hStep T
    induction T with
    | zero =>
      dsimp [pow2Nat]
      omega
    | succ t ih =>
      dsimp [pow2Nat]
      have ht : 2 * E (t + 1) ≤ E t := hStep t
      have hmul : pow2Nat t * (2 * E (t + 1)) ≤ pow2Nat t * E t := by
        induction pow2Nat t with
        | zero => simp [Nat.zero_mul]
        | succ k ihk =>
          rw [Nat.succ_mul k (2 * E (t + 1)), Nat.succ_mul k (E t)]
          exact Nat.add_le_add ihk ht
      have hassoc : (2 * pow2Nat t) * E (t + 1) = pow2Nat t * (2 * E (t + 1)) := by
        calc
          (2 * pow2Nat t) * E (t + 1) = (pow2Nat t * 2) * E (t + 1) := by rw [Nat.mul_comm 2 (pow2Nat t)]
          _ = pow2Nat t * (2 * E (t + 1)) := Nat.mul_assoc (pow2Nat t) 2 (E (t + 1))
      omega
  · intro T e0
    induction T with
    | zero =>
      dsimp [doubleIter, pow2Nat]
      omega
    | succ t ih =>
      dsimp [doubleIter, pow2Nat]
      rw [ih]
      exact (Nat.mul_assoc 2 (pow2Nat t) e0).symm

/-! ## Bridge 6 (`oai-extremal` ↔ `tauceti`): Frank–Wolfe Duality Gap Certificate vs. Unbounded Domain Failure -/

/-- Linearized Frank–Wolfe gap term `f'(x)(x - s) = 2 x (x - s)` for convex `f(x) = x^2`. -/
def fwPairGap (x s : Int) : Int :=
  (2 * x) * (x - s)

theorem extremal_tauceti_frank_wolfe_duality_gap_certificate_vs_unbounded_domain_failure_bridge :
    -- Exact Bregman convexity identity: fwPairGap x s - (x^2 - s^2) = (x - s)^2 ≥ 0, so
    -- fwPairGap x s ALWAYS upper-bounds true suboptimality x^2 - s^2 for every feasible s!
    (∀ x s : Int,
      fwPairGap x s - (x * x - s * s) = (x - s) * (x - s) ∧
      x * x - s * s ≤ fwPairGap x s) ∧
    -- Unbounded-domain premise failure: at x = 1 (true suboptimality x^2 - 0 = 1),
    -- letting s = -M ∈ ℤ makes fwPairGap 1 (-M) = 2(1 + M) arbitrarily large!
    (∀ M : Int, 0 ≤ M → 2 + 2 * M = fwPairGap 1 (-M)) := by
  refine ⟨?_, ?_⟩
  · intro x s
    have hid : fwPairGap x s - (x * x - s * s) = (x - s) * (x - s) := by
      dsimp [fwPairGap]
      have hL : (2 * x) * (x - s) = 2 * (x * x) - 2 * (x * s) := by
        calc
          (2 * x) * (x - s) = (2 * x) * x - (2 * x) * s := Int.mul_sub (2 * x) x s
          _ = 2 * (x * x) - 2 * (x * s) := by rw [Int.mul_assoc 2 x x, Int.mul_assoc 2 x s]
      have hR : (x - s) * (x - s) = x * x - 2 * (x * s) + s * s := by
        calc
          (x - s) * (x - s) = x * (x - s) - s * (x - s) := Int.sub_mul x s (x - s)
          _ = (x * x - x * s) - (s * x - s * s) := by rw [Int.mul_sub x x s, Int.mul_sub s x s]
          _ = (x * x - x * s) - (x * s - s * s) := by rw [Int.mul_comm s x]
          _ = x * x - 2 * (x * s) + s * s := by omega
      rw [hL, hR]
      omega
    have hnn : 0 ≤ (x - s) * (x - s) := int_sq_nonneg (x - s)
    refine ⟨hid, ?_⟩
    omega
  · intro M _
    dsimp [fwPairGap]
    omega

end CommonGround.Verification.TheoremAtlasPolyakLojasiewiczDescentSymplecticMomentumDampingOnlineToBatchRegretAndSaddleEscapeBridge
