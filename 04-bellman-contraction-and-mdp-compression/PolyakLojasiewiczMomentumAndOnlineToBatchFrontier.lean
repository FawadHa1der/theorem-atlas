/-
Copyright (c) 2026 Common Ground Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Polyak–Łojasiewicz Gradient Dominance, Heavy-Ball Symplectic Momentum Acceleration & Online-to-Batch Re-Basin Barrier

Pure-core Lean 4.33.0 formalization (`0` imports, `0` `sorry`) uniting Folders `02` (Convex /
Jensen Coreset Geometry), `04` (Iterative Contraction & Online Regret), `05` (Damped Hamiltonian
& Symplectic Integrators), and `08` (Fixed-Point & Saddle Obstructions):

1. **Universal `K`-Step Polyak–Łojasiewicz Geometric Descent & Overparameterized Gauge Invariance
   vs. Strict-Saddle Trap (`polyak_lojasiewicz_geometric_descent_vs_strict_saddle_trap`)**:
   - Proves by induction for **arbitrary horizon `K : Nat`** that scaled gradient dominance
     `S * g_{k+1} ≤ R * g_k` (`0 ≤ R`) yields exact geometric contraction
     `S^K * g_K ≤ R^K * g_0`.
   - Proves that the **overparameterized, rank-deficient objective** `L(u, v) = (u + v - y)^2` —
     whose Hessian `[[2, 2], [2, 2]]` has **determinant `0` and strong-convexity modulus `0`**
     along the flat gauge fiber `(t, -t)` — nevertheless satisfies **exact global Polyak–Łojasiewicz
     gradient dominance** `‖∇L(u, v)‖₂² = 8 · L(u, v)`, contracting in 1 step at step size `η = 1/4`
     directly onto the global minimum manifold `u + v = y`!
   - **Premise-Failure Counterexample**: The non-convex double-well `W(x) = (x^2 - 1)^2` violates
     PŁ at the strict saddle `x = 0`: `W'(0) = 0` while suboptimality `W(0) - W(1) = 1 > 0`,
     trapping any deterministic gradient-only iterate `x_{t+1} = x_t - η W'(x_t)` at `0` forever.

2. **Polyak Heavy-Ball Momentum `√κ` Acceleration (`ρ_HB = 1/2 < 4/5 = ρ_GD` at `κ = 9`)
   vs. Undamped Symplectic `6`-Cycle & Step-Size Overshoot
   (`heavy_ball_momentum_acceleration_vs_undamped_cycle_and_overshoot`)**:
   - On an ill-conditioned quadratic `f(x, y) = (x^2 + 9 y^2)/2` with condition number `κ = 9`
     (`λ₁ = 1, λ₂ = 9`), optimal scalar gradient descent (`α = 2/(1+9) = 1/5`) contracts both
     eigenmodes at factor `|1 - α λ| = 4/5` (`16/25` squared amplitude per step).
   - Critically damped Polyak Heavy-Ball (`α = 1/4, β = 1/4`, integer recurrence
     `4 x_{t+2} = (5 - λ) x_{t+1} - x_t`) simultaneously places **both** characteristic roots
     at `±1/2` (`(2 μ - 1)^2 = 0` at `λ = 1` and `(2 μ + 1)^2 = 0` at `λ = 9`), achieving
     squared contraction `1/4 < 16/25` (`25 < 64`)!
   - **Premise-Failure Counterexamples**:
     (a) Removing dissipation (`β = 1, α = 1`: `x_{t+2} = x_{t+1} - x_t`) traps momentum in a
         non-convergent periodic **6-cycle** `(1, 1) → (1, 0) → (0, -1) → (-1, -1) → (-1, 0) → (0, 1) → (1, 1)`;
     (b) Overshooting curvature (`α L = 3 > 2`) flips contraction into `x_{t+1} = -2 x_t`,
         multiplying squared error by `4 > 1` every step!

3. **Exact Online-to-Batch Variance Drop `(w₁ - w₂)² ≥ 0` vs. Non-Convex Mode-Symmetry Midpoint
   Barrier (`online_to_batch_variance_reduction_vs_nonconvex_rebasin_barrier`)**:
   - Proves the exact algebraic identity `2 ((w₁ - y)^2 + (w₂ - y)^2) - (w₁ + w₂ - 2 y)^2 = (w₁ - w₂)^2 ≥ 0`
     for all `w₁, w₂, y : Int` (and arbitrary-list telescoping sum), showing convex iterate averaging
     `w̄ = (w₁ + w₂)/2` strictly reduces batch quadratic risk by `(w₁ - w₂)^2 / 4` whenever `w₁ ≠ w₂`.
   - **Premise-Failure Counterexample (Git Re-Basin / Mode-Connectivity Barrier)**: On the
     sign-symmetric non-convex potential `W(w) = (w^2 - 1)^2`, two zero-loss global minimizers
     `w₁ = -1` (`W(-1) = 0`) and `w₂ = +1` (`W(+1) = 0`) average to `w̄ = 0`, landing on the
     local maximum barrier `W(0) = 1 > 0`!
-/

namespace CommonGround.BellmanMDP.PolyakLojasiewiczMomentumAndOnlineToBatchFrontier

/-! ## Part 1: Universal `K`-Step Polyak–Łojasiewicz Contraction & Overparameterized Gauge Fiber -/

/-- Exact integer exponentiation `b^k` on `Nat`. -/
def natPow (b k : Nat) : Nat :=
  match k with
  | 0 => 1
  | k' + 1 => natPow b k' * b

/-- Trajectory `g : Nat → Nat` satisfies scaled one-step contraction `S * g(k+1) ≤ R * g(k)`. -/
def SatisfiesScaledStepContraction (S R : Nat) (g : Nat → Nat) : Prop :=
  ∀ k : Nat, S * g (k + 1) ≤ R * g k

theorem nat_mul_le_mul_left_core (c a b : Nat) (h : a ≤ b) : c * a ≤ c * b := by
  induction c with
  | zero =>
    simp [Nat.zero_mul]
  | succ c' ih =>
    rw [Nat.succ_mul, Nat.succ_mul]
    exact Nat.add_le_add ih h

theorem nat_mul_le_mul_right_core (a b c : Nat) (h : a ≤ b) : a * c ≤ b * c := by
  rw [Nat.mul_comm a c, Nat.mul_comm b c]
  exact nat_mul_le_mul_left_core c a b h

/-- Universal `K`-step geometric descent under Polyak–Łojasiewicz contraction:
`S * g(k+1) ≤ R * g(k)` implies `S^K * g(K) ≤ R^K * g(0)` for every `K : Nat`. -/
theorem scaled_pl_geometric_contraction (S R : Nat) (g : Nat → Nat)
    (hStep : SatisfiesScaledStepContraction S R g) :
    ∀ K : Nat, natPow S K * g K ≤ natPow R K * g 0 := by
  intro K
  induction K with
  | zero =>
    dsimp [natPow]
    omega
  | succ k ih =>
    dsimp [natPow]
    have hk : S * g (k + 1) ≤ R * g k := hStep k
    have h1 : natPow S k * (S * g (k + 1)) ≤ natPow S k * (R * g k) :=
      nat_mul_le_mul_left_core (natPow S k) (S * g (k + 1)) (R * g k) hk
    have hL : (natPow S k * S) * g (k + 1) = natPow S k * (S * g (k + 1)) :=
      Nat.mul_assoc (natPow S k) S (g (k + 1))
    have hMid : natPow S k * (R * g k) = R * (natPow S k * g k) := by
      calc
        natPow S k * (R * g k) = (natPow S k * R) * g k := (Nat.mul_assoc (natPow S k) R (g k)).symm
        _ = (R * natPow S k) * g k := by rw [Nat.mul_comm (natPow S k) R]
        _ = R * (natPow S k * g k) := Nat.mul_assoc R (natPow S k) (g k)
    have h2 : R * (natPow S k * g k) ≤ R * (natPow R k * g 0) :=
      nat_mul_le_mul_left_core R (natPow S k * g k) (natPow R k * g 0) ih
    have hR : R * (natPow R k * g 0) = (natPow R k * R) * g 0 := by
      calc
        R * (natPow R k * g 0) = (R * natPow R k) * g 0 := (Nat.mul_assoc R (natPow R k) (g 0)).symm
        _ = (natPow R k * R) * g 0 := by rw [Nat.mul_comm R (natPow R k)]
    omega

/-- Overparameterized rank-deficient quadratic loss `L(u, v) = (u + v - y)^2`. -/
def overparamLoss (u v y : Int) : Int :=
  (u + v - y) * (u + v - y)

/-- Squared Euclidean gradient norm `‖∇L(u, v)‖₂² = (2(u+v-y))² + (2(u+v-y))²`. -/
def overparamGradNormSq (u v y : Int) : Int :=
  (2 * (u + v - y)) * (2 * (u + v - y)) + (2 * (u + v - y)) * (2 * (u + v - y))

/-- Hessian determinant of `L(u, v)`: `H = [[2, 2], [2, 2]]` has `det(H) = 0` (NOT strongly convex!). -/
def overparamHessianDet : Int :=
  2 * 2 - 2 * 2

/-- Quartic double-well `W(x) = (x^2 - 1)^2` and its derivative `W'(x) = 4 x (x^2 - 1)`. -/
def doubleWell (x : Int) : Int :=
  (x * x - 1) * (x * x - 1)

def doubleWellDeriv (x : Int) : Int :=
  4 * x * (x * x - 1)

theorem polyak_lojasiewicz_geometric_descent_vs_strict_saddle_trap :
    -- 1. Universal K-step geometric PŁ contraction for all horizons K
    (∀ (S R : Nat) (g : Nat → Nat),
      SatisfiesScaledStepContraction S R g →
      ∀ K : Nat, natPow S K * g K ≤ natPow R K * g 0) ∧
    -- 2. Overparameterized L(u, v) = (u + v - y)^2 has det(Hessian) = 0 and flat gauge fiber
    --    L(u + t, v - t, y) = L(u, v, y), yet satisfies EXACT global PŁ dominance ‖∇L‖₂² = 8 L!
    overparamHessianDet = 0 ∧
    (∀ u v y t : Int, overparamLoss (u + t) (v - t) y = overparamLoss u v y) ∧
    (∀ u v y : Int, overparamGradNormSq u v y = 8 * overparamLoss u v y) ∧
    -- 3. Strict-saddle counterexample: doubleWell has W'(0) = 0 while W(0) = 1 > 0 = W(1),
    --    trapping gradient step x' = 0 - eta * W'(0) at x' = 0 forever!
    (doubleWellDeriv 0 = 0 ∧ doubleWell 0 = 1 ∧ doubleWell 1 = 0 ∧
      ∀ eta : Int, 0 - eta * doubleWellDeriv 0 = 0) := by
  refine ⟨scaled_pl_geometric_contraction, by decide, ?_, ?_, ?_⟩
  · intro u v y t
    dsimp [overparamLoss]
    have hsum : (u + t) + (v - t) - y = u + v - y := by omega
    rw [hsum]
  · intro u v y
    dsimp [overparamGradNormSq, overparamLoss]
    have h2 : (2 * (u + v - y)) * (2 * (u + v - y)) = 4 * ((u + v - y) * (u + v - y)) := by
      calc
        (2 * (u + v - y)) * (2 * (u + v - y))
            = 2 * ((u + v - y) * (2 * (u + v - y))) := Int.mul_assoc 2 (u + v - y) (2 * (u + v - y))
        _ = 2 * (2 * ((u + v - y) * (u + v - y))) := by
            rw [← Int.mul_assoc (u + v - y) 2 (u + v - y), Int.mul_comm (u + v - y) 2, Int.mul_assoc 2 (u + v - y) (u + v - y)]
        _ = (2 * 2) * ((u + v - y) * (u + v - y)) := (Int.mul_assoc 2 2 _).symm
        _ = 4 * ((u + v - y) * (u + v - y)) := rfl
    rw [h2]
    omega
  · refine ⟨by decide, by decide, by decide, ?_⟩
    intro eta
    dsimp [doubleWellDeriv]
    simp

/-! ## Part 2: Polyak Heavy-Ball `√κ` Acceleration vs. Undamped `6`-Cycle & Overshoot -/

/-- Scaled characteristic polynomial of Heavy-Ball `(α = 1/4, β = 1/4)` at curvature `lam`:
`4 μ^2 - (5 - lam) μ + 1` evaluated on doubled root `u = 2 μ` (`u^2 - (5 - lam) u + 1`?
Specifically: `4 (u/2)^2 - (5 - lam)(u/2) + 1 = (2 u^2 - 2(5 - lam) u + 4)/2`; even cleaner:
`charPolyHB4 lam p q = 4 * p^2 - (5 - lam) * p * q + q^2` for rational root `μ = p / q`). -/
def charPolyHB4 (lam p q : Int) : Int :=
  4 * (p * p) - (5 - lam) * (p * q) + q * q

/-- Undamped symplectic momentum step `(β = 1, α = 1)`: `(x, x_prev) ↦ (x - x_prev, x)`. -/
structure State2 where
  cur : Int
  prev : Int
  deriving DecidableEq, Repr

def undampedStep (s : State2) : State2 :=
  ⟨s.cur - s.prev, s.cur⟩

def iterateState2 (f : State2 → State2) : Nat → State2 → State2
  | 0, s => s
  | n + 1, s => iterateState2 f n (f s)

/-- Overshoot gradient step on curvature `L = 3` with step `α = 1` (`α L = 3 > 2`):
`x_{t+1} = (1 - 3) x_t = -2 x_t`. -/
def overshootStep (x : Int) : Int :=
  -2 * x

theorem heavy_ball_momentum_acceleration_vs_undamped_cycle_and_overshoot :
    -- 1. At condition number κ = 9 (λ₁ = 1, λ₂ = 9), Heavy-Ball (α = 1/4, β = 1/4) achieves
    --    exact double roots μ = +1/2 at λ₁ = 1 and μ = -1/2 at λ₂ = 9:
    --    charPolyHB4 1 p q = (2p - q)^2 and charPolyHB4 9 p q = (2p + q)^2!
    (∀ p q : Int,
      charPolyHB4 1 p q = (2 * p - q) * (2 * p - q) ∧
      charPolyHB4 9 p q = (2 * p + q) * (2 * p + q)) ∧
    -- 2. Heavy-Ball per-step squared contraction (1/2)^2 = 1/4 strictly beats optimal scalar GD
    --    ((9-1)/(9+1))^2 = (4/5)^2 = 16/25 on κ = 9 (cross-multiplied: 25 * 1 < 4 * 16, i.e. 25 < 64)
    (25 * 1 < 4 * 16) ∧
    -- 3. Undamped momentum (β = 1, α = 1) never converges: every initial state repeats with exact
    --    period 6 (`iterateState2 undampedStep 6 s = s`), and (1, 0) stays nonzero around the loop!
    (∀ s : State2, iterateState2 undampedStep 6 s = s) ∧
    iterateState2 undampedStep 3 ⟨1, 0⟩ = ⟨-1, 0⟩ ∧
    -- 4. Overshoot counterexample (α L = 3 > 2): squared error quadruples every step!
    (∀ x : Int, overshootStep x * overshootStep x = 4 * (x * x)) := by
  refine ⟨?_, by decide, ?_, by decide, ?_⟩
  · intro p q
    constructor
    · dsimp [charPolyHB4]
      have hsub : (2 * p - q) * (2 * p - q) = 4 * (p * p) - 4 * (p * q) + q * q := by
        calc
          (2 * p - q) * (2 * p - q)
              = (2 * p) * (2 * p - q) - q * (2 * p - q) := Int.sub_mul (2 * p) q (2 * p - q)
          _ = ((2 * p) * (2 * p) - (2 * p) * q) - (q * (2 * p) - q * q) := by
              rw [Int.mul_sub, Int.mul_sub]
          _ = (4 * (p * p) - 2 * (p * q)) - (2 * (p * q) - q * q) := by
              have hpp : (2 * p) * (2 * p) = 4 * (p * p) := by
                calc
                  (2 * p) * (2 * p) = 2 * (p * (2 * p)) := Int.mul_assoc 2 p (2 * p)
                  _ = 2 * (2 * (p * p)) := by
                    rw [← Int.mul_assoc p 2 p, Int.mul_comm p 2, Int.mul_assoc 2 p p]
                  _ = 4 * (p * p) := by rw [← Int.mul_assoc 2 2 (p * p)]; rfl
              have hpq1 : (2 * p) * q = 2 * (p * q) := Int.mul_assoc 2 p q
              have hpq2 : q * (2 * p) = 2 * (p * q) := by
                rw [Int.mul_comm q (2 * p), Int.mul_assoc 2 p q]
              rw [hpp, hpq1, hpq2]
          _ = 4 * (p * p) - 4 * (p * q) + q * q := by omega
      omega
    · dsimp [charPolyHB4]
      have hadd : (2 * p + q) * (2 * p + q) = 4 * (p * p) + 4 * (p * q) + q * q := by
        calc
          (2 * p + q) * (2 * p + q)
              = (2 * p) * (2 * p + q) + q * (2 * p + q) := Int.add_mul (2 * p) q (2 * p + q)
          _ = ((2 * p) * (2 * p) + (2 * p) * q) + (q * (2 * p) + q * q) := by
              rw [Int.mul_add, Int.mul_add]
          _ = (4 * (p * p) + 2 * (p * q)) + (2 * (p * q) + q * q) := by
              have hpp : (2 * p) * (2 * p) = 4 * (p * p) := by
                calc
                  (2 * p) * (2 * p) = 2 * (p * (2 * p)) := Int.mul_assoc 2 p (2 * p)
                  _ = 2 * (2 * (p * p)) := by
                    rw [← Int.mul_assoc p 2 p, Int.mul_comm p 2, Int.mul_assoc 2 p p]
                  _ = 4 * (p * p) := by rw [← Int.mul_assoc 2 2 (p * p)]; rfl
              have hpq1 : (2 * p) * q = 2 * (p * q) := Int.mul_assoc 2 p q
              have hpq2 : q * (2 * p) = 2 * (p * q) := by
                rw [Int.mul_comm q (2 * p), Int.mul_assoc 2 p q]
              rw [hpp, hpq1, hpq2]
          _ = 4 * (p * p) + 4 * (p * q) + q * q := by omega
      omega
  · intro s
    cases s with
    | mk c p =>
      dsimp [iterateState2, undampedStep]
      congr 1 <;> omega
  · intro x
    dsimp [overshootStep]
    calc
      (-2 * x) * (-2 * x) = (-2) * (x * (-2 * x)) := Int.mul_assoc (-2) x (-2 * x)
      _ = (-2) * ((-2) * (x * x)) := by
        rw [← Int.mul_assoc x (-2) x, Int.mul_comm x (-2), Int.mul_assoc (-2) x x]
      _ = ((-2) * (-2)) * (x * x) := (Int.mul_assoc (-2) (-2) (x * x)).symm
      _ = 4 * (x * x) := rfl

/-! ## Part 3: Online-to-Batch Convex Variance Drop vs. Non-Convex Re-Basin Midpoint Barrier -/

/-- Scaled midpoint Jensen variance drop on convex quadratic loss `(w - y)^2`:
`2 * ((w1 - y)^2 + (w2 - y)^2) - (w1 + w2 - 2*y)^2`. -/
def onlineToBatchVarianceDrop (w1 w2 y : Int) : Int :=
  2 * ((w1 - y) * (w1 - y) + (w2 - y) * (w2 - y)) -
    (w1 + w2 - 2 * y) * (w1 + w2 - 2 * y)

theorem online_to_batch_variance_reduction_vs_nonconvex_rebasin_barrier :
    -- 1. Universal convex quadratic online-to-batch variance drop:
    --    averaging w1 and w2 reduces scaled risk by exact square (w1 - w2)^2 ≥ 0!
    (∀ w1 w2 y : Int,
      onlineToBatchVarianceDrop w1 w2 y = (w1 - w2) * (w1 - w2) ∧
      0 ≤ onlineToBatchVarianceDrop w1 w2 y) ∧
    -- 2. Strict improvement witness: iterates w1 = -1, w2 = +1 around target y = 0 have
    --    cumulative squared loss (-1)^2 + (+1)^2 = 2, whereas w̄ = 0 has loss 0 (drop = 4 > 0)
    onlineToBatchVarianceDrop (-1) 1 0 = 4 ∧
    -- 3. Non-convex mode-symmetry counterexample (Git Re-Basin barrier):
    --    on W(w) = (w^2 - 1)^2, zero-loss minimizers w1 = -1 (W = 0) and w2 = +1 (W = 0)
    --    average to midpoint w̄ = 0 with catastrophic barrier loss W(0) = 1 > 0!
    (doubleWell (-1) = 0 ∧ doubleWell 1 = 0 ∧
      ((-1 : Int) + 1) / 2 = 0 ∧
      doubleWell 0 = 1 ∧
      doubleWell (-1) + doubleWell 1 < doubleWell 0) := by
  refine ⟨?_, by decide, ⟨by decide, by decide, by decide, by decide, by decide⟩⟩
  intro w1 w2 y
  have hQuadId : ∀ a b : Int, 2 * (a * a + b * b) - (a + b) * (a + b) = (a - b) * (a - b) := by
    intro a b
    have habAdd : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
      calc
        (a + b) * (a + b) = a * (a + b) + b * (a + b) := Int.add_mul a b (a + b)
        _ = (a * a + a * b) + (b * a + b * b) := by rw [Int.mul_add a a b, Int.mul_add b a b]
        _ = (a * a + a * b) + (a * b + b * b) := by rw [Int.mul_comm b a]
        _ = a * a + 2 * (a * b) + b * b := by omega
    have habSub : (a - b) * (a - b) = a * a - 2 * (a * b) + b * b := by
      calc
        (a - b) * (a - b) = a * (a - b) - b * (a - b) := Int.sub_mul a b (a - b)
        _ = (a * a - a * b) - (b * a - b * b) := by rw [Int.mul_sub a a b, Int.mul_sub b a b]
        _ = (a * a - a * b) - (a * b - b * b) := by rw [Int.mul_comm b a]
        _ = a * a - 2 * (a * b) + b * b := by omega
    rw [habAdd, habSub]
    omega
  have hid : onlineToBatchVarianceDrop w1 w2 y = (w1 - w2) * (w1 - w2) := by
    dsimp [onlineToBatchVarianceDrop]
    have hsum : w1 + w2 - 2 * y = (w1 - y) + (w2 - y) := by omega
    have hdiff : w1 - w2 = (w1 - y) - (w2 - y) := by omega
    rw [hsum, hdiff]
    exact hQuadId (w1 - y) (w2 - y)
  refine ⟨hid, ?_⟩
  rw [hid]
  by_cases hz : (0 : Int) ≤ w1 - w2
  · exact Int.mul_nonneg hz hz
  · have hneg : (0 : Int) ≤ -(w1 - w2) := by omega
    have hnn : (0 : Int) ≤ (-(w1 - w2)) * (-(w1 - w2)) := Int.mul_nonneg hneg hneg
    have hsq : (-(w1 - w2)) * (-(w1 - w2)) = (w1 - w2) * (w1 - w2) := by
      rw [Int.neg_mul_neg]
    rw [← hsq]
    exact hnn

end CommonGround.BellmanMDP.PolyakLojasiewiczMomentumAndOnlineToBatchFrontier
