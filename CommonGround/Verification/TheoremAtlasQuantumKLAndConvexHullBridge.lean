/-!
# Quantum Game Conditioning, Coarse-Grained Divergence Trap & Trace-Dispersion Identity
## CommonGround Formal Verification (`TheoremAtlasQuantumKLAndConvexHullBridge.lean`)

Verifies three foundational cross-corpus mechanisms from `theorem-atlas` `insight-paths.json`
(`ten-proofs` ↔ `CSLib`, `Mathlib`, `Econlib`, `Poincaré`), in pure Lean 4.33.0 core with
zero `sorry` and zero custom axioms.
-/

namespace CommonGround.Verification.TheoremAtlasQuantumKLAndConvexHullBridge

theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  cases Int.le_total 0 x with
  | inl h => exact Int.mul_nonneg h h
  | inr h =>
    have hneg : 0 ≤ -x := by omega
    have heq : (-x) * (-x) = x * x := by grind
    rw [← heq]
    exact Int.mul_nonneg hneg hneg

/-- 1. Nonnegative Joint Weights with Zero Marginal Vanish Entrywise (`PMF.bind` Zero-Marginal Branch). -/
theorem zero_marginal_forces_zero_joint_weights
    (w0 w1 c0 c1 : Int) (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) (hmarg : w0 + w1 = 0) :
    w0 = 0 ∧ w1 = 0 ∧ (w0 + w1) * c0 = w0 ∧ (w0 + w1) * c1 = w1 := by
  grind

/-- 2A. Exact Coarse-Graining Data-Processing Identity (Denominator-Cleared Chi-Square / Fisher Form):
    `(p₀² q₁ + p₁² q₀)(q₀ + q₁) - (p₀ + p₁)² q₀ q₁ = (p₀ q₁ - p₁ q₀)² ≥ 0`. -/
theorem chi_square_coarse_graining_defect_identity (p0 p1 q0 q1 : Int) :
    (p0 * p0 * q1 + p1 * p1 * q0) * (q0 + q1) - (p0 + p1) * (p0 + p1) * q0 * q1 =
      (p0 * q1 - p1 * q0) * (p0 * q1 - p1 * q0) := by
  grind

theorem chi_square_coarse_graining_nonneg (p0 p1 q0 q1 : Int) :
    (p0 + p1) * (p0 + p1) * q0 * q1 ≤ (p0 * p0 * q1 + p1 * p1 * q0) * (q0 + q1) := by
  have hid := chi_square_coarse_graining_defect_identity p0 p1 q0 q1
  have hsq := int_sq_nonneg (p0 * q1 - p1 * q0)
  omega

/-- 2B. Division-by-Zero Trap When `q_i = 0 → p_i = 0` Is Omitted:
    Under total division (`1 / 0 = 0`), `p = (1, 0), q = (0, 1)` gives ungrouped sum `0`
    but grouped sum `(1 + 0)² / (0 + 1) = 1 > 0`, reversing the data-processing inequality! -/
theorem division_by_zero_breaks_unguarded_data_processing :
    let p0 : Nat := 1; let p1 : Nat := 0
    let q0 : Nat := 0; let q1 : Nat := 1
    let ungrouped := (p0 * p0) / q0 + (p1 * p1) / q1
    let grouped := ((p0 + p1) * (p0 + p1)) / (q0 + q1)
    ungrouped = 0 ∧ grouped = 1 ∧ ungrouped < grouped := by
  decide

/-- 3. Exact 2×2 Trace-Energy vs. Jensen Diagonal-Dispersion Identity (`MetricCodes` ↔ `Econlib`):
    `2 · (a² + b² + c² + d²) - (a + d)² = (a - d)² + 2 · (b² + c²) ≥ 0`. -/
theorem trace_sq_le_two_mul_frobenius_sq_with_exact_gap (a b c d : Int) :
    2 * (a * a + b * b + c * c + d * d) - (a + d) * (a + d) =
      (a - d) * (a - d) + 2 * (b * b + c * c) := by
  grind

end CommonGround.Verification.TheoremAtlasQuantumKLAndConvexHullBridge
