/-!
# Sparse Moments Meet Graph Flow Energy — & The Disconnected Kirchhoff Vacuity Boundary
## CommonGround Formal Verification (`TheoremAtlasGraphMomentAndVacuityBridge.lean`)

Verifies the mathematical foundations of `theorem-atlas` `GraphMoment.lean` (`graph_moment`)
before Observatory integration, using exact integer arithmetic in pure Lean 4.33.0 core with
zero `sorry` and zero custom axioms:

1. **Discrete Divergence–Gradient Pairing (`path3_divergence_gradient_pairing`)**
2. **Affine-Feature Cancellation (`affine_feature_cancels_under_matched_mass_and_moment`)**
3. **Exact Residual Flow-Energy Bound (`residual_query_sq_le_flow_energy_mul_edge_roughness`)**
4. **Critique / Vacuity Boundary (`disconnected_graph_no_flow_across_components`)**
-/

namespace CommonGround.Verification.TheoremAtlasGraphMomentAndVacuityBridge

theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  cases Int.le_total 0 x with
  | inl h => exact Int.mul_nonneg h h
  | inr h =>
    have hneg : 0 ≤ -x := by omega
    have heq : (-x) * (-x) = x * x := by grind
    rw [← heq]
    exact Int.mul_nonneg hneg hneg

/-- 1. Exact Discrete Divergence–Gradient Pairing on `0 → 1 → 2`:
    `(-J₀)·q₀ + (J₀ - J₁)·q₁ + J₁·q₂ = J₀·(q₁ - q₀) + J₁·(q₂ - q₁)`. -/
theorem path3_divergence_gradient_pairing (J0 J1 q0 q1 q2 : Int) :
    (-J0) * q0 + (J0 - J1) * q1 + J1 * q2 =
      J0 * (q1 - q0) + J1 * (q2 - q1) := by
  grind

/-- 2. Exact Affine Cancellation under Matched Mass & First Moment on `{0, 1, 2}`:
    If `w0 + w1 + w2 = p0 + p1 + p2` and `w1 + 2*w2 = p1 + 2*p2`,
    then subtracting `g(x) = c + a·x` does not alter the query discrepancy! -/
theorem affine_feature_cancels_under_matched_mass_and_moment
    (p0 p1 p2 w0 w1 w2 q0 q1 q2 c a : Int)
    (hmass : w0 + w1 + w2 = p0 + p1 + p2)
    (hmom : w1 + 2 * w2 = p1 + 2 * p2) :
    (p0 * (q0 - c) + p1 * (q1 - (c + a)) + p2 * (q2 - (c + 2 * a))) -
      (w0 * (q0 - c) + w1 * (q1 - (c + a)) + w2 * (q2 - (c + 2 * a))) =
    (p0 * q0 + p1 * q1 + p2 * q2) - (w0 * q0 + w1 * q1 + w2 * q2) := by
  grind

/-- Exact 2-Edge Lagrange Identity:
    `(J₀² + J₁²)(r₀² + r₁²) - (J₀ r₀ + J₁ r₁)² = (J₀ r₁ - J₁ r₀)²`. -/
theorem lagrange_two_edge_identity (J0 J1 r0 r1 : Int) :
    (J0 * J0 + J1 * J1) * (r0 * r0 + r1 * r1) - (J0 * r0 + J1 * r1) * (J0 * r0 + J1 * r1) =
      (J0 * r1 - J1 * r0) * (J0 * r1 - J1 * r0) := by
  grind

/-- 3. Residual Flow-Energy Bound (Graph-Moment Core Theorem):
    When `div J = p - w` and `(w0, w1, w2)` matches mass and 1st moment of `(p0, p1, p2)`,
    squared query error `D²` is bounded by `(J₀² + J₁²) · (r₀² + r₁²)` for any affine reducer `c + a·x`. -/
theorem residual_query_sq_le_flow_energy_mul_edge_roughness
    (p0 p1 p2 w0 w1 w2 J0 J1 q0 q1 q2 c a : Int)
    (hmass : w0 + w1 + w2 = p0 + p1 + p2)
    (hmom : w1 + 2 * w2 = p1 + 2 * p2)
    (hdiv0 : -J0 = p0 - w0)
    (hdiv1 : J0 - J1 = p1 - w1)
    (_hdiv2 : J1 = p2 - w2) :
    let D := (p0 * q0 + p1 * q1 + p2 * q2) - (w0 * q0 + w1 * q1 + w2 * q2)
    let r0 := (q1 - (c + a)) - (q0 - c)
    let r1 := (q2 - (c + 2 * a)) - (q1 - (c + a))
    D * D ≤ (J0 * J0 + J1 * J1) * (r0 * r0 + r1 * r1) := by
  intro D r0 r1
  have hD : D = J0 * r0 + J1 * r1 := by grind
  rw [hD]
  have hlag := lagrange_two_edge_identity J0 J1 r0 r1
  have hsq := int_sq_nonneg (J0 * r1 - J1 * r0)
  omega

/-- Concrete Worked Witness (Scaled by 2 for Exact Integers). -/
theorem worked_quadratic_coreset_witness_attains_sharp_bound :
    let p0 := 1; let p1 := 2; let p2 := 1
    let w0 := 2; let w1 := 0; let w2 := 2
    let q0 := 0; let q1 := 1; let q2 := 4
    let J0 := 1; let J1 := -1
    let D := (p0 * q0 + p1 * q1 + p2 * q2) - (w0 * q0 + w1 * q1 + w2 * q2)
    let naiveEdgeEnergy := (q1 - q0) * (q1 - q0) + (q2 - q1) * (q2 - q1)
    let affineReducedEnergy := ((q1 - 2) - q0) * ((q1 - 2) - q0) + ((q2 - 4) - (q1 - 2)) * ((q2 - 4) - (q1 - 2))
    D = -2 ∧ D * D = 4 ∧ naiveEdgeEnergy = 10 ∧ (J0 * J0 + J1 * J1) * affineReducedEnergy = 4 := by
  decide

/-- 4. Disconnected-Component Kirchhoff Vacuity Theorem. -/
theorem disconnected_graph_no_flow_across_components :
    ¬ ∃ (J0 : Int), (-J0 = (1 : Int) - 2) ∧ (J0 = (2 : Int) - 0) ∧ ((0 : Int) = 1 - 2) := by
  intro h
  rcases h with ⟨J0, _, _, h2⟩
  omega

end CommonGround.Verification.TheoremAtlasGraphMomentAndVacuityBridge
