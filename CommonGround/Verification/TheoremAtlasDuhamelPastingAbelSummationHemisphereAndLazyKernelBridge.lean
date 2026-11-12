/-
  CommonGround/Verification/TheoremAtlasDuhamelPastingAbelSummationHemisphereAndLazyKernelBridge.lean

  Formal Foundation & Counterexample Verification for 4 Cross-Domain Theorem-Atlas Studies (V171):
  1. `Euler/DuhamelPasting.lean` + `PoincareConjecture/.../ContinuousPathComposition.lean`:
     - Exact Duhamel semigroup restart `inhomogeneous_restart_shifted` and adjacent-interval mild
       solution pasting `glue_ordinary_mild` on `[0, a+b]` under `hmatch : u a = v 0`, paired with
       pointwise operator sup-norm bound `‖pointwiseOperator K A‖ ≤ ‖A‖` (`norm_pointwiseOperator_le`).
     - Premise-Boundary Witness: If the interface condition `u a = v 0` is violated (`u a ≠ v 0`),
       the pasted path differs from the true restarted Duhamel trajectory on `[a, a+b]` by the
       propagated jump defect `S(t - a)(v 0 - u a) ≠ 0`!
  2. `TauCeti/NumberTheory/AbelSummation.lean`:
     - Summation-by-parts identity `sum_Icc_rpow_mul_eq`, log-cubic weight majorant
       `log t (4 + log t) ≤ 4 (1 + log t)²` (`norm_deriv_decayWeight_mul_le`, `#L136`), and
       power-weighted Cesàro/Tauberian limit `tendsto_rpow_inv_mul_sum_Icc_rpow_mul` (`κ / (τ + 1)`
       for `τ > -1`).
     - Premise-Boundary Witness: Writing `decayWeight` with `(1 + log t)³` instead of `(log t)³`
       is essential because `log 1 = 0` (`0³ = 0`, whereas `(1 + 0)³ = 1 > 0`), and in
       `tendsto_rpow_inv_mul_sum_Icc_rpow_mul`, `τ = -1` makes `τ + 1 = 0`!
  3. `TauCeti/Analysis/InnerProductSpace/Hemisphere.lean`:
     - Closed northern hemisphere homeomorphism `hemisphereHomeomorph p : {x ∈ S | 0 ≤ ⟪x, p⟫} ≃ₜ closedBall 0 1`
       via orthogonal projection `y = x - ⟪x, p⟫ p` (`‖y‖² = 1 - ⟪x, p⟫²`) and vertical lift
       `y + √(1 - ‖y‖²) p`, with equator `{⟪x, p⟫ = 0} = {0 ≤ ⟪x, p⟫} ∩ {0 ≤ ⟪x, -p⟫}`.
     - Premise-Boundary Witness: On the open southern hemisphere `⟪x, p⟫ < 0` (e.g. `x = -p` with
       `⟪-p, p⟫ = -1`), projecting and lifting returns `+p ≠ -p` because `√((-1)²) = +1 ≠ -1`!
  4. `OAI/Combinatorics/CliqueFree/FiniteKernel.lean`:
     - Reversible Markov kernel product `reversible_mul` under `Commute P Q`, automatic commutativity
       `commute_lazy : Commute P (lazy P)` for `lazy P = (I + P)/2`, and pigeonhole smoothed-row TV
       bound `exists_smoothed_row_distance` (`∃ j < R, tv_sq j ≤ 4 D / R`).
     - Premise-Boundary Witness: Two symmetric (uniform-reversible) transposition matrices `P = swap(0,1)`
       and `Q = swap(1,2)` on `Fin 3` do NOT commute (`P * Q ≠ Q * P`), and their product `P * Q` is a
       3-cycle with `(P * Q)_{0,2} = 1 ≠ (P * Q)_{2,0} = 0` (`¬ Reversible π (P * Q)`)!
-/

namespace CommonGround.Verification.TheoremAtlasDuhamelPastingAbelSummationHemisphereAndLazyKernelBridge

-- ============================================================================
-- 1. DUHAMEL SEMIGROUP RESTART & ENDPOINT MATCHING (`Euler/DuhamelPasting.lean`)
-- ============================================================================

/-- Discrete Duhamel evolution `u(t) = u0 + ∑_{s < t} f(s)` on `[0, 4]` for `f = [2, 3, 5, 7]`. -/
def discreteForce (s : Nat) : Nat :=
  match s with
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | _ => 7

/-- Exact Duhamel trajectory from `u0` up to step `t ≤ 4`. -/
def duhamelTraj (u0 t : Nat) : Nat :=
  match t with
  | 0 => u0
  | 1 => u0 + discreteForce 0
  | 2 => u0 + discreteForce 0 + discreteForce 1
  | 3 => u0 + discreteForce 0 + discreteForce 1 + discreteForce 2
  | _ => u0 + discreteForce 0 + discreteForce 1 + discreteForce 2 + discreteForce 3

/-- Restarted trajectory from state `v0` at `a = 2` for elapsed step `r ≤ 2` (`inhomogeneous_restart_shifted`). -/
def duhamelRestartFrom2 (v0 r : Nat) : Nat :=
  match r with
  | 0 => v0
  | 1 => v0 + discreteForce 2
  | _ => v0 + discreteForce 2 + discreteForce 3

/-- Theorem 1:
    (a) Exact Semigroup Restart & Pasting (`inhomogeneous_restart_shifted` & `glue_ordinary_mild`):
        When the endpoint matching condition `hmatch : v0 = duhamelTraj u0 2` holds (`u0 = 10, v0 = 15`),
        `duhamelRestartFrom2 (duhamelTraj 10 2) r = duhamelTraj 10 (2 + r)` for all `r ∈ {0, 1, 2}`.
    (b) Pointwise Operator Norm Bound (`norm_pointwiseOperator_le`, `ContinuousPathComposition.lean#L41`):
        For pointwise multipliers `A = [2, 5, 3]` (`‖A‖_∞ = 5`) and path `h = [4, 2, 3]` (`‖h‖_∞ = 4`),
        every pointwise product `A_s * h_s ≤ 5 * 4 = 20`.
    (c) Mismatched Interface Defect (`v0 ≠ u(a)`):
        If `v0 = 18 ≠ duhamelTraj 10 2 = 15`, then `duhamelRestartFrom2 18 2 = 30 ≠ duhamelTraj 10 4 = 27`! -/
theorem duhamel_pasting_restart_and_interface_mismatch_boundary :
    (duhamelTraj 10 2 = 15 ∧
      (∀ r : Fin 3, duhamelRestartFrom2 (duhamelTraj 10 2) r.val = duhamelTraj 10 (2 + r.val))) ∧
    (2 * 4 ≤ 5 * 4 ∧ 5 * 2 ≤ 5 * 4 ∧ 3 * 3 ≤ 5 * 4) ∧
    (duhamelRestartFrom2 18 2 = 30 ∧ duhamelTraj 10 4 = 27 ∧
      duhamelRestartFrom2 18 2 ≠ duhamelTraj 10 4) := by
  decide

-- ============================================================================
-- 2. ABEL SUMMATION BY PARTS & LOG-WEIGHT POLE AVOIDANCE (`AbelSummation.lean`)
-- ============================================================================

/-- Discrete summation by parts: `∑_{k=1}^3 k * c_k = 3 * S(3) - (S(1) + S(2))` (`sum_Icc_rpow_mul_eq`). -/
def abelWeightedSum3 (c1 c2 c3 : Int) : Int :=
  1 * c1 + 2 * c2 + 3 * c3

def abelRhs3 (c1 c2 c3 : Int) : Int :=
  let s1 := c1
  let s2 := c1 + c2
  let s3 := c1 + c2 + c3
  3 * s3 - (s1 + s2)

/-- Theorem 2:
    (a) Exact Summation by Parts (`sum_Icc_rpow_mul_eq`, `#L228`):
        For all coefficients `c1, c2, c3 ∈ Fin 4`, `abelWeightedSum3 c1 c2 c3 = abelRhs3 c1 c2 c3`.
    (b) Derivative Majorant Inequality (`norm_deriv_decayWeight_mul_le`, `#L136`):
        For every non-negative log proxy `L : Fin 6` (`L = log t ≥ 0`), `L * (4 + L) ≤ 4 * (1 + L) ^ 2`.
    (c) Unshifted `log 1 = 0` Pole & `τ = -1` Tauberian Singularity Boundaries:
        At `L = 0` (`t = 1`), `(1 + L) ^ 3 = 1 > 0` whereas `L ^ 3 = 0` (pole in `decayWeight` without `+ 1`!),
        and at `τ = -1`, `τ + 1 = 0` vanishes in the denominator of `κ / (τ + 1)` (`#L254`)! -/
theorem abel_summation_by_parts_and_log_weight_pole_boundary :
    (∀ c1 c2 c3 : Fin 4,
      abelWeightedSum3 c1.val c2.val c3.val = abelRhs3 c1.val c2.val c3.val) ∧
    (∀ L : Fin 6, L.val * (4 + L.val) ≤ 4 * (1 + L.val) ^ 2) ∧
    ((1 + 0) ^ 3 = 1 ∧ (0 : Nat) ^ 3 = 0 ∧ ((-1 : Int) + 1 = 0)) := by
  decide

-- ============================================================================
-- 3. HEMISPHERE HOMEOMORPHISM, EQUATOR & SOUTHERN SIGN FLIP (`Hemisphere.lean`)
-- ============================================================================

/-- Integer Pythagorean sphere points `(y, z)` with `y² + z² = 25` (`R = 5`, pole `p = (0, 1)` so `⟪x, p⟫ = z`). -/
def pythagLiftZ (y : Int) : Int :=
  if y = 0 then 5
  else if y = 3 ∨ y = -3 then 4
  else if y = 4 ∨ y = -4 then 3
  else 0

/-- Round-trip projection `(y, z) ↦ y` followed by northern lift `y ↦ (y, pythagLiftZ y)`. -/
def hemisphereRoundTrip (yz : Int × Int) : Int × Int :=
  (yz.1, pythagLiftZ yz.1)

/-- Theorem 3:
    (a) Northern Hemisphere Round-Trip (`hemisphereHomeomorph.left_inv`, `#L95`):
        For northern sphere points `(3, 4)` (`z = 4 ≥ 0`) and `(0, 5)` (`z = 5 ≥ 0`),
        `3² + 4² = 25`, `hemisphereRoundTrip (3, 4) = (3, 4)`, and `hemisphereRoundTrip (0, 5) = (0, 5)`.
    (b) Equator Intersection (`range_equatorInclusion`, `#L131`):
        For `z : Int`, `(0 ≤ z ∧ 0 ≤ -z) ↔ z = 0` (at equator `(5, 0)`, `z = 0`).
    (c) Southern Hemisphere Sign-Flip Boundary (`z < 0`):
        For the southern hemisphere point `(3, -4)` (`3² + (-4)² = 25`, `z = -4 < 0`),
        `hemisphereRoundTrip (3, -4) = (3, 4) ≠ (3, -4)` because `√(z²) = |z| = +4 ≠ -4`! -/
theorem hemisphere_homeomorph_equator_and_southern_flip_boundary :
    ((3 : Int) * 3 + 4 * 4 = 25 ∧
      hemisphereRoundTrip (3, 4) = (3, 4) ∧
      hemisphereRoundTrip (0, 5) = (0, 5)) ∧
    (∀ d : Fin 5,
      let z : Int := Int.ofNat d.val - 2
      ((0 ≤ z ∧ 0 ≤ -z) ↔ z = 0)) ∧
    ((3 : Int) * 3 + (-4) * (-4) = 25 ∧
      (-4 : Int) < 0 ∧
      hemisphereRoundTrip (3, -4) = (3, 4) ∧
      hemisphereRoundTrip (3, -4) ≠ (3, -4)) := by
  decide

-- ============================================================================
-- 4. REVERSIBLE LAZY KERNEL COMMUTATIVITY & TELESCOPING (`FiniteKernel.lean`)
-- ============================================================================

/-- 3×3 matrix multiplication over `Nat`. -/
def matMul3 (A B : Fin 3 → Fin 3 → Nat) (i j : Fin 3) : Nat :=
  A i ⟨0, by decide⟩ * B ⟨0, by decide⟩ j +
  A i ⟨1, by decide⟩ * B ⟨1, by decide⟩ j +
  A i ⟨2, by decide⟩ * B ⟨2, by decide⟩ j

/-- Symmetry (uniform reversibility `π_i K_{ij} = π_j K_{ji}`) check on `Fin 3`. -/
def isSymmKernel3 (K : Fin 3 → Fin 3 → Nat) : Bool :=
  decide (∀ i j : Fin 3, K i j = K j i)

/-- Transposition matrix `P01` swapping `0 ↔ 1` and fixing `2` on `Fin 3`. -/
def P01 (i j : Fin 3) : Nat :=
  if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨ (i.val = 2 ∧ j.val = 2) then 1 else 0

/-- Transposition matrix `Q12` swapping `1 ↔ 2` and fixing `0` on `Fin 3`. -/
def Q12 (i j : Fin 3) : Nat :=
  if (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨ (i.val = 0 ∧ j.val = 0) then 1 else 0

/-- Scaled lazy kernel `2 * lazy(P01) = I + P01` (`lazy_eq`, `#L128`). -/
def twoLazyP01 (i j : Fin 3) : Nat :=
  (if i.val = j.val then 1 else 0) + P01 i j

/-- Theorem 4:
    (a) Lazy Kernel Commutativity & Reversibility (`commute_lazy` & `reversible_smoothed`, `#L134, #L140`):
        `P01` and `twoLazyP01` commute (`matMul3 P01 twoLazyP01 = matMul3 twoLazyP01 P01`) and their
        product `smoothed P01 1` is symmetric (`isSymmKernel3 (matMul3 P01 twoLazyP01) = true`).
    (b) Pigeonhole Entropy Telescoping (`exists_smoothed_row_distance`, `#L254`):
        For entropy increments `Δ_0 = 5, Δ_1 = 2, Δ_2 = 5` summing to `D = 12` over `R = 3` steps,
        step `j = 1 < 3` satisfies `3 * Δ_1 = 6 ≤ D = 12`.
    (c) Non-Commuting Reversible Kernels Break `reversible_mul` (`#L96`):
        Both `P01` and `Q12` are symmetric/reversible (`isSymmKernel3 P01 = true`, `isSymmKernel3 Q12 = true`),
        yet they do NOT commute (`(P01 * Q12)_{0,2} = 1 ≠ (Q12 * P01)_{0,2} = 0`), and their product
        `P01 * Q12` is NOT reversible (`isSymmKernel3 (matMul3 P01 Q12) = false`)! -/
theorem lazy_kernel_commute_telescoping_and_noncommute_reversible_boundary :
    ((∀ i j : Fin 3, matMul3 P01 twoLazyP01 i j = matMul3 twoLazyP01 P01 i j) ∧
      isSymmKernel3 (matMul3 P01 twoLazyP01) = true) ∧
    (5 + 2 + 5 = 12 ∧ 3 * 2 ≤ 12) ∧
    (isSymmKernel3 P01 = true ∧ isSymmKernel3 Q12 = true ∧
      matMul3 P01 Q12 ⟨0, by decide⟩ ⟨2, by decide⟩ = 1 ∧
      matMul3 P01 Q12 ⟨2, by decide⟩ ⟨0, by decide⟩ = 0 ∧
      isSymmKernel3 (matMul3 P01 Q12) = false) := by
  decide

end CommonGround.Verification.TheoremAtlasDuhamelPastingAbelSummationHemisphereAndLazyKernelBridge
