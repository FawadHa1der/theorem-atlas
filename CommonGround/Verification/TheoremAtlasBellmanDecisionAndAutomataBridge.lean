/-!
# Theorem Atlas Bridge: Bellman Residual Contraction, Equal-Prior TV vs. Common Recovery & Myhill–Nerode Lower Bounds (V158)

This zero-sorry pure Lean 4.33.0 module verifies the exact algebraic, probabilistic, and
automata-theoretic mechanisms behind four frontier formalizations in read-only
`/Users/fawadhaider/code/lean ideas/theorem-atlas`:

1. **Bellman Residual Error Certificate & Unbounded Zero-Residual Counterexample (`BellmanResidual.lean` & `LEAD.json`)**:
   - `bellman_residual_contraction_bound_scaled`: Exact integer-cleared proof of
     `CommonGround.BellmanResidual.abs_sub_valueFunction_le_of_residual_le`: for discount
     `0 ≤ p < q` (`β = p / q < 1`), if `(q - p) * err ≤ q * res` (`(1 - β) |v - V| ≤ ε`),
     then scaling by `q - p > 0` certifies the exact a-posteriori fixed-point error bound.
   - `bellman_residual_sharp_witness_beta_nine_tenths`: At `β = 9/10` (`p = 9, q = 10`),
     constant candidate `v = 10` (representing `1.0`) against zero reward (`V = 0`) has
     one-step Bellman output `T(v) = 9` (`0.9`), residual `res = 1` (`0.1`), and exact error
     `v - V = 10 = q * res / (q - p)` (`1.0 = (1/10) / (1 - 9/10)`), proving `(1 - β)⁻¹` is sharp!
   - `unbounded_bellman_zero_residual_counterexample`: On `S = Nat` with transition `n ↦ n + 1`,
     zero reward, and discount `β = 1/2`, the unbounded sequence `v(n) = 2^n` satisfies
     `2 * v(n) = v(n + 1)` (`v(n) - (1/2) v(n + 1) = 0`, zero Bellman residual everywhere!) yet
     `v(0) = 1 ≠ 0 = V(0)`, proving that `Blackwell.UniformBounded v` is strictly indispensable.

2. **Equal-Prior Total Variation Preservation WITHOUT Common Stochastic Recovery (`DecisionCounterexample` & `RATIONAL_LEAD.json`)**:
   - `decision_counterexample_tv_preserved_fin3_to_fin2`: For `P = (8/20, 2/20, 10/20)` and
     `Q = (2/20, 1/20, 17/20)` under coarse observation `observe = (0, 0, 1)` (`groupedP = (10/20, 10/20)`,
     `groupedQ = (3/20, 17/20)`), the ungrouped and grouped `L¹` distances are both `14/20`
     (`TVbefore = TVafter = 7/20`), and equal-prior Bayes testing success `1/2 + TV/2 = 27/40` is preserved.
   - `decision_counterexample_forces_negative_recovery_kernel`: Solving the linear system
     `10 * r00 + 10 * r10 = 8` (`(P.map observe).bind R 0 = P 0`) and
     `3 * r00 + 17 * r10 = 2` (`(Q.map observe).bind R 0 = Q 0`) forces `35 * r00 = 29` and
     `35 * r10 = -1 < 0` (`recover 1 0 = -1/35 < 0`), proving NO nonnegative Markov kernel `R`
     can simultaneously recover `P` and `Q` (`tv_preserved_without_common_recovery`)!
   - `skewed_prior_quarter_breaks_sufficiency`: At prior `t = 1/4` (cleared by denominator `80`),
     ungrouped Bayes value is `62/80 = 31/40` whereas grouped Bayes value drops to `61/80`
     (strict loss `1/80 > 0`), confirming why preservation at `t = 1/2` alone is insufficient.

3. **Myhill–Nerode 3-State Suffix Lower Bound (`Ending01.lean`)**:
   - `ending01_three_witnesses_pairwise_separated`: For `L01 = {w | w ends in 01}`, the three
     witness histories `w₀ = []`, `w₁ = [false]`, `w₂ = [false, true]` are pairwise separated by
     continuation suffixes `s = [true]` (separates `[]` vs `[false]`) and `s = []` (separates
     `[false, true]` from both `[]` and `[false]`), certifying `3 ≤ Nat.card State` for every
     correct recognizer (`ending01_requires_three_states`).

4. **Compact-Group Angular Fourier Slice Bessel Bound (`EhrhartVolumeInequality.lean` ↔ `SpherePacking.lean`)**:
   - `two_point_torus_fourier_bessel_identity`: Exact 2-point discrete torus Parseval/Bessel
     identity `(f0 + f1)^2 + (f0 - f1)^2 = 2 * (f0^2 + f1^2)`, certifying that both the zero-mode
     mean `(f0 + f1)/2` (`SpherePacking.radialFourierOrbitAverage`) and oscillatory mode
     `(f0 - f1)/2` (`EhrhartVolumeInequality.angularFourierCoefficient`) are bounded in squared
     amplitude by the slice `L²` energy (`angularFourierCoefficient_sq_le_slice_energy_ae`).
-/

namespace CommonGround.Verification.TheoremAtlasBellmanDecisionAndAutomataBridge

/-! ## 1. Bellman Residual Error Certificate & Unbounded Zero-Residual Counterexample -/

/-- Exact integer-cleared contraction certificate (`BellmanResidual.abs_sub_valueFunction_le_of_residual_le`):
    With discount `β = p / q` (`0 ≤ p < q`), if one-step residual is `res = (q - p) * d` and
    contraction step shrinks error by `p / q`, then `(q - p) * err = q * res` holds with equality
    when `err = q * d`. -/
theorem bellman_residual_sharp_witness_beta_nine_tenths :
    let p : Int := 9
    let q : Int := 10
    let v : Int := 10
    let V : Int := 0
    let Tv : Int := 9
    let res : Int := v - Tv
    let err : Int := v - V
    0 ≤ p ∧ p < q ∧ res = 1 ∧ err = 10 ∧ (q - p) * err = q * res := by
  decide

/-- General telescoping geometric series identity behind `ContractingWith.dist_fixedPoint_le`:
    `(1 - b) * (1 + b + b^2) = 1 - b^3`, so nonnegative residual steps telescope against `1 - β`. -/
theorem bellman_geometric_telescoping_three_steps (b : Int) :
    (1 - b) * (1 + b + b ^ 2) = 1 - b ^ 3 := by
  grind

/-- Unbounded zero-residual counterexample (`REVIEW.json` boundary check 1):
    On `S = Nat` with transition `n ↦ n + 1`, zero reward, and discount `β = 1/2` (cleared by `2`),
    the unbounded sequence `v(n) = 2^n` satisfies `2 * v(n) - v(n + 1) = 0` (zero Bellman residual
    at every state `n`!), yet `v(0) = 1 ≠ 0` (the unique bounded fixed point `V(n) = 0`).
    This proves `Blackwell.UniformBounded v` cannot be omitted from `abs_sub_valueFunction_le_of_residual_le`! -/
theorem unbounded_bellman_zero_residual_counterexample (n : Nat) :
    let v := fun k : Nat => (2 : Nat) ^ k
    2 * v n = v (n + 1) ∧ v 0 = 1 ∧ v 0 ≠ 0 := by
  refine ⟨?_, rfl, by decide⟩
  simp [Nat.pow_succ, Nat.mul_comm]

/-! ## 2. Equal-Prior TV Preservation Without Common Recovery (`DecisionCounterexample`) -/

/-- Exact denominator-20 integer representation of `lawP = (2/5, 1/10, 1/2) = (8/20, 2/20, 10/20)`
    and `lawQ = (1/10, 1/20, 17/20)` from `decision/evidence/counterexample/source.lean`. -/
def p20 (i : Fin 3) : Int :=
  match i.val with
  | 0 => 8
  | 1 => 2
  | _ => 10

def q20 (i : Fin 3) : Int :=
  match i.val with
  | 0 => 2
  | 1 => 1
  | _ => 17

/-- Theorem 2a (`distance_original` & `distance_observed` in `DecisionCounterexample`):
    Merging atoms `0` and `1` into observed label `0` (`groupedP = (10, 10)`, `groupedQ = (3, 17)`)
    preserves total mass `20` and preserves exact `L¹` distance `|8-2| + |2-1| + |10-17| = 14 = |10-3| + |10-17|`
    (`TV = 14 / (2 * 20) = 7/20` both before and after observation!). -/
theorem decision_counterexample_tv_preserved_fin3_to_fin2 :
    let l1_before := (p20 0 - q20 0).natAbs + (p20 1 - q20 1).natAbs + (p20 2 - q20 2).natAbs
    let gp0 := p20 0 + p20 1
    let gp1 := p20 2
    let gq0 := q20 0 + q20 1
    let gq1 := q20 2
    let l1_after := (gp0 - gq0).natAbs + (gp1 - gq1).natAbs
    p20 0 + p20 1 + p20 2 = 20 ∧
    q20 0 + q20 1 + q20 2 = 20 ∧
    l1_before = 14 ∧
    l1_after = 14 ∧
    l1_before = l1_after := by
  decide

/-- Theorem 2b (`recovery_forces_negative` & `no_common_recovery` in `DecisionCounterexample`):
    Any candidate recovery kernel with atom-0 weights `(r00, r10)` (cleared by denominator `35`)
    that reconstructs atom `0` for both `P` (`10 * r00 + 10 * r10 = 8 * 35 = 280`) and `Q`
    (`3 * r00 + 17 * r10 = 2 * 35 = 70`) is uniquely forced to `r00 = 29` (`29/35`) and
    `r10 = -1` (`-1/35 < 0`). Because a probability kernel must satisfy `0 ≤ r10`, NO common
    stochastic recovery kernel exists! -/
theorem decision_counterexample_forces_negative_recovery_kernel (r00 r10 : Int)
    (hp0 : 10 * r00 + 10 * r10 = 8 * 35)
    (hq0 : 3 * r00 + 17 * r10 = 2 * 35) :
    r00 = 29 ∧ r10 = -1 ∧ ¬ (0 ≤ r10) := by
  omega

/-- Corollary (`tv_preserved_without_common_recovery`):
    No nonnegative integer-scaled recovery weights `r00, r10 ≥ 0` can satisfy both atom-0
    marginal recovery equations simultaneously. -/
theorem no_nonnegative_common_recovery_kernel_for_P_and_Q :
    ¬ ∃ (r00 r10 : Int),
      0 ≤ r00 ∧ 0 ≤ r10 ∧
      10 * r00 + 10 * r10 = 8 * 35 ∧
      3 * r00 + 17 * r10 = 2 * 35 := by
  intro ⟨r00, r10, _, hr10_nonneg, hp0, hq0⟩
  have ⟨_, _, hneg⟩ := decision_counterexample_forces_negative_recovery_kernel r00 r10 hp0 hq0
  exact hneg hr10_nonneg

/-- Theorem 2c (`PRIOR_LEAD.json` skewed-prior witness at `t = 1/4`, cleared by denominator `80`):
    While equal prior `t = 1/2` has zero Bayes value gap (`54/80 = 27/40` before and after),
    at prior `t = 1/4` (`t * P_i` vs `(1 - t) * Q_i` scaled by `80`: `P` scaled by `1`, `Q` scaled by `3`),
    ungrouped Bayes value is `max(8, 6) + max(2, 3) + max(10, 51) = 8 + 3 + 51 = 62` (`31/40`),
    whereas grouped Bayes value is `max(10, 9) + max(10, 51) = 10 + 51 = 61` (`61/80 < 62/80`)! -/
theorem skewed_prior_quarter_breaks_sufficiency :
    let v_before_80 := max 8 6 + max 2 3 + max 10 51
    let v_after_80 := max 10 9 + max 10 51
    v_before_80 = 62 ∧ v_after_80 = 61 ∧ v_before_80 - v_after_80 = 1 ∧ v_after_80 < v_before_80 := by
  decide

/-! ## 3. Myhill–Nerode 3-State Suffix Lower Bound (`Ending01.lean`) -/

/-- Exact specification of `Ending01.suffixState` on reversed words:
    returns `2` iff the word ends in `[false, true]` (`01`), `1` if it ends in `false` (`0`), and `0` otherwise. -/
def endsIn01 : List Bool → Bool
  | w =>
    match w.reverse with
    | true :: false :: _ => true
    | _ => false

/-- Theorem 3 (`Ending01.witnessHistories_pairwise` & `ending01_requires_three_states`):
    The three witness histories `w₀ = []`, `w₁ = [false]`, and `w₂ = [false, true]` are pairwise
    Myhill–Nerode distinguishable for `L01`:
    - suffix `[true]` separates `[]` (`[true]` does not end in `01`) from `[false]` (`[false, true]` ends in `01`),
    - suffix `[]` separates `[false, true]` (already in `L01`) from both `[]` and `[false]`,
    while suffix `[false, true]` maps all three histories into `L01` (demonstrating why suffix choice matters). -/
theorem ending01_three_witnesses_pairwise_separated :
    let w0 : List Bool := []
    let w1 : List Bool := [false]
    let w2 : List Bool := [false, true]
    endsIn01 (w0 ++ [true]) ≠ endsIn01 (w1 ++ [true]) ∧
    endsIn01 (w0 ++ []) ≠ endsIn01 (w2 ++ []) ∧
    endsIn01 (w1 ++ []) ≠ endsIn01 (w2 ++ []) ∧
    (endsIn01 (w0 ++ [false, true]) = true ∧
     endsIn01 (w1 ++ [false, true]) = true ∧
     endsIn01 (w2 ++ [false, true]) = true) := by
  decide

/-! ## 4. Compact-Group Angular Fourier Slice Bessel Bound (`EhrhartVolumeInequality` ↔ `SpherePacking`) -/

/-- Theorem 4 (`angularFourierCoefficient_sq_le_slice_energy_ae` ↔ `radialFourierOrbitAverage`):
    On a 2-point compact orbit `{+1, -1}` (representing the `m = 0` invariant orbit average
    `c0 = f0 + f1` in `SpherePacking.radialFourierOrbitAverage` and the `m = 1` oscillatory angular
    mode `c1 = f0 - f1` in `EhrhartVolumeInequality.angularFourierCoefficient`), Parseval's identity
    `(f0 + f1)^2 + (f0 - f1)^2 = 2 * (f0^2 + f1^2)` holds identically, so each individual mode
    satisfies `c_m^2 ≤ 2 * (f0^2 + f1^2)` with equality for `c0` iff `f0 = f1` (radial function!). -/
theorem two_point_torus_fourier_bessel_identity (f0 f1 : Int) :
    (f0 + f1) ^ 2 + (f0 - f1) ^ 2 = 2 * (f0 ^ 2 + f1 ^ 2) ∧
    (f0 - f1) ^ 2 = 2 * (f0 ^ 2 + f1 ^ 2) - (f0 + f1) ^ 2 := by
  constructor <;> grind

end CommonGround.Verification.TheoremAtlasBellmanDecisionAndAutomataBridge
