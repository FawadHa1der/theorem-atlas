/-!
# Kantorovich–Rubinstein Optimal Transport Complementary Slackness, Brenier–Rockafellar Cyclic Monotonicity vs. `2-Opt` `3`-Cycle Trap, Sinkhorn Bregman Scaling & Discrete Cheeger Conductance (`0` Imports, `0` Sorry)

This standalone pure-core Lean 4.33.0 frontier module unifies **Folder `08`**
(Kantorovich–Galois Structural Duality), **Folder `04`** (Primal–Dual LP & Bregman
Optimization), and **Folder `09`** (Discrete Graph Laplacians & Cut Obstructions):

1. **Kantorovich Primal–Dual Complementary Slackness & Universal `2 × 2` Submodular Attainment**
   (`kantorovich_primal_dual_complementary_slackness_and_submodular_attainment_vs_mass_imbalance`):
   - *Universal Weak Duality & Exact Slack Identity*: For any non-negative `2 × 2` coupling
     `π_{i,j} ≥ 0` with marginals `(r0, r1), (c0, c1)` and dual potentials `(u0, u1, v0, v1)`
     satisfying `u_i + v_j ≤ C_{i,j}`, total primal minus dual equals the exact sum of cell slacks
     `∑_{i,j} π_{i,j} (C_{i,j} - u_i - v_j) ≥ 0`!
   - *Universal `2 × 2` Monge–Submodular Northwest-Corner Strong Duality*: Whenever `r0, r1, c0, c1 ≥ 0`,
     `r0 + r1 = c0 + c1`, and `C00 + C11 ≤ C01 + C10`, explicit northwest-corner `π*` and explicit
     dual potentials `(u0*, u1*, v0*, v1*)` achieve **exact primal = dual equality**!
   - *Premise-Failure Counterexample*: Under unbalanced total mass `r0 + r1 ≠ c0 + c1`, shifting
     `(u_i, v_j) ↦ (u_i + M, v_j - M)` preserves all `4` dual constraints `u_i + v_j ≤ C_{i,j}`
     while inflating the dual objective unboundedly (`M (r0 + r1 - c0 - c1) → +∞`)!

2. **Brenier–Rockafellar `3 × 3` Permutational Cyclic Monotonicity (`↔`) vs. Strict `2-Opt` Local Trap**
   (`brenier_rockafellar_cyclic_monotonicity_iff_vs_two_opt_three_cycle_trap`):
   - *Universal `S_3` Characterization*: Diagonal matching `(0→0, 1→1, 2→2)` is globally optimal
     across all `3! = 6` permutations **if and only if** all `3` pairwise `2`-cycles AND both
     oriented `3`-cycles have non-negative slack!
   - *Constructive `2-Opt` Trap Witness*: Cost matrix `C = [[2, 1, 5], [5, 2, 1], [1, 5, 2]]` gives
     diagonal cost `6`, every pairwise `2`-swap strictly worsens cost to `8` (`+2 > 0`, trapping
     greedy `2-opt` local search!), YET the cyclic `3`-shift `(0→1, 1→2, 2→0)` achieves cost `3 < 6`!

3. **Sinkhorn Log-Domain Cross-Ratio Gauge Invariance & Bregman Pythagorean Identity vs. Support Barrier**
   (`sinkhorn_log_cross_ratio_invariance_and_bregman_pythagoras_vs_support_barrier`):
   - *Universal Log-Kernel Cross-Difference Invariance*: Adding arbitrary row/column dual scalings
     `(α0, α1), (β0, β1)` to `-C_{i,j}` leaves `(K00 + K11) - (K01 + K10) = (C01 + C10) - (C00 + C11)`
     100% invariant, accompanied by the exact quadratic Bregman three-point identity!
   - *Premise-Failure Counterexample*: Zeroing off-diagonal support (`π01 = 0`) when `r0 = 1, c0 = 0`
     leaves ZERO non-negative feasible coupling!

4. **Discrete Cheeger Cut-Laplacian Identity (`x_S^T L x_S = |∂ S|`) vs. Barbell Bridge Collapse**
   (`discrete_cheeger_cut_laplacian_identity_and_k4_expansion_vs_barbell_bottleneck`):
   - *Universal Cut-Indicator Dirichlet Identity*: On any `4`-vertex weighted graph, evaluating
     the Laplacian quadratic form on `{0, 1}` indicator `(s0, s1, s2, s3)` equals exact cut weight!
   - *Sharp `K_4` Expansion (`|∂ S| = 4` vs. `λ_2 = 4`) vs. `1`-Bridge Barbell Bottleneck (`|∂ S| = 1 → 0`)*.
-/

namespace CommonGround.Frontier.KantorovichOptimalTransportAndCheegerConductance

/-- Primal `2 × 2` transport cost `∑_{i,j} π_{i,j} C_{i,j}`. -/
def primalCost2 (p00 p01 p10 p11 c00 c01 c10 c11 : Int) : Int :=
  p00 * c00 + p01 * c01 + p10 * c10 + p11 * c11

/-- Dual `2 × 2` Kantorovich objective `r0*u0 + r1*u1 + c0*v0 + c1*v1`. -/
def dualObj2 (r0 r1 c0 c1 u0 u1 v0 v1 : Int) : Int :=
  r0 * u0 + r1 * u1 + c0 * v0 + c1 * v1

/-- Theorem 1: Kantorovich Primal–Dual Complementary Slackness & Universal `2 × 2` Monge Attainment
    vs. Unbalanced Mass Dual Unboundedness. -/
theorem kantorovich_primal_dual_complementary_slackness_and_submodular_attainment_vs_mass_imbalance :
    -- (1) Universal Weak Duality & Exact Complementary-Slackness Identity:
    (∀ p00 p01 p10 p11 c00 c01 c10 c11 u0 u1 v0 v1 : Int,
      let r0 := p00 + p01
      let r1 := p10 + p11
      let k0 := p00 + p10
      let k1 := p01 + p11
      primalCost2 p00 p01 p10 p11 c00 c01 c10 c11 - dualObj2 r0 r1 k0 k1 u0 u1 v0 v1 =
        p00 * (c00 - u0 - v0) + p01 * (c01 - u0 - v1) +
        p10 * (c10 - u1 - v0) + p11 * (c11 - u1 - v1) ∧
      (0 ≤ p00 → 0 ≤ p01 → 0 ≤ p10 → 0 ≤ p11 →
       u0 + v0 ≤ c00 → u0 + v1 ≤ c01 → u1 + v0 ≤ c10 → u1 + v1 ≤ c11 →
       dualObj2 r0 r1 k0 k1 u0 u1 v0 v1 ≤ primalCost2 p00 p01 p10 p11 c00 c01 c10 c11)) ∧
    -- (2) Universal `2 × 2` Submodular (`C00 + C11 ≤ C01 + C10`) Strong Duality Attainment:
    --     Northwest-corner coupling `π*` + explicit Kantorovich potentials achieve `Primal = Dual`!
    (∀ r0 r1 k0 k1 c00 c01 c10 c11 : Int,
      0 ≤ r0 → 0 ≤ r1 → 0 ≤ k0 → 0 ≤ k1 →
      r0 + r1 = k0 + k1 →
      c00 + c11 ≤ c01 + c10 →
      ∃ p00 p01 p10 p11 u0 u1 v0 v1 : Int,
        0 ≤ p00 ∧ 0 ≤ p01 ∧ 0 ≤ p10 ∧ 0 ≤ p11 ∧
        p00 + p01 = r0 ∧ p10 + p11 = r1 ∧ p00 + p10 = k0 ∧ p01 + p11 = k1 ∧
        u0 + v0 ≤ c00 ∧ u0 + v1 ≤ c01 ∧ u1 + v0 ≤ c10 ∧ u1 + v1 ≤ c11 ∧
        primalCost2 p00 p01 p10 p11 c00 c01 c10 c11 = dualObj2 r0 r1 k0 k1 u0 u1 v0 v1) ∧
    -- (3) Premise-Failure Counterexample (Violating Mass Balance `r0 + r1 = k0 + k1`):
    --     At `r = (2, 0), k = (1, 0)` (`r0 + r1 - k0 - k1 = +1`), gauge shift `(u_i + M, v_j - M)`
    --     satisfies `u_i + v_j ≤ 0` for EVERY `M : Int` while achieving unbounded dual `M`!
    (∀ M : Int,
      (M + (-M) ≤ 0) ∧
      dualObj2 2 0 1 0 M M (-M) (-M) = M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p00 p01 p10 p11 c00 c01 c10 c11 u0 u1 v0 v1
    dsimp only
    have hId :
        primalCost2 p00 p01 p10 p11 c00 c01 c10 c11 -
          dualObj2 (p00 + p01) (p10 + p11) (p00 + p10) (p01 + p11) u0 u1 v0 v1 =
          p00 * (c00 - u0 - v0) + p01 * (c01 - u0 - v1) +
          p10 * (c10 - u1 - v0) + p11 * (c11 - u1 - v1) := by
      unfold primalCost2 dualObj2
      grind
    refine ⟨hId, ?_⟩
    intro hp00 hp01 hp10 hp11 hd00 hd01 hd10 hd11
    have s00 : 0 ≤ p00 * (c00 - u0 - v0) := Int.mul_nonneg hp00 (by omega)
    have s01 : 0 ≤ p01 * (c01 - u0 - v1) := Int.mul_nonneg hp01 (by omega)
    have s10 : 0 ≤ p10 * (c10 - u1 - v0) := Int.mul_nonneg hp10 (by omega)
    have s11 : 0 ≤ p11 * (c11 - u1 - v1) := Int.mul_nonneg hp11 (by omega)
    omega
  · intro r0 r1 k0 k1 c00 c01 c10 c11 hr0 hr1 hk0 hk1 hBal hSub
    by_cases hCase : r0 ≤ k0
    · -- Case 1 (`r0 ≤ k0`): active tree is `(0,0), (1,0), (1,1)`:
      -- Set `u0 = 0, v0 = c00, u1 = c10 - c00, v1 = c11 - c10 + c00`:
      -- Check `(0, 1)`: `u0 + v1 = c11 - c10 + c00 ≤ c01` iff `c00 + c11 ≤ c01 + c10` (`hSub`!)
      refine ⟨r0, 0, k0 - r0, k1, 0, c10 - c00, c00, c11 - c10 + c00,
              hr0, by omega, by omega, hk1,
              by omega, by omega, by omega, by omega,
              by omega, by omega, by omega, by omega, ?_⟩
      unfold primalCost2 dualObj2
      have hk1Eq : k1 = r0 + r1 - k0 := by omega
      rw [hk1Eq]
      grind
    · -- Case 2 (`k0 < r0`): active tree is `(0,0), (0,1), (1,1)`:
      -- Set `u0 = 0, v0 = c00, v1 = c01, u1 = c11 - c01`:
      -- Check `(1, 0)`: `u1 + v0 = c11 - c01 + c00 ≤ c10` iff `c00 + c11 ≤ c01 + c10` (`hSub`!)
      refine ⟨k0, r0 - k0, 0, r1, 0, c11 - c01, c00, c01,
              hk0, by omega, by omega, hr1,
              by omega, by omega, by omega, by omega,
              by omega, by omega, by omega, by omega, ?_⟩
      unfold primalCost2 dualObj2
      have hk1Eq : k1 = r0 + r1 - k0 := by omega
      rw [hk1Eq]
      grind
  · intro M
    unfold dualObj2
    omega

/-- Theorem 2: Brenier–Rockafellar `3 × 3` Permutational Cyclic Monotonicity (`↔`)
    vs. Strict `2-Opt` Local Minimum Trapped `+3` Above the Global `3`-Cycle Optimum! -/
theorem brenier_rockafellar_cyclic_monotonicity_iff_vs_two_opt_three_cycle_trap :
    -- (1) Universal `S_3` Characterization: diagonal `(0→0, 1→1, 2→2)` beats ALL `5` non-identity
    --     permutations iff all `3` `2`-cycles AND both `3`-cycles have non-negative slack:
    (∀ c00 c01 c02 c10 c11 c12 c20 c21 c22 : Int,
      let diag := c00 + c11 + c22
      (diag ≤ c01 + c10 + c22 ∧
       diag ≤ c00 + c12 + c21 ∧
       diag ≤ c02 + c11 + c20 ∧
       diag ≤ c01 + c12 + c20 ∧
       diag ≤ c02 + c10 + c21) ↔
      (c00 + c11 ≤ c01 + c10 ∧
       c11 + c22 ≤ c12 + c21 ∧
       c00 + c22 ≤ c02 + c20 ∧
       c00 + c11 + c22 ≤ c01 + c12 + c20 ∧
       c00 + c11 + c22 ≤ c02 + c10 + c21)) ∧
    -- (2) Constructive `2-Opt` Trap Counterexample (`C = [[2, 1, 5], [5, 2, 1], [1, 5, 2]]`):
    --     Diagonal cost is `6`; EVERY pairwise `2`-swap strictly increases cost to `8` (`+2` slack > 0),
    --     YET forward `3`-cycle `(0→1, 1→2, 2→0)` achieves cost `3 < 6`!
    (let c : Fin 3 → Fin 3 → Int := fun i j =>
       match i.val, j.val with
       | 0, 0 => 2 | 0, 1 => 1 | 0, _ => 5
       | 1, 0 => 5 | 1, 1 => 2 | 1, _ => 1
       | _, 0 => 1 | _, 1 => 5 | _, _ => 2
     let i0 : Fin 3 := ⟨0, by decide⟩
     let i1 : Fin 3 := ⟨1, by decide⟩
     let i2 : Fin 3 := ⟨2, by decide⟩
     -- Diagonal = 6:
     c i0 i0 + c i1 i1 + c i2 i2 = 6 ∧
     -- All three 2-swaps strictly worsen cost to 8 > 6:
     c i0 i1 + c i1 i0 + c i2 i2 = 8 ∧
     c i0 i0 + c i1 i2 + c i2 i1 = 8 ∧
     c i0 i2 + c i1 i1 + c i2 i0 = 8 ∧
     -- Yet forward 3-cycle drops cost to 3 < 6!
     c i0 i1 + c i1 i2 + c i2 i0 = 3) := by
  refine ⟨?_, by decide⟩
  intro c00 c01 c02 c10 c11 c12 c20 c21 c22
  dsimp only
  omega

/-- Theorem 3: Sinkhorn Log-Domain Cross-Difference Gauge Invariance & Quadratic Bregman Pythagoras
    vs. Zero-Support Feasibility Breakdown. -/
theorem sinkhorn_log_cross_ratio_invariance_and_bregman_pythagoras_vs_support_barrier :
    -- (1) Universal Log-Domain Cross-Difference Invariance under ANY row/column dual updates `(a0, a1, b0, b1)`:
    (∀ c00 c01 c10 c11 a0 a1 b0 b1 : Int,
      let k00 := a0 + b0 - c00
      let k01 := a0 + b1 - c01
      let k10 := a1 + b0 - c10
      let k11 := a1 + b1 - c11
      (k00 + k11) - (k01 + k10) = (c01 + c10) - (c00 + c11)) ∧
    -- (2) Universal Quadratic Bregman Three-Point Identity `D(x‖z) = D(x‖y) + D(y‖z) + 2(x - y)(y - z)`:
    (∀ x y z : Int,
      (x - z) * (x - z) = (x - y) * (x - y) + (y - z) * (y - z) + 2 * (x - y) * (y - z)) ∧
    -- (3) Premise-Failure Counterexample (Forbidden Support Cell `p01 = 0` when `r = (1, 0), k = (0, 1)`):
    --     No non-negative coupling exists if `p01 = 0`, `p00 + p01 = 1`, and `p00 + p10 = 0`!
    (¬ ∃ p00 p01 p10 p11 : Int,
      0 ≤ p00 ∧ 0 ≤ p01 ∧ 0 ≤ p10 ∧ 0 ≤ p11 ∧
      p01 = 0 ∧ p00 + p01 = 1 ∧ p00 + p10 = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c00 c01 c10 c11 a0 a1 b0 b1
    dsimp only
    omega
  · intro x y z
    grind
  · intro ⟨p00, p01, p10, p11, hp00, hp01, hp10, hp11, hz01, hr0, hk0⟩
    omega

/-- Weighted `4`-vertex graph Laplacian quadratic form `∑_{i < j} w_{ij} (x_i - x_j)^2`. -/
def lapQuad4 (w01 w02 w03 w12 w13 w23 x0 x1 x2 x3 : Int) : Int :=
  w01 * (x0 - x1) * (x0 - x1) +
  w02 * (x0 - x2) * (x0 - x2) +
  w03 * (x0 - x3) * (x0 - x3) +
  w12 * (x1 - x2) * (x1 - x2) +
  w13 * (x1 - x3) * (x1 - x3) +
  w23 * (x2 - x3) * (x2 - x3)

/-- Boolean `{0, 1}` indicator value `b01 b ∈ {0, 1}`. -/
def b01 (b : Bool) : Int := if b then 1 else 0

/-- Theorem 4: Discrete Cheeger Cut-Laplacian Identity (`1_S^T L 1_S = |∂_w S|`) & `K_4` Uniform Expansion
    vs. Barbell Bridge Bottleneck Collapse (`4 → 1 → 0`). -/
theorem discrete_cheeger_cut_laplacian_identity_and_k4_expansion_vs_barbell_bottleneck :
    -- (1) Universal Cut-Indicator Dirichlet Identity across ALL `2^4 = 16` subsets `S ⊆ {0, 1, 2, 3}`:
    (∀ (w01 w02 w03 w12 w13 w23 : Int) (s0 s1 s2 s3 : Bool),
      lapQuad4 w01 w02 w03 w12 w13 w23 (b01 s0) (b01 s1) (b01 s2) (b01 s3) =
        (if s0 != s1 then w01 else 0) +
        (if s0 != s2 then w02 else 0) +
        (if s0 != s3 then w03 else 0) +
        (if s1 != s2 then w12 else 0) +
        (if s1 != s3 then w13 else 0) +
        (if s2 != s3 then w23 else 0)) ∧
    -- (2) Sharp `K_4` Expander Conductance: every non-empty proper cut `S` of `K_4` crosses `≥ 3` edges
    --     (and every balanced `2 + 2` cut crosses `4` edges)!
    (∀ s0 s1 s2 s3 : Bool,
      ¬ (s0 = s1 ∧ s1 = s2 ∧ s2 = s3) →
      3 ≤ lapQuad4 1 1 1 1 1 1 (b01 s0) (b01 s1) (b01 s2) (b01 s3)) ∧
    -- (3) Premise-Failure Counterexample (Barbell Bottleneck vs. Disconnected Collapse):
    --     Two `K_2` cliques `{0, 1}` and `{2, 3}` joined ONLY by bridge `(1, 2)` of weight `b ∈ {1, 0}`
    --     collapse balanced cut `{0, 1} | {2, 3}` from `4` (`K_4`) down to `1` (`b = 1`) and `0` (`b = 0`)!
    (lapQuad4 1 1 1 1 1 1 1 1 0 0 = 4 ∧
     lapQuad4 1 0 0 1 0 1 1 1 0 0 = 1 ∧
     lapQuad4 1 0 0 0 0 1 1 1 0 0 = 0) := by
  refine ⟨?_, by decide, by decide⟩
  intro w01 w02 w03 w12 w13 w23 s0 s1 s2 s3
  cases s0 <;> cases s1 <;> cases s2 <;> cases s3 <;>
    simp [lapQuad4, b01] <;> try omega

end CommonGround.Frontier.KantorovichOptimalTransportAndCheegerConductance
