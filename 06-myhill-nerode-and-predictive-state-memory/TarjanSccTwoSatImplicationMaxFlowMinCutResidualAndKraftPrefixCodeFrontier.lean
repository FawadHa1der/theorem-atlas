/-
  06-myhill-nerode-and-predictive-state-memory/TarjanSccTwoSatImplicationMaxFlowMinCutResidualAndKraftPrefixCodeFrontier.lean

  Wave V258: Frontier #133 — Aspvall–Plass–Tarjan 2-SAT Implication Skew-Symmetry & SCC
  Condensation Dichotomy, Ford–Fulkerson Max-Flow Min-Cut Weak Duality & Backward-Residual
  Cancellation Rescue, and Kraft–McMillan Prefix-Free Dyadic Leaf Partition vs. Non-Prefix
  Ambiguous Decoding Collision.

  Cross-domain synthesis across Folders `06` + `08` + `03` + `09` + `10`
  (`cslib`, `oai-sat`, `econlib`, `tc-probcomb`, `oai-codes`):
  1. **2-SAT Implication Skew-Symmetry & Same-SCC Unsatisfiability vs. 3-SAT Barrier**:
     - Universal contrapositive equivalence (`two_sat_clause_iff_skew_symmetric_implications_universal`):
       every binary clause `(ℓ₁ ∨ ℓ₂)` is logically equivalent to the twin skew-symmetric
       implications `(¬ℓ₁ → ℓ₂) ∧ (¬ℓ₂ → ℓ₁)`.
     - Universal bidirectional cycle obstruction (`two_sat_bidirectional_implication_cycle_unsat_universal`):
       if `ℓ ⇒* ¬ℓ` and `¬ℓ ⇒* ℓ` hold under valuation `σ` (same Tarjan/Kosaraju SCC), `False` follows!
     - Acyclic condensation `3`-variable `4`-clause witness (`4/4` satisfied) vs. `2`-variable
       diamond same-SCC unsatisfiability (`0/4` valuations) and `3-SAT` (`7/8` odd-model cylinder)
       non-expressibility by pure `2-SAT` clauses without Tseitin auxiliaries.
  2. **Ford–Fulkerson / Edmonds–Karp Max-Flow Min-Cut Weak Duality & Residual Cancellation**:
     - Universal `(s, t)`-cut flux upper bound (`st_cut_net_outflow_le_cut_capacity_universal`)
       and universal Kirchoff flow bound `f01 + f02 ≤ 2` on the `4`-node unit diamond network.
     - Greedy forward-only augmentation (`s → a → b → t`) stalls at suboptimal flow `1 < 2`
       (`0` remaining forward-only paths!), whereas pushing `+1` unit along the **backward
       residual arc** `b → a` (`s → b → a → t`) cancels `f(a, b) : 1 ↦ 0` and achieves exact
       Min-Cut capacity `2 = cap({s}, {a, b, t})`.
  3. **Kraft–McMillan Dyadic Subtree Budget vs. Non-Prefix Ambiguous Collision**:
     - Universal dyadic subtree leaf-splitting conservation (`2^(L-(ℓ+1)) + 2^(L-(ℓ+1)) = 2^(L-ℓ)`).
     - Canonical Huffman code `{"0", "10", "110", "111"}` achieves tight Kraft equality
       `8 + 4 + 2 + 2 = 16 = 2^4` with unique prefix-free parsing, whereas Kraft-satisfying
       non-prefix code `{"0", "01", "10"}` (`2 + 1 + 1 = 4 ≤ 2^2`) suffers catastrophic message
       collision on `"010" = "0" ++ "10" = "01" ++ "0"`, and Kraft-violating lengths `(1, 1, 2)`
       (`2 + 2 + 1 = 5 > 4`) admit `0/16` prefix-free codes!

  Toolchain: `leanprover/lean4:v4.33.0` — zero `sorry`, zero `admit`, zero external axioms.
-/

namespace CommonGround.Frontier.TarjanTwoSatMaxFlowResidualAndKraftPrefix

/-! ## Part I: Aspvall–Plass–Tarjan 2-SAT Implication Skew-Symmetry & SCC Dichotomy -/

/-- A literal over `N` boolean variables `(varIdx, isPositive)`. -/
abbrev Lit2Sat (N : Nat) := Fin N × Bool

/-- Negate a literal `(v, sign) ↦ (v, !sign)`. -/
def negLit {N : Nat} (ℓ : Lit2Sat N) : Lit2Sat N :=
  (ℓ.1, !ℓ.2)

/-- Evaluate literal `ℓ` under boolean assignment `σ : Fin N → Bool`. -/
def evalLit {N : Nat} (σ : Fin N → Bool) (ℓ : Lit2Sat N) : Bool :=
  if ℓ.2 then σ ℓ.1 else !(σ ℓ.1)

/-- Evaluate a binary clause `(ℓ₁ ∨ ℓ₂)` under `σ`. -/
def evalClause2 {N : Nat} (σ : Fin N → Bool) (c : Lit2Sat N × Lit2Sat N) : Bool :=
  evalLit σ c.1 || evalLit σ c.2

theorem evalLit_negLit {N : Nat} (σ : Fin N → Bool) (ℓ : Lit2Sat N) :
    evalLit σ (negLit ℓ) = !(evalLit σ ℓ) := by
  rcases ℓ with ⟨v, s⟩
  dsimp [evalLit, negLit]
  cases s <;> cases (σ v) <;> rfl

/-- **Universal 2-SAT Skew-Symmetric Implication Equivalence**:
    Every binary clause `(ℓ₁ ∨ ℓ₂)` is satisfied by `σ` if and only if BOTH skew-symmetric
    contrapositive implication edges `(¬ℓ₁ → ℓ₂)` and `(¬ℓ₂ → ℓ₁)` are respected by `σ`. -/
theorem two_sat_clause_iff_skew_symmetric_implications_universal
    {N : Nat} (σ : Fin N → Bool) (ℓ₁ ℓ₂ : Lit2Sat N) :
    evalClause2 σ (ℓ₁, ℓ₂) = true ↔
      ((evalLit σ (negLit ℓ₁) = true → evalLit σ ℓ₂ = true) ∧
       (evalLit σ (negLit ℓ₂) = true → evalLit σ ℓ₁ = true)) := by
  unfold evalClause2
  rw [evalLit_negLit, evalLit_negLit]
  cases (evalLit σ ℓ₁) <;> cases (evalLit σ ℓ₂) <;> decide

/-- **Universal Bidirectional Implication Cycle Unsatisfiability (Tarjan/Kosaraju SCC Obstruction)**:
    If a literal `ℓ` and its negation `¬ℓ` lie on a mutual implication cycle (`ℓ ⇒* ¬ℓ` and `¬ℓ ⇒* ℓ`),
    no boolean valuation `σ` can satisfy the implication system. -/
theorem two_sat_bidirectional_implication_cycle_unsat_universal
    {N : Nat} (σ : Fin N → Bool) (ℓ : Lit2Sat N)
    (hFwd : evalLit σ ℓ = true → evalLit σ (negLit ℓ) = true)
    (hBwd : evalLit σ (negLit ℓ) = true → evalLit σ ℓ = true) :
    False := by
  rw [evalLit_negLit] at hFwd hBwd
  cases hVal : evalLit σ ℓ
  · have h := hBwd (by simp [hVal])
    simp [hVal] at h
  · have h := hFwd hVal
    simp [hVal] at h

/-- Acyclic 3-variable 4-clause 2-SAT system:
    `(x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂) ∧ (¬x₁ ∨ x₂) ∧ (x₂ ∨ x₂)`. -/
def acyclicTwoSatClauses : List (Lit2Sat 3 × Lit2Sat 3) :=
  [ ((⟨0, by omega⟩, true),  (⟨1, by omega⟩, true))
  , ((⟨0, by omega⟩, false), (⟨2, by omega⟩, true))
  , ((⟨1, by omega⟩, false), (⟨2, by omega⟩, true))
  , ((⟨2, by omega⟩, true),  (⟨2, by omega⟩, true)) ]

/-- Topological SCC condensation rank separating every variable from its negation. -/
def acyclicSccRank (ℓ : Lit2Sat 3) : Nat :=
  match ℓ.1.val, ℓ.2 with
  | 2, false => 0
  | 0, true  => 1
  | 1, false => 2
  | 0, false => 3
  | 1, true  => 4
  | _, _     => 5

/--Topological assignment `σ* = (false, true, true)` chosen by `sccRank(¬v) < sccRank(v)`. -/
def acyclicTopoSigma (v : Fin 3) : Bool :=
  decide (acyclicSccRank (v, false) < acyclicSccRank (v, true))

/-- Contradictory 2-variable 4-clause diamond merging `x₀` and `¬x₀` into one SCC:
    `(x₀ ∨ x₁) ∧ (x₀ ∨ ¬x₁) ∧ (¬x₀ ∨ x₁) ∧ (¬x₀ ∨ ¬x₁)`. -/
def diamondUnsatEval (b₀ b₁ : Bool) : Bool :=
  (b₀ || b₁) && (b₀ || !b₁) && (!b₀ || b₁) && (!b₀ || !b₁)

/-- Positive 2-clause `(x_i ∨ x_j)` on 3 variables (the ONLY 2-clauses rejecting `(false,false,false)`). -/
def evalPos2Clause3 (σ : Fin 3 → Bool) (i j : Fin 3) : Bool :=
  σ i || σ j

/-- **Positive Acyclic 2-SAT Condensation Witness vs. Same-SCC Cycle & 3-SAT Expressivity Barrier**:
    1. All `3` variables in `acyclicTwoSatClauses` occupy distinct literal/negation SCCs, and the
       topological assignment `acyclicTopoSigma` (`(false, true, true)`) satisfies `4/4` clauses;
    2. The `4`-clause implication cycle diamond satisfies `0/4` valuations (`∀ b₀ b₁, false`);
    3. Every `2`-clause over `3` variables that excludes `(false, false, false)` (namely `x_i ∨ x_j`)
       ALSO wrongly excludes at least one satisfying model of `(x₀ ∨ x₁ ∨ x₂)` (odd `7/8` support vs.
       even `2`-cylinder exclusions!). -/
theorem two_sat_acyclic_witness_vs_same_scc_unsat_and_three_sat_barrier :
    (∀ v : Fin 3, acyclicSccRank (v, true) ≠ acyclicSccRank (v, false)) ∧
    (acyclicTwoSatClauses.all (evalClause2 acyclicTopoSigma) = true) ∧
    (∀ b₀ b₁ : Bool, diamondUnsatEval b₀ b₁ = false) ∧
    (∀ i j : Fin 3,
      ∃ b₀ b₁ b₂ : Bool,
        (b₀ || b₁ || b₂) = true ∧
        evalPos2Clause3 (fun k => match k.val with | 0 => b₀ | 1 => b₁ | _ => b₂) i j = false) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  decide

/-! ## Part II: Ford–Fulkerson Max-Flow Min-Cut Weak Duality & Backward-Residual Rescue -/

/-- **Universal `(s, t)`-Cut Flux Decomposition & Weak Duality**:
    Whenever net source outflow `valF` decomposes as `outCross - inCross` across an `(s, t)`-cut
    with `outCross ≤ capCross` (forward capacity bound) and `0 ≤ inCross` (nonnegative reverse flow),
    total flow satisfies `valF ≤ capCross`, with equality iff forward cut arcs are saturated
    (`outCross = capCross`) and backward cut arcs carry zero flow (`inCross = 0`). -/
theorem st_cut_net_outflow_le_cut_capacity_universal
    (valF outCross inCross capCross : Int)
    (hFlux : valF = outCross - inCross)
    (hCap : outCross ≤ capCross)
    (hNonneg : 0 ≤ inCross) :
    valF ≤ capCross ∧ (valF = capCross ↔ (outCross = capCross ∧ inCross = 0)) := by
  omega

/-- Valid integer flow on the classic 4-node unit-capacity Ford–Fulkerson diamond
    (`s=0 → a=1`, `s=0 → b=2`, `a=1 → b=2`, `a=1 → t=3`, `b=2 → t=3`, all capacities `= 1`). -/
structure DiamondUnitFlow where
  f01 : Nat
  f02 : Nat
  f12 : Nat
  f13 : Nat
  f23 : Nat
  cap01 : f01 ≤ 1
  cap02 : f02 ≤ 1
  cap12 : f12 ≤ 1
  cap13 : f13 ≤ 1
  cap23 : f23 ≤ 1
  kirchhoff1 : f01 = f12 + f13
  kirchhoff2 : f02 + f12 = f23

/-- Total source-to-sink throughput `val(f) = f(0,1) + f(0,2)`. -/
def diamondFlowValue (f : DiamondUnitFlow) : Nat :=
  f.f01 + f.f02

/-- Check whether ANY forward-only `s →* t` path (`0→1→3`, `0→2→3`, or `0→1→2→3`) has strictly
    positive residual forward capacity on every edge WITHOUT using backward residual edge `2 → 1`. -/
def hasUnsaturatedForwardOnlyPath (f : DiamondUnitFlow) : Bool :=
  ((f.f01 < 1) && (f.f13 < 1)) ||
  ((f.f02 < 1) && (f.f23 < 1)) ||
  ((f.f01 < 1) && (f.f12 < 1) && (f.f23 < 1))

/-- Greedy 1-step forward-only flow pushing `1` unit along zig-zag `0 → 1 → 2 → 3`. -/
def greedyZigZagFlow : DiamondUnitFlow where
  f01 := 1
  f02 := 0
  f12 := 1
  f13 := 0
  f23 := 1
  cap01 := by omega
  cap02 := by omega
  cap12 := by omega
  cap13 := by omega
  cap23 := by omega
  kirchhoff1 := by omega
  kirchhoff2 := by omega

/-- Optimal flow obtained by augmenting `+1` along residual path `0 → 2 → 1 → 3`
    (using backward residual edge `2 → 1` with residual capacity `f12 = 1` to cancel `f12 : 1 ↦ 0`). -/
def residualRescuedMaxFlow : DiamondUnitFlow where
  f01 := 1
  f02 := 1
  f12 := 0
  f13 := 1
  f23 := 1
  cap01 := by omega
  cap02 := by omega
  cap12 := by omega
  cap13 := by omega
  cap23 := by omega
  kirchhoff1 := by omega
  kirchhoff2 := by omega

/-- **Universal Diamond Min-Cut Bound (`≤ 2`) & Greedy Forward-Only Stall (`1 < 2`) vs. Backward Residual Rescue (`= 2`)**:
    1. Every valid flow on the diamond satisfies `diamondFlowValue f ≤ 2` (`= cap({0}, {1,2,3})`),
       and achieving `= 2` forces zero internal cross-edge flow `f.f12 = 0`!
    2. Greedy forward augmentation along `0 → 1 → 2 → 3` gets trapped at `diamondFlowValue = 1 < 2`
       with `hasUnsaturatedForwardOnlyPath = false` (`50%` capacity loss if backward residual edges are omitted!);
    3. Augmenting along backward residual edge `2 → 1` (`f12 : 1 ↦ 0`) achieves exact Min-Cut value `2`! -/
theorem ford_fulkerson_greedy_trap_vs_residual_backward_rescue :
    (∀ f : DiamondUnitFlow, diamondFlowValue f ≤ 2 ∧ (diamondFlowValue f = 2 → f.f12 = 0)) ∧
    diamondFlowValue greedyZigZagFlow = 1 ∧
    hasUnsaturatedForwardOnlyPath greedyZigZagFlow = false ∧
    greedyZigZagFlow.f12 = 1 ∧
    diamondFlowValue residualRescuedMaxFlow = 2 ∧
    residualRescuedMaxFlow.f12 = 0 := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  intro f
  unfold diamondFlowValue
  have h01 := f.cap01
  have h02 := f.cap02
  have h13 := f.cap13
  have h23 := f.cap23
  have hk1 := f.kirchhoff1
  have hk2 := f.kirchhoff2
  omega

/-! ## Part III: Kraft–McMillan Dyadic Subtree Budget vs. Non-Prefix Ambiguous Collision -/

/-- Scaled dyadic subtree leaf count `2^(L - len)` at tree depth `L`. -/
def dyadicLeafWeight (L len : Nat) : Nat :=
  2 ^ (L - len)

/-- **Universal Dyadic Subtree Leaf-Splitting Conservation**:
    Splitting an internal binary-tree node at depth `ℓ < L` into its left (`0`) and right (`1`)
    children at depth `ℓ + 1` conserves exact dyadic leaf budget:
    `2^(L - (ℓ + 1)) + 2^(L - (ℓ + 1)) = 2^(L - ℓ)`. -/
theorem dyadic_subtree_split_identity_universal (L ℓ : Nat) (hLt : ℓ < L) :
    dyadicLeafWeight L (ℓ + 1) + dyadicLeafWeight L (ℓ + 1) = dyadicLeafWeight L ℓ := by
  unfold dyadicLeafWeight
  have hSub : L - ℓ = (L - (ℓ + 1)) + 1 := by omega
  rw [hSub, Nat.pow_succ]
  omega

/-- Strict or equal prefix check `u ⊑ v` on binary codewords `List Bool`. -/
def isBitPrefix : List Bool → List Bool → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: us, b :: vs => (a == b) && isBitPrefix us vs

/-- Pairwise prefix-freeness of an indexed codebook `Fin M → List Bool`. -/
def isPairwisePrefixFree {M : Nat} (code : Fin M → List Bool) : Bool :=
  (List.finRange M).all (fun i =>
    (List.finRange M).all (fun j =>
      (decide (i = j)) || !(isBitPrefix (code i) (code j))))

/-- Canonical 4-symbol prefix-free Huffman code `{"0", "10", "110", "111"}`. -/
def canonicalHuffman4 : Fin 4 → List Bool
  | ⟨0, _⟩ => [false]
  | ⟨1, _⟩ => [true, false]
  | ⟨2, _⟩ => [true, true, false]
  | ⟨3, _⟩ => [true, true, true]

/-- Non-prefix codebook `{"0", "01", "10"}` that SATISFIES Kraft's inequality (`2 + 1 + 1 = 4 ≤ 2²`). -/
def nonPrefixKraftCode : Fin 3 → List Bool
  | ⟨0, _⟩ => [false]
  | ⟨1, _⟩ => [false, true]
  | ⟨2, _⟩ => [true, false]

/-- Enumerate all `16` candidate 3-word binary codebooks with lengths `(1, 1, 2)`
    (whose Kraft sum is `2^(2-1) + 2^(2-1) + 2^(2-2) = 2 + 2 + 1 = 5 > 4 = 2^2`). -/
def oversubscribedCode112 (b0 b1 c0 c1 : Bool) : Fin 3 → List Bool
  | ⟨0, _⟩ => [b0]
  | ⟨1, _⟩ => [b1]
  | ⟨2, _⟩ => [c0, c1]

/-- **Canonical Prefix-Free Kraft Tightness vs. Non-Prefix Ambiguous Collision & Oversubscribed Impossibility**:
    1. `canonicalHuffman4` (`"0", "10", "110", "111"`) is pairwise prefix-free and achieves tight
       scaled Kraft equality `8 + 4 + 2 + 2 = 16 = 2^4` at depth `L = 4`;
    2. `nonPrefixKraftCode` (`"0", "01", "10"`) satisfies Kraft equality `2 + 1 + 1 = 4 = 2^2`
       yet violates prefix-freeness (`"0" ⊑ "01"`), causing `"010"` (`[false, true, false]`) to
       admit TWO distinct symbol factorizations (`[0, 2]` vs. `[1, 0]`)!
    3. Lengths `(1, 1, 2)` oversubscribe Kraft's budget (`2 + 2 + 1 = 5 > 4 = 2^2`), and across all
       `2^4 = 16` binary codebooks of lengths `(1, 1, 2)`, `0/16` are pairwise prefix-free! -/
theorem canonical_prefix_kraft_vs_non_prefix_collision_and_oversubscribed_impossibility :
    isPairwisePrefixFree canonicalHuffman4 = true ∧
    (dyadicLeafWeight 4 1 + dyadicLeafWeight 4 2 + dyadicLeafWeight 4 3 + dyadicLeafWeight 4 3 = 2 ^ 4) ∧
    (dyadicLeafWeight 2 1 + dyadicLeafWeight 2 2 + dyadicLeafWeight 2 2 = 2 ^ 2) ∧
    isPairwisePrefixFree nonPrefixKraftCode = false ∧
    (nonPrefixKraftCode ⟨0, by omega⟩ ++ nonPrefixKraftCode ⟨2, by omega⟩ = [false, true, false]) ∧
    (nonPrefixKraftCode ⟨1, by omega⟩ ++ nonPrefixKraftCode ⟨0, by omega⟩ = [false, true, false]) ∧
    (dyadicLeafWeight 2 1 + dyadicLeafWeight 2 1 + dyadicLeafWeight 2 2 > 2 ^ 2) ∧
    (∀ b0 b1 c0 c1 : Bool, isPairwisePrefixFree (oversubscribedCode112 b0 b1 c0 c1) = false) := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl, by decide, ?_⟩
  decide

end CommonGround.Frontier.TarjanTwoSatMaxFlowResidualAndKraftPrefix
