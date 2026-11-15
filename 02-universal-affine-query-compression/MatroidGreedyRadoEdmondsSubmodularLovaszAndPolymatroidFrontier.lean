/-
  MatroidGreedyRadoEdmondsSubmodularLovaszAndPolymatroidFrontier.lean
  -------------------------------------------------------------------
   Frontier #98 (Folder 02 — Universal Affine Query & Combinatorial Compression):
   Machine-checked pure-core Lean 4.33.0 (`0` imports, `0` sorry) formalization of:
   1. Rado–Edmonds Matroid Symmetric Basis Exchange (`8` spanning trees of the Diamond
      graph `K₄ - e` across all `5,120` exchange triples) & Universal `U_{2,4}` Greedy
      Optimality vs. `P₃` Matching Augmentation Failure & `2`-for-`1` Greedy Suboptimality (`4 < 6`),
   2. Submodular Diminishing-Returns `↔` & Universal Lovász Extension Subadditivity
      `lovasz2(x + y) ≤ lovasz2(x) + lovasz2(y)` over `ℤ²` vs. Supermodular Synergy Concavity,
   3. Edmonds Polymatroid Base Polytope `B(f)` Extreme-Point Minimax Duality
      (`max_{b ∈ B(f)} ⟨x, b⟩ = lovasz2(x)`) vs. Non-Submodular Empty Base Polytope (`B(f) = ∅`),
   4. Nemhauser–Wolsey–Fisher `(1 - (1 - 1/k)^k)` Monotone Submodular Greedy Contraction
      (`4 · F₂ ≥ 3 · OPT` at `k = 2`) vs. Complement Zero-Marginal Greedy Stall (`F₂ = 0 < 10`).
-/

namespace CommonGround.Frontier.MatroidSubmodularLovasz

/-! ## 1. Diamond Graphic Matroid `M(K₄ - e)` Basis Exchange vs. `P₃` Non-Matroid Matching -/

/-- Bit-count of a `5`-bit edge subset mask (`0 .. 31`). -/
def popcount5 (m : Nat) : Nat :=
  (m &&& 1) + ((m >>> 1) &&& 1) + ((m >>> 2) &&& 1) + ((m >>> 3) &&& 1) + ((m >>> 4) &&& 1)

/-- Membership of edge `e ∈ {0..4}` in a `5`-bit mask. -/
def memEdge5 (m e : Nat) : Bool :=
  ((m >>> e) &&& 1) == 1

/-- Spanning-tree basis predicate of the `5`-edge Diamond graph `K₄ - e`:
    edges `0={A,B}, 1={B,C}, 2={A,C}` (upper triangle, mask `7`) and
    edges `2={A,C}, 3={A,D}, 4={C,D}` (lower triangle, mask `28`).
    A `3`-edge subset is a spanning tree iff it avoids both `3`-cycles `7` and `28`. -/
def isDiamondBasis (m : Nat) : Bool :=
  (m < 32) && (popcount5 m == 3) && !(m == 7) && !(m == 28)

/-- Count of spanning trees of `K₄ - e` across all `32` edge subsets. -/
def diamondBasisCount : Nat :=
  let rec loop (k acc : Nat) : Nat :=
    match k with
    | 0 => acc
    | n + 1 => loop n (if isDiamondBasis n then acc + 1 else acc)
  loop 32 0

/-- Brualdi Strong Symmetric Basis Exchange check across all `32 × 32 × 5 = 5,120` triples:
    whenever `B₁, B₂` are bases of `M(K₄ - e)` and `x ∈ B₁ \ B₂`, there exists `y ∈ B₂ \ B₁`
    such that BOTH `(B₁ \ {x}) ∪ {y}` and `(B₂ \ {y}) ∪ {x}` are bases of `M(K₄ - e)`. -/
def checkDiamondStrongExchange : Bool :=
  let rec loopB1 (b1 : Nat) : Bool :=
    match b1 with
    | 0 => true
    | m1 + 1 =>
      let okM1 :=
        if !isDiamondBasis m1 then true
        else
          let rec loopB2 (b2 : Nat) : Bool :=
            match b2 with
            | 0 => true
            | m2 + 1 =>
              let okM2 :=
                if !isDiamondBasis m2 then true
                else
                  let rec loopX (x : Nat) : Bool :=
                    match x with
                    | 0 => true
                    | ex + 1 =>
                      let in1Not2 := memEdge5 m1 ex && !memEdge5 m2 ex
                      let okEx :=
                        if !in1Not2 then true
                        else
                          let rec findY (y : Nat) : Bool :=
                            match y with
                            | 0 => false
                            | ey + 1 =>
                              let in2Not1 := memEdge5 m2 ey && !memEdge5 m1 ey
                              let swap1 := (m1 ^^^ (1 <<< ex)) ||| (1 <<< ey)
                              let swap2 := (m2 ^^^ (1 <<< ey)) ||| (1 <<< ex)
                              (in2Not1 && isDiamondBasis swap1 && isDiamondBasis swap2) || findY ey
                          findY 5
                      okEx && loopX ex
                  loopX 5
              okM2 && loopB2 m2
          loopB2 32
      okM1 && loopB1 m1
  loopB1 32

/-- Matching independence predicate on the `3`-edge path `P₃` (`e₀={v₀,v₁}, e₁={v₁,v₂}, e₂={v₂,v₃}`):
    no two adjacent edges (`{0,1}` mask `3` or `{1,2}` mask `6`) may co-occur. -/
def isP3Matching (m : Nat) : Bool :=
  (m < 8) && ((m &&& 3) != 3) && ((m &&& 6) != 6)

/-- **Theorem 1 (Rado–Edmonds Matroid Basis Exchange & Greedy Optimality vs. `P₃` Matching Failure)**:
    1. The Diamond graphic matroid `M(K₄ - e)` has exactly `8` spanning-tree bases and satisfies
       Brualdi's Strong Symmetric Basis Exchange across all `5,120` `(B₁, B₂, x)` triples.
    2. On `U_{2,4}`, for ANY sorted integer weights `w₀ ≥ w₁ ≥ w₂ ≥ w₃`, the Rado–Edmonds greedy
       top-`2` basis `{0,1}` dominates all `6` rank-`2` bases simultaneously.
    3. Conversely, on the `3`-edge path `P₃` with weights `(3, 4, 3)`, matchings form a hereditary
       independence system that violates matroid augmentation at `I = {1}` (`mask 2`) vs `J = {0,2}`
       (`mask 5`), causing Greedy to lock in `{1}` (`weight 4`) and miss `{0,2}` (`weight 6`). -/
theorem rado_edmonds_matroid_basis_exchange_and_greedy_optimality_vs_p3_matching_failure :
    diamondBasisCount = 8 ∧
    checkDiamondStrongExchange = true ∧
    (∀ w0 w1 w2 w3 : Int,
      w3 ≤ w2 → w2 ≤ w1 → w1 ≤ w0 →
      w0 + w2 ≤ w0 + w1 ∧ w0 + w3 ≤ w0 + w1 ∧
      w1 + w2 ≤ w0 + w1 ∧ w1 + w3 ≤ w0 + w1 ∧ w2 + w3 ≤ w0 + w1) ∧
    (isP3Matching 2 = true ∧ isP3Matching 5 = true ∧
     isP3Matching (2 ||| 1) = false ∧ isP3Matching (2 ||| 4) = false ∧
     (4 : Int) < 3 + 3) := by
  refine ⟨by decide, by decide, ?_, ⟨by decide, by decide, by decide, by decide, by omega⟩⟩
  intro w0 w1 w2 w3 h32 h21 h10
  omega

/-! ## 2. Submodular Diminishing Returns & Universal Lovász Extension Convexity -/

/-- Normalized `2`-element Lovász extension (`f(∅) = 0, f({0}) = v10, f({1}) = v01, f({0,1}) = v11`)
    evaluated at arbitrary `(x0, x1) ∈ ℤ²`. -/
def lovasz2 (v10 v01 v11 x0 x1 : Int) : Int :=
  if x1 ≤ x0 then (x0 - x1) * v10 + x1 * v11
  else (x1 - x0) * v01 + x0 * v11

/-- Helper lemma: under submodularity `v11 ≤ v10 + v01`, both permutation-chamber linear forms
    minorize `lovasz2 v10 v01 v11 x0 x1` on ALL `(x0, x1) ∈ ℤ²`. -/
theorem lovasz2_chamber_majorizes_both_orders
    (v10 v01 v11 x0 x1 : Int) (hSub : v11 ≤ v10 + v01) :
    (x0 - x1) * v10 + x1 * v11 ≤ lovasz2 v10 v01 v11 x0 x1 ∧
    (x1 - x0) * v01 + x0 * v11 ≤ lovasz2 v10 v01 v11 x0 x1 := by
  unfold lovasz2
  by_cases hCmp : x1 ≤ x0
  · simp [hCmp]
    have hDiff : 0 ≤ (x0 - x1) * (v10 + v01 - v11) :=
      Int.mul_nonneg (by omega) (by omega)
    have hId : ((x0 - x1) * v10 + x1 * v11) - ((x1 - x0) * v01 + x0 * v11) =
        (x0 - x1) * (v10 + v01 - v11) := by grind
    omega
  · simp [hCmp]
    have hDiff : 0 ≤ (x1 - x0) * (v10 + v01 - v11) :=
      Int.mul_nonneg (by omega) (by omega)
    have hId : ((x1 - x0) * v01 + x0 * v11) - ((x0 - x1) * v10 + x1 * v11) =
        (x1 - x0) * (v10 + v01 - v11) := by grind
    omega

/-- **Theorem 2 (Submodular Diminishing Returns `↔` & Universal Lovász Extension Subadditivity vs. Supermodular Failure)**:
    1. Exact equivalence: `v11 ≤ v10 + v01 ↔ v11 - v01 ≤ v10` (marginal gain of `0` shrinks with `{1}`).
    2. Exact Boolean extension: `lovasz2` agrees with `f` on `(0,0), (1,0), (0,1), (1,1)`.
    3. **Lovász Extension Convexity Theorem (`1983`)**: Whenever `v11 ≤ v10 + v01`, `lovasz2` is
       globally subadditive (`lovasz2(x + y) ≤ lovasz2(x) + lovasz2(y)`) for ALL `x0, x1, y0, y1 : Int`.
    4. **Supermodular Premise Failure**: For complementary synergy `(v10, v01, v11) = (0, 0, 2)`
       (`v10 + v01 = 0 < 2 = v11`), `lovasz2(1, 0) + lovasz2(0, 1) = 0 < 2 = lovasz2(1, 1)`. -/
theorem submodular_diminishing_returns_iff_and_lovasz_extension_convexity_vs_supermodular_concavity :
    (∀ v10 v01 v11 : Int, (v11 ≤ v10 + v01 ↔ v11 - v01 ≤ v10)) ∧
    (∀ v10 v01 v11 : Int,
      lovasz2 v10 v01 v11 0 0 = 0 ∧
      lovasz2 v10 v01 v11 1 0 = v10 ∧
      lovasz2 v10 v01 v11 0 1 = v01 ∧
      lovasz2 v10 v01 v11 1 1 = v11) ∧
    (∀ v10 v01 v11 x0 x1 y0 y1 : Int,
      v11 ≤ v10 + v01 →
      lovasz2 v10 v01 v11 (x0 + y0) (x1 + y1) ≤
        lovasz2 v10 v01 v11 x0 x1 + lovasz2 v10 v01 v11 y0 y1) ∧
    (lovasz2 0 0 2 1 0 + lovasz2 0 0 2 0 1 < lovasz2 0 0 2 (1 + 0) (0 + 1)) := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro v10 v01 v11
    omega
  · intro v10 v01 v11
    unfold lovasz2
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  · intro v10 v01 v11 x0 x1 y0 y1 hSub
    have hx := lovasz2_chamber_majorizes_both_orders v10 v01 v11 x0 x1 hSub
    have hy := lovasz2_chamber_majorizes_both_orders v10 v01 v11 y0 y1 hSub
    unfold lovasz2
    by_cases hSum : x1 + y1 ≤ x0 + y0
    · simp only [hSum, ↓reduceIte]
      have hLin : ((x0 + y0) - (x1 + y1)) * v10 + (x1 + y1) * v11 =
          ((x0 - x1) * v10 + x1 * v11) + ((y0 - y1) * v10 + y1 * v11) := by grind
      have hx1 := hx.1
      have hy1 := hy.1
      unfold lovasz2 at hx1 hy1
      omega
    · simp only [hSum, ↓reduceIte]
      have hLin : ((x1 + y1) - (x0 + y0)) * v01 + (x0 + y0) * v11 =
          ((x1 - x0) * v01 + x0 * v11) + ((y1 - y0) * v01 + y0 * v11) := by grind
      have hx2 := hx.2
      have hy2 := hy.2
      unfold lovasz2 at hx2 hy2
      omega

/-! ## 3. Edmonds Polymatroid Base Polytope Minimax vs. Empty Base Polytope -/

/-- Membership in the `2`-element Edmonds base polytope `B(f) = {b ∈ ℤ² | b₀ ≤ v10 ∧ b₁ ≤ v01 ∧ b₀ + b₁ = v11}`. -/
def inBasePolytope2 (v10 v01 v11 b0 b1 : Int) : Prop :=
  b0 ≤ v10 ∧ b1 ≤ v01 ∧ b0 + b1 = v11

/-- **Theorem 3 (Edmonds Polymatroid Greedy Extreme-Point Minimax vs. Non-Submodular Empty `B(f)`)**:
    1. Under `v11 ≤ v10 + v01`, both permutation-greedy vectors `g⁰¹ = (v10, v11 - v10)` and
       `g¹⁰ = (v11 - v01, v01)` belong to `B(f)`.
    2. Weak LP Duality: for EVERY `(b0, b1) ∈ B(f)` and EVERY `(x0, x1) ∈ ℤ²`,
       `x0 * b0 + x1 * b1 ≤ lovasz2 v10 v01 v11 x0 x1`.
    3. Strong Greedy Attainment: `g⁰¹` attains `lovasz2(x)` when `x1 ≤ x0`, and `g¹⁰` attains it when `x0 ≤ x1`.
    4. **Non-Submodular Base-Polytope Collapse**: When `(v10, v01, v11) = (1, 1, 3)` (`1 + 1 < 3`),
       `B(f)` is strictly empty (`∀ b0 b1, ¬ inBasePolytope2 1 1 3 b0 b1`). -/
theorem edmonds_polymatroid_greedy_extreme_points_vs_nonsubmodular_empty_base_polytope :
    (∀ v10 v01 v11 : Int, v11 ≤ v10 + v01 →
      inBasePolytope2 v10 v01 v11 v10 (v11 - v10) ∧
      inBasePolytope2 v10 v01 v11 (v11 - v01) v01) ∧
    (∀ v10 v01 v11 b0 b1 x0 x1 : Int,
      inBasePolytope2 v10 v01 v11 b0 b1 →
      x0 * b0 + x1 * b1 ≤ lovasz2 v10 v01 v11 x0 x1) ∧
    (∀ v10 v01 v11 x0 x1 : Int,
      (x1 ≤ x0 → x0 * v10 + x1 * (v11 - v10) = lovasz2 v10 v01 v11 x0 x1) ∧
      (x0 < x1 → x0 * (v11 - v01) + x1 * v01 = lovasz2 v10 v01 v11 x0 x1)) ∧
    (∀ b0 b1 : Int, ¬ inBasePolytope2 1 1 3 b0 b1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v10 v01 v11 hSub
    unfold inBasePolytope2
    omega
  · intro v10 v01 v11 b0 b1 x0 x1 hB
    rcases hB with ⟨hb0, hb1, hSum⟩
    unfold lovasz2
    by_cases hCmp : x1 ≤ x0
    · simp only [hCmp, ↓reduceIte]
      have hSlack : 0 ≤ (x0 - x1) * (v10 - b0) := Int.mul_nonneg (by omega) (by omega)
      have hId : ((x0 - x1) * v10 + x1 * (b0 + b1)) - (x0 * b0 + x1 * b1) =
          (x0 - x1) * (v10 - b0) := by grind
      rw [← hSum]
      omega
    · simp only [hCmp, ↓reduceIte]
      have hSlack : 0 ≤ (x1 - x0) * (v01 - b1) := Int.mul_nonneg (by omega) (by omega)
      have hId : ((x1 - x0) * v01 + x0 * (b0 + b1)) - (x0 * b0 + x1 * b1) =
          (x1 - x0) * (v01 - b1) := by grind
      rw [← hSum]
      omega
  · intro v10 v01 v11 x0 x1
    unfold lovasz2
    refine ⟨?_, ?_⟩
    · intro hLe
      simp only [hLe, ↓reduceIte]
      grind
    · intro hLt
      have hNotLe : ¬ (x1 ≤ x0) := by omega
      simp only [hNotLe, ↓reduceIte]
      grind
  · intro b0 b1 hB
    unfold inBasePolytope2 at hB
    omega

/-! ## 4. Nemhauser–Wolsey Submodular Greedy `(1 - (1 - 1/k)^k)` Contraction vs. Complement Stall -/

/-- Non-submodular monotone complement bundle valuation on `3` items `{0,1,2}` (`3`-bit mask):
    worth `10` iff BOTH `{0,1}` (`mask 3`) are present, else `0`. -/
def complementBundleVal (mask : Nat) : Int :=
  if (mask &&& 3) == 3 then 10 else 0

/-- **Theorem 4 (Nemhauser–Wolsey Submodular Greedy Contraction vs. Complement Zero-Marginal Stall)**:
    1. Universal `k`-step residual contraction: whenever `k ≥ 1` and greedy step `t + 1` captures at
       least `1/k` of the remaining optimal gap (`OPT - F_t ≤ k * (F_{t+1} - F_t)`), the residual gap
       contracts by `(k - 1)/k`: `k * (OPT - F_{t+1}) ≤ (k - 1) * (OPT - F_t)`.
    2. At cardinality `k = 2` (`F₀ = 0`), two greedy steps satisfy `4 * F₂ ≥ 3 * OPT` (`≥ 75%` of `OPT`).
    3. **Complement Synergy Stall**: For `complementBundleVal` (`OPT = f({0,1}) = 10`, non-submodular
       since `f({0}) + f({1}) = 0 < 10`), all three singletons `{0}, {1}, {2}` have identical zero
       marginal gain `0` at `∅`, and greedy tie-breaking `{2}` then `{0}` yields `F₂ = f({0,2}) = 0`
       (`4 * F₂ = 0 < 30 = 3 * OPT`). -/
theorem nemhauser_wolsey_submodular_greedy_contraction_vs_complement_zero_marginal_stall :
    (∀ k opt f_t f_next : Int,
      1 ≤ k → opt - f_t ≤ k * (f_next - f_t) →
      k * (opt - f_next) ≤ (k - 1) * (opt - f_t)) ∧
    (∀ opt f1 f2 : Int,
      opt ≤ 2 * f1 → opt - f1 ≤ 2 * (f2 - f1) →
      3 * opt ≤ 4 * f2) ∧
    (complementBundleVal 1 = 0 ∧ complementBundleVal 2 = 0 ∧ complementBundleVal 4 = 0 ∧
     complementBundleVal 3 = 10 ∧ complementBundleVal 5 = 0 ∧
     4 * complementBundleVal 5 < 3 * complementBundleVal 3) := by
  refine ⟨?_, ?_, ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩⟩
  · intro k opt f_t f_next hk hStep
    have hId : (k - 1) * (opt - f_t) - k * (opt - f_next) =
        k * (f_next - f_t) - (opt - f_t) := by grind
    omega
  · intro opt f1 f2 h1 h2
    omega

end CommonGround.Frontier.MatroidSubmodularLovasz
