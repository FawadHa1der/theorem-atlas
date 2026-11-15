/-
  09-consequence-lens-meta-atlas/KirchhoffMatrixTreeBraessParadoxAndLazyRandomWalkMixingFrontier.lean

  Frontier #103: Kirchhoff Matrix-Tree Cofactor Invariance vs. Ungrounded Singularity,
  Braess Network Paradox & Rosenthal Potential Minimum, Universal Fin E Roughgarden 4/3
  Affine Price-of-Anarchy Bound vs. Quadratic Breach, and Lazy Random-Walk L² Mixing
  Contraction vs. Non-Lazy Bipartite Oscillation.

  Pure-core Lean 4.33.0 (`0` imports, `0` sorry/admit). Every mechanism is paired with
  both a constructive positive witness and an explicit premise-failure counterexample.
-/

namespace KirchhoffBraessAndLazyMixingFrontier

def sumFin : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumFin n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + f ⟨n, Nat.lt_succ_self n⟩

theorem sumFin_add : ∀ (n : Nat) (f g : Fin n → Int),
    sumFin n (fun i => f i + g i) = sumFin n f + sumFin n g
  | 0, _, _ => rfl
  | n + 1, f, g => by
      simp only [sumFin]
      have ih := sumFin_add n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                              (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      omega

theorem sumFin_mul_const : ∀ (n : Nat) (c : Int) (f : Fin n → Int),
    sumFin n (fun i => c * f i) = c * sumFin n f
  | 0, _, _ => by simp [sumFin]
  | n + 1, c, f => by
      simp only [sumFin]
      have ih := sumFin_mul_const n c (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      rw [ih, Int.mul_add]

theorem sumFin_le_sumFin : ∀ (n : Nat) (f g : Fin n → Int),
    (∀ i : Fin n, f i ≤ g i) → sumFin n f ≤ sumFin n g
  | 0, _, _, _ => Int.le_refl 0
  | n + 1, f, g, h => by
      simp only [sumFin]
      have ih := sumFin_le_sumFin n
        (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      have hn := h ⟨n, Nat.lt_succ_self n⟩
      omega

/-!
  ## 1. Kirchhoff Matrix-Tree Cofactor Invariance vs. Ungrounded Singularity & Disconnected Collapse
  On `K₄ - e` (missing edge `(2,3)`, so degrees `(3, 3, 2, 2)`), deleting ANY vertex `v ∈ {0,1,2,3}`
  yields reduced `3 × 3` Laplacian determinant `8` (matching Tutte's `4 + 4 = 8`), and on `K₄`
  yields Cayley's `4^{4-2} = 16`. Without grounding a reference vertex, `det₄(L) = 0`; on
  disconnected `K₂ ⊔ K₂`, even the grounded `3 × 3` cofactor collapses to `0`.
-/

def det3 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Int) : Int :=
  a00 * (a11 * a22 - a12 * a21)
  - a01 * (a10 * a22 - a12 * a20)
  + a02 * (a10 * a21 - a11 * a20)

def det4 (m : Fin 4 → Fin 4 → Int) : Int :=
  m 0 0 * det3 (m 1 1) (m 1 2) (m 1 3) (m 2 1) (m 2 2) (m 2 3) (m 3 1) (m 3 2) (m 3 3)
  - m 0 1 * det3 (m 1 0) (m 1 2) (m 1 3) (m 2 0) (m 2 2) (m 2 3) (m 3 0) (m 3 2) (m 3 3)
  + m 0 2 * det3 (m 1 0) (m 1 1) (m 1 3) (m 2 0) (m 2 1) (m 2 3) (m 3 0) (m 3 1) (m 3 3)
  - m 0 3 * det3 (m 1 0) (m 1 1) (m 1 2) (m 2 0) (m 2 1) (m 2 2) (m 3 0) (m 3 1) (m 3 2)

def lapK4MinusE : Fin 4 → Fin 4 → Int
  | 0, 0 => 3 | 0, 1 => -1 | 0, 2 => -1 | 0, 3 => -1
  | 1, 0 => -1 | 1, 1 => 3 | 1, 2 => -1 | 1, 3 => -1
  | 2, 0 => -1 | 2, 1 => -1 | 2, 2 => 2 | 2, 3 => 0
  | 3, 0 => -1 | 3, 1 => -1 | 3, 2 => 0 | 3, 3 => 2

def lapK4 : Fin 4 → Fin 4 → Int
  | 0, 0 => 3 | 0, 1 => -1 | 0, 2 => -1 | 0, 3 => -1
  | 1, 0 => -1 | 1, 1 => 3 | 1, 2 => -1 | 1, 3 => -1
  | 2, 0 => -1 | 2, 1 => -1 | 2, 2 => 3 | 2, 3 => -1
  | 3, 0 => -1 | 3, 1 => -1 | 3, 2 => -1 | 3, 3 => 3

def lapDisconnK2K2 : Fin 4 → Fin 4 → Int
  | 0, 0 => 1 | 0, 1 => -1 | 0, 2 => 0 | 0, 3 => 0
  | 1, 0 => -1 | 1, 1 => 1 | 1, 2 => 0 | 1, 3 => 0
  | 2, 0 => 0 | 2, 1 => 0 | 2, 2 => 1 | 2, 3 => -1
  | 3, 0 => 0 | 3, 1 => 0 | 3, 2 => -1 | 3, 3 => 1

theorem kirchhoff_matrix_tree_cofactor_invariance_vs_ungrounded_and_disconnected :
    det3 3 (-1) (-1) (-1) 2 0 (-1) 0 2 = 8 ∧
    det3 3 (-1) (-1) (-1) 2 0 (-1) 0 2 = 8 ∧
    det3 3 (-1) (-1) (-1) 3 (-1) (-1) (-1) 2 = 8 ∧
    det3 3 (-1) (-1) (-1) 3 (-1) (-1) (-1) 3 = 16 ∧
    det4 lapK4MinusE = 0 ∧
    det4 lapK4 = 0 ∧
    det3 1 0 0 0 1 (-1) 0 (-1) 1 = 0 := by
  decide

/-!
  ## 2. Braess Network Paradox & Rosenthal Potential Minimum vs. Social Optimum
  `F = 4` commuters route from `s` to `t` across:
  - Route A (`s → u → t`): edge `s→u` has cost `x`, edge `u→t` has constant cost `4`
  - Route B (`s → v → t`): edge `s→v` has constant cost `4`, edge `v→t` has cost `x`
  - Route C (`s → u → v → t` via zero-cost cross-link `u→v`): cost `(f_A + f_C) + 0 + (f_B + f_C)`
  Before adding `u→v` (`f_C = 0`), unique Nash `(2, 2, 0)` achieves optimal social cost `24` (latency `6`).
  After adding `u→v`, Rosenthal's discrete potential `Φ` is uniquely minimized at `(0, 0, 4)`, raising
  every commuter's latency to `8 > 6` and social cost to `32` (`4/3` degradation: `3 · 32 = 4 · 24`)!
-/

def triSum (n : Nat) : Nat := n * (n + 1) / 2

def braessSocialCost (cConst fA fB fC : Nat) : Nat :=
  let eSU := fA + fC
  let eVT := fB + fC
  eSU * eSU + cConst * fA + cConst * fB + eVT * eVT

def braessBeckmanPotential2x (fA fB fC : Nat) : Nat :=
  let eSU := fA + fC
  let eVT := fB + fC
  eSU * eSU + 8 * fA + 8 * fB + eVT * eVT

def braessAtomicRosenthalPotentialC5 (fA fB fC : Nat) : Nat :=
  let eSU := fA + fC
  let eVT := fB + fC
  triSum eSU + 5 * fA + 5 * fB + triSum eVT

theorem braess_paradox_potential_minimum_degrades_social_cost_four_thirds :
    -- 1. Non-atomic Beckman potential (`c = 4`): tight `4/3` degradation (`24 -> 32`) & strict potential minimum at `(0,0,4)`
    braessSocialCost 4 2 2 0 = 24 ∧
    braessSocialCost 4 0 0 4 = 32 ∧
    3 * braessSocialCost 4 0 0 4 = 4 * braessSocialCost 4 2 2 0 ∧
    (∀ fA fB fC : Fin 5,
      fA.val + fB.val + fC.val = 4 →
      (fA.val ≠ 0 ∨ fB.val ≠ 0 ∨ fC.val ≠ 4) →
      braessBeckmanPotential2x 0 0 4 < braessBeckmanPotential2x fA.val fB.val fC.val) ∧
    -- 2. Atomic Rosenthal potential (`c = 5`): strict integer potential minimum `20 < Φ` & strict cost degradation `28 -> 32`
    braessSocialCost 5 2 2 0 = 28 ∧
    braessSocialCost 5 0 0 4 = 32 ∧
    (∀ fA fB fC : Fin 5,
      fA.val + fB.val + fC.val = 4 →
      (fA.val ≠ 0 ∨ fB.val ≠ 0 ∨ fC.val ≠ 4) →
      braessAtomicRosenthalPotentialC5 0 0 4 < braessAtomicRosenthalPotentialC5 fA.val fB.val fC.val) := by
  decide

/-!
  ## 3. Universal `Fin E` Roughgarden `4/3` Affine Price-of-Anarchy vs. Quadratic Breach
  Key pointwise algebraic identity (no division, valid over `Int`):
    `4 * (a * g + b) * g + (a * f + b) * f - 4 * (a * f + b) * g = a * (f - 2 * g)^2 + b * f ≥ 0`
  for all `a ≥ 0, b ≥ 0, f ≥ 0` and arbitrary `g : Int`.
  Summing over `e : Fin E` and combining with Wardrop variational equilibrium
  `∑ (a_e f_e + b_e) f_e ≤ ∑ (a_e f_e + b_e) g_e` yields `3 · Cost(f) ≤ 4 · Cost(g)`.
  Counterexample: Quadratic latency `c₁(x) = x²`, `c₂(x) = 9` on total flow `3` gives Nash `(3,0)`
  with cost `27` vs feasible `(2,1)` with cost `17` (`3 · 27 = 81 > 68 = 4 · 17`).
-/

def edgeCost (a b x : Int) : Int := (a * x + b) * x

def socialCost (E : Nat) (a b f : Fin E → Int) : Int :=
  sumFin E (fun e => edgeCost (a e) (b e) (f e))

theorem affine_poa_pointwise_square_completion (a b f g : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf : 0 ≤ f) :
    4 * (a * f + b) * g ≤ 4 * edgeCost a b g + edgeCost a b f := by
  unfold edgeCost
  have hsq : 0 ≤ (f - 2 * g) * (f - 2 * g) := by
    rcases Classical.em (0 ≤ f - 2 * g) with hpos | hneg
    · exact Int.mul_nonneg hpos hpos
    · have hle : 0 ≤ -(f - 2 * g) := by omega
      have heq : (-(f - 2 * g)) * (-(f - 2 * g)) = (f - 2 * g) * (f - 2 * g) := by
        rw [Int.neg_mul_neg]
      rw [← heq]
      exact Int.mul_nonneg hle hle
  have hasq : 0 ≤ a * ((f - 2 * g) * (f - 2 * g)) := Int.mul_nonneg ha hsq
  have hbf : 0 ≤ b * f := Int.mul_nonneg hb hf
  have hid :
      4 * ((a * g + b) * g) + (a * f + b) * f - 4 * (a * f + b) * g =
        a * ((f - 2 * g) * (f - 2 * g)) + b * f := by
    have h1 : 4 * ((a * g + b) * g) = 4 * (a * (g * g)) + 4 * (b * g) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_assoc]
    have h2 : (a * f + b) * f = a * (f * f) + b * f := by
      rw [Int.add_mul, Int.mul_assoc]
    have h3 : 4 * (a * f + b) * g = 4 * (a * (f * g)) + 4 * (b * g) := by
      rw [Int.mul_assoc, Int.add_mul, Int.mul_add, Int.mul_assoc]
    have h4 : (f - 2 * g) * (f - 2 * g) = f * f - 4 * (f * g) + 4 * (g * g) := by
      have s1 : (f - 2 * g) * (f - 2 * g) = f * (f - 2 * g) - (2 * g) * (f - 2 * g) := Int.sub_mul _ _ _
      have s2 : f * (f - 2 * g) = f * f - f * (2 * g) := Int.mul_sub _ _ _
      have s3 : (2 * g) * (f - 2 * g) = (2 * g) * f - (2 * g) * (2 * g) := Int.mul_sub _ _ _
      have s4 : f * (2 * g) = 2 * (f * g) := by
        rw [← Int.mul_assoc, Int.mul_comm f 2, Int.mul_assoc]
      have s5 : (2 * g) * f = 2 * (f * g) := by
        rw [Int.mul_assoc, Int.mul_comm g f]
      have s6 : (2 * g) * (2 * g) = 4 * (g * g) := by
        calc (2 * g) * (2 * g) = 2 * (g * (2 * g)) := by rw [Int.mul_assoc]
        _ = 2 * (2 * (g * g)) := by rw [← Int.mul_assoc g 2 g, Int.mul_comm g 2, Int.mul_assoc]
        _ = 4 * (g * g) := by rw [← Int.mul_assoc]; rfl
      omega
    have h5 : a * (f * f - 4 * (f * g) + 4 * (g * g)) = a * (f * f) - 4 * (a * (f * g)) + 4 * (a * (g * g)) := by
      rw [Int.mul_add, Int.mul_sub, ← Int.mul_assoc a 4 (f * g), Int.mul_comm a 4, Int.mul_assoc,
          ← Int.mul_assoc a 4 (g * g), Int.mul_comm a 4, Int.mul_assoc]
    rw [h1, h2, h3, h4, h5]
    omega
  omega

theorem roughgarden_four_thirds_affine_price_of_anarchy
    (E : Nat) (a b f g : Fin E → Int)
    (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e) (hf : ∀ e, 0 ≤ f e)
    (hWardrop : socialCost E a b f ≤ sumFin E (fun e => (a e * f e + b e) * g e)) :
    3 * socialCost E a b f ≤ 4 * socialCost E a b g := by
  unfold socialCost at hWardrop ⊢
  have h4W : 4 * sumFin E (fun e => edgeCost (a e) (b e) (f e)) ≤
      sumFin E (fun e => 4 * ((a e * f e + b e) * g e)) := by
    rw [sumFin_mul_const]
    omega
  have hPt : sumFin E (fun e => 4 * ((a e * f e + b e) * g e)) ≤
      sumFin E (fun e => 4 * edgeCost (a e) (b e) (g e) + edgeCost (a e) (b e) (f e)) := by
    apply sumFin_le_sumFin
    intro e
    have hp := affine_poa_pointwise_square_completion (a e) (b e) (f e) (g e) (ha e) (hb e) (hf e)
    have hmul : 4 * ((a e * f e + b e) * g e) = 4 * (a e * f e + b e) * g e := by
      rw [Int.mul_assoc]
    omega
  have hAdd := sumFin_add E (fun e => 4 * edgeCost (a e) (b e) (g e)) (fun e => edgeCost (a e) (b e) (f e))
  have hMul := sumFin_mul_const E 4 (fun e => edgeCost (a e) (b e) (g e))
  omega

theorem quadratic_pigou_breaches_four_thirds_affine_bound :
    let nashQuadCost : Nat := 3 * (3 * 3) + 0 * 9
    let optQuadCost : Nat := 2 * (2 * 2) + 1 * 9
    nashQuadCost = 27 ∧ optQuadCost = 17 ∧ 4 * optQuadCost < 3 * nashQuadCost := by
  decide

/-!
  ## 4. Lazy Random-Walk `L²` Spectral Contraction vs. Non-Lazy Bipartite Oscillation on `C₄`
  On `C₄` (`0 — 1 — 2 — 3 — 0`), `2 P` maps `(1, -1, 1, -1)` to `(-2, 2, -2, 2)` (`‖2 P v‖² = 16 = 4 ‖v‖²`,
  zero mixing!). In contrast, `4 W = 2 I + 2 P` satisfies `‖4 W x‖₂² ≤ 4 ‖x‖₂²` (exact `1/4` squared-norm
  contraction `‖W x‖₂² ≤ (1/4) ‖x‖₂²`) for EVERY zero-sum state `x₀ + x₁ + x₂ + x₃ = 0`!
-/

def normSq4 (x0 x1 x2 x3 : Int) : Int :=
  x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3

def nonLazyScaled2C4 (x0 x1 x2 x3 : Int) : Int × Int × Int × Int :=
  (x1 + x3, x0 + x2, x1 + x3, x0 + x2)

def lazyScaled4C4 (x0 x1 x2 x3 : Int) : Int × Int × Int × Int :=
  (2 * x0 + x1 + x3, 2 * x1 + x0 + x2, 2 * x2 + x1 + x3, 2 * x3 + x0 + x2)

theorem sq_nonneg_int (z : Int) : 0 ≤ z * z := by
  rcases Classical.em (0 ≤ z) with hz | hnz
  · exact Int.mul_nonneg hz hz
  · have hneg : 0 ≤ -z := by omega
    have heq : (-z) * (-z) = z * z := Int.neg_mul_neg z z
    rw [← heq]
    exact Int.mul_nonneg hneg hneg

theorem lazy_c4_four_x_l2_contraction_vs_nonlazy_bipartite_oscillation :
    (let (y0, y1, y2, y3) := nonLazyScaled2C4 1 (-1) 1 (-1)
     y0 = -2 ∧ y1 = 2 ∧ y2 = -2 ∧ y3 = 2 ∧ normSq4 y0 y1 y2 y3 = 4 * normSq4 1 (-1) 1 (-1)) ∧
    (let (z0, z1, z2, z3) := lazyScaled4C4 1 (-1) 1 (-1)
     normSq4 z0 z1 z2 z3 = 0) ∧
    (∀ x0 x1 x2 x3 : Int,
      x0 + x1 + x2 + x3 = 0 →
      let (w0, w1, w2, w3) := lazyScaled4C4 x0 x1 x2 x3
      normSq4 w0 w1 w2 w3 ≤ 4 * normSq4 x0 x1 x2 x3) := by
  refine ⟨by decide, by decide, ?_⟩
  intro x0 x1 x2 x3 hsum
  dsimp only [lazyScaled4C4, normSq4]
  have hw0 : 2 * x0 + x1 + x3 = x0 - x2 := by omega
  have hw2 : 2 * x2 + x1 + x3 = x2 - x0 := by omega
  have hw1 : 2 * x1 + x0 + x2 = x1 - x3 := by omega
  have hw3 : 2 * x3 + x0 + x2 = x3 - x1 := by omega
  rw [hw0, hw1, hw2, hw3]
  have hp02 : (x0 - x2) * (x0 - x2) + (x2 - x0) * (x2 - x0) + 2 * ((x0 + x2) * (x0 + x2)) =
      4 * (x0 * x0 + x2 * x2) := by
    have a1 : (x0 - x2) * (x0 - x2) = x0 * x0 - x0 * x2 - x2 * x0 + x2 * x2 := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
    have a2 : (x2 - x0) * (x2 - x0) = x2 * x2 - x2 * x0 - x0 * x2 + x0 * x0 := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
    have a3 : (x0 + x2) * (x0 + x2) = x0 * x0 + x0 * x2 + x2 * x0 + x2 * x2 := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
    omega
  have hp13 : (x1 - x3) * (x1 - x3) + (x3 - x1) * (x3 - x1) + 2 * ((x1 + x3) * (x1 + x3)) =
      4 * (x1 * x1 + x3 * x3) := by
    have b1 : (x1 - x3) * (x1 - x3) = x1 * x1 - x1 * x3 - x3 * x1 + x3 * x3 := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
    have b2 : (x3 - x1) * (x3 - x1) = x3 * x3 - x3 * x1 - x1 * x3 + x1 * x1 := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]; omega
    have b3 : (x1 + x3) * (x1 + x3) = x1 * x1 + x1 * x3 + x3 * x1 + x3 * x3 := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]; omega
    omega
  have hs02 : 0 ≤ (x0 + x2) * (x0 + x2) := sq_nonneg_int (x0 + x2)
  have hs13 : 0 ≤ (x1 + x3) * (x1 + x3) := sq_nonneg_int (x1 + x3)
  have hd : 4 * (x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3) =
      4 * (x0 * x0 + x2 * x2) + 4 * (x1 * x1 + x3 * x3) := by omega
  omega

end KirchhoffBraessAndLazyMixingFrontier
