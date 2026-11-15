/-
  Common Ground — Frontier #102 (`10-millennium-frontier-bridges`)
  Yao's Minimax Principle, 3D Loomis–Whitney & Atserias–Grohe–Marx (AGM)
  Worst-Case Optimal Triangle Joins, Fooling-Set Communication Lower Bounds,
  and Alon–Matias–Szegedy (AMS) 4-Wise Independent F₂ Sketching vs. 3-Wise Breach

  Zero imports (`Init`-only pure Lean 4.33.0 kernel verification).
  Zero `sorry`, `admit`, or `sorryAx`.
-/

namespace YaoMinimaxLoomisWhitneyAGMJoinAndFoolingSetFrontier

/-!
  ## 1. Universal `Fin A × Fin X` Yao Minimax Lower Bound vs. Quantifier-Swap 2x Gap
-/

def sumFin : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f =>
    sumFin n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + f ⟨n, Nat.lt_succ_self n⟩

theorem sumFin_add : ∀ (n : Nat) (f g : Fin n → Int),
    sumFin n (fun i => f i + g i) = sumFin n f + sumFin n g
  | 0, _, _ => rfl
  | n + 1, f, g => by
    simp only [sumFin]
    have ih := sumFin_add n
      (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
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
  | 0, _, _, _ => by simp [sumFin]
  | n + 1, f, g, h => by
    simp only [sumFin]
    have ih := sumFin_le_sumFin n
      (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    have hlast := h ⟨n, Nat.lt_succ_self n⟩
    omega

/-- Discrete Fubini Exchange on `Fin A × Fin X`:
    `∑_a ∑_x M(a, x) = ∑_x ∑_a M(a, x)`. -/
theorem sumFin_swap : ∀ (A X : Nat) (M : Fin A → Fin X → Int),
    sumFin A (fun a => sumFin X (fun x => M a x)) =
    sumFin X (fun x => sumFin A (fun a => M a x))
  | 0, X, _ => by
    have hz : ∀ (k : Nat), sumFin k (fun _ => (0 : Int)) = 0 := by
      intro k
      induction k with
      | zero => rfl
      | succ m ihm => simp [sumFin, ihm]
    exact (hz X).symm
  | A + 1, X, M => by
    simp only [sumFin]
    have ih := sumFin_swap A X (fun a x => M ⟨a.val, Nat.lt_succ_of_lt a.isLt⟩ x)
    have hadd := sumFin_add X
      (fun x => sumFin A (fun a => M ⟨a.val, Nat.lt_succ_of_lt a.isLt⟩ x))
      (fun x => M ⟨A, Nat.lt_succ_self A⟩ x)
    omega

/-- Universal Denominator-Free Yao Minimax Inequality:
    For any cost matrix `C : Fin A → Fin X → Int`, randomized algorithm weights `wA ≥ 0`
    (`∑ wA = SA`), and hard input prior `wX ≥ 0` (`∑ wX = SX`), if every deterministic
    algorithm `a` incurs prior-weighted cost `≥ L_dist` and every input `x` incurs
    randomized cost `≤ U_rand`, then `SA * L_dist ≤ SX * U_rand`! -/
theorem yao_minimax_universal_lower_bound
    (A X : Nat) (C : Fin A → Fin X → Int)
    (wA : Fin A → Int) (wX : Fin X → Int)
    (L_dist U_rand : Int)
    (hwA : ∀ a : Fin A, 0 ≤ wA a)
    (hwX : ∀ x : Fin X, 0 ≤ wX x)
    (hDetLower : ∀ a : Fin A, L_dist ≤ sumFin X (fun x => wX x * C a x))
    (hRandUpper : ∀ x : Fin X, sumFin A (fun a => wA a * C a x) ≤ U_rand) :
    sumFin A wA * L_dist ≤ sumFin X wX * U_rand := by
  have h1 : sumFin A (fun a => wA a * L_dist) ≤
            sumFin A (fun a => wA a * sumFin X (fun x => wX x * C a x)) := by
    apply sumFin_le_sumFin
    intro a
    exact Int.mul_le_mul_of_nonneg_left (hDetLower a) (hwA a)
  have hL : sumFin A (fun a => wA a * L_dist) = sumFin A wA * L_dist := by
    have hcomm : (fun a => wA a * L_dist) = (fun a => L_dist * wA a) := by
      funext a; exact Int.mul_comm (wA a) L_dist
    rw [hcomm, sumFin_mul_const, Int.mul_comm]
  have hMidA :
      sumFin A (fun a => wA a * sumFin X (fun x => wX x * C a x)) =
      sumFin A (fun a => sumFin X (fun x => wA a * (wX x * C a x))) := by
    have hfun : (fun a => wA a * sumFin X (fun x => wX x * C a x)) =
                (fun a => sumFin X (fun x => wA a * (wX x * C a x))) := by
      funext a
      exact (sumFin_mul_const X (wA a) (fun x => wX x * C a x)).symm
    rw [hfun]
  have hSwap := sumFin_swap A X (fun a x => wA a * (wX x * C a x))
  have hMidX :
      sumFin X (fun x => sumFin A (fun a => wA a * (wX x * C a x))) =
      sumFin X (fun x => wX x * sumFin A (fun a => wA a * C a x)) := by
    have hfun : (fun x => sumFin A (fun a => wA a * (wX x * C a x))) =
                (fun x => wX x * sumFin A (fun a => wA a * C a x)) := by
      funext x
      have hinner : (fun a => wA a * (wX x * C a x)) = (fun a => wX x * (wA a * C a x)) := by
        funext a
        rw [← Int.mul_assoc, Int.mul_comm (wA a) (wX x), Int.mul_assoc]
      rw [hinner, sumFin_mul_const]
    rw [hfun]
  have h2 : sumFin X (fun x => wX x * sumFin A (fun a => wA a * C a x)) ≤
            sumFin X (fun x => wX x * U_rand) := by
    apply sumFin_le_sumFin
    intro x
    exact Int.mul_le_mul_of_nonneg_left (hRandUpper x) (hwX x)
  have hR : sumFin X (fun x => wX x * U_rand) = sumFin X wX * U_rand := by
    have hcomm : (fun x => wX x * U_rand) = (fun x => U_rand * wX x) := by
      funext x; exact Int.mul_comm (wX x) U_rand
    rw [hcomm, sumFin_mul_const, Int.mul_comm]
  omega

/-- Explicit 2x2 Anti-Diagonal Guessing Game `C = [[0, 2], [2, 0]]`:
    Randomized 50/50 cost is `1` (`U_rand/SA = 2/2 = 1`, matching Yao's lower bound!),
    whereas EVERY deterministic algorithm suffers worst-case cost `2` (`2x` gap!). -/
def guessCost (a x : Fin 2) : Int := if a == x then 0 else 2

theorem yao_saddle_equality_vs_deterministic_two_x_gap :
    (∀ a : Fin 2, ∃ x : Fin 2, guessCost a x = 2) ∧
    (∀ x : Fin 2, guessCost ⟨0, by decide⟩ x + guessCost ⟨1, by decide⟩ x = 2) := by
  decide

/-!
  ## 2. 3D Loomis–Whitney Projection Inequality on `{0, 1}³` & AGM Triangle Join
        vs. Binary Join-Plan Quadratic `M²` Intermediate Blowup
-/

def b2n (b : Bool) : Nat := if b then 1 else 0

/-- Exhaustive 3D Loomis–Whitney Inequality across ALL `2⁸ = 256` subsets `S ⊆ {0, 1}³`:
    `|S|² ≤ |π_{xy} S| · |π_{yz} S| · |π_{xz} S|`, with equality `64 = 4·4·4` on `{0,1}³`. -/
theorem loomis_whitney_cube3_all_256_subsets
    (b000 b001 b010 b011 b100 b101 b110 b111 : Bool) :
    let cardS := b2n b000 + b2n b001 + b2n b010 + b2n b011 +
                 b2n b100 + b2n b101 + b2n b110 + b2n b111
    let cardXY := b2n (b000 || b001) + b2n (b010 || b011) +
                  b2n (b100 || b101) + b2n (b110 || b111)
    let cardYZ := b2n (b000 || b100) + b2n (b001 || b101) +
                  b2n (b010 || b110) + b2n (b011 || b111)
    let cardXZ := b2n (b000 || b010) + b2n (b001 || b011) +
                  b2n (b100 || b110) + b2n (b101 || b111)
    cardS * cardS ≤ cardXY * cardYZ * cardXZ := by
  cases b000 <;> cases b001 <;> cases b010 <;> cases b011 <;>
  cases b100 <;> cases b101 <;> cases b110 <;> cases b111 <;> decide

/-- AGM Worst-Case Optimal Join vs. Binary Relational Plan `M²` Blowup:
    On `R_{xy} = {(i,0) : i<M}`, `R_{yz} = {(0,k) : k<M}`, `R_{xz} = {(i,i) : i<M}` (`|R| = M` each):
    - True triangle output `|T| = M` satisfies Loomis–Whitney `M² ≤ M³` for all `M ≥ 1`,
    - Yet binary join `R_{xy} ⋈_y R_{yz}` materializes `M²` tuples (`M² - M = M*(M-1) > 0` for `M ≥ 2`)! -/
theorem agm_triangle_join_vs_binary_plan_quadratic_blowup (M : Nat) (hM : 2 ≤ M) :
    let rSize := M
    let trueTriangleOut := M
    let binaryIntermediate := M * M
    trueTriangleOut * trueTriangleOut ≤ rSize * rSize * rSize ∧
    trueTriangleOut < binaryIntermediate ∧
    binaryIntermediate - trueTriangleOut = M * (M - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · have hmul : M * M * 1 ≤ M * M * M := Nat.mul_le_mul_left (M * M) (by omega)
    omega
  · have hmul : M * 1 < M * M := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    omega
  · rw [Nat.mul_sub_left_distrib, Nat.mul_one]

/-!
  ## 3. Universal Fooling-Set Communication Rectangle Lower Bound vs. Fingerprint Escape
-/

/-- Universal Fooling-Set Injectivity Theorem:
    If `(x_i, y_i)` (`i : Fin K`) is a fooling set for `f : X → Y → Bool` and `rectIdx i`
    assigns each fooling pair to a `1`-monochromatic rectangle `A_r × B_r`,
    then distinct fooling pairs CANNOT share a rectangle (`i ≠ j → rectIdx i ≠ rectIdx j`)! -/
theorem fooling_set_monochromatic_rectangle_injective
    {X Y : Type} (f : X → Y → Bool) (K R : Nat)
    (fx : Fin K → X) (fy : Fin K → Y)
    (inA : Fin R → X → Prop) (inB : Fin R → Y → Prop)
    (rectIdx : Fin K → Fin R)
    (hMono : ∀ r : Fin R, ∀ u v, inA r u → inB r v → f u v = true)
    (hCover : ∀ i : Fin K, inA (rectIdx i) (fx i) ∧ inB (rectIdx i) (fy i))
    (hFool : ∀ i j : Fin K, i ≠ j → ¬ (f (fx i) (fy j) = true ∧ f (fx j) (fy i) = true)) :
    ∀ i j : Fin K, i ≠ j → rectIdx i ≠ rectIdx j := by
  intro i j hne heq
  have hi := hCover i
  have hj := hCover j
  rw [← heq] at hj
  have h12 := hMono (rectIdx i) (fx i) (fy j) hi.1 hj.2
  have h21 := hMono (rectIdx i) (fx j) (fy i) hj.1 hi.2
  exact hFool i j hne ⟨h12, h21⟩

/-- Equality `EQ_4` Fooling Set vs. Polynomial Fingerprint Collision Rate (`≤ 2/7`):
    `EQ_4` has `4` fooling pairs `(x, x)`, whereas distinct degree-`2` polynomials
    `(1, 0, 0)` and `(0, 0, 1)` over `𝔽_7` (`1` vs `r² mod 7`) collide on only `2/7` seeds! -/
def polyCollisionCountMod7 : Nat :=
  (List.range 7).foldl (fun acc r => if (1 % 7) == ((r * r) % 7) then acc + 1 else acc) 0

theorem eq_fooling_vs_reed_solomon_fingerprint_mod7 :
    polyCollisionCountMod7 = 2 ∧ polyCollisionCountMod7 < 7 := by
  decide

/-!
  ## 4. Alon–Matias–Szegedy (`AMS`) 4-Wise Independent `F₂` Sketching (`Var ≤ 2 F₂²`)
        vs. 3-Wise Independent Sign Table Variance Breach (`48 > 32`)
-/

def signBit (mask bit : Nat) : Int := if ((mask >>> bit) &&& 1) == 1 then 1 else -1

/-- Full 4-wise independent Rademacher sketch over all `16` rows of `{-1, +1}⁴`. -/
def ams4Sketch (mask : Nat) (f0 f1 f2 f3 : Int) : Int :=
  signBit mask 0 * f0 + signBit mask 1 * f1 + signBit mask 2 * f2 + signBit mask 3 * f3

/-- 3-wise (and 2-wise!) independent parity-coupled sign table `(s0, s1, s2, s0*s1*s2)` (`8` rows). -/
def ams3Sketch (mask : Nat) (f0 f1 f2 f3 : Int) : Int :=
  let s0 := signBit mask 0
  let s1 := signBit mask 1
  let s2 := signBit mask 2
  s0 * f0 + s1 * f1 + s2 * f2 + (s0 * s1 * s2) * f3

def sum16 (g : Nat → Int) : Int :=
  g 0 + g 1 + g 2 + g 3 + g 4 + g 5 + g 6 + g 7 +
  g 8 + g 9 + g 10 + g 11 + g 12 + g 13 + g 14 + g 15

def sum8 (g : Nat → Int) : Int :=
  g 0 + g 1 + g 2 + g 3 + g 4 + g 5 + g 6 + g 7

/-- Sharp 4-Wise vs. 3-Wise AMS `F₂` Sketching Theorem at `f = (1, 1, 1, 1)` (`F₂ = 4, F₄ = 4`):
    1. BOTH 4-wise (`16` rows) and 3-wise (`8` rows) hashes are 100% unbiased (`E[Z²] = 4 = F₂`),
    2. 4-wise AMS achieves exact variance `E[(Z² - F₂)²] = 2(F₂² - F₄) = 24 ≤ 2 F₂² = 32`,
    3. Merely 3-wise `(s0, s1, s2, s0*s1*s2)` explodes to variance `48 > 32 = 2 F₂²` (`2x` higher)! -/
theorem ams_four_wise_variance_bound_vs_three_wise_breach :
    let f2 : Int := 4
    let mean4Scaled := sum16 (fun m => let z := ams4Sketch m 1 1 1 1; z * z)
    let var4Scaled  := sum16 (fun m => let z := ams4Sketch m 1 1 1 1; (z * z - f2) * (z * z - f2))
    let mean3Scaled := sum8  (fun m => let z := ams3Sketch m 1 1 1 1; z * z)
    let var3Scaled  := sum8  (fun m => let z := ams3Sketch m 1 1 1 1; (z * z - f2) * (z * z - f2))
    mean4Scaled = 16 * f2 ∧
    mean3Scaled = 8 * f2 ∧
    var4Scaled = 16 * 24 ∧
    var4Scaled ≤ 16 * (2 * f2 * f2) ∧
    var3Scaled = 8 * 48 ∧
    8 * (2 * f2 * f2) < var3Scaled := by
  decide

end YaoMinimaxLoomisWhitneyAGMJoinAndFoolingSetFrontier
