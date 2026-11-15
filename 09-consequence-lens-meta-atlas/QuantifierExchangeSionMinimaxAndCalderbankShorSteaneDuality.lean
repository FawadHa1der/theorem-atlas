/-
Copyright (c) 2026 Common Ground Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Quantifier Exchange (Sion / von Neumann Minimax), Calderbank–Shor–Steane `[[7, 1, 3]]` Symplectic Self-Duality, and Doeblin–Birkhoff Positive-Cone Contraction

This standalone zero-sorry pure-core Lean 4.33.0 module (`0` imports) unifies three pillars of
Folder `09` (`09-consequence-lens-meta-atlas`):

1. **Universal Bilinear Fubini Saddle-Value Locking vs. Pure-Strategy Matching-Pennies Duality Gap**:
   For any `m × n` integer payoff matrix `A` (`1 ≤ m, n`) and any nonnegative mixed-strategy weight
   vectors `p` (`∑_{i<m} p_i = P > 0`) and `q` (`∑_{j<n} q_j = Q > 0`), if `p` guarantees column
   floor `∀ j < n, P * u ≤ ∑_{i<m} p_i A_{i,j}` and `q` enforces row cap
   `∀ i < m, ∑_{j<n} A_{i,j} q_j ≤ Q * v`, then Fubini double-sum exchange forces
   `(P * Q) * u ≤ (P * Q) * v`, hence `u ≤ v` (and exact saddle uniqueness `u = v` whenever mutual
   best responses meet). By contrast, without convex randomization, pure quantifier exchange on
   `2 × 2` Matching Pennies exhibits a strict gap `max_i min_j MP_{i,j} = -1 < +1 = min_j max_i MP_{i,j}`,
   closed to `0 = 0` by the uniform mixture `p = q = (1, 1)`.

2. **Calderbank–Shor–Steane `[[7, 1, 3]]` Steane Quantum Code Symplectic Commutativity & Distance 3**:
   Exhaustively verified across all `2^7 = 128` 7-bit error configurations in Lean 4's kernel:
   - The `[7, 4, 3]` Hamming parity-check matrix `H₇` (`3 × 7` over `𝔽₂`) satisfies exact
     symplectic self-orthogonality `H₇ H₇ᵀ ≡ 0 (mod 2)` across all `9` row pairs, certifying that
     every `X`-type and `Z`-type CSS stabilizer generator commutes;
   - Every nonzero kernel vector `e ∈ ker(H₇) \ {0}` has Hamming weight `wt₇(e) ≥ 3` (`d = 3`), and
     the `3`-bit syndrome map is nonzero and strictly injective on all `7` single-qubit errors;
   - Replacing even-weight `4`-ones parity rows with the odd-weight `3`-bit check `[1, 1, 1]`
     violates symplectic self-orthogonality (`(1 + 1 + 1) % 2 = 1 ≠ 0`), causing `X₁X₂X₃` and
     `Z₁Z₂Z₃` to anticommute.

3. **Doeblin–Birkhoff Strict Positive-Matrix Markov Contraction vs. Boundary Swap Oscillation**:
   For any `2 × 2` column-stochastic matrix `[[a, b], [c, d]]` (`a + c = S`, `b + d = S`) with
   uniform positive Doeblin floor `a, b, c, d ≥ μ > 0`, acting on any two equal-mass distributions
   `x₁ + y₁ = x₂ + y₂` strictly contracts `ℓ¹` separation:
   `|X₁ - X₂| = |a - b| · |x₁ - x₂| ≤ (S - 2μ) · |x₁ - x₂| < S · |x₁ - x₂|` whenever `x₁ ≠ x₂`.
   At the boundary `μ = 0`, the swap permutation `[[0, 1], [1, 0]]` has `|a - b| = 1 = S`,
   preserving separation without contraction (`|0 - 1| = |1 - 0| = 1`) in a period-2 cycle.
-/

namespace CommonGround.Frontier.ConsequenceMetaAtlas

/-! ## Section 1: Pure-Core Finite Sums & Bilinear Fubini Saddle-Value Locking -/

/-- Pure-core finite sum `∑_{k=0}^{n-1} f(k)`. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

theorem sumRange_zero (n : Nat) : sumRange n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp [sumRange, ih]

theorem sumRange_add (n : Nat) (f g : Nat → Int) :
    sumRange n (fun k => f k + g k) = sumRange n f + sumRange n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [sumRange, ih]
      omega

theorem sumRange_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    c * sumRange n f = sumRange n (fun k => c * f k) := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
      simp only [sumRange, Int.mul_add, ih]

theorem sumRange_mul_right (n : Nat) (f : Nat → Int) (c : Int) :
    sumRange n f * c = sumRange n (fun k => f k * c) := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih =>
      simp only [sumRange, Int.add_mul, ih]

theorem sumRange_congr (n : Nat) (f g : Nat → Int)
    (h : ∀ k, k < n → f k = g k) :
    sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have ih' : sumRange k f = sumRange k g := ih (fun i hi => h i (by omega))
      have hk : f k = g k := h k (by omega)
      simp [sumRange, ih', hk]

theorem sumRange_mono (n : Nat) (f g : Nat → Int)
    (h : ∀ k, k < n → f k ≤ g k) :
    sumRange n f ≤ sumRange n g := by
  induction n with
  | zero =>
      simp [sumRange]
  | succ k ih =>
      have ih' : sumRange k f ≤ sumRange k g := ih (fun i hi => h i (by omega))
      have hk : f k ≤ g k := h k (by omega)
      simp only [sumRange]
      omega

/-- Discrete Fubini theorem: exchanging finite row and column summation order. -/
theorem sumRange_comm (m n : Nat) (g : Nat → Nat → Int) :
    sumRange m (fun i => sumRange n (fun j => g i j)) =
      sumRange n (fun j => sumRange m (fun i => g i j)) := by
  induction m with
  | zero =>
      simp [sumRange, sumRange_zero]
  | succ k ih =>
      simp only [sumRange, ih]
      exact (sumRange_add n (fun j => sumRange k (fun i => g i j)) (fun j => g k j)).symm

/-- Cancellation of a strictly positive integer multiplier across `≤`. -/
theorem le_of_pos_mul_le (K x y : Int) (hK : 0 < K) (h : K * x ≤ K * y) :
    x ≤ y := by
  by_cases hxy : x ≤ y
  · exact hxy
  · have hdiff : 0 < x - y := by omega
    have hpos : 0 < K * (x - y) := Int.mul_pos hK hdiff
    rw [Int.mul_sub] at hpos
    omega

/-- `2 × 2` Matching Pennies payoff matrix `[[+1, -1], [-1, +1]]`. -/
def matchingPennies (i j : Nat) : Int :=
  if i % 2 == j % 2 then 1 else -1

/-- Pure-strategy row worst-case payoff `min(A_{i,0}, A_{i,1})` on `2 × 2` games. -/
def rowMin2 (A : Nat → Nat → Int) (i : Nat) : Int :=
  if A i 0 ≤ A i 1 then A i 0 else A i 1

/-- Pure-strategy column worst-case payoff `max(A_{0,j}, A_{1,j})` on `2 × 2` games. -/
def colMax2 (A : Nat → Nat → Int) (j : Nat) : Int :=
  if A 0 j ≤ A 1 j then A 1 j else A 0 j

/-- Pure maximin `max_{i<2} min_{j<2} A_{i,j}`. -/
def pureMaximin2 (A : Nat → Nat → Int) : Int :=
  if rowMin2 A 0 ≤ rowMin2 A 1 then rowMin2 A 1 else rowMin2 A 0

/-- Pure minimax `min_{j<2} max_{i<2} A_{i,j}`. -/
def pureMinimax2 (A : Nat → Nat → Int) : Int :=
  if colMax2 A 0 ≤ colMax2 A 1 then colMax2 A 0 else colMax2 A 1

/--
**Theorem 1 (Universal Bilinear Fubini Saddle-Value Locking vs. Pure Matching-Pennies Gap)**:
1. (*Mixed-Strategy Saddle Locking*): For any `m × n` payoff matrix `A`, positive total weights
   `P = ∑_{i<m} p_i > 0`, `Q = ∑_{j<n} q_j > 0` (`p_i, q_j ≥ 0`), column floor
   `∀ j < n, P * u ≤ ∑_{i<m} p_i A_{i,j}`, and row cap `∀ i < m, ∑_{j<n} A_{i,j} q_j ≤ Q * v`,
   Fubini exchange forces `(P * Q) * u ≤ (P * Q) * v` and hence `u ≤ v`.
2. (*Non-Convex Pure-Strategy Quantifier Gap*): On `2 × 2` Matching Pennies, pure quantifier
   reversal has a strict gap `pureMaximin2 = -1 < +1 = pureMinimax2`, whereas the uniform mixture
   `p = q = (1, 1)` (`P = Q = 2`) achieves exact saddle equality `0 = 0` across every row and column.
-/
theorem weak_minimax_quantifier_order_and_saddle_uniqueness_vs_matching_pennies_gap :
    (∀ (m n : Nat) (A : Nat → Nat → Int) (p q : Nat → Int) (P Q u v : Int),
      0 < P →
      0 < Q →
      sumRange m p = P →
      sumRange n q = Q →
      (∀ i, i < m → 0 ≤ p i) →
      (∀ j, j < n → 0 ≤ q j) →
      (∀ j, j < n → P * u ≤ sumRange m (fun i => p i * A i j)) →
      (∀ i, i < m → sumRange n (fun j => A i j * q j) ≤ Q * v) →
      u ≤ v) ∧
    (pureMaximin2 matchingPennies = -1 ∧
     pureMinimax2 matchingPennies = 1 ∧
     pureMaximin2 matchingPennies < pureMinimax2 matchingPennies ∧
     (∀ j, j < 2 → sumRange 2 (fun i => 1 * matchingPennies i j) = 0) ∧
     (∀ i, i < 2 → sumRange 2 (fun j => matchingPennies i j * 1) = 0)) := by
  refine ⟨?_, ?_⟩
  · intro m n A p q P Q u v hP hQ hSumP hSumQ hpNonneg hqNonneg hFloor hCap
    have hLow : (P * Q) * u ≤ sumRange n (fun j => sumRange m (fun i => (p i * A i j) * q j)) := by
      have hStep1 :
          sumRange n (fun j => (P * u) * q j) ≤
            sumRange n (fun j => sumRange m (fun i => p i * A i j) * q j) := by
        apply sumRange_mono
        intro j hj
        exact Int.mul_le_mul_of_nonneg_right (hFloor j hj) (hqNonneg j hj)
      have hLHS : sumRange n (fun j => (P * u) * q j) = (P * Q) * u := by
        rw [← sumRange_mul_left n (P * u) q, hSumQ]
        rw [Int.mul_assoc, Int.mul_comm u Q, ← Int.mul_assoc]
      have hRHS :
          sumRange n (fun j => sumRange m (fun i => p i * A i j) * q j) =
            sumRange n (fun j => sumRange m (fun i => (p i * A i j) * q j)) := by
        apply sumRange_congr
        intro j _
        exact sumRange_mul_right m (fun i => p i * A i j) (q j)
      rw [hLHS, hRHS] at hStep1
      exact hStep1
    have hHigh : sumRange m (fun i => sumRange n (fun j => p i * (A i j * q j))) ≤ (P * Q) * v := by
      have hStep2 :
          sumRange m (fun i => p i * sumRange n (fun j => A i j * q j)) ≤
            sumRange m (fun i => p i * (Q * v)) := by
        apply sumRange_mono
        intro i hi
        exact Int.mul_le_mul_of_nonneg_left (hCap i hi) (hpNonneg i hi)
      have hLHS2 :
          sumRange m (fun i => p i * sumRange n (fun j => A i j * q j)) =
            sumRange m (fun i => sumRange n (fun j => p i * (A i j * q j))) := by
        apply sumRange_congr
        intro i _
        exact sumRange_mul_left n (p i) (fun j => A i j * q j)
      have hRHS2 : sumRange m (fun i => p i * (Q * v)) = (P * Q) * v := by
        rw [← sumRange_mul_right m p (Q * v), hSumP, Int.mul_assoc]
      rw [hLHS2, hRHS2] at hStep2
      exact hStep2
    have hBilinEq :
        sumRange n (fun j => sumRange m (fun i => (p i * A i j) * q j)) =
          sumRange m (fun i => sumRange n (fun j => p i * (A i j * q j))) := by
      rw [← sumRange_comm m n (fun i j => (p i * A i j) * q j)]
      apply sumRange_congr
      intro i _
      apply sumRange_congr
      intro j _
      exact Int.mul_assoc (p i) (A i j) (q j)
    have hPQ : 0 < P * Q := Int.mul_pos hP hQ
    have hComb : (P * Q) * u ≤ (P * Q) * v := by
      rw [hBilinEq] at hLow
      omega
    exact le_of_pos_mul_le (P * Q) u v hPQ hComb
  · refine ⟨by decide, by decide, by decide, ?_, ?_⟩
    · intro j hj
      match j with
      | 0 => decide
      | 1 => decide
      | k + 2 => omega
    · intro i hi
      match i with
      | 0 => decide
      | 1 => decide
      | k + 2 => omega

/-! ## Section 2: Calderbank–Shor–Steane `[[7, 1, 3]]` Symplectic Self-Duality & Distance 3 -/

/-- Extract bit `j` (`0..6`) of a `7`-bit vector `e ∈ Fin 128`. -/
def bit7 (e : Fin 128) (j : Fin 7) : Nat :=
  (e.val >>> j.val) &&& 1

/-- `[7, 4, 3]` Hamming parity-check matrix `H₇`: column `j` encodes `j + 1` (`1..7`) in binary. -/
def hammingH7 (r : Fin 3) (j : Fin 7) : Nat :=
  ((j.val + 1) >>> r.val) &&& 1

/-- Symplectic `𝔽₂` inner product between row `r₁` (`X`-stabilizer) and row `r₂` (`Z`-stabilizer). -/
def hammingRowSymplecticMod2 (r₁ r₂ : Fin 3) : Nat :=
  (hammingH7 r₁ ⟨0, by decide⟩ * hammingH7 r₂ ⟨0, by decide⟩ +
   hammingH7 r₁ ⟨1, by decide⟩ * hammingH7 r₂ ⟨1, by decide⟩ +
   hammingH7 r₁ ⟨2, by decide⟩ * hammingH7 r₂ ⟨2, by decide⟩ +
   hammingH7 r₁ ⟨3, by decide⟩ * hammingH7 r₂ ⟨3, by decide⟩ +
   hammingH7 r₁ ⟨4, by decide⟩ * hammingH7 r₂ ⟨4, by decide⟩ +
   hammingH7 r₁ ⟨5, by decide⟩ * hammingH7 r₂ ⟨5, by decide⟩ +
   hammingH7 r₁ ⟨6, by decide⟩ * hammingH7 r₂ ⟨6, by decide⟩) % 2

/-- Single parity-check row evaluation mod `2` on `e ∈ Fin 128`. -/
def synRow7 (e : Fin 128) (r : Fin 3) : Nat :=
  (bit7 e ⟨0, by decide⟩ * hammingH7 r ⟨0, by decide⟩ +
   bit7 e ⟨1, by decide⟩ * hammingH7 r ⟨1, by decide⟩ +
   bit7 e ⟨2, by decide⟩ * hammingH7 r ⟨2, by decide⟩ +
   bit7 e ⟨3, by decide⟩ * hammingH7 r ⟨3, by decide⟩ +
   bit7 e ⟨4, by decide⟩ * hammingH7 r ⟨4, by decide⟩ +
   bit7 e ⟨5, by decide⟩ * hammingH7 r ⟨5, by decide⟩ +
   bit7 e ⟨6, by decide⟩ * hammingH7 r ⟨6, by decide⟩) % 2

/-- `3`-bit syndrome `(s₀, s₁, s₂)` of a `7`-qubit error pattern `e ∈ Fin 128`. -/
def syndrome7 (e : Fin 128) : Nat × Nat × Nat :=
  (synRow7 e ⟨0, by decide⟩, synRow7 e ⟨1, by decide⟩, synRow7 e ⟨2, by decide⟩)

/-- Hamming weight `wt₇(e)` of `e ∈ Fin 128`. -/
def wt7 (e : Fin 128) : Nat :=
  bit7 e ⟨0, by decide⟩ + bit7 e ⟨1, by decide⟩ + bit7 e ⟨2, by decide⟩ +
  bit7 e ⟨3, by decide⟩ + bit7 e ⟨4, by decide⟩ + bit7 e ⟨5, by decide⟩ +
  bit7 e ⟨6, by decide⟩

/-- Weight-`1` single-qubit error pattern at qubit `i ∈ Fin 7`. -/
def singleBit7 : Fin 7 → Fin 128
  | ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩ => ⟨2, by decide⟩
  | ⟨2, _⟩ => ⟨4, by decide⟩
  | ⟨3, _⟩ => ⟨8, by decide⟩
  | ⟨4, _⟩ => ⟨16, by decide⟩
  | ⟨5, _⟩ => ⟨32, by decide⟩
  | ⟨6, _⟩ => ⟨64, by decide⟩

/-- Odd-weight `3`-qubit check `r_odd = [1, 1, 1]` symplectic self-overlap mod `2`. -/
def oddParity3SymplecticMod2 : Nat :=
  (1 * 1 + 1 * 1 + 1 * 1) % 2

/--
**Theorem 2 (Steane `[[7, 1, 3]]` CSS Symplectic Self-Orthogonality & Distance 3 vs. Odd-Parity Failure)**:
1. (*Symplectic Commutativity*): All `9` pairs `(r₁, r₂) ∈ Fin 3 × Fin 3` satisfy
   `hammingRowSymplecticMod2 r₁ r₂ = 0`, certifying `H₇ H₇ᵀ ≡ 0 (mod 2)` so all CSS `X` and `Z`
   stabilizers commute.
2. (*Exact Quantum Distance `d = 3` & Single-Qubit Syndrome Injectivity*): Every nonzero syndrome-zero
   vector `e ∈ ker(H₇) \ {0}` has `3 ≤ wt7 e`, there exists a weight-`3` codeword (`e = 7 = 0b0000111`),
   and `syndrome7` maps the `7` single-qubit errors injectively onto the `7` nonzero `3`-bit syndromes.
3. (*Odd-Parity Premise Failure*): Replacing `4`-ones even rows with `r_odd = [1, 1, 1]` yields
   `oddParity3SymplecticMod2 = 1 ≠ 0`, so `X₁X₂X₃` and `Z₁Z₂Z₃` anticommute!
-/
theorem steane_seven_qubit_css_symplectic_commutativity_and_distance_three_vs_odd_parity_failure :
    (∀ r₁ r₂ : Fin 3, hammingRowSymplecticMod2 r₁ r₂ = 0) ∧
    (∀ e : Fin 128, e.val ≠ 0 → syndrome7 e = (0, 0, 0) → 3 ≤ wt7 e) ∧
    (syndrome7 ⟨7, by decide⟩ = (0, 0, 0) ∧ wt7 ⟨7, by decide⟩ = 3) ∧
    (∀ i : Fin 7, syndrome7 (singleBit7 i) ≠ (0, 0, 0)) ∧
    (∀ i j : Fin 7, syndrome7 (singleBit7 i) = syndrome7 (singleBit7 j) → i = j) ∧
    (oddParity3SymplecticMod2 = 1 ∧ oddParity3SymplecticMod2 ≠ 0) := by
  decide

/-! ## Section 3: Doeblin–Birkhoff Positive-Matrix Contraction vs. Swap Permutation Cycle -/

/-- Pure-core integer absolute value `|z|`. -/
def absInt (z : Int) : Int :=
  if 0 ≤ z then z else -z

/-- `2 × 2` linear operator `M = [[a, b], [c, d]]` acting on `(x, y) ∈ ℤ²`. -/
def matAct2 (a b c d : Int) (p : Int × Int) : Int × Int :=
  (a * p.1 + b * p.2, c * p.1 + d * p.2)

/-- `ℓ¹` total-variation distance `|p₁ - q₁| + |p₂ - q₂|` on `ℤ²`. -/
def tvDist2 (p q : Int × Int) : Int :=
  absInt (p.1 - q.1) + absInt (p.2 - q.2)

/--
**Theorem 3 (Doeblin–Birkhoff Strict Positive-Matrix Contraction vs. Boundary Swap Oscillation)**:
1. (*Strict Doeblin–Birkhoff Contraction*): Whenever `a, b, c, d ≥ μ > 0` with equal column sums
   `a + c = S` and `b + d = S`, for any two distributions `p = (x₁, y₁)` and `q = (x₂, y₂)` of
   equal total mass `x₁ + y₁ = x₂ + y₂`:
   - `matAct2` scales total mass by `S`,
   - `tvDist2 (Mp) (Mq) = absInt (a - b) * tvDist2 p q`,
   - `absInt (a - b) ≤ S - 2 * μ < S`, hence `tvDist2 (Mp) (Mq) < S * tvDist2 p q` whenever `p ≠ q`!
2. (*Boundary Permutation Failure at `μ = 0`*): The swap matrix `[[0, 1], [1, 0]]` (`S = 1, μ = 0`)
   satisfies `tvDist2 (Swap (1, 0)) (Swap (0, 1)) = 2 = 1 * tvDist2 (1, 0) (0, 1)` and oscillates
   `(1, 0) ↔ (0, 1)` without ever contracting!
-/
theorem birkhoff_positive_matrix_contraction_vs_permuting_swap_oscillation :
    (∀ (a b c d μ S x₁ y₁ x₂ y₂ : Int),
      0 < μ →
      μ ≤ a → μ ≤ b → μ ≤ c → μ ≤ d →
      a + c = S →
      b + d = S →
      x₁ + y₁ = x₂ + y₂ →
      let p := (x₁, y₁)
      let q := (x₂, y₂)
      let mp := matAct2 a b c d p
      let mq := matAct2 a b c d q
      mp.1 + mp.2 = S * (x₁ + y₁) ∧
      absInt (a - b) ≤ S - 2 * μ ∧
      S - 2 * μ < S ∧
      tvDist2 mp mq ≤ (S - 2 * μ) * tvDist2 p q ∧
      ((x₁ ≠ x₂) → tvDist2 mp mq < S * tvDist2 p q)) ∧
    (matAct2 0 1 1 0 (1, 0) = (0, 1) ∧
     matAct2 0 1 1 0 (0, 1) = (1, 0) ∧
     tvDist2 (matAct2 0 1 1 0 (1, 0)) (matAct2 0 1 1 0 (0, 1)) =
       1 * tvDist2 (1, 0) (0, 1)) := by
  refine ⟨?_, by decide⟩
  intro a b c d μ S x₁ y₁ x₂ y₂ hμ ha hb hc hd hCol1 hCol2 hMass
  dsimp [matAct2, tvDist2]
  have hMass1 : a * x₁ + b * y₁ + (c * x₁ + d * y₁) = S * (x₁ + y₁) := by
    have h1 : a * x₁ + b * y₁ + (c * x₁ + d * y₁) = (a + c) * x₁ + (b + d) * y₁ := by
      rw [Int.add_mul, Int.add_mul]
      omega
    rw [h1, hCol1, hCol2, Int.mul_add]
  have hy : y₁ - y₂ = -(x₁ - x₂) := by omega
  have hDiff1 : (a * x₁ + b * y₁) - (a * x₂ + b * y₂) = (a - b) * (x₁ - x₂) := by
    have hSub :
        (a * x₁ + b * y₁) - (a * x₂ + b * y₂) = a * (x₁ - x₂) + b * (y₁ - y₂) := by
      rw [Int.mul_sub, Int.mul_sub]
      omega
    rw [hSub, hy, Int.mul_neg, Int.sub_mul]
    omega
  have hcd : c - d = -(a - b) := by omega
  have hDiff2 : (c * x₁ + d * y₁) - (c * x₂ + d * y₂) = -(a - b) * (x₁ - x₂) := by
    have hSub :
        (c * x₁ + d * y₁) - (c * x₂ + d * y₂) = c * (x₁ - x₂) + d * (y₁ - y₂) := by
      rw [Int.mul_sub, Int.mul_sub]
      omega
    rw [hSub, hy, Int.mul_neg]
    have hSub2 : c * (x₁ - x₂) + -(d * (x₁ - x₂)) = (c - d) * (x₁ - x₂) := by
      rw [Int.sub_mul]
      omega
    rw [hSub2, hcd]
  have habBound : absInt (a - b) ≤ S - 2 * μ := by
    unfold absInt
    split <;> omega
  have hAbsMul : ∀ u v : Int, absInt (u * v) = absInt u * absInt v := by
    intro u v
    unfold absInt
    by_cases hu : 0 ≤ u <;> by_cases hv : 0 ≤ v
    · have huv : 0 ≤ u * v := Int.mul_nonneg hu hv
      simp [hu, hv, huv]
    · have hv' : 0 ≤ -v := by omega
      have huv' : 0 ≤ u * (-v) := Int.mul_nonneg hu hv'
      rw [Int.mul_neg] at huv'
      by_cases h0 : u * v = 0
      · simp only [if_pos hu, if_neg hv, h0]
        rw [Int.mul_neg, h0]
        rfl
      · have hneg : ¬ (0 ≤ u * v) := by omega
        simp [hu, hv, hneg, Int.mul_neg]
    · have hu' : 0 ≤ -u := by omega
      have huv' : 0 ≤ (-u) * v := Int.mul_nonneg hu' hv
      rw [Int.neg_mul] at huv'
      by_cases h0 : u * v = 0
      · simp only [if_neg hu, if_pos hv, h0]
        rw [Int.neg_mul, h0]
        rfl
      · have hneg : ¬ (0 ≤ u * v) := by omega
        simp [hu, hv, hneg, Int.neg_mul]
    · have hu' : 0 ≤ -u := by omega
      have hv' : 0 ≤ -v := by omega
      have huv : 0 ≤ (-u) * (-v) := Int.mul_nonneg hu' hv'
      rw [Int.neg_mul_neg] at huv
      simp [hu, hv, huv, Int.neg_mul_neg]
  have hAbsNeg : ∀ z : Int, absInt (-z) = absInt z := by
    intro z
    unfold absInt
    split <;> split <;> omega
  have hTVp : absInt (x₁ - x₂) + absInt (y₁ - y₂) = 2 * absInt (x₁ - x₂) := by
    rw [hy, hAbsNeg]
    omega
  have hTVmp :
      absInt ((a * x₁ + b * y₁) - (a * x₂ + b * y₂)) +
        absInt ((c * x₁ + d * y₁) - (c * x₂ + d * y₂)) =
      absInt (a - b) * (absInt (x₁ - x₂) + absInt (y₁ - y₂)) := by
    rw [hDiff1, hDiff2, Int.neg_mul, hAbsNeg, hAbsMul, hy, hAbsNeg, Int.mul_add]
  have hTVNonneg : 0 ≤ absInt (x₁ - x₂) + absInt (y₁ - y₂) := by
    unfold absInt
    split <;> split <;> omega
  have hContrLe :
      absInt ((a * x₁ + b * y₁) - (a * x₂ + b * y₂)) +
        absInt ((c * x₁ + d * y₁) - (c * x₂ + d * y₂)) ≤
      (S - 2 * μ) * (absInt (x₁ - x₂) + absInt (y₁ - y₂)) := by
    rw [hTVmp]
    exact Int.mul_le_mul_of_nonneg_right habBound hTVNonneg
  refine ⟨hMass1, habBound, by omega, hContrLe, ?_⟩
  intro hNe
  have hTVPos : 0 < absInt (x₁ - x₂) + absInt (y₁ - y₂) := by
    rw [hTVp]
    unfold absInt
    split <;> omega
  have hStrictGap :
      (S - 2 * μ) * (absInt (x₁ - x₂) + absInt (y₁ - y₂)) <
        S * (absInt (x₁ - x₂) + absInt (y₁ - y₂)) := by
    have hPosProd : 0 < (2 * μ) * (absInt (x₁ - x₂) + absInt (y₁ - y₂)) :=
      Int.mul_pos (by omega) hTVPos
    rw [Int.sub_mul]
    omega
  omega

end CommonGround.Frontier.ConsequenceMetaAtlas
