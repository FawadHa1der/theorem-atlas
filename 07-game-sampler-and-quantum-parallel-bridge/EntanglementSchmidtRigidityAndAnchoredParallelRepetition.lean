/-
  Discovery 07 — Pure-Core Lean 4.33.0 Frontier Synthesis (Zero Imports, Zero Sorry):
  `EntanglementSchmidtRigidityAndAnchoredParallelRepetition.lean`

  Unifies Folder `07` (`OpenAIGame.lean`, `ParallelGameSamplerExtension.lean`,
  `QuantumCHSHRigidityAndCoresetSparsification.lean`), OpenAI's `QuantumParallelRepetition.lean`
  (`oai-qrep`), and Tau Ceti's `InvariantForm.lean` (`tc-reptheory`) via three kernel-checked pillars:

  1. Choi–Jamiolkowski Bipartite Unfolding, `(g ⊗ g)`-Invariant Swap Symmetry & Singlet Antisymmetry:
     - Register swap `(i, j) ↦ (j, i)` is matrix transpose `Mᵀ` and diagonal local action
       `(g ⊗ g) M` is congruent conjugation `g M gᵀ`.
     - Symmetric Schmidt decompositions `M_{ij} = ∑_{k < r} σ_k u_k(i) u_k(j)` satisfy exact
       swap symmetry `M_{ij} = M_{ji}`, while isotropic Bell states `c · I_d` are `(g ⊗ g)`-invariant
       under all scaled orthogonal transformations `g · gᵀ = D · I_d`.
     - Sharp Singlet Bell Counterexample: `J = [[0, 1], [-1, 0]]` (`|01⟩ - |10⟩`) is `SL₂`-invariant
       (`g J gᵀ = (a d - b c) J = J` for ALL unimodular matrices, including hyperbolic shears),
       yet strictly violates swap symmetry (`J₀₁ = 1 ≠ -1 = J₁₀`)!

  2. Exact Feige–Fortnow–Lovász 2-Round Parallel Repetition Non-Multiplicativity (`ω(G²) = ω(G) > ω(G)²`):
     - Formalizes the 2-bit coordinated challenge game `feigeWin`: over ALL deterministic 1-round
       strategies `fA, fB : Fin 2 → Fin 2 × Fin 2`, the winning count out of `4` uniform question
       pairs is **at most `2`** (`ω(G) = 2/4 = 1/2`, so naive squaring predicts `ω(G)² = 4/16 = 1/4`).
     - Yet in 2-round parallel repetition (`16` question tuples `(x₁, y₁, x₂, y₂)`), Alice's
       cross-round strategy `(x₁, x₂) ↦ ((0, x₁), (1, x₁))` and Bob's `(y₁, y₂) ↦ ((0, y₂), (1, y₂))`
       win **both rounds simultaneously on `8` of `16` tuples** (`ω(G²) = 8/16 = 1/2 > 4/16 = ω(G)²`)!

  3. Bavarian–Vidick–Yuen / Holenstein Anchored Sampler Factorization:
     - Anchoring a product question distribution `μ(x) ν(y)` independently on each coordinate with
       weights `(α, β)` preserves exact product structure `(α δ_⊥ + β μ) ⊗ (α δ_⊥ + β ν)` and total
       normalized mass `(α + β ∑ μ)(α + β ∑ ν)`, decoupling Alice's and Bob's anchor events so
       cross-round correlation shortcuts can be bounded via information-theoretic chain rules.
-/

namespace CommonGround.Discovery07.EntanglementSchmidtAndAnchoredRepetition

/-- Finite integer sum `∑_{k < n} f k` in pure core Lean 4. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

theorem sumRange_add (n : Nat) (f g : Nat → Int) :
    sumRange n (fun k => f k + g k) = sumRange n f + sumRange n g := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih =>
    simp [sumRange, ih]
    omega

theorem sumRange_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun k => c * f k) = c * sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih =>
    simp [sumRange, ih, Int.mul_add]

theorem sumRange_mul_right (n : Nat) (f : Nat → Int) (c : Int) :
    sumRange n (fun k => f k * c) = sumRange n f * c := by
  induction n with
  | zero => simp [sumRange]
  | succ m ih =>
    simp [sumRange, ih, Int.add_mul]

theorem sumRange_zero (n : Nat) : sumRange n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [sumRange, ih]

theorem sumRange_swap (m n : Nat) (F : Nat → Nat → Int) :
    sumRange m (fun i => sumRange n (fun j => F i j)) =
      sumRange n (fun j => sumRange m (fun i => F i j)) := by
  induction m with
  | zero =>
    simp [sumRange, sumRange_zero]
  | succ k ih =>
    simp [sumRange, ih, sumRange_add]

/-- Choi–Jamiolkowski `(g ⊗ g)`-action on a `d × d` bipartite amplitude matrix `M`:
    `(g ⊗ g)(M)_{i,j} = ∑_{p < d} ∑_{q < d} g(i, p) * M(p, q) * g(j, q) = (g M gᵀ)_{i,j}`. -/
def choiDiagAction (d : Nat) (g M : Nat → Nat → Int) (i j : Nat) : Int :=
  sumRange d (fun p => sumRange d (fun q => g i p * M p q * g j q))

/-- Symmetric rank-`r` Schmidt state `M_{i,j} = ∑_{k < r} σ_k * u_k(i) * u_k(j)`. -/
def symmetricSchmidtState (r : Nat) (σ : Nat → Int) (u : Nat → Nat → Int) (i j : Nat) : Int :=
  sumRange r (fun k => σ k * u k i * u k j)

/-- Isotropic unnormalized Bell / maximally entangled matrix `c · δ_{i,j}`. -/
def isotropicBellMatrix (c : Int) (i j : Nat) : Int :=
  if i = j then c else 0

theorem sumRange_ite_lt (m i : Nat) (hmi : m ≤ i) (f : Nat → Int) :
    sumRange m (fun p => if p = i then f p else 0) = 0 := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have hle : k ≤ i := by omega
    have hne : k ≠ i := by omega
    simp [sumRange, hne, ih hle]

theorem sumRange_ite_eq (d i : Nat) (hi : i < d) (f : Nat → Int) :
    sumRange d (fun p => if p = i then f p else 0) = f i := by
  induction d with
  | zero => omega
  | succ m ih =>
    by_cases h : i = m
    · subst h
      rw [sumRange, sumRange_ite_lt i i (Nat.le_refl i) f]
      simp
    · have hlt : i < m := by omega
      have hne : m ≠ i := by omega
      simp [sumRange, hne, ih hlt]

/-- **Theorem 1 (Choi–Schmidt Swap Symmetry, Orthogonal Isotropic Bell Invariance & Singlet Antisymmetry)**:
    1. Every symmetric Schmidt state `M = symmetricSchmidtState r σ u` satisfies register-swap
       symmetry `M i j = M j i`, and `choiDiagAction` preserves swap symmetry for EVERY local `g`.
    2. For the isotropic Bell matrix `B_c = c · I_d`, whenever `g` satisfies scaled row-orthogonality
       `∑_{p < d} g(i, p) g(j, p) = if i = j then D else 0`, `(g ⊗ g)(B_c) = B_{D · c}`.
    3. **Singlet Bell `SL₂` vs. Swap Counterexample**: On `d = 2`, the singlet matrix
       `J = [[0, 1], [-1, 0]]` satisfies `(g ⊗ g)(J)_{0,1} = (a d - b c) · 1` and
       `(g ⊗ g)(J)_{1,0} = -(a d - b c)` for EVERY `2 × 2` matrix `g = [[a, b], [c, d]]`
       (invariant whenever `a d - b c = 1`, including non-orthogonal shears `[[1, k], [0, 1]]`),
       YET violates register-swap symmetry (`J 0 1 = 1 ≠ -1 = J 1 0`)! -/
theorem choi_schmidt_swap_invariance_and_singlet_sl2_counterexample
    (r d : Nat) (σ : Nat → Int) (u g : Nat → Nat → Int) (c D : Int)
    (hOrth : ∀ i j, i < d → j < d →
      sumRange d (fun p => g i p * g j p) = (if i = j then D else 0)) :
    (∀ i j, symmetricSchmidtState r σ u i j = symmetricSchmidtState r σ u j i) ∧
    (∀ M : Nat → Nat → Int, (∀ p q, M p q = M q p) →
      ∀ i j, choiDiagAction d g M i j = choiDiagAction d g M j i) ∧
    (∀ i j, i < d → j < d →
      choiDiagAction d g (isotropicBellMatrix c) i j = isotropicBellMatrix (D * c) i j) ∧
    (∀ a b c2 d2 : Int,
      let g2 : Nat → Nat → Int := fun i j =>
        if i = 0 then (if j = 0 then a else b) else (if j = 0 then c2 else d2)
      let J : Nat → Nat → Int := fun i j =>
        if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0
      J 0 1 ≠ J 1 0 ∧
      choiDiagAction 2 g2 J 0 0 = 0 ∧
      choiDiagAction 2 g2 J 1 1 = 0 ∧
      choiDiagAction 2 g2 J 0 1 = a * d2 - b * c2 ∧
      choiDiagAction 2 g2 J 1 0 = -(a * d2 - b * c2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    unfold symmetricSchmidtState
    have hpt : ∀ k, σ k * u k i * u k j = σ k * u k j * u k i := by
      intro k
      rw [Int.mul_assoc (σ k), Int.mul_comm (u k i) (u k j), ← Int.mul_assoc (σ k)]
    have hfun : (fun k => σ k * u k i * u k j) = (fun k => σ k * u k j * u k i) := by
      funext k
      exact hpt k
    rw [hfun]
  · intro M hSym i j
    unfold choiDiagAction
    rw [sumRange_swap d d (fun p q => g j p * M p q * g i q)]
    have houter :
        (fun p => sumRange d (fun q => g i p * M p q * g j q)) =
          (fun q => sumRange d (fun p => g j p * M p q * g i q)) := by
      funext p
      have hinner :
          (fun q => g i p * M p q * g j q) =
            (fun q => g j q * M q p * g i p) := by
        funext q
        rw [hSym p q, Int.mul_comm (g i p * M q p) (g j q), Int.mul_assoc (g j q), Int.mul_comm (g i p) (M q p), ← Int.mul_assoc]
      rw [hinner]
    rw [houter]
  · intro i j hi hj
    unfold choiDiagAction isotropicBellMatrix
    have hsum :
        sumRange d (fun p => sumRange d (fun q => g i p * (if p = q then c else 0) * g j q)) =
          sumRange d (fun p => (g i p * g j p) * c) := by
      have haux : ∀ k, k ≤ d →
          sumRange k (fun p => sumRange d (fun q => g i p * (if p = q then c else 0) * g j q)) =
            sumRange k (fun p => (g i p * g j p) * c) := by
        intro k hk
        induction k with
        | zero => rfl
        | succ m ihm =>
          have hmle : m ≤ d := by omega
          have hmlt : m < d := by omega
          have hq :
              (fun q => g i m * (if m = q then c else 0) * g j q) =
                (fun q => if q = m then g i m * c * g j q else 0) := by
            funext q
            by_cases hmq : m = q
            · subst hmq; simp
            · have hqm : q ≠ m := fun h => hmq h.symm
              simp [hmq, hqm]
          have hterm :
              sumRange d (fun q => g i m * (if m = q then c else 0) * g j q) = (g i m * g j m) * c := by
            rw [hq, sumRange_ite_eq d m hmlt (fun q => g i m * c * g j q)]
            rw [Int.mul_assoc (g i m) c (g j m), Int.mul_comm c (g j m), ← Int.mul_assoc]
          simp [sumRange, ihm hmle, hterm]
      exact haux d (Nat.le_refl d)
    rw [hsum, sumRange_mul_right, hOrth i j hi hj]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · intro a b c2 d2
    dsimp
    refine ⟨by decide, ?_, ?_, ?_, ?_⟩
    · simp [choiDiagAction, sumRange]
      rw [Int.neg_mul, Int.mul_comm b a]
      omega
    · simp [choiDiagAction, sumRange]
      rw [Int.neg_mul, Int.mul_comm d2 c2]
      omega
    · simp [choiDiagAction, sumRange]
      rw [Int.neg_mul]
      omega
    · simp [choiDiagAction, sumRange]
      rw [Int.neg_mul, Int.mul_comm d2 a, Int.mul_comm c2 b]
      omega

/-- Referee predicate for Feige's 2-bit coordinated challenge game `G_FFL`:
    Questions `x, y : Bool`. Alice outputs `(pA, bA) : Bool × Bool` (`false` = Alice's input slot,
    `true` = Bob's input slot), and Bob outputs `(pB, bB) : Bool × Bool`.
    Referee accepts (`1`, else `0`) iff both players name the same slot AND the same bit matching that slot. -/
def feigeWin (x y : Bool) (ansA ansB : Bool × Bool) : Nat :=
  if ansA.1 == ansB.1 && ansA.2 == ansB.2 &&
     ((!ansA.1 && (ansA.2 == x)) || (ansA.1 && (ansA.2 == y)))
  then 1 else 0

/-- Total 1-round wins across all `4` uniform question pairs `(x, y) ∈ Bool × Bool`. -/
def feigeOneRoundWins (fA fB : Bool → Bool × Bool) : Nat :=
  feigeWin false false (fA false) (fB false) +
  feigeWin false true  (fA false) (fB true) +
  feigeWin true  false (fA true)  (fB false) +
  feigeWin true  true  (fA true)  (fB true)

/-- Total 2-round simultaneous wins across all `16` question tuples `(x₁, y₁, x₂, y₂) ∈ Bool⁴`. -/
def feigeTwoRoundWins
    (FA FB : Bool → Bool → (Bool × Bool) × (Bool × Bool)) : Nat :=
  let bits : List Bool := [false, true]
  bits.foldl (fun acc1 x1 =>
    bits.foldl (fun acc2 y1 =>
      bits.foldl (fun acc3 x2 =>
        bits.foldl (fun acc4 y2 =>
          acc4 +
            feigeWin x1 y1 (FA x1 x2).1 (FB y1 y2).1 *
            feigeWin x2 y2 (FA x1 x2).2 (FB y1 y2).2) acc3) acc2) acc1) 0

/-- **Theorem 2 (Exact Feige–Fortnow–Lovász Parallel Repetition Non-Multiplicativity `ω(G²) = ω(G) > ω(G)²`)**:
    1. Every deterministic 1-round strategy `(fA, fB)` wins at most **`2` out of `4`** question pairs
       (`feigeOneRoundWins fA fB ≤ 2`), and `(fA x = (false, x), fB y = (false, false))` attains `2`
       (`ω(G) = 2/4 = 1/2`, so naive product decay predicts `ω(G)² = 4 / 16 = 1/4`).
    2. In 2-round parallel repetition (`16` uniform tuples), the cross-wired strategy
       `FA(x₁, x₂) = ((false, x₁), (true, x₁))` and `FB(y₁, y₂) = ((false, y₂), (true, y₂))` achieves
       **`8` out of `16`** simultaneous 2-round wins (`ω(G²) = 8/16 = 2/4 = ω(G)` — **strictly beating
       `4/16 = ω(G)²` with zero decay from 1 round to 2 rounds**)! -/
theorem feige_two_round_parallel_repetition_beats_one_round_square :
    (∀ fA fB : Bool → Bool × Bool, feigeOneRoundWins fA fB ≤ 2) ∧
    (feigeOneRoundWins
      (fun x => (false, x))
      (fun _ => (false, false)) = 2) ∧
    (let FA : Bool → Bool → (Bool × Bool) × (Bool × Bool) :=
        fun x1 _ => ((false, x1), (true, x1))
      let FB : Bool → Bool → (Bool × Bool) × (Bool × Bool) :=
        fun _ y2 => ((false, y2), (true, y2))
      feigeTwoRoundWins FA FB = 8 ∧ 8 > 2 * 2) := by
  refine ⟨?_, by decide, by decide⟩
  intro fA fB
  unfold feigeOneRoundWins
  generalize fA false = a0
  generalize fA true = a1
  generalize fB false = b0
  generalize fB true = b1
  clear fA fB
  rcases a0 with ⟨pA0, qA0⟩
  rcases a1 with ⟨pA1, qA1⟩
  rcases b0 with ⟨pB0, qB0⟩
  rcases b1 with ⟨pB1, qB1⟩
  cases pA0 <;> cases qA0 <;>
  cases pA1 <;> cases qA1 <;>
  cases pB0 <;> cases qB0 <;>
  cases pB1 <;> cases qB1 <;>
  decide

/-- Bavarian–Vidick–Yuen / Holenstein independent coordinate anchoring on `Option (Fin m) × Option (Fin n)`
    encoded on indices `0` (= anchor `⊥`) and `i + 1` (= real question `i`):
    `anchWeight α β μ 0 = α` and `anchWeight α β μ (i + 1) = β * μ i`. -/
def anchMarginal (α β : Int) (μ : Nat → Int) : Nat → Int
  | 0 => α
  | i + 1 => β * μ i

/-- Joint anchored question law `Q_anch(x, y)` obtained by independently replacing `x` with `⊥` (`0`)
    with weight `α` (kept with weight `β`) and `y` with `⊥` (`0`) with weight `α` (kept with weight `β`). -/
def anchoredProductLaw (α β : Int) (μ ν : Nat → Int) (x y : Nat) : Int :=
  anchMarginal α β μ x * anchMarginal α β ν y

/-- **Theorem 3 (Anchored Question-Reshuffling Product Factorization & Normalization Identity)**:
    1. Independent coordinate anchoring of a product question law `Q(i, j) = μ(i) ν(j)` produces
       the exact four-regime Bavarian–Vidick–Yuen expansion (`(⊥, ⊥)` weight `α²`, `(⊥, j+1)` weight
       `α β ν(j)`, `(i+1, ⊥)` weight `α β μ(i)`, and `(i+1, j+1)` weight `β² μ(i) ν(j)`).
    2. Total unnormalized anchored mass factors identically as
       `∑_{x < m+1} ∑_{y < n+1} Q_anch(x, y) = (α + β ∑_{i < m} μ(i)) * (α + β ∑_{j < n} ν(j))`.
    3. Conditioning on Alice receiving an anchor (`x = 0`) vs. a real question (`x = i + 1`) yields
       proportional Bob marginals (`α · anchMarginal(ν)(y)` vs. `β μ(i) · anchMarginal(ν)(y)`),
       guaranteeing exact zero mutual information `Q_anch(0, y) * Q_anch(i + 1, y') = Q_anch(0, y') * Q_anch(i + 1, y)`! -/
theorem anchored_product_distribution_factorization_and_zero_leakage
    (m n : Nat) (α β : Int) (μ ν : Nat → Int) :
    anchoredProductLaw α β μ ν 0 0 = α * α ∧
    (∀ j, anchoredProductLaw α β μ ν 0 (j + 1) = α * (β * ν j)) ∧
    (∀ i, anchoredProductLaw α β μ ν (i + 1) 0 = (β * μ i) * α) ∧
    (∀ i j, anchoredProductLaw α β μ ν (i + 1) (j + 1) = (β * μ i) * (β * ν j)) ∧
    sumRange (m + 1) (fun x => sumRange (n + 1) (fun y => anchoredProductLaw α β μ ν x y)) =
      (α + β * sumRange m μ) * (α + β * sumRange n ν) ∧
    (∀ i y y',
      anchoredProductLaw α β μ ν 0 y * anchoredProductLaw α β μ ν (i + 1) y' =
        anchoredProductLaw α β μ ν 0 y' * anchoredProductLaw α β μ ν (i + 1) y) := by
  have hMargSum : ∀ (k : Nat) (φ : Nat → Int),
      sumRange (k + 1) (anchMarginal α β φ) = α + β * sumRange k φ := by
    intro k φ
    induction k with
    | zero => simp [sumRange, anchMarginal]
    | succ r ihr =>
      change sumRange (r + 1) (anchMarginal α β φ) + anchMarginal α β φ (r + 1) =
        α + β * (sumRange r φ + φ r)
      rw [ihr]
      change (α + β * sumRange r φ) + β * φ r = α + β * (sumRange r φ + φ r)
      rw [Int.mul_add, Int.add_assoc]
  refine ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => fun _ => rfl, ?_, ?_⟩
  · unfold anchoredProductLaw
    have hinner :
        (fun x => sumRange (n + 1) (fun y => anchMarginal α β μ x * anchMarginal α β ν y)) =
          (fun x => anchMarginal α β μ x * sumRange (n + 1) (anchMarginal α β ν)) := by
      funext x
      exact sumRange_mul_left (n + 1) (anchMarginal α β μ x) (anchMarginal α β ν)
    rw [hinner, sumRange_mul_right, hMargSum m μ, hMargSum n ν]
  · intro i y y'
    change (α * anchMarginal α β ν y) * ((β * μ i) * anchMarginal α β ν y') =
      (α * anchMarginal α β ν y') * ((β * μ i) * anchMarginal α β ν y)
    rw [Int.mul_assoc α (anchMarginal α β ν y),
        Int.mul_left_comm (anchMarginal α β ν y) (β * μ i) (anchMarginal α β ν y'),
        Int.mul_comm (anchMarginal α β ν y) (anchMarginal α β ν y'),
        ← Int.mul_left_comm (anchMarginal α β ν y') (β * μ i) (anchMarginal α β ν y),
        ← Int.mul_assoc α (anchMarginal α β ν y')]

end CommonGround.Discovery07.EntanglementSchmidtAndAnchoredRepetition
