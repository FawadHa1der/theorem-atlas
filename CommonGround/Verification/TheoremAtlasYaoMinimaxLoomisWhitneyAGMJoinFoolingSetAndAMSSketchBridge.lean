/-
  Common Ground — Verification Suite #628 (`CommonGround/Verification`)
  Cross-Domain Bridge: Count-Min Sketch One-Sided Bound vs. Turnstile Underestimation,
  Karchmer–Wigderson Monotone Formula Separation vs. XOR Failure, Spectral Triangle
  Trace (`tr(A³) = 6·T`) vs. Self-Loop/Directed Distortion, Prime Pairwise-Uniform
  Hashing vs. Composite-Modulus 2x Collision, and Idempotent MinHash Mergeability

  Zero imports (`Init`-only pure Lean 4.33.0 kernel verification).
  Zero `sorry`, `admit`, or `sorryAx`.
-/

namespace CommonGround.Verification.TheoremAtlasYaoMinimaxLoomisWhitneyAGMJoinFoolingSetAndAMSSketchBridge

/-!
  ## 1. Count-Min Sketch Non-Negative Point-Query Bound vs. Signed Turnstile Underestimate
-/

def sumFin : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f =>
    sumFin n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + f ⟨n, Nat.lt_succ_self n⟩

theorem sumFin_nonneg : ∀ (n : Nat) (f : Fin n → Int),
    (∀ i : Fin n, 0 ≤ f i) → 0 ≤ sumFin n f
  | 0, _, _ => by simp [sumFin]
  | n + 1, f, h => by
    simp only [sumFin]
    have ih := sumFin_nonneg n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    have hlast := h ⟨n, Nat.lt_succ_self n⟩
    omega

theorem sumFin_ge_single : ∀ (n : Nat) (f : Fin n → Int) (q : Fin n),
    (∀ i : Fin n, 0 ≤ f i) → f q ≤ sumFin n f
  | 0, _, q, _ => nomatch q
  | n + 1, f, q, h => by
    simp only [sumFin]
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ q.isLt) with hEq | hLt
    · have hq : q = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hEq
      rw [hq]
      have hpre := sumFin_nonneg n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      omega
    · have ih := sumFin_ge_single n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) ⟨q.val, hLt⟩
        (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      dsimp only at ih
      have hq : q = ⟨q.val, Nat.lt_succ_of_lt hLt⟩ := Fin.ext rfl
      rw [hq]
      have hlast := h ⟨n, Nat.lt_succ_self n⟩
      omega

/-- Universal Count-Min Sketch One-Sided Point-Query Bound:
    for non-negative stream frequencies `f i ≥ 0`, if `inBucket q = true`, then
    `f q ≤ ∑_i (if inBucket i then f i else 0)`. -/
theorem count_min_nonneg_point_query_upper_bound
    (N : Nat) (f : Fin N → Int) (inBucket : Fin N → Bool) (q : Fin N)
    (hNonneg : ∀ i : Fin N, 0 ≤ f i)
    (hSelf : inBucket q = true) :
    f q ≤ sumFin N (fun i => if inBucket i then f i else 0) := by
  have hsingle := sumFin_ge_single N (fun i => if inBucket i then f i else 0) q (by
    intro i
    cases inBucket i
    · simp
    · simpa using hNonneg i)
  simpa [hSelf] using hsingle

/-- Premise-Failure Counterexample 1 (Signed Turnstile Deletion):
    Dropping `f i ≥ 0` (`f = [3, -5]` colliding in the same bucket) causes Count-Min
    to return `-2 < 3 = f 0`, breaking the one-sided upper bound! -/
def turnstileStream (i : Fin 2) : Int := if i.val == 0 then 3 else -5

theorem count_min_turnstile_deletion_underestimate :
    sumFin 2 turnstileStream < turnstileStream ⟨0, by decide⟩ ∧
    sumFin 2 turnstileStream = -2 := by
  decide

/-!
  ## 2. Karchmer–Wigderson Monotone Separation (`∃ i, x_i = 1 ∧ y_i = 0`) vs. XOR₂ Failure
-/

def boolLe (a b : Bool) : Prop := a = true → b = true

theorem exists_true_false_of_not_forall_le : ∀ (n : Nat) (x y : Fin n → Bool),
    ¬ (∀ i : Fin n, boolLe (x i) (y i)) →
    ∃ i : Fin n, x i = true ∧ y i = false
  | 0, _, _, h => False.elim (h (fun i => nomatch i))
  | n + 1, x, y, h => by
    rcases Classical.em (x ⟨n, Nat.lt_succ_self n⟩ = true ∧ y ⟨n, Nat.lt_succ_self n⟩ = false) with hLast | hNotLast
    · exact ⟨⟨n, Nat.lt_succ_self n⟩, hLast⟩
    · have hPrefix : ¬ (∀ i : Fin n, boolLe (x ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) (y ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) := by
        intro hAll
        apply h
        intro j
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ j.isLt) with hEq | hLt
        · have hj : j = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hEq
          rw [hj]
          intro hxj
          cases hy : y ⟨n, Nat.lt_succ_self n⟩
          · exact False.elim (hNotLast ⟨hxj, hy⟩)
          · rfl
        · exact hAll ⟨j.val, hLt⟩
      rcases exists_true_false_of_not_forall_le n
        (fun i => x ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i => y ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) hPrefix with ⟨i, hi⟩
      exact ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, hi⟩

/-- Universal Karchmer–Wigderson Monotone Relation Totalness Theorem:
    if `f : (Fin n → Bool) → Bool` is monotone, `f x = true`, and `f y = false`,
    then `∃ i : Fin n, x i = true ∧ y i = false`! -/
theorem karchmer_wigderson_monotone_witness_exists
    (n : Nat) (f : (Fin n → Bool) → Bool)
    (hMono : ∀ u v, (∀ i : Fin n, boolLe (u i) (v i)) → boolLe (f u) (f v))
    (x y : Fin n → Bool)
    (hx : f x = true) (hy : f y = false) :
    ∃ i : Fin n, x i = true ∧ y i = false := by
  apply exists_true_false_of_not_forall_le n x y
  intro hle
  have hfy := hMono x y hle hx
  rw [hy] at hfy
  contradiction

/-- Premise-Failure Counterexample 2 (Non-Monotone `XOR₂`):
    `xor2(false, true) = true` and `xor2(true, true) = false`, yet NO coordinate `i`
    has `x_i = true ∧ y_i = false`! -/
def xor2Vec (v : Fin 2 → Bool) : Bool := v ⟨0, by decide⟩ != v ⟨1, by decide⟩
def kwX (i : Fin 2) : Bool := i.val == 1
def kwY (_ : Fin 2) : Bool := true

theorem xor2_breaks_monotone_karchmer_wigderson :
    xor2Vec kwX = true ∧
    xor2Vec kwY = false ∧
    (∀ i : Fin 2, ¬ (kwX i = true ∧ kwY i = false)) := by
  decide

/-!
  ## 3. Spectral Triangle Trace (`tr(A³) = 6 · #Triangles`) vs. Self-Loop & Directed 3-Cycle
-/

def traceCube4 (adj : Fin 4 → Fin 4 → Nat) : Nat :=
  let verts : List (Fin 4) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]
  verts.foldl (fun s i =>
    verts.foldl (fun s2 j =>
      verts.foldl (fun s3 k => s3 + adj i j * adj j k * adj k i) s2) s) 0

def adjK4 (i j : Fin 4) : Nat := if i == j then 0 else 1
def adjK4MinusE (i j : Fin 4) : Nat :=
  if i == j || (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2) then 0 else 1
def adjSelfLoop0 (i j : Fin 4) : Nat := if i.val == 0 && j.val == 0 then 1 else 0
def adjDir3Cycle (i j : Fin 4) : Nat :=
  if (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 2) || (i.val == 2 && j.val == 0) then 1 else 0

theorem spectral_triangle_trace_six_fold_vs_selfloop_and_directed :
    traceCube4 adjK4 = 6 * 4 ∧
    traceCube4 adjK4MinusE = 6 * 2 ∧
    traceCube4 adjSelfLoop0 = 1 ∧
    traceCube4 adjDir3Cycle = 3 ∧
    traceCube4 adjDir3Cycle % 6 ≠ 0 := by
  decide

/-!
  ## 4. Prime `p = 5` Pairwise-Uniform Affine Hashing vs. Composite `m = 4` Double Collision
-/

def affinePairHitsMod5 (x y u v : Fin 5) : Nat :=
  let vals : List Nat := [0, 1, 2, 3, 4]
  vals.foldl (fun acc a =>
    vals.foldl (fun acc2 b =>
      if (a * x.val + b) % 5 == u.val && (a * y.val + b) % 5 == v.val then acc2 + 1 else acc2) acc) 0

def affineCollisionsMod4 (x y : Nat) : Nat :=
  let vals : List Nat := [0, 1, 2, 3]
  vals.foldl (fun acc a =>
    vals.foldl (fun acc2 b =>
      if (a * x + b) % 4 == (a * y + b) % 4 then acc2 + 1 else acc2) acc) 0

theorem prime_mod5_exact_pairwise_uniform_vs_composite_mod4_double_collision :
    (∀ x y u v : Fin 5, x ≠ y → affinePairHitsMod5 x y u v = 1) ∧
    affineCollisionsMod4 0 2 = 8 ∧
    4 < affineCollisionsMod4 0 2 := by
  decide

/-!
  ## 5. Idempotent MinHash Distributed Mergeability vs. Additive Overlap Double-Counting
-/

def intMin (a b : Int) : Int := if a ≤ b then a else b

theorem minhash_idempotent_merge_vs_additive_overlap_bias
    (a b c cardS cardT cardInter : Int) (hOverlap : 1 ≤ cardInter) :
    intMin a a = a ∧
    intMin (intMin a b) (intMin b c) = intMin a (intMin b c) ∧
    (cardS + cardT) - (cardS + cardT - cardInter) = cardInter ∧
    0 < (cardS + cardT) - (cardS + cardT - cardInter) := by
  refine ⟨by unfold intMin; split <;> omega, ?_, by omega, by omega⟩
  rcases Classical.em (a ≤ b) with hab | hab <;>
  rcases Classical.em (b ≤ c) with hbc | hbc <;>
  rcases Classical.em (a ≤ c) with hac | hac <;>
  simp [intMin, hab, hbc, hac] <;> omega

end CommonGround.Verification.TheoremAtlasYaoMinimaxLoomisWhitneyAGMJoinFoolingSetAndAMSSketchBridge
