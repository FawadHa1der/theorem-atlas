/-!
# Fine-Grained Subcubic Reductions (`OV ↔ Min-Plus / APSP`), Williams's Polynomial-Method Low-Rank Factorization, and Razborov–Rudich Natural Proofs Barriers

Pure-core Lean 4.33.0 formalization (zero external dependencies, zero `sorry`) uniting two
cornerstones of modern fine-grained and circuit complexity in `10-millennium-frontier-bridges`:

1. **Tropical Min-Plus Matrix Product Orthogonality Detector (`min_plus_entry_gt_neg_two_iff_orthogonal`)**:
   For Boolean vectors `u, v ∈ {0, 1}^d`, encoding `M_{i,k} = -u_k` and `N_{k,j} = -v_k` reduces
   Orthogonal Vectors (`OV`) directly to a single tropical min-plus matrix product entry:
   `min_{k < d} (-(u_k + v_k)) > -2  ↔  ∀ k < d, u_k * v_k = 0`
   (and `min_{k < d} (-(u_k + v_k)) = -2  ↔  ∃ k < d, u_k = 1 ∧ v_k = 1`).
   Hence any truly subcubic `(n × d) ⋆ (d × n)` min-plus / `APSP` algorithm immediately refutes `OV`
   and the Strong Exponential Time Hypothesis (`SETH`).

2. **Sharp Non-Boolean Premise-Failure Counterexample (`non_boolean_entry_breaks_min_plus_orthogonality_detector`)**:
   If vector entries leave `{0, 1}` — e.g., `u = (2, 0)` and `v = (0, 0)` — then `u` and `v` ARE
   orthogonal (`2 * 0 + 0 * 0 = 0`), yet `min_{k < 2} (-(u_k + v_k)) = -2`, falsely triggering the
   non-orthogonality threshold! Thus `{0, 1}` range normalization is indispensable.

3. **Williams's Polynomial-Method Bilinear Low-Rank Compression & Mod-2 Rank Collapse (`low_rank_bilinear_sum_factorization` & `mod2_rank_collapse_false_orthogonality_witness`)**:
   Any rank-`R` polynomial decomposition `P(i, j) = ∑_{r < R} L_r(i) · M_r(j)` over `ℤ` factors the
   `N × N` batch evaluation `∑_{i < N} ∑_{j < N} P(i, j)` into `∑_{r < R} (∑_{i < N} L_r(i)) · (∑_{j < N} M_r(j))`,
   replacing `N²` pairwise evaluations by `2 R N` unary evaluations (the core mechanism behind Ryan
   Williams's `2^n / n^ω` `ACC⁰`-SAT algorithm). Conversely, truncating the exact multilinear
   orthogonality polynomial `(1 - u₀ v₀)(1 - u₁ v₁)` (`rank = 4`) to its mod-`2` linear surrogate
   `1 - (u₀ v₀ + u₁ v₁) % 2` (`rank ≤ 3`) misclassifies `u = (1, 1), v = (1, 1)` (`u · v = 2 ≠ 0`)!

4. **Razborov–Rudich Natural Proofs PRF Distinguisher Theorem & Non-Large Affine Escape (`natural_property_breaks_prf_advantage_bound` & `affine_boolean_nonlarge_escapes_razborov_rudich`)**:
   Any combinatorial truth-table property `PropNat : Nat → Bool` on `M` truth tables that is
   **useful** against an `S`-keyed circuit family `F` (`∀ k < S, PropNat (F k) = false`) and
   **`L`-large** (`L ≤ countTrue M PropNat`) immediately yields a black-box statistical PRF
   distinguisher with integer-scaled advantage
   `S * L ≤ S * countTrue M PropNat - M * countFamilyTrue S F PropNat`.
   Conversely, algebraic degree-`1` / 2nd-order discrete-derivative annihilator tests (`isAffine8`)
   accept strictly `16` out of `256` (`1/16`, generally `2^{n+1} / 2^{2^n}`) 3-variable Boolean
   truth tables — escaping largeness via exponential sparsity while their negation `notAffine8`
   (`240 / 256`) is large and therefore only proves lower bounds against circuit classes (`𝔽₂`-linear)
   incapable of computing PRFs!
-/

namespace CommonGround.Frontier.FineGrainedSubcubicReductionsAndNaturalProofs

/-- Minimum of two integers. -/
def intMin (a b : Int) : Int :=
  if a ≤ b then a else b

theorem intMin_gt_iff (a b c : Int) :
    c < intMin a b ↔ (c < a ∧ c < b) := by
  unfold intMin
  split <;> omega

theorem intMin_ge_neg_two (a b : Int) (ha : -2 ≤ a) (hb : -2 ≤ b) :
    -2 ≤ intMin a b := by
  unfold intMin
  split <;> omega

/-- Tropical min-plus inner entry `min_{k < d} (-(u k + v k))` initialized at `0` for `d = 0`. -/
def minPlusNegDot : Nat → (Nat → Int) → (Nat → Int) → Int
  | 0, _, _ => 0
  | d + 1, u, v => intMin (minPlusNegDot d u v) (-(u d + v d))

/-- Boolean `{0, 1}` coordinate predicate on the first `d` coordinates. -/
def IsBooleanVec (d : Nat) (u : Nat → Int) : Prop :=
  ∀ k : Nat, k < d → (u k = 0 ∨ u k = 1)

theorem boolean_coord_orth_iff_neg_sum_gt_neg_two (a b : Int)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    -2 < -(a + b) ↔ a * b = 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega

/-- **Theorem 1 (Tropical Min-Plus Matrix Product Orthogonality Detector)**:
For any dimension `d` and Boolean vectors `u, v ∈ {0, 1}^d`, the tropical min-plus product entry
`minPlusNegDot d u v = min_{k < d} (-(u_k + v_k))` strictly exceeds `-2` if and only if `u` and `v`
are orthogonal (`∀ k < d, u k * v k = 0`). -/
theorem min_plus_entry_gt_neg_two_iff_orthogonal (d : Nat) (u v : Nat → Int)
    (hu : IsBooleanVec d u) (hv : IsBooleanVec d v) :
    -2 < minPlusNegDot d u v ↔ ∀ k : Nat, k < d → u k * v k = 0 := by
  induction d with
  | zero =>
    simp [minPlusNegDot]
  | succ d ih =>
    have hu' : IsBooleanVec d u := fun k hk => hu k (by omega)
    have hv' : IsBooleanVec d v := fun k hk => hv k (by omega)
    simp only [minPlusNegDot]
    rw [intMin_gt_iff, ih hu' hv',
      boolean_coord_orth_iff_neg_sum_gt_neg_two (u d) (v d) (hu d (by omega)) (hv d (by omega))]
    constructor
    · intro ⟨hPrev, hLast⟩ k hk
      by_cases hkd : k < d
      · exact hPrev k hkd
      · have hEq : k = d := by omega
        subst hEq
        exact hLast
    · intro hAll
      exact ⟨fun k hk => hAll k (by omega), hAll d (by omega)⟩

theorem minPlusNegDot_ge_neg_two (d : Nat) (u v : Nat → Int)
    (hu : IsBooleanVec d u) (hv : IsBooleanVec d v) :
    -2 ≤ minPlusNegDot d u v := by
  induction d with
  | zero => simp [minPlusNegDot]
  | succ d ih =>
    have hu' : IsBooleanVec d u := fun k hk => hu k (by omega)
    have hv' : IsBooleanVec d v := fun k hk => hv k (by omega)
    have hd1 := hu d (by omega)
    have hd2 := hv d (by omega)
    have hTerm : -2 ≤ -(u d + v d) := by
      rcases hd1 with h1 | h1 <;> rcases hd2 with h2 | h2 <;> omega
    exact intMin_ge_neg_two _ _ (ih hu' hv') hTerm

theorem exists_common_one_of_eq_neg_two :
    ∀ (d : Nat) (u v : Nat → Int),
      IsBooleanVec d u → IsBooleanVec d v → minPlusNegDot d u v = -2 →
        ∃ k : Nat, k < d ∧ u k = 1 ∧ v k = 1
  | 0, _, _, _, _, hEq => by simp [minPlusNegDot] at hEq
  | d + 1, u, v, hu, hv, hEq => by
    by_cases hLast : u d = 1 ∧ v d = 1
    · exact ⟨d, by omega, hLast.1, hLast.2⟩
    · have hu' : IsBooleanVec d u := fun k hk => hu k (by omega)
      have hv' : IsBooleanVec d v := fun k hk => hv k (by omega)
      have hd1 := hu d (by omega)
      have hd2 := hv d (by omega)
      have hTermGt : -2 < -(u d + v d) := by
        rcases hd1 with h1 | h1 <;> rcases hd2 with h2 | h2
        · omega
        · omega
        · omega
        · exfalso; exact hLast ⟨h1, h2⟩
      simp only [minPlusNegDot, intMin] at hEq
      have hPrevLe := minPlusNegDot_ge_neg_two d u v hu' hv'
      have hPrevEq : minPlusNegDot d u v = -2 := by
        split at hEq <;> omega
      obtain ⟨k, hk, huk, hvk⟩ := exists_common_one_of_eq_neg_two d u v hu' hv' hPrevEq
      exact ⟨k, by omega, huk, hvk⟩

/-- Complementary Witness Equivalence: Under Boolean `{0, 1}` coordinates, `minPlusNegDot d u v` is
always bounded below by `-2`, and equals `-2` iff `u` and `v` share a common `1` (`∃ k < d, u k = 1 ∧ v k = 1`). -/
theorem min_plus_entry_eq_neg_two_iff_common_one (d : Nat) (u v : Nat → Int)
    (hu : IsBooleanVec d u) (hv : IsBooleanVec d v) :
    (-2 ≤ minPlusNegDot d u v) ∧
    (minPlusNegDot d u v = -2 ↔ ∃ k : Nat, k < d ∧ u k = 1 ∧ v k = 1) := by
  have hLower := minPlusNegDot_ge_neg_two d u v hu hv
  have hOrth := min_plus_entry_gt_neg_two_iff_orthogonal d u v hu hv
  refine ⟨hLower, ⟨exists_common_one_of_eq_neg_two d u v hu hv, ?_⟩⟩
  rintro ⟨k, hk, huk, hvk⟩
  have hNotOrth : ¬ (∀ j : Nat, j < d → u j * v j = 0) := by
    intro hAll
    have h0 := hAll k hk
    rw [huk, hvk] at h0
    omega
  have hNotGt : ¬ (-2 < minPlusNegDot d u v) := fun h => hNotOrth (hOrth.mp h)
  omega

/-- **Premise-Failure Counterexample 1 (Non-Boolean `{0, 1}` Violation)**:
For `u = (2, 0)` and `v = (0, 0)` (`u 0 = 2 ∉ {0, 1}`), `u` and `v` ARE orthogonal
(`u 0 * v 0 + u 1 * v 1 = 0`), yet `minPlusNegDot 2 u v = -2`, falsely signaling non-orthogonality! -/
theorem non_boolean_entry_breaks_min_plus_orthogonality_detector :
    let u : Nat → Int := fun k => if k = 0 then 2 else 0
    let v : Nat → Int := fun _ => 0
    (∀ k : Nat, k < 2 → u k * v k = 0) ∧
    (minPlusNegDot 2 u v = -2) ∧
    ¬ (-2 < minPlusNegDot 2 u v) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro k _hk
    by_cases hk0 : k = 0 <;> simp [hk0]
  · simp [minPlusNegDot, intMin]
  · simp [minPlusNegDot, intMin]

/-- Finite integer sum `∑_{i < n} f i`. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

theorem sumRange_zero (n : Nat) :
    sumRange n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumRange, ih]

theorem sumRange_congr (n : Nat) (f g : Nat → Int)
    (h : ∀ i : Nat, i < n → f i = g i) :
    sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hPrev : sumRange n f = sumRange n g := ih (fun i hi => h i (by omega))
    have hLast : f n = g n := h n (by omega)
    simp only [sumRange, hPrev, hLast]

theorem sumRange_add (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumRange, ih]
    omega

theorem sumRange_mul_const_right (n : Nat) (f : Nat → Int) (c : Int) :
    sumRange n (fun i => f i * c) = (sumRange n f) * c := by
  induction n with
  | zero =>
    simp [sumRange]
  | succ n ih =>
    simp only [sumRange, ih, Int.add_mul]

theorem sumRange_mul_const_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun i => c * f i) = c * (sumRange n f) := by
  induction n with
  | zero =>
    simp [sumRange]
  | succ n ih =>
    simp only [sumRange, ih, Int.mul_add]

theorem sumRange_comm (n m : Nat) (F : Nat → Nat → Int) :
    sumRange n (fun i => sumRange m (fun j => F i j)) =
      sumRange m (fun j => sumRange n (fun i => F i j)) := by
  induction n with
  | zero =>
    simp only [sumRange]
    exact (sumRange_zero m).symm
  | succ n ihn =>
    simp only [sumRange]
    rw [ihn, ← sumRange_add]

/-- **Theorem 2 (Williams's Polynomial-Method Low-Rank Bilinear Sum Compression)**:
If a pairwise predicate/kernel `P(i, j)` admits a rank-`R` decomposition
`P(i, j) = ∑_{r < R} L r i * M r j`, then the `N × N` all-pairs sum equals
`∑_{r < R} (∑_{i < N} L r i) * (∑_{j < N} M r j)`, compressing `N²` pairwise evaluations into
`2 R N` unary evaluations. -/
theorem low_rank_bilinear_sum_factorization (N R : Nat) (L M : Nat → Nat → Int) :
    sumRange N (fun i => sumRange N (fun j => sumRange R (fun r => L r i * M r j))) =
      sumRange R (fun r => (sumRange N (fun i => L r i)) * (sumRange N (fun j => M r j))) := by
  have h1 :
      sumRange N (fun i => sumRange N (fun j => sumRange R (fun r => L r i * M r j))) =
        sumRange N (fun i => sumRange R (fun r => sumRange N (fun j => L r i * M r j))) := by
    apply sumRange_congr
    intro i _hi
    exact sumRange_comm N R (fun j r => L r i * M r j)
  rw [h1, sumRange_comm N R]
  apply sumRange_congr
  intro r _hr
  have h2 :
      sumRange N (fun i => sumRange N (fun j => L r i * M r j)) =
        sumRange N (fun i => L r i * sumRange N (fun j => M r j)) := by
    apply sumRange_congr
    intro i _hi
    exact sumRange_mul_const_left N (L r i) (fun j => M r j)
  rw [h2, sumRange_mul_const_right]

/-- **Premise-Failure Counterexample 2 (Mod-2 Polynomial Rank Collapse vs. Exact Orthogonality)**:
Over `{0, 1}²`, the exact multilinear orthogonality indicator `(1 - u₀ v₀)(1 - u₁ v₁)` has rank `4`
and vanishes on `u = (1, 1), v = (1, 1)` (`u · v = 2 ≠ 0`), whereas the rank-`≤ 3` mod-`2` parity
surrogate `1 - ((u₀ v₀ + u₁ v₁) % 2)` evaluates to `1` on `u = (1, 1), v = (1, 1)` (`2 % 2 = 0`),
creating a false orthogonality collision unless randomized Razborov–Smolensky subspace projections are used! -/
theorem mod2_rank_collapse_false_orthogonality_witness :
    let exactOrth (u0 u1 v0 v1 : Int) : Int := (1 - u0 * v0) * (1 - u1 * v1)
    let mod2Surrogate (u0 u1 v0 v1 : Int) : Int := 1 - ((u0 * v0 + u1 * v1) % 2)
    (∀ u0 u1 v0 v1 : Int,
      (u0 = 0 ∨ u0 = 1) → (u1 = 0 ∨ u1 = 1) → (v0 = 0 ∨ v0 = 1) → (v1 = 0 ∨ v1 = 1) →
        (exactOrth u0 u1 v0 v1 = 1 ↔ u0 * v0 + u1 * v1 = 0)) ∧
    (1 * 1 + 1 * 1 = (2 : Int) ∧ mod2Surrogate 1 1 1 1 = 1 ∧ exactOrth 1 1 1 1 = 0) := by
  dsimp only
  refine ⟨?_, by omega⟩
  intro u0 u1 v0 v1 hu0 hu1 hv0 hv1
  rcases hu0 with rfl | rfl <;> rcases hu1 with rfl | rfl <;>
    rcases hv0 with rfl | rfl <;> rcases hv1 with rfl | rfl <;> omega

/-- Count how many truth tables `t < M` satisfy a Boolean property `P`. -/
def countTrue : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | m + 1, P => countTrue m P + (if P m then 1 else 0)

/-- Split `countTrue (a + b)` across two blocks so large truth-table counts evaluate at shallow depth. -/
theorem countTrue_add (a b : Nat) (P : Nat → Bool) :
    countTrue (a + b) P = countTrue a P + countTrue b (fun i => P (a + i)) := by
  induction b with
  | zero =>
    simp [countTrue]
  | succ b ih =>
    have hEq : a + (b + 1) = (a + b) + 1 := by omega
    rw [hEq]
    simp only [countTrue, ih]
    omega

theorem countTrue_mul_16 (P : Nat → Bool) :
    countTrue 256 P =
      countTrue 16 (fun t => P (0 + t)) +
      countTrue 16 (fun t => P (16 + t)) +
      countTrue 16 (fun t => P (32 + t)) +
      countTrue 16 (fun t => P (48 + t)) +
      countTrue 16 (fun t => P (64 + t)) +
      countTrue 16 (fun t => P (80 + t)) +
      countTrue 16 (fun t => P (96 + t)) +
      countTrue 16 (fun t => P (112 + t)) +
      countTrue 16 (fun t => P (128 + t)) +
      countTrue 16 (fun t => P (144 + t)) +
      countTrue 16 (fun t => P (160 + t)) +
      countTrue 16 (fun t => P (176 + t)) +
      countTrue 16 (fun t => P (192 + t)) +
      countTrue 16 (fun t => P (208 + t)) +
      countTrue 16 (fun t => P (224 + t)) +
      countTrue 16 (fun t => P (240 + t)) := by
  have h128 : (256 : Nat) = 128 + 128 := rfl
  have h64  : (128 : Nat) = 64 + 64 := rfl
  have h32  : (64 : Nat) = 32 + 32 := rfl
  have h16  : (32 : Nat) = 16 + 16 := rfl
  rw [h128, countTrue_add]
  rw [h64, countTrue_add, countTrue_add]
  rw [h32, countTrue_add, countTrue_add, countTrue_add, countTrue_add]
  rw [h16]
  repeat rw [countTrue_add 16 16]
  simp only [← Nat.add_assoc, Nat.zero_add]

/-- Count how many circuit keys `k < S` satisfy `P (F k) = true`. -/
def countFamilyTrue (S : Nat) (F : Nat → Nat) (P : Nat → Bool) : Nat :=
  countTrue S (fun k => P (F k))

theorem countTrue_eq_zero_of_all_false (n : Nat) (Q : Nat → Bool)
    (hFalse : ∀ i : Nat, i < n → Q i = false) :
    countTrue n Q = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hPrev : countTrue n Q = 0 := ih (fun i hi => hFalse i (by omega))
    have hLast : Q n = false := hFalse n (by omega)
    simp [countTrue, hPrev, hLast]

/-- **Theorem 3 (Razborov–Rudich Natural Proofs PRF Distinguisher Advantage Theorem)**:
If a Boolean truth-table property `PropNat : Nat → Bool` over `M` truth tables is:
1. **Useful against `F`**: `∀ k < S, PropNat (F k) = false` (rejects every function in the `S`-keyed
   circuit family `F`), and
2. **`L`-Large**: `L ≤ countTrue M PropNat` (accepts at least `L` of the `M` uniform truth tables),
then `countFamilyTrue S F PropNat = 0`, and the integer-scaled PRF distinguishing advantage satisfies
`S * L ≤ S * countTrue M PropNat - M * countFamilyTrue S F PropNat` (equivalently, advantage `≥ L / M`). -/
theorem natural_property_breaks_prf_advantage_bound
    (M S L : Nat) (F : Nat → Nat) (PropNat : Nat → Bool)
    (hUseful : ∀ k : Nat, k < S → PropNat (F k) = false)
    (hLarge : L ≤ countTrue M PropNat) :
    countFamilyTrue S F PropNat = 0 ∧
    S * L ≤ S * countTrue M PropNat - M * countFamilyTrue S F PropNat := by
  have hFamZero : countFamilyTrue S F PropNat = 0 :=
    countTrue_eq_zero_of_all_false S (fun k => PropNat (F k)) hUseful
  refine ⟨hFamZero, ?_⟩
  rw [hFamZero, Nat.mul_zero, Nat.sub_zero]
  exact Nat.mul_le_mul_left S hLarge

/-- Extract bit `i` of a natural-number truth table `tt`. -/
def ttBit (tt i : Nat) : Nat :=
  (tt / (2 ^ i)) % 2

/-- 2-variable (`4`-bit truth table `0..15`) affine linearity test: `b₀ ⊕ b₁ ⊕ b₂ ⊕ b₃ = 0`. -/
def isAffine4 (tt : Nat) : Bool :=
  decide ((ttBit tt 0 + ttBit tt 1 + ttBit tt 2 + ttBit tt 3) % 2 == 0)

/-- 3-variable (`8`-bit truth table `0..255`) affine linearity test (`deg_{𝔽₂}(f) ≤ 1`):
all 4 linearly independent 2nd/3rd-order Möbius/face derivatives vanish (`x₁x₂|_{x₃=0}`,
`x₁x₂|_{x₃=1}`, `x₁x₃|_{x₂=0}`, `x₂x₃|_{x₁=0}` — cutting `𝔽₂^8` down to `2^4 = 16` affine functions). -/
def isAffine8 (tt : Nat) : Bool :=
  decide (
    (ttBit tt 0 + ttBit tt 1 + ttBit tt 2 + ttBit tt 3) % 2 == 0 ∧
    (ttBit tt 4 + ttBit tt 5 + ttBit tt 6 + ttBit tt 7) % 2 == 0 ∧
    (ttBit tt 0 + ttBit tt 1 + ttBit tt 4 + ttBit tt 5) % 2 == 0 ∧
    (ttBit tt 0 + ttBit tt 2 + ttBit tt 4 + ttBit tt 6) % 2 == 0
  )

/-- **Theorem 4 (Non-Largeness Escape Witness vs. Large Nonlinear Complement)**:
- On `n = 2` (`16` truth tables), `isAffine4` accepts `8 / 16` (`1 / 2`), whereas on `n = 3` (`256`
  truth tables), `isAffine8` accepts **strictly `16 / 256` (`1 / 16`, `2^{n+1} / 2^{2^n}`)** —
  demonstrating exponential decay below any polynomial-inverse largeness threshold!
- Conversely, its complement `notAffine8` ("nonlinear Boolean function, useful against `𝔽₂`-linear
  circuits") accepts **`240 / 256` (`15 / 16`, large!)** — which is compatible with Razborov–Rudich
  precisely because `𝔽₂`-linear circuits CANNOT compute pseudorandom functions! -/
theorem affine_boolean_nonlarge_escapes_razborov_rudich :
    countTrue 16 isAffine4 = 8 ∧
    countTrue 256 isAffine8 = 16 ∧
    countTrue 256 (fun tt => !isAffine8 tt) = 240 ∧
    16 * countTrue 256 isAffine8 = 256 := by
  have hAff : countTrue 256 isAffine8 = 16 := by
    rw [countTrue_mul_16]
    decide
  have hNonAff : countTrue 256 (fun tt => !isAffine8 tt) = 240 := by
    rw [countTrue_mul_16]
    decide
  refine ⟨by decide, hAff, hNonAff, ?_⟩
  rw [hAff]

end CommonGround.Frontier.FineGrainedSubcubicReductionsAndNaturalProofs
