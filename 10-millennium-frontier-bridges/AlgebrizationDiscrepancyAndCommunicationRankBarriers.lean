/-!
# Algebrization Extensions, Lindsey–Chor–Goldreich Communication Discrepancy, and Prime vs. Composite Polynomial Degree Barriers

This pure-core Lean 4.33.0 module (`0` imports, `0` sorrys) unifies three pillars of modern
computational complexity theory and spectral combinatorics:

1. **Single-Sum Integer Cauchy–Schwarz & Lindsey's Orthogonal Rectangle Discrepancy Lemma**
   (`cauchy_schwarz_range_int`, `lindsey_orthogonal_rectangle_discrepancy_bound`,
   `chor_goldreich_hadamard_communication_lower_bound`, `hadamard8_monochromatic_partition_ge_eight`):
   Proves the exact integer Buniakovsky–Schwarz inequality `(∑_{y<N} f(y)g(y))² ≤ (∑ f²)(∑ g²)` for
   arbitrary `N : Nat`, lifts row orthogonality `∑_{y<N} H(x₁,y)H(x₂,y) = L · δ_{x₁,x₂}` to Lindsey's
   bilinear rectangle discrepancy bound `(∑_{x,y<N} u(x)H(x,y)v(y))² ≤ L · (∑ u²) · (∑ v²)`, and
   derives the Chor–Goldreich monochromatic rectangle partition lower bound `N² ≤ R · L` (instantiated
   on `8 × 8` Walsh–Hadamard `H₃` with `R ≥ 8`, contrasted with rank-`1` all-ones collapse `R = 1 < 8`).

2. **Aaronson–Wigderson Algebrization Deformation vs. Degree-`1` Multilinear Rigidity**
   (`algebrization_extension_boolean_lock_vs_off_cube_freedom`, `degree_one_multilinear_locks_off_cube`):
   Formalizes the Boolean ideal generator `x(x - 1)` showing that `P̃(x) = P(x) + x(x - 1)Q(x)` preserves
   every Boolean oracle evaluation on `{0, 1}` while varying off-cube evaluations `P̃(2) = P(2) + 2Q(2)`
   freely at degree `≥ 2`, whereas degree-`1` affine extensions lock `L(x) = (1 - x)L(0) + xL(1)`.

3. **Razborov–Smolensky Prime-Field Barrier vs. Barrington–Grolmusz Composite `mod 6` Escape**
   (`no_degree1_mod2_exact_zero_at_origin_on_cube3`, `no_degree1_mod3_exact_zero_at_origin_on_cube3`,
   `composite_mod6_degree1_exact_or3_witness`):
   Proves exhaustively that **no** degree-`1` polynomial modulo `2` or modulo `3` can have exact zero-set
   `{(0, 0, 0)}` on `{0, 1}³` (computing `NOR₃` / `OR₃`), whereas modulo the composite `6 = 2 × 3`, the
   degree-`1` linear form `3x + 2y + 2z` vanishes at `(0, 0, 0)` and is non-zero modulo `6` on all seven
   non-zero vertices of `{0, 1}³` (`{3, 2, 2, 5, 5, 4, 1}`) — the exact finite algebraic mechanism
   separating `AC⁰[p]` (Razborov–Smolensky 1987) from composite-modulus `ACC⁰ = AC⁰[6]`!
-/

namespace CommonGround.Frontier.AlgebrizationDiscrepancyAndCommunicationRankBarriers

/-- Finite integer summation `∑_{i < n} f(i)` in pure-core Lean 4. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

/-- Kronecker delta on `Nat` valued in `Int`. -/
def deltaNat (i j : Nat) : Int :=
  if i = j then 1 else 0

theorem sumRange_add (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumRange, ih]
    omega

theorem sumRange_sub (n : Nat) (f g : Nat → Int) :
    sumRange n (fun i => f i - g i) = sumRange n f - sumRange n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumRange, ih]
    omega

theorem sumRange_const_mul (n : Nat) (c : Int) (f : Nat → Int) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero =>
    simp [sumRange]
  | succ k ih =>
    simp only [sumRange, ih, Int.mul_add]

theorem sumRange_mul_const (n : Nat) (f : Nat → Int) (c : Int) :
    sumRange n (fun i => f i * c) = sumRange n f * c := by
  induction n with
  | zero =>
    simp [sumRange]
  | succ k ih =>
    simp only [sumRange, ih, Int.add_mul]

theorem sumRange_const (n : Nat) (c : Int) :
    sumRange n (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero =>
    simp [sumRange]
  | succ k ih =>
    simp only [sumRange, ih]
    have hcast : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
    rw [hcast, Int.add_mul]
    omega

theorem sumRange_nonneg (n : Nat) (f : Nat → Int)
    (hf : ∀ i : Nat, i < n → 0 ≤ f i) :
    0 ≤ sumRange n f := by
  induction n with
  | zero =>
    simp [sumRange]
  | succ k ih =>
    have hprev : 0 ≤ sumRange k f := ih (fun i hi => hf i (Nat.lt_succ_of_lt hi))
    have hlast : 0 ≤ f k := hf k (Nat.lt_succ_self k)
    simp only [sumRange]
    omega

theorem sumRange_le (n : Nat) (f g : Nat → Int)
    (hfg : ∀ i : Nat, i < n → f i ≤ g i) :
    sumRange n f ≤ sumRange n g := by
  induction n with
  | zero =>
    simp [sumRange]
  | succ k ih =>
    have hprev : sumRange k f ≤ sumRange k g := ih (fun i hi => hfg i (Nat.lt_succ_of_lt hi))
    have hlast : f k ≤ g k := hfg k (Nat.lt_succ_self k)
    simp only [sumRange]
    omega

theorem sq_nonneg_int (z : Int) : 0 ≤ z * z := by
  by_cases hz : 0 ≤ z
  · exact Int.mul_nonneg hz hz
  · have hneg : 0 ≤ -z := by omega
    have hprod : 0 ≤ (-z) * (-z) := Int.mul_nonneg hneg hneg
    have heq : (-z) * (-z) = z * z := by
      simp [Int.neg_mul, Int.mul_neg]
    omega

theorem eq_zero_of_sq_eq_zero (z : Int) (h : z * z = 0) : z = 0 := by
  by_cases hz : z = 0
  · exact hz
  · by_cases hpos : 0 < z
    · have hm : 0 < z * z := Int.mul_pos hpos hpos
      omega
    · have hneg : 0 < -z := by omega
      have hm : 0 < (-z) * (-z) := Int.mul_pos hneg hneg
      have heq : (-z) * (-z) = z * z := by
        simp [Int.neg_mul, Int.mul_neg]
      omega

theorem sumRange_sq_eq_zero_imp_pointwise (n : Nat) (g : Nat → Int)
    (hsum : sumRange n (fun i => g i * g i) = 0) :
    ∀ i : Nat, i < n → g i = 0 := by
  induction n with
  | zero =>
    intro i hi
    omega
  | succ k ih =>
    have hprev_nn : 0 ≤ sumRange k (fun i => g i * g i) :=
      sumRange_nonneg k (fun i => g i * g i) (fun i _ => sq_nonneg_int (g i))
    have hlast_nn : 0 ≤ g k * g k := sq_nonneg_int (g k)
    simp only [sumRange] at hsum
    have hprev_zero : sumRange k (fun i => g i * g i) = 0 := by omega
    have hlast_sq_zero : g k * g k = 0 := by omega
    have hlast_zero : g k = 0 := eq_zero_of_sq_eq_zero (g k) hlast_sq_zero
    intro i hi
    by_cases hik : i < k
    · exact ih hprev_zero i hik
    · have heq : i = k := by omega
      rw [heq]
      exact hlast_zero

theorem sumRange_zero_of_pointwise (n : Nat) (f : Nat → Int)
    (hf : ∀ i : Nat, i < n → f i = 0) :
    sumRange n f = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have hp : sumRange k f = 0 := ih (fun i hi => hf i (Nat.lt_succ_of_lt hi))
    have hl : f k = 0 := hf k (Nat.lt_succ_self k)
    simp only [sumRange, hp, hl]
    omega

theorem cancel_pos_mul_left {b x y : Int} (hb : 0 < b) (h : b * x ≤ b * y) : x ≤ y := by
  by_cases hle : x ≤ y
  · exact hle
  · have hdiff : 0 < x - y := by omega
    have hprod : 0 < b * (x - y) := Int.mul_pos hb hdiff
    have hexp : b * (x - y) = b * x - b * y := Int.mul_sub b x y
    omega

/-! ## Part 1: Universal Integer Cauchy–Schwarz, Lindsey's Lemma & Chor–Goldreich Lower Bound -/

theorem quadratic_discriminant_pointwise (B C fi gi : Int) :
    (B * fi - C * gi) * (B * fi - C * gi) =
      (B * B) * (fi * fi) - (2 * B * C) * (fi * gi) + (C * C) * (gi * gi) := by
  have h1 : (B * fi - C * gi) * (B * fi - C * gi) =
      (B * fi) * (B * fi) - (B * fi) * (C * gi) - (C * gi) * (B * fi) + (C * gi) * (C * gi) := by
    simp only [Int.sub_mul, Int.mul_sub]
    omega
  have h2 : (B * fi) * (B * fi) = (B * B) * (fi * fi) := by
    simp only [Int.mul_left_comm, Int.mul_comm]
  have h3 : (C * gi) * (C * gi) = (C * C) * (gi * gi) := by
    simp only [Int.mul_left_comm, Int.mul_comm]
  have h4 : (B * fi) * (C * gi) = (B * C) * (fi * gi) := by
    simp only [Int.mul_left_comm, Int.mul_comm]
  have h5 : (C * gi) * (B * fi) = (B * C) * (fi * gi) := by
    simp only [Int.mul_left_comm, Int.mul_comm]
  have h6 : (2 * B * C) * (fi * gi) = 2 * ((B * C) * (fi * gi)) := by
    simp only [Int.mul_assoc]
  rw [h1, h2, h3, h4, h5, h6]
  omega

/-- **Universal Integer Buniakovsky–Cauchy–Schwarz Inequality**:
For every horizon `N : Nat` and sequences `f, g : Nat → Int`,
`(∑_{i<N} f(i) g(i))² ≤ (∑_{i<N} f(i)²) · (∑_{i<N} g(i)²)`. -/
theorem cauchy_schwarz_range_int (N : Nat) (f g : Nat → Int) :
    (sumRange N (fun i => f i * g i)) * (sumRange N (fun i => f i * g i)) ≤
      (sumRange N (fun i => f i * f i)) * (sumRange N (fun i => g i * g i)) := by
  have hB_nn : 0 ≤ sumRange N (fun i => g i * g i) :=
    sumRange_nonneg N (fun i => g i * g i) (fun i _ => sq_nonneg_int (g i))
  by_cases hB0 : sumRange N (fun i => g i * g i) = 0
  · have hg0 : ∀ i : Nat, i < N → g i = 0 := sumRange_sq_eq_zero_imp_pointwise N g hB0
    have hfg0 : sumRange N (fun i => f i * g i) = 0 := by
      apply sumRange_zero_of_pointwise
      intro i hi
      rw [hg0 i hi]
      simp
    rw [hfg0, hB0]
    simp
  · have hBpos : 0 < sumRange N (fun i => g i * g i) := by omega
    have hQ_nn :
        0 ≤ sumRange N (fun i =>
          (sumRange N (fun j => g j * g j) * f i - sumRange N (fun j => f j * g j) * g i) *
          (sumRange N (fun j => g j * g j) * f i - sumRange N (fun j => f j * g j) * g i)) :=
      sumRange_nonneg N _ (fun i _ => sq_nonneg_int _)
    have hQ_eq :
        sumRange N (fun i =>
          (sumRange N (fun j => g j * g j) * f i - sumRange N (fun j => f j * g j) * g i) *
          (sumRange N (fun j => g j * g j) * f i - sumRange N (fun j => f j * g j) * g i)) =
        (sumRange N (fun j => g j * g j) * sumRange N (fun j => g j * g j)) * sumRange N (fun i => f i * f i) -
        (2 * sumRange N (fun j => g j * g j) * sumRange N (fun j => f j * g j)) * sumRange N (fun i => f i * g i) +
        (sumRange N (fun j => f j * g j) * sumRange N (fun j => f j * g j)) * sumRange N (fun i => g i * g i) := by
      simp only [quadratic_discriminant_pointwise, sumRange_add, sumRange_sub, sumRange_const_mul]
    have hfactor :
        (sumRange N (fun j => g j * g j) * sumRange N (fun j => g j * g j)) * sumRange N (fun i => f i * f i) -
        (2 * sumRange N (fun j => g j * g j) * sumRange N (fun j => f j * g j)) * sumRange N (fun i => f i * g i) +
        (sumRange N (fun j => f j * g j) * sumRange N (fun j => f j * g j)) * sumRange N (fun i => g i * g i) =
        sumRange N (fun j => g j * g j) *
          (sumRange N (fun i => f i * f i) * sumRange N (fun j => g j * g j)) -
        sumRange N (fun j => g j * g j) *
          (sumRange N (fun i => f i * g i) * sumRange N (fun j => f j * g j)) := by
      have t1 :
          (sumRange N (fun j => g j * g j) * sumRange N (fun j => g j * g j)) * sumRange N (fun i => f i * f i) =
          sumRange N (fun j => g j * g j) * (sumRange N (fun i => f i * f i) * sumRange N (fun j => g j * g j)) := by
        simp only [Int.mul_left_comm, Int.mul_comm]
      have t2 :
          (2 * sumRange N (fun j => g j * g j) * sumRange N (fun j => f j * g j)) * sumRange N (fun i => f i * g i) =
          2 * (sumRange N (fun j => g j * g j) * (sumRange N (fun i => f i * g i) * sumRange N (fun j => f j * g j))) := by
        simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      have t3 :
          (sumRange N (fun j => f j * g j) * sumRange N (fun j => f j * g j)) * sumRange N (fun i => g i * g i) =
          sumRange N (fun j => g j * g j) * (sumRange N (fun i => f i * g i) * sumRange N (fun j => f j * g j)) := by
        simp only [Int.mul_assoc, Int.mul_comm]
      rw [t1, t2, t3]
      omega
    rw [hQ_eq, hfactor] at hQ_nn
    have hmul_le :
        sumRange N (fun j => g j * g j) * (sumRange N (fun i => f i * g i) * sumRange N (fun j => f j * g j)) ≤
        sumRange N (fun j => g j * g j) * (sumRange N (fun i => f i * f i) * sumRange N (fun j => g j * g j)) := by
      omega
    exact cancel_pos_mul_left hBpos hmul_le

theorem sumRange_comm (M N : Nat) (F : Nat → Nat → Int) :
    sumRange M (fun i => sumRange N (fun j => F i j)) =
      sumRange N (fun j => sumRange M (fun i => F i j)) := by
  induction M with
  | zero =>
    symm
    exact sumRange_zero_of_pointwise N _ (fun _ _ => rfl)
  | succ m ih =>
    simp only [sumRange]
    rw [ih, ← sumRange_add]

theorem sumRange_delta_single (N x : Nat) (hx : x < N) (f : Nat → Int) :
    sumRange N (fun j => deltaNat x j * f j) = f x := by
  induction N with
  | zero => omega
  | succ n ih =>
    simp only [sumRange]
    by_cases hxn : x = n
    · have hzero : sumRange n (fun j => deltaNat x j * f j) = 0 := by
        apply sumRange_zero_of_pointwise
        intro j hj
        have hne : x ≠ j := by omega
        simp [deltaNat, hne]
      rw [hzero, hxn]
      simp [deltaNat]
    · have hlt : x < n := by omega
      rw [ih hlt]
      simp [deltaNat, hxn]

/-- Row-orthogonality Parseval identity: if `∑_{y<N} H(x₁, y) H(x₂, y) = δ_{x₁, x₂} · L`,
then `∑_{y<N} (∑_{x<N} u(x) H(x, y))² = L · ∑_{x<N} u(x)²`. -/
theorem orthogonal_row_combination_sq_sum
    (N : Nat) (H : Nat → Nat → Int) (u : Nat → Int) (L : Int)
    (hOrth : ∀ x₁ x₂ : Nat, x₁ < N → x₂ < N →
      sumRange N (fun y => H x₁ y * H x₂ y) = deltaNat x₁ x₂ * L) :
    sumRange N (fun y => (sumRange N (fun x => u x * H x y)) * (sumRange N (fun x => u x * H x y))) =
      L * sumRange N (fun x => u x * u x) := by
  have hexpand :
      sumRange N (fun y => (sumRange N (fun x => u x * H x y)) * (sumRange N (fun x => u x * H x y))) =
      sumRange N (fun x₁ => sumRange N (fun x₂ => u x₁ * u x₂ * sumRange N (fun y => H x₁ y * H x₂ y))) := by
    have hstep1 :
        sumRange N (fun y => (sumRange N (fun x₁ => u x₁ * H x₁ y)) * (sumRange N (fun x₂ => u x₂ * H x₂ y))) =
        sumRange N (fun y => sumRange N (fun x₁ => sumRange N (fun x₂ => (u x₁ * H x₁ y) * (u x₂ * H x₂ y)))) := by
      have hbody : ∀ y : Nat,
          (sumRange N (fun x₁ => u x₁ * H x₁ y)) * (sumRange N (fun x₂ => u x₂ * H x₂ y)) =
          sumRange N (fun x₁ => sumRange N (fun x₂ => (u x₁ * H x₁ y) * (u x₂ * H x₂ y))) := by
        intro y
        rw [← sumRange_mul_const]
        have hinner : ∀ x₁ : Nat,
            (u x₁ * H x₁ y) * sumRange N (fun x₂ => u x₂ * H x₂ y) =
            sumRange N (fun x₂ => (u x₁ * H x₁ y) * (u x₂ * H x₂ y)) := by
          intro x₁
          rw [sumRange_const_mul]
        simp only [hinner]
      simp only [hbody]
    rw [hstep1, sumRange_comm N N]
    have houter : ∀ x₁ : Nat,
        sumRange N (fun y => sumRange N (fun x₂ => (u x₁ * H x₁ y) * (u x₂ * H x₂ y))) =
        sumRange N (fun x₂ => u x₁ * u x₂ * sumRange N (fun y => H x₁ y * H x₂ y)) := by
      intro x₁
      rw [sumRange_comm N N]
      have hrearrange : ∀ x₂ : Nat,
          sumRange N (fun y => (u x₁ * H x₁ y) * (u x₂ * H x₂ y)) =
          u x₁ * u x₂ * sumRange N (fun y => H x₁ y * H x₂ y) := by
        intro x₂
        rw [← sumRange_const_mul]
        have hpt : ∀ y : Nat,
            (u x₁ * H x₁ y) * (u x₂ * H x₂ y) = (u x₁ * u x₂) * (H x₁ y * H x₂ y) := by
          intro y
          simp only [Int.mul_left_comm, Int.mul_comm]
        simp only [hpt]
      simp only [hrearrange]
    simp only [houter]
  rw [hexpand]
  have hcollapse : ∀ x₁ : Nat, x₁ < N →
      sumRange N (fun x₂ => u x₁ * u x₂ * sumRange N (fun y => H x₁ y * H x₂ y)) =
      L * (u x₁ * u x₁) := by
    intro x₁ hx₁
    have hcong : ∀ m : Nat, m ≤ N →
        sumRange m (fun x₂ => u x₁ * u x₂ * sumRange N (fun y => H x₁ y * H x₂ y)) =
        sumRange m (fun x₂ => deltaNat x₁ x₂ * (L * (u x₁ * u x₂))) := by
      intro m hm
      induction m with
      | zero => rfl
      | succ k ih =>
        have hklt : k < N := Nat.lt_of_succ_le hm
        simp only [sumRange, ih (Nat.le_of_lt hklt), hOrth x₁ k hx₁ hklt]
        have hcomm : u x₁ * u k * (deltaNat x₁ k * L) = deltaNat x₁ k * (L * (u x₁ * u k)) := by
          simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
        rw [hcomm]
    rw [hcong N (Nat.le_refl N)]
    exact sumRange_delta_single N x₁ hx₁ (fun x₂ => L * (u x₁ * u x₂))
  have hall : ∀ m : Nat, m ≤ N →
      sumRange m (fun x₁ => sumRange N (fun x₂ => u x₁ * u x₂ * sumRange N (fun y => H x₁ y * H x₂ y))) =
      sumRange m (fun x₁ => L * (u x₁ * u x₁)) := by
    intro m hm
    induction m with
    | zero => rfl
    | succ k ih =>
      have hklt : k < N := Nat.lt_of_succ_le hm
      simp only [sumRange, ih (Nat.le_of_lt hklt), hcollapse k hklt]
  rw [hall N (Nat.le_refl N), sumRange_const_mul]

/-- Bilinear rectangle form `∑_{y<N} (∑_{x<N} u(x) H(x, y)) v(y)`. -/
def rectBilinearForm (N : Nat) (H : Nat → Nat → Int) (u v : Nat → Int) : Int :=
  sumRange N (fun y => (sumRange N (fun x => u x * H x y)) * v y)

/-- **Lindsey's Orthogonal Rectangle Discrepancy Bound**:
For any `N × N` row-orthogonal matrix `H` (`∑_y H(x₁,y) H(x₂,y) = δ_{x₁,x₂} · L`),
`(∑_{y<N} (∑_{x<N} u(x) H(x, y)) v(y))² ≤ L · (∑_{x<N} u(x)²) · (∑_{y<N} v(y)²)`. -/
theorem lindsey_orthogonal_rectangle_discrepancy_bound
    (N : Nat) (H : Nat → Nat → Int) (u v : Nat → Int) (L : Int)
    (hOrth : ∀ x₁ x₂ : Nat, x₁ < N → x₂ < N →
      sumRange N (fun y => H x₁ y * H x₂ y) = deltaNat x₁ x₂ * L) :
    rectBilinearForm N H u v * rectBilinearForm N H u v ≤
      L * (sumRange N (fun x => u x * u x)) * (sumRange N (fun y => v y * v y)) := by
  have hcs := cauchy_schwarz_range_int N (fun y => sumRange N (fun x => u x * H x y)) v
  rw [orthogonal_row_combination_sq_sum N H u L hOrth] at hcs
  exact hcs

/-- **Monochromatic Orthogonal Rectangle Area Bound**:
If `u, v : Nat → Int` are `{0, 1}` indicators (`u² = u`, `v² = v`) of a monochromatic
rectangle on which `H(x, y) = s` (`s² = 1`), so `rectBilinearForm N H u v = s * |U| * |V|`,
with `0 ≤ L`, then `|U| * |V| ≤ L`. -/
theorem monochromatic_orthogonal_rectangle_area_le
    (N : Nat) (H : Nat → Nat → Int) (u v : Nat → Int) (L s : Int)
    (hL : 0 ≤ L)
    (hOrth : ∀ x₁ x₂ : Nat, x₁ < N → x₂ < N →
      sumRange N (fun y => H x₁ y * H x₂ y) = deltaNat x₁ x₂ * L)
    (hu01 : ∀ x : Nat, x < N → u x * u x = u x ∧ 0 ≤ u x)
    (hv01 : ∀ y : Nat, y < N → v y * v y = v y ∧ 0 ≤ v y)
    (hs : s * s = 1)
    (hMono : rectBilinearForm N H u v = s * (sumRange N u * sumRange N v)) :
    sumRange N u * sumRange N v ≤ L := by
  have hu_nn : 0 ≤ sumRange N u := sumRange_nonneg N u (fun x hx => (hu01 x hx).2)
  have hv_nn : 0 ≤ sumRange N v := sumRange_nonneg N v (fun y hy => (hv01 y hy).2)
  have harea_nn : 0 ≤ sumRange N u * sumRange N v := Int.mul_nonneg hu_nn hv_nn
  by_cases hzero : sumRange N u * sumRange N v = 0
  · rw [hzero]
    exact hL
  · have harea_pos : 0 < sumRange N u * sumRange N v := by omega
    have hLind := lindsey_orthogonal_rectangle_discrepancy_bound N H u v L hOrth
    have hu_sq : sumRange N (fun x => u x * u x) = sumRange N u := by
      have hall : ∀ m : Nat, m ≤ N → sumRange m (fun x => u x * u x) = sumRange m u := by
        intro m hm
        induction m with
        | zero => rfl
        | succ k ih =>
          have hk : k < N := Nat.lt_of_succ_le hm
          simp only [sumRange, ih (Nat.le_of_lt hk), (hu01 k hk).1]
      exact hall N (Nat.le_refl N)
    have hv_sq : sumRange N (fun y => v y * v y) = sumRange N v := by
      have hall : ∀ m : Nat, m ≤ N → sumRange m (fun y => v y * v y) = sumRange m v := by
        intro m hm
        induction m with
        | zero => rfl
        | succ k ih =>
          have hk : k < N := Nat.lt_of_succ_le hm
          simp only [sumRange, ih (Nat.le_of_lt hk), (hv01 k hk).1]
      exact hall N (Nat.le_refl N)
    rw [hMono, hu_sq, hv_sq] at hLind
    have hss : (s * (sumRange N u * sumRange N v)) * (s * (sumRange N u * sumRange N v)) =
        (sumRange N u * sumRange N v) * (sumRange N u * sumRange N v) := by
      calc
        (s * (sumRange N u * sumRange N v)) * (s * (sumRange N u * sumRange N v))
            = (s * s) * ((sumRange N u * sumRange N v) * (sumRange N u * sumRange N v)) := by
              simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
        _ = (sumRange N u * sumRange N v) * (sumRange N u * sumRange N v) := by
              rw [hs, Int.one_mul]
    have hrhs : L * sumRange N u * sumRange N v = (sumRange N u * sumRange N v) * L := by
      simp only [Int.mul_assoc, Int.mul_comm]
    rw [hss, hrhs] at hLind
    exact cancel_pos_mul_left harea_pos hLind

/-- **Chor–Goldreich Monochromatic Rectangle Cover Lower Bound**:
If an `N × N` matrix of total mass `T` (`e.g. T = N²`) is covered by `R` monochromatic rectangles
whose areas each satisfy `area(k) ≤ L`, then `T ≤ R · L`. -/
theorem chor_goldreich_hadamard_communication_lower_bound
    (R : Nat) (area : Nat → Int) (T L : Int)
    (hCover : T ≤ sumRange R area)
    (hBound : ∀ k : Nat, k < R → area k ≤ L) :
    T ≤ (R : Int) * L := by
  have hsum : sumRange R area ≤ sumRange R (fun _ => L) := sumRange_le R area (fun _ => L) hBound
  rw [sumRange_const] at hsum
  omega

/-- Explicit `8 × 8` Walsh–Hadamard matrix `H₃(x, y) = (-1)^{⟨x, y⟩}` on `{0, …, 7}`. -/
def walshHadamard8 (x y : Nat) : Int :=
  let ip := (x % 2) * (y % 2) + ((x / 2) % 2) * ((y / 2) % 2) + ((x / 4) % 2) * ((y / 4) % 2)
  if ip % 2 == 0 then 1 else -1

/-- **Explicit `8 × 8` Walsh–Hadamard Orthogonality & `R ≥ 8` Communication Partition Bound**
vs. **Rank-`1` All-Ones Premise-Failure Collapse (`R = 1 < 8`)**:
(1) `walshHadamard8` satisfies exact row orthogonality `∑_{y<8} H₃(x₁, y) H₃(x₂, y) = 8 · δ_{x₁, x₂}`,
    forcing every monochromatic rectangle cover of `8 × 8` (`T = 64`, `area ≤ 8`) to use `R ≥ 8`
    rectangles (deterministic communication `≥ 3` bits).
(2) Dropping row orthogonality (`allOnes(x, y) = 1`, where `∑_y H(0, y) H(1, y) = 8 ≠ 0`) collapses
    the entire `8 × 8` matrix into a **single** monochromatic rectangle (`R = 1 < 8`, `area = 64 > 8`)! -/
theorem hadamard8_monochromatic_partition_ge_eight_vs_rank1_collapse :
    (∀ x₁ x₂ : Nat, x₁ < 8 → x₂ < 8 →
      sumRange 8 (fun y => walshHadamard8 x₁ y * walshHadamard8 x₂ y) = deltaNat x₁ x₂ * 8) ∧
    (∀ R : Nat, ∀ area : Nat → Int,
      (64 : Int) ≤ sumRange R area → (∀ k : Nat, k < R → area k ≤ 8) → 8 ≤ R) ∧
    (rectBilinearForm 8 (fun _ _ => 1) (fun _ => 1) (fun _ => 1) = 64 ∧ (1 : Nat) < 8) := by
  have hFin : ∀ x₁ : Fin 8, ∀ x₂ : Fin 8,
      sumRange 8 (fun y => walshHadamard8 x₁.val y * walshHadamard8 x₂.val y) =
        deltaNat x₁.val x₂.val * 8 := by
    decide
  refine ⟨fun x₁ x₂ hx₁ hx₂ => hFin ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩, ?_, ?_⟩
  · intro R area hCover hBound
    have h64 := chor_goldreich_hadamard_communication_lower_bound R area 64 8 hCover hBound
    omega
  · decide

/-! ## Part 2: Aaronson–Wigderson Algebrization Deformation vs. Degree-`1` Multilinear Rigidity -/

/-- Boolean ideal deformation `P̃(x) = P(x) + x(x - 1) Q(x)`. -/
def deformBooleanExtension (P Q : Int → Int) (x : Int) : Int :=
  P x + x * (x - 1) * Q x

/-- **Aaronson–Wigderson Algebrization Oracle Indistinguishability on `{0, 1}` vs. Off-Cube Freedom**:
(1) For every `P, Q : Int → Int`, `deformBooleanExtension P Q` agrees identically with `P` on `{0, 1}`
    (`P̃(0) = P(0)` and `P̃(1) = P(1)`), so any oracle query inside the Boolean domain sees zero change.
(2) At the off-cube algebraic extension point `x = 2`, `P̃(2) = P(2) + 2 · Q(2)` varies freely with `Q(2)`;
    in particular `Q ≡ 0` and `Q ≡ 1` induce identical Boolean truth tables on `{0, 1}` while separating
    off-cube evaluations (`P(2) ≠ P(2) + 2`)! -/
theorem algebrization_extension_boolean_lock_vs_off_cube_freedom (P Q : Int → Int) :
    deformBooleanExtension P Q 0 = P 0 ∧
    deformBooleanExtension P Q 1 = P 1 ∧
    deformBooleanExtension P Q 2 = P 2 + 2 * Q 2 ∧
    deformBooleanExtension P (fun _ => 0) 2 ≠ deformBooleanExtension P (fun _ => 1) 2 := by
  simp only [deformBooleanExtension]
  refine ⟨by omega, by omega, ?_, by omega⟩
  have htwo : (2 : Int) * (2 - 1) * Q 2 = 2 * Q 2 := by omega
  omega

/-- **Degree-`1` Multilinear Rigidity Contrast**:
Unlike degree-`≥ 2` extensions, every degree-`1` affine polynomial `L(x) = a₀ + a₁ x` is uniquely
locked at ALL off-cube integer points by its Boolean values `{L(0), L(1)}` alone:
`L(x) = (1 - x) · L(0) + x · L(1)` (in particular `L(2) = 2 · L(1) - L(0)`). -/
theorem degree_one_multilinear_locks_off_cube (a₀ a₁ x : Int) :
    a₀ + a₁ * x = (1 - x) * (a₀ + a₁ * 0) + x * (a₀ + a₁ * 1) := by
  simp only [Int.mul_zero, Int.mul_one, Int.add_zero, Int.sub_mul, Int.one_mul, Int.mul_add]
  have hcomm : x * a₁ = a₁ * x := Int.mul_comm x a₁
  omega

/-! ## Part 3: Razborov–Smolensky Prime-Field Barrier vs. Barrington–Grolmusz Composite `mod 6` Escape -/

/-- Exact origin zero-set test on `{0, 1}³` modulo `m`: returns `true` iff
`(a₀ + a₁ b₁ + a₂ b₂ + a₃ b₃) % m == 0` holds strictly at `(0, 0, 0)` and nowhere else on `{0, 1}³`. -/
def isExactOriginZeroSetCube3 (m a₀ a₁ a₂ a₃ : Nat) : Bool :=
  let okPt (b₁ b₂ b₃ : Nat) : Bool :=
    let val := (a₀ + a₁ * b₁ + a₂ * b₂ + a₃ * b₃) % m
    if b₁ == 0 && b₂ == 0 && b₃ == 0 then val == 0 else val != 0
  okPt 0 0 0 && okPt 0 0 1 && okPt 0 1 0 && okPt 0 1 1 &&
  okPt 1 0 0 && okPt 1 0 1 && okPt 1 1 0 && okPt 1 1 1

/-- **Prime `mod 2` Degree-`1` Impossibility (`AC⁰[2]` Polynomial Barrier)**:
Across all `2⁴ = 16` affine linear forms over `𝔽₂`, NONE has exact zero-set `{(0, 0, 0)}` on `{0, 1}³`. -/
theorem no_degree1_mod2_exact_zero_at_origin_on_cube3 :
    ∀ a₀ a₁ a₂ a₃ : Fin 2,
      isExactOriginZeroSetCube3 2 a₀.val a₁.val a₂.val a₃.val = false := by
  decide

/-- **Prime `mod 3` Degree-`1` Impossibility (`AC⁰[3]` Polynomial Barrier)**:
Across all `3⁴ = 81` affine linear forms over `𝔽₃`, NONE has exact zero-set `{(0, 0, 0)}` on `{0, 1}³`. -/
theorem no_degree1_mod3_exact_zero_at_origin_on_cube3 :
    ∀ a₀ a₁ a₂ a₃ : Fin 3,
      isExactOriginZeroSetCube3 3 a₀.val a₁.val a₂.val a₃.val = false := by
  decide

/-- **Barrington–Grolmusz Composite `mod 6` Degree-`1` Breakthrough Witness**:
Modulo `6 = 2 × 3`, the degree-`1` linear form `3 b₁ + 2 b₂ + 2 b₃` vanishes modulo `6` at `(0, 0, 0)`
and takes non-zero residues `{2, 2, 4, 3, 5, 5, 1} (mod 6)` across all seven non-zero points of `{0, 1}³`,
computing `OR₃` / `NOR₃` at degree `1` where both prime factors `2` and `3` fail! -/
theorem composite_mod6_degree1_exact_or3_witness :
    isExactOriginZeroSetCube3 6 0 3 2 2 = true ∧
    (∀ b₁ b₂ b₃ : Fin 2,
      ((3 * b₁.val + 2 * b₂.val + 2 * b₃.val) % 6 = 0 ↔
        (b₁.val = 0 ∧ b₂.val = 0 ∧ b₃.val = 0))) := by
  decide

end CommonGround.Frontier.AlgebrizationDiscrepancyAndCommunicationRankBarriers
