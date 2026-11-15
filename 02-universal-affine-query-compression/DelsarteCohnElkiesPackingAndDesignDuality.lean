/-
  Delsarte–Cohn–Elkies Primal-Dual Linear Programming Bounds:
  Packing Upper Bounds, Viazovska-Style Double-Zero Complementary Slackness & Universal Cubature `t`-Design Lower Bounds
  ======================================================================================================================
  Pure-core Lean 4.33.0 formalization (`0` external imports, `0` sorrys) unifying:
  1. Universal Finite Bochner–Parseval Double-Sum Identity (`bochner_parseval_double_sum_identity`):
     `∑_{x<N} ∑_{y<N} C(x) C(y) F(x, y) = ∑_{r<K} w_r (∑_{x<N} C(x) χ_r(x))²`
     for arbitrary `N, K : Nat` and arbitrary feature/character dictionaries `χ_r`.
  2. Delsarte–Cohn–Elkies Packing Upper Bound & Complementary Slackness (`delsarte_cohn_elkies_universal_packing_bound`,
     `delsarte_cohn_elkies_complementary_slackness_iff`):
     Spectral positivity (`w_r ≥ 0`) + spatial sign barrier (`F(x, y) ≤ 0` on distinct `x ≠ y` in `C`)
     proves `w_0 · |C|² ≤ F_diag · |C|` (`w_0 · |C| ≤ F_diag` for `|C| ≥ 1`), with equality iff every higher
     spectral mode `r ≥ 1` with `w_r > 0` vanishes AND every distinct pair in `C` sits at a root `F(x, y) = 0`.
  3. Viazovska-Style Double-Zero Magic Kernel on `{0, 1}³` (`viazovska_style_double_zero_parity_code_exact_attainment`):
     Walsh weights `w = (3, 2, 2, 1, 2, 1, 1, 0)` produce radial profile `F(d) = (12, 4, 0, 0)` vanishing at both
     `d = 2` and `d = 3`, certifying `|C| ≤ 4` for all minimum-distance-`2` codes and exact attainment `|C*| = 4`
     on the `[3, 2, 2]` parity code `{000, 011, 101, 110}`.
  4. Dual Universal Cubature / Spherical `t`-Design Lower Bound (`delsarte_quadrature_design_lower_bound` +
     `degree_one_walsh_design_tightness_witness`):
     Spatial non-negativity (`G(x, y) ≥ 0`) + exact harmonic annihilation (`modeMoment_r(D) = 0` for `1 ≤ r < K`)
     proves the Delsarte–Goethals–Seidel coreset cardinality lower bound `G_diag · |D| ≤ w_0 · |D|²`, attained with
     equality `|D*| = 2` by `{(0,0), (1,1)}` on `{0, 1}²` for `G(x,y) = 2 + χ_{01}(x)χ_{01}(y) + χ_{10}(x)χ_{10}(y)`.
  5. Sharp Premise-Failure Counterexamples (`negative_fourier_mode_and_positive_off_diagonal_packing_failures`):
     Dropping `w_r ≥ 0` (`w_{11} = -2 < 0` on `{0, 1}²`) breaks `w_0 |C| ≤ F_diag` (`2 > 1`), and dropping
     `F(x, y) ≤ 0` (`F_{pos}(x, y) ∈ {0, 2}`) breaks `w_0 |C| ≤ F_diag` (`4 > 2`).
-/

namespace CommonGround.UniversalAffineQueryCompression.DelsarteCohnElkiesDuality

/-! ## 1. Finite Integer Summation & Algebraic Lemmas -/

/-- Sum `f 0 + f 1 + ... + f (N - 1)` over `{0, ..., N - 1}`. -/
def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

theorem sumRange_zero_const (N : Nat) : sumRange N (fun _ => (0 : Int)) = 0 := by
  induction N with
  | zero => rfl
  | succ n ih => simp [sumRange, ih]

theorem sumRange_add (N : Nat) (f g : Nat → Int) :
    sumRange N (fun i => f i + g i) = sumRange N f + sumRange N g := by
  induction N with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange, ih]
    omega

theorem sumRange_mul_left (N : Nat) (c : Int) (f : Nat → Int) :
    sumRange N (fun i => c * f i) = c * sumRange N f := by
  induction N with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange, ih, Int.mul_add]

theorem sumRange_mul_right (N : Nat) (f : Nat → Int) (c : Int) :
    sumRange N (fun i => f i * c) = sumRange N f * c := by
  induction N with
  | zero => simp [sumRange]
  | succ n ih =>
    simp only [sumRange, ih, Int.add_mul]

theorem sumRange_congr {N : Nat} {f g : Nat → Int}
    (h : ∀ i, i < N → f i = g i) :
    sumRange N f = sumRange N g := by
  induction N with
  | zero => rfl
  | succ n ih =>
    have ih' := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hn := h n (Nat.lt_succ_self n)
    simp only [sumRange, ih', hn]

theorem sumRange_le {N : Nat} {f g : Nat → Int}
    (h : ∀ i, i < N → f i ≤ g i) :
    sumRange N f ≤ sumRange N g := by
  induction N with
  | zero => simp [sumRange]
  | succ n ih =>
    have ih' := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hn := h n (Nat.lt_succ_self n)
    simp only [sumRange]
    omega

theorem sumRange_eq_zero_of_nonpos_eq {N : Nat} {f g : Nat → Int}
    (hle : ∀ i, i < N → f i ≤ g i)
    (heq : sumRange N f = sumRange N g) :
    ∀ i, i < N → f i = g i := by
  induction N with
  | zero =>
    intro i hi
    exact False.elim (Nat.not_lt_zero i hi)
  | succ n ih =>
    simp only [sumRange] at heq
    have hsub : sumRange n f ≤ sumRange n g :=
      sumRange_le (fun j hj => hle j (Nat.lt_succ_of_lt hj))
    have hn : f n ≤ g n := hle n (Nat.lt_succ_self n)
    have hsum_eq : sumRange n f = sumRange n g := by omega
    have hn_eq : f n = g n := by omega
    intro i hi
    by_cases hlt : i < n
    · exact ih (fun j hj => hle j (Nat.lt_succ_of_lt hj)) hsum_eq i hlt
    · have hieq : i = n := by omega
      subst hieq
      exact hn_eq

theorem sumRange_swap (N K : Nat) (F : Nat → Nat → Int) :
    sumRange N (fun x => sumRange K (fun r => F x r)) =
    sumRange K (fun r => sumRange N (fun x => F x r)) := by
  induction N with
  | zero =>
    simp [sumRange, sumRange_zero_const]
  | succ n ih =>
    simp only [sumRange, ih]
    exact (sumRange_add K (fun r => sumRange n (fun x => F x r)) (fun r => F n r)).symm

theorem int_sq_nonneg (a : Int) : 0 ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -a := by omega
    have hsq : (-a) * (-a) = a * a := by simp [Int.neg_mul_neg]
    rw [← hsq]
    exact Int.mul_nonneg hn hn

theorem cancel_pos_mul_right {a b m : Int} (hm : 1 ≤ m) (hle : a * m ≤ b * m) : a ≤ b := by
  by_cases h : a ≤ b
  · exact h
  · have hGt : b + 1 ≤ a := by omega
    have hStrict : (b + 1) * m ≤ a * m := Int.mul_le_mul_of_nonneg_right hGt (by omega)
    have hExp : (b + 1) * m = b * m + m := by simp [Int.add_mul]
    omega

/-! ## 2. Bochner–Mercer Kernel & Universal Parseval Double-Sum Identity -/

/-- Finite Bochner–Mercer harmonic kernel `F(x, y) = ∑_{r<K} w_r χ_r(x) χ_r(y)`. -/
def bochnerKernel (K : Nat) (w : Nat → Int) (chi : Nat → Nat → Int) (x y : Nat) : Int :=
  sumRange K (fun r => w r * (chi r x * chi r y))

/-- Spectral mode moment `M_r(C) = ∑_{x<N} C(x) χ_r(x)`. -/
def modeMoment (N : Nat) (C : Nat → Int) (chi : Nat → Nat → Int) (r : Nat) : Int :=
  sumRange N (fun x => C x * chi r x)

/--
**Theorem 1 (Universal Bochner–Parseval Double-Sum Identity)**:
For any finite state size `N`, mode count `K`, weights `w`, feature dictionary `chi`, and measure `C`,
the spatial quadratic energy equals the spectral weighted squared-moment sum:
`∑_{x<N} ∑_{y<N} C(x) C(y) F(x, y) = ∑_{r<K} w_r · (modeMoment_r(C))²`.
-/
theorem bochner_parseval_double_sum_identity
    (N K : Nat) (w : Nat → Int) (chi : Nat → Nat → Int) (C : Nat → Int) :
    sumRange N (fun x => sumRange N (fun y => C x * C y * bochnerKernel K w chi x y)) =
    sumRange K (fun r => w r * (modeMoment N C chi r * modeMoment N C chi r)) := by
  have h1 :
      sumRange N (fun x => sumRange N (fun y => C x * C y * bochnerKernel K w chi x y)) =
      sumRange N (fun x => sumRange N (fun y =>
        sumRange K (fun r => w r * ((C x * chi r x) * (C y * chi r y))))) := by
    apply sumRange_congr
    intro x _
    apply sumRange_congr
    intro y _
    unfold bochnerKernel
    rw [← sumRange_mul_left K (C x * C y)]
    apply sumRange_congr
    intro r _
    simp only [Int.mul_left_comm, Int.mul_comm]
  rw [h1]
  have h2 :
      sumRange N (fun x => sumRange N (fun y =>
        sumRange K (fun r => w r * ((C x * chi r x) * (C y * chi r y))))) =
      sumRange N (fun x => sumRange K (fun r =>
        sumRange N (fun y => w r * ((C x * chi r x) * (C y * chi r y))))) := by
    apply sumRange_congr
    intro x _
    exact sumRange_swap N K (fun y r => w r * ((C x * chi r x) * (C y * chi r y)))
  rw [h2]
  rw [sumRange_swap N K]
  apply sumRange_congr
  intro r _
  have h3 :
      sumRange N (fun x => sumRange N (fun y => w r * ((C x * chi r x) * (C y * chi r y)))) =
      sumRange N (fun x => w r * ((C x * chi r x) * modeMoment N C chi r)) := by
    apply sumRange_congr
    intro x _
    have hy :
        sumRange N (fun y => w r * ((C x * chi r x) * (C y * chi r y))) =
        sumRange N (fun y => (w r * (C x * chi r x)) * (C y * chi r y)) := by
      apply sumRange_congr
      intro y _
      simp only [Int.mul_assoc]
    rw [hy, sumRange_mul_left, Int.mul_assoc]
    rfl
  rw [h3]
  have hx :
      sumRange N (fun x => w r * ((C x * chi r x) * modeMoment N C chi r)) =
      w r * sumRange N (fun x => (C x * chi r x) * modeMoment N C chi r) :=
    sumRange_mul_left N (w r) (fun x => (C x * chi r x) * modeMoment N C chi r)
  rw [hx, sumRange_mul_right]
  rfl

/-! ## 3. Delsarte–Cohn–Elkies Packing Upper Bound & Complementary Slackness -/

/-- Kronecker indicator `deltaNat x y = 1` if `x = y` else `0`. -/
def deltaNat (x y : Nat) : Int :=
  if x = y then 1 else 0

theorem sumRange_deltaNat {N x : Nat} (hx : x < N) (v : Int) :
    sumRange N (fun y => deltaNat x y * v) = v := by
  induction N with
  | zero => exact False.elim (Nat.not_lt_zero x hx)
  | succ n ih =>
    simp only [sumRange]
    by_cases hlt : x < n
    · have hne : x ≠ n := by omega
      rw [ih hlt]
      have hdn : deltaNat x n = 0 := by simp [deltaNat, hne]
      rw [hdn]
      omega
    · have heq : x = n := by omega
      subst heq
      have h0 : sumRange x (fun y => deltaNat x y * v) = sumRange x (fun _ => (0 : Int)) := by
        apply sumRange_congr
        intro y hy
        have hxy : x ≠ y := by omega
        have hdy : deltaNat x y = 0 := by simp [deltaNat, hxy]
        rw [hdy, Int.zero_mul]
      rw [h0, sumRange_zero_const]
      have hdx : deltaNat x x = 1 := by simp [deltaNat]
      rw [hdx]
      omega

theorem sumRange_head_le_nonneg {K : Nat} (hK : 1 ≤ K) {g : Nat → Int}
    (hnonneg : ∀ r, 1 ≤ r → r < K → 0 ≤ g r) :
    g 0 ≤ sumRange K g := by
  induction K with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      simp [sumRange]
    · have hk1 : 1 ≤ k := by omega
      have ih' := ih hk1 (fun r hr1 hrk => hnonneg r hr1 (Nat.lt_succ_of_lt hrk))
      have hlast := hnonneg k hk1 (Nat.lt_succ_self k)
      simp only [sumRange]
      omega

theorem modeMoment_zero_eq_card (N : Nat) (C : Nat → Int) (chi : Nat → Nat → Int)
    (hchi0 : ∀ x, x < N → chi 0 x = 1) :
    modeMoment N C chi 0 = sumRange N C := by
  unfold modeMoment
  apply sumRange_congr
  intro x hx
  simp [hchi0 x hx]

/--
**Theorem 2A (Delsarte–Cohn–Elkies Universal Packing Upper Bound)**:
Under spectral non-negativity (`w_r ≥ 0` for `r < K`), trivial zero mode (`χ_0 = 1`),
`{0, 1}` code indicator `C`, diagonal bound `F(x, x) ≤ Fdiag` on `supp(C)`, and off-diagonal
forbidden-zone sign barrier `F(x, y) ≤ 0` for distinct `x ≠ y` in `supp(C)`,
the code size `M = ∑_{x<N} C(x)` satisfies:
1. `w 0 * (M * M) ≤ Fdiag * M`, and
2. if `1 ≤ M` (`C` is non-empty), `w 0 * M ≤ Fdiag`.
-/
theorem delsarte_cohn_elkies_universal_packing_bound
    (N K : Nat) (w : Nat → Int) (chi : Nat → Nat → Int) (C : Nat → Int) (Fdiag : Int)
    (hK : 1 ≤ K)
    (hw : ∀ r, r < K → 0 ≤ w r)
    (hchi0 : ∀ x, x < N → chi 0 x = 1)
    (hC01 : ∀ x, x < N → C x = 0 ∨ C x = 1)
    (hDiag : ∀ x, x < N → C x = 1 → bochnerKernel K w chi x x ≤ Fdiag)
    (hOff : ∀ x y, x < N → y < N → x ≠ y → C x = 1 → C y = 1 → bochnerKernel K w chi x y ≤ 0) :
    w 0 * (sumRange N C * sumRange N C) ≤ Fdiag * sumRange N C ∧
    (1 ≤ sumRange N C → w 0 * sumRange N C ≤ Fdiag) := by
  have hSpec :
      w 0 * (sumRange N C * sumRange N C) ≤
      sumRange K (fun r => w r * (modeMoment N C chi r * modeMoment N C chi r)) := by
    have h0 : modeMoment N C chi 0 = sumRange N C := modeMoment_zero_eq_card N C chi hchi0
    have hle := sumRange_head_le_nonneg hK
      (g := fun r => w r * (modeMoment N C chi r * modeMoment N C chi r))
      (fun r _ hrK => Int.mul_nonneg (hw r hrK) (int_sq_nonneg (modeMoment N C chi r)))
    simpa [h0] using hle
  have hPointwise :
      ∀ x, x < N →
        sumRange N (fun y => C x * C y * bochnerKernel K w chi x y) ≤ Fdiag * C x := by
    intro x hx
    have hInner :
        sumRange N (fun y => C x * C y * bochnerKernel K w chi x y) ≤
        sumRange N (fun y => deltaNat x y * (Fdiag * C x)) := by
      apply sumRange_le
      intro y hy
      by_cases hxy : x = y
      · subst hxy
        simp only [deltaNat, ite_true, Int.one_mul]
        rcases hC01 x hx with hx0 | hx1
        · simp [hx0]
        · simp only [hx1, Int.one_mul, Int.mul_one]
          exact hDiag x hx hx1
      · simp only [deltaNat, hxy, ite_false, Int.zero_mul]
        rcases hC01 x hx with hx0 | hx1
        · simp [hx0]
        · rcases hC01 y hy with hy0 | hy1
          · simp [hy0]
          · simp only [hx1, hy1, Int.one_mul]
            exact hOff x y hx hy hxy hx1 hy1
    rw [sumRange_deltaNat hx (Fdiag * C x)] at hInner
    exact hInner
  have hSpat :
      sumRange N (fun x => sumRange N (fun y => C x * C y * bochnerKernel K w chi x y)) ≤
      Fdiag * sumRange N C := by
    have hsum := sumRange_le hPointwise
    rw [sumRange_mul_left N Fdiag C] at hsum
    exact hsum
  have hQuad : w 0 * (sumRange N C * sumRange N C) ≤ Fdiag * sumRange N C := by
    have hEq := bochner_parseval_double_sum_identity N K w chi C
    omega
  refine ⟨hQuad, ?_⟩
  intro hM1
  have hMul : (w 0 * sumRange N C) * sumRange N C ≤ Fdiag * sumRange N C := by
    simpa [Int.mul_assoc] using hQuad
  exact cancel_pos_mul_right hM1 hMul

/--
**Theorem 2B (Complementary Slackness Characterization — Viazovska / Delsarte Root Locking)**:
When `F(x, x) = Fdiag` on `supp(C)`, equality `w 0 * |C|² = Fdiag * |C|` holds if and only if
1. every higher spectral energy term vanishes (`∑_{r<K} w_r M_r(C)² = w_0 |C|²`), AND
2. every distinct codeword pair `x ≠ y` in `supp(C)` sits at a root `F(x, y) = 0`!
-/
theorem delsarte_cohn_elkies_complementary_slackness_iff
    (N K : Nat) (w : Nat → Int) (chi : Nat → Nat → Int) (C : Nat → Int) (Fdiag : Int)
    (hK : 1 ≤ K)
    (hw : ∀ r, r < K → 0 ≤ w r)
    (hchi0 : ∀ x, x < N → chi 0 x = 1)
    (hC01 : ∀ x, x < N → C x = 0 ∨ C x = 1)
    (hDiagEq : ∀ x, x < N → C x = 1 → bochnerKernel K w chi x x = Fdiag)
    (hOff : ∀ x y, x < N → y < N → x ≠ y → C x = 1 → C y = 1 → bochnerKernel K w chi x y ≤ 0) :
    w 0 * (sumRange N C * sumRange N C) = Fdiag * sumRange N C ↔
      (sumRange K (fun r => w r * (modeMoment N C chi r * modeMoment N C chi r)) =
        w 0 * (sumRange N C * sumRange N C) ∧
       ∀ x y, x < N → y < N → x ≠ y → C x = 1 → C y = 1 → bochnerKernel K w chi x y = 0) := by
  have h0 : modeMoment N C chi 0 = sumRange N C := modeMoment_zero_eq_card N C chi hchi0
  have hParseval := bochner_parseval_double_sum_identity N K w chi C
  have hSpecLe :
      w 0 * (sumRange N C * sumRange N C) ≤
      sumRange K (fun r => w r * (modeMoment N C chi r * modeMoment N C chi r)) := by
    have hle := sumRange_head_le_nonneg hK
      (g := fun r => w r * (modeMoment N C chi r * modeMoment N C chi r))
      (fun r _ hrK => Int.mul_nonneg (hw r hrK) (int_sq_nonneg (modeMoment N C chi r)))
    simpa [h0] using hle
  have hTermLe :
      ∀ x y, x < N → y < N →
        C x * C y * bochnerKernel K w chi x y ≤ deltaNat x y * (Fdiag * C x) := by
    intro x y hx hy
    by_cases hxy : x = y
    · subst hxy
      simp only [deltaNat, ite_true, Int.one_mul]
      rcases hC01 x hx with hx0 | hx1
      · simp [hx0]
      · simp [hx1, hDiagEq x hx hx1]
    · simp only [deltaNat, hxy, ite_false, Int.zero_mul]
      rcases hC01 x hx with hx0 | hx1
      · simp [hx0]
      · rcases hC01 y hy with hy0 | hy1
        · simp [hy0]
        · simp only [hx1, hy1, Int.one_mul]
          exact hOff x y hx hy hxy hx1 hy1
  have hRowLe :
      ∀ x, x < N →
        sumRange N (fun y => C x * C y * bochnerKernel K w chi x y) ≤ Fdiag * C x := by
    intro x hx
    have hr := sumRange_le (fun y hy => hTermLe x y hx hy)
    rw [sumRange_deltaNat hx (Fdiag * C x)] at hr
    exact hr
  have hSpatLe :
      sumRange N (fun x => sumRange N (fun y => C x * C y * bochnerKernel K w chi x y)) ≤
      Fdiag * sumRange N C := by
    have hs := sumRange_le hRowLe
    rw [sumRange_mul_left N Fdiag C] at hs
    exact hs
  constructor
  · intro hTight
    have hSpecEq :
        sumRange K (fun r => w r * (modeMoment N C chi r * modeMoment N C chi r)) =
        w 0 * (sumRange N C * sumRange N C) := by
      omega
    have hSpatEq :
        sumRange N (fun x => sumRange N (fun y => C x * C y * bochnerKernel K w chi x y)) =
        sumRange N (fun x => Fdiag * C x) := by
      rw [sumRange_mul_left N Fdiag C]
      omega
    have hRowEq := sumRange_eq_zero_of_nonpos_eq hRowLe hSpatEq
    refine ⟨hSpecEq, ?_⟩
    intro x y hx hy hxy hx1 hy1
    have hxRow :
        sumRange N (fun z => C x * C z * bochnerKernel K w chi x z) =
        sumRange N (fun z => deltaNat x z * (Fdiag * C x)) := by
      rw [sumRange_deltaNat hx (Fdiag * C x)]
      exact hRowEq x hx
    have hCellEq := sumRange_eq_zero_of_nonpos_eq (fun z hz => hTermLe x z hx hz) hxRow y hy
    simpa [deltaNat, hxy, hx1, hy1] using hCellEq
  · rintro ⟨hSpecEq, hRoot⟩
    have hSpatEq :
        sumRange N (fun x => sumRange N (fun y => C x * C y * bochnerKernel K w chi x y)) =
        Fdiag * sumRange N C := by
      rw [← sumRange_mul_left N Fdiag C]
      apply sumRange_congr
      intro x hx
      rw [← sumRange_deltaNat hx (Fdiag * C x)]
      apply sumRange_congr
      intro y hy
      by_cases hxy : x = y
      · subst hxy
        simp only [deltaNat, ite_true, Int.one_mul]
        rcases hC01 x hx with hx0 | hx1
        · simp [hx0]
        · simp [hx1, hDiagEq x hx hx1]
      · simp only [deltaNat, hxy, ite_false, Int.zero_mul]
        rcases hC01 x hx with hx0 | hx1
        · simp [hx0]
        · rcases hC01 y hy with hy0 | hy1
          · simp [hy0]
          · simp [hx1, hy1, hRoot x y hx hy hxy hx1 hy1]
    omega

/-! ## 4. Viazovska-Style Double-Zero Magic Kernel Witness on `{0, 1}³` -/

/-- Bit `b` (`0, 1, 2`) of integer index `x ∈ {0, ..., 7}`. -/
def bit3 (x b : Nat) : Nat :=
  (x / (2 ^ b)) % 2

/-- Hamming distance on `{0, 1}³`. -/
def hamming3 (x y : Nat) : Nat :=
  (if bit3 x 0 = bit3 y 0 then 0 else 1) +
  (if bit3 x 1 = bit3 y 1 then 0 else 1) +
  (if bit3 x 2 = bit3 y 2 then 0 else 1)

/-- Walsh–Hadamard character `χ_r(x) = (-1)^{⟨r, x⟩_2}` on `{0, 1}³`. -/
def walsh3 (r x : Nat) : Int :=
  let ip := bit3 r 0 * bit3 x 0 + bit3 r 1 * bit3 x 1 + bit3 r 2 * bit3 x 2
  if ip % 2 = 0 then 1 else -1

/-- Magic Fourier weights `w = (3, 2, 2, 1, 2, 1, 1, 0)` indexed by `r ∈ {0..7}`. -/
def magicW3 : Nat → Int
  | 0 => 3
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | 4 => 2
  | 5 => 1
  | 6 => 1
  | _ => 0

/-- Even-weight `[3, 2, 2]` parity code `C* = {000, 011, 101, 110}` (`x ∈ {0, 3, 5, 6}`). -/
def parityCode3 : Nat → Int
  | 0 => 1
  | 3 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

/--
**Theorem 3 (Viazovska-Style Double-Zero Magic Kernel & Exact `[3, 2, 2]` Parity Attainment)**:
1. `magicW3 r ≥ 0` for all `r < 8`, with `magicW3 0 = 3` and `F(x, x) = 12` for all `x < 8`.
2. `bochnerKernel 8 magicW3 walsh3 x y = 0` at **every** pair `x, y < 8` with `hamming3 x y ≥ 2`
   (simultaneous double zero at both `d = 2` and `d = 3`!).
3. Every minimum-distance-`2` `{0, 1}`-code `C` on `{0, 1}³` satisfies `|C| ≤ 4`.
4. `parityCode3` achieves exact complementary-slackness equality `|C*| = 4` (`3 · 4² = 48 = 12 · 4`),
   annihilating modes `1..6` while concentrating its remaining spectral spike at `r = 7` where `magicW3 7 = 0`!
-/
theorem viazovska_style_double_zero_parity_code_exact_attainment :
    (∀ r, r < 8 → 0 ≤ magicW3 r) ∧
    (∀ x, x < 8 → bochnerKernel 8 magicW3 walsh3 x x = 12) ∧
    (∀ x y, x < 8 → y < 8 → 2 ≤ hamming3 x y → bochnerKernel 8 magicW3 walsh3 x y = 0) ∧
    (∀ C : Nat → Int,
      (∀ x, x < 8 → C x = 0 ∨ C x = 1) →
      (∀ x y, x < 8 → y < 8 → x ≠ y → C x = 1 → C y = 1 → 2 ≤ hamming3 x y) →
      1 ≤ sumRange 8 C →
      sumRange 8 C ≤ 4) ∧
    (sumRange 8 parityCode3 = 4 ∧
     (∀ r, 1 ≤ r → r ≤ 6 → modeMoment 8 parityCode3 walsh3 r = 0) ∧
     modeMoment 8 parityCode3 walsh3 7 = 4 ∧
     magicW3 7 = 0) := by
  have hwFin : ∀ r : Fin 8, 0 ≤ magicW3 r.val := by decide
  have hwNonneg : ∀ r, r < 8 → 0 ≤ magicW3 r := fun r hr => hwFin ⟨r, hr⟩
  have hDiagFin : ∀ x : Fin 8, bochnerKernel 8 magicW3 walsh3 x.val x.val = 12 := by decide
  have hDiag12 : ∀ x, x < 8 → bochnerKernel 8 magicW3 walsh3 x x = 12 := fun x hx => hDiagFin ⟨x, hx⟩
  have hDZFin : ∀ x : Fin 8, ∀ y : Fin 8, 2 ≤ hamming3 x.val y.val →
      bochnerKernel 8 magicW3 walsh3 x.val y.val = 0 := by decide
  have hDoubleZero : ∀ x y, x < 8 → y < 8 → 2 ≤ hamming3 x y →
      bochnerKernel 8 magicW3 walsh3 x y = 0 := fun x y hx hy hd => hDZFin ⟨x, hx⟩ ⟨y, hy⟩ hd
  have hChiFin : ∀ x : Fin 8, walsh3 0 x.val = 1 := by decide
  have hChi0 : ∀ x, x < 8 → walsh3 0 x = 1 := fun x hx => hChiFin ⟨x, hx⟩
  have hParModesFin : ∀ r : Fin 8, 1 ≤ r.val → r.val ≤ 6 →
      modeMoment 8 parityCode3 walsh3 r.val = 0 := by decide
  refine ⟨hwNonneg, hDiag12, hDoubleZero, ?_, ?_⟩
  · intro C hC01 hMinDist hNonempty
    have hLP := (delsarte_cohn_elkies_universal_packing_bound 8 8 magicW3 walsh3 C 12
      (by omega) hwNonneg hChi0 hC01
      (fun x hx _ => by rw [hDiag12 x hx]; exact Int.le_refl 12)
      (fun x y hx hy hxy hx1 hy1 => by
        rw [hDoubleZero x y hx hy (hMinDist x y hx hy hxy hx1 hy1)]
        exact Int.le_refl 0)).2 hNonempty
    change 3 * sumRange 8 C ≤ 12 at hLP
    omega
  · refine ⟨by decide, ?_, by decide, rfl⟩
    intro r hr1 hr6
    exact hParModesFin ⟨r, by omega⟩ hr1 hr6

/-! ## 5. Dual Universal Cubature / Spherical `t`-Design Lower Bound -/

theorem sumRange_eq_head_of_tail_zero {K : Nat} (hK : 1 ≤ K) {g : Nat → Int}
    (htail : ∀ r, 1 ≤ r → r < K → g r = 0) :
    sumRange K g = g 0 := by
  induction K with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      simp [sumRange]
    · have hk1 : 1 ≤ k := by omega
      have ih' := ih hk1 (fun r hr1 hrk => htail r hr1 (Nat.lt_succ_of_lt hrk))
      have hlast := htail k hk1 (Nat.lt_succ_self k)
      simp [sumRange, ih', hlast]

/--
**Theorem 4A (Dual Universal Cubature / Spherical `t`-Design Lower Bound)**:
If the test kernel `G(x, y) = bochnerKernel K w chi x y` satisfies `G(x, x) ≥ Gdiag` on `supp(D)` and
`G(x, y) ≥ 0` off-diagonally on `supp(D)`, and the `{0, 1}`-design `D` annihilates all non-trivial
harmonics `1 ≤ r < K` (`modeMoment N D chi r = 0`), then `M = ∑_{x<N} D(x)` satisfies:
1. `Gdiag * M ≤ w 0 * (M * M)`, and
2. if `1 ≤ M` and `w 0 = 1`, `Gdiag ≤ M`.
-/
theorem delsarte_quadrature_design_lower_bound
    (N K : Nat) (w : Nat → Int) (chi : Nat → Nat → Int) (D : Nat → Int) (Gdiag : Int)
    (hK : 1 ≤ K)
    (hchi0 : ∀ x, x < N → chi 0 x = 1)
    (hD01 : ∀ x, x < N → D x = 0 ∨ D x = 1)
    (hDiag : ∀ x, x < N → D x = 1 → Gdiag ≤ bochnerKernel K w chi x x)
    (hOffNonneg : ∀ x y, x < N → y < N → x ≠ y → D x = 1 → D y = 1 → 0 ≤ bochnerKernel K w chi x y)
    (hDesign : ∀ r, 1 ≤ r → r < K → modeMoment N D chi r = 0) :
    Gdiag * sumRange N D ≤ w 0 * (sumRange N D * sumRange N D) ∧
    (1 ≤ sumRange N D → w 0 = 1 → Gdiag ≤ sumRange N D) := by
  have hSpecEq :
      sumRange K (fun r => w r * (modeMoment N D chi r * modeMoment N D chi r)) =
      w 0 * (sumRange N D * sumRange N D) := by
    have hHead := sumRange_eq_head_of_tail_zero hK
      (g := fun r => w r * (modeMoment N D chi r * modeMoment N D chi r))
      (fun r hr1 hrK => by simp [hDesign r hr1 hrK])
    rw [hHead, modeMoment_zero_eq_card N D chi hchi0]
  have hRowGe :
      ∀ x, x < N →
        Gdiag * D x ≤ sumRange N (fun y => D x * D y * bochnerKernel K w chi x y) := by
    intro x hx
    rw [← sumRange_deltaNat hx (Gdiag * D x)]
    apply sumRange_le
    intro y hy
    by_cases hxy : x = y
    · subst hxy
      simp only [deltaNat, ite_true, Int.one_mul]
      rcases hD01 x hx with hx0 | hx1
      · simp [hx0]
      · simp only [hx1, Int.one_mul, Int.mul_one]
        exact hDiag x hx hx1
    · simp only [deltaNat, hxy, ite_false, Int.zero_mul]
      rcases hD01 x hx with hx0 | hx1
      · simp [hx0]
      · rcases hD01 y hy with hy0 | hy1
        · simp [hy0]
        · simp only [hx1, hy1, Int.one_mul]
          exact hOffNonneg x y hx hy hxy hx1 hy1
  have hSpatGe :
      Gdiag * sumRange N D ≤
      sumRange N (fun x => sumRange N (fun y => D x * D y * bochnerKernel K w chi x y)) := by
    have hs := sumRange_le hRowGe
    rw [sumRange_mul_left N Gdiag D] at hs
    exact hs
  have hParseval := bochner_parseval_double_sum_identity N K w chi D
  have hQuad : Gdiag * sumRange N D ≤ w 0 * (sumRange N D * sumRange N D) := by omega
  refine ⟨hQuad, ?_⟩
  intro hM1 hw0
  rw [hw0, Int.one_mul] at hQuad
  exact cancel_pos_mul_right hM1 hQuad

/-- Walsh basis on `{0, 1}²` (`N = 4`, modes `00, 01, 10, 11`). -/
def walsh2 (r x : Nat) : Int :=
  let ip := (r % 2) * (x % 2) + ((r / 2) % 2) * ((x / 2) % 2)
  if ip % 2 = 0 then 1 else -1

/-- Non-negative degree-`1` test weights `w = (2, 1, 1)` (`G(x,y) = 2 + χ_{01}(x)χ_{01}(y) + χ_{10}(x)χ_{10}(y) ∈ {0, 2, 4}`). -/
def designW2 : Nat → Int
  | 0 => 2
  | 1 => 1
  | 2 => 1
  | _ => 0

/-- Tight `2`-point antipodal `1`-design `D* = {(0,0), (1,1)}` (`x ∈ {0, 3}`). -/
def antipodalDesign2 : Nat → Int
  | 0 => 1
  | 3 => 1
  | _ => 0

/--
**Theorem 4B (Degree-`1` Walsh Design Tightness Witness on `{0, 1}²`)**:
Every non-empty `{0, 1}`-design `D ⊆ {0, 1}²` annihilating both linear modes `r = 1, 2`
satisfies `2 ≤ |D|`, and `antipodalDesign2 = {(0,0), (1,1)}` attains exact equality `|D*| = 2`!
-/
theorem degree_one_walsh_design_tightness_witness :
    (∀ x y, x < 4 → y < 4 → 0 ≤ bochnerKernel 3 designW2 walsh2 x y) ∧
    (∀ x, x < 4 → bochnerKernel 3 designW2 walsh2 x x = 4) ∧
    (∀ D : Nat → Int,
      (∀ x, x < 4 → D x = 0 ∨ D x = 1) →
      (∀ r, 1 ≤ r → r < 3 → modeMoment 4 D walsh2 r = 0) →
      1 ≤ sumRange 4 D →
      2 ≤ sumRange 4 D) ∧
    (sumRange 4 antipodalDesign2 = 2 ∧
     modeMoment 4 antipodalDesign2 walsh2 1 = 0 ∧
     modeMoment 4 antipodalDesign2 walsh2 2 = 0) := by
  have hNonnegFin : ∀ x : Fin 4, ∀ y : Fin 4, 0 ≤ bochnerKernel 3 designW2 walsh2 x.val y.val := by decide
  have hNonneg : ∀ x y, x < 4 → y < 4 → 0 ≤ bochnerKernel 3 designW2 walsh2 x y :=
    fun x y hx hy => hNonnegFin ⟨x, hx⟩ ⟨y, hy⟩
  have hDiagFin : ∀ x : Fin 4, bochnerKernel 3 designW2 walsh2 x.val x.val = 4 := by decide
  have hDiag4 : ∀ x, x < 4 → bochnerKernel 3 designW2 walsh2 x x = 4 :=
    fun x hx => hDiagFin ⟨x, hx⟩
  have hChiFin : ∀ x : Fin 4, walsh2 0 x.val = 1 := by decide
  have hChi0 : ∀ x, x < 4 → walsh2 0 x = 1 := fun x hx => hChiFin ⟨x, hx⟩
  refine ⟨hNonneg, hDiag4, ?_, by decide⟩
  intro D hD01 hDes hM1
  have hQuad := (delsarte_quadrature_design_lower_bound 4 3 designW2 walsh2 D 4
    (by omega) hChi0 hD01
    (fun x hx _ => by rw [hDiag4 x hx]; exact Int.le_refl 4)
    (fun x y hx hy _ _ _ => hNonneg x y hx hy)
    hDes).1
  change 4 * sumRange 4 D ≤ 2 * (sumRange 4 D * sumRange 4 D) at hQuad
  have hCancel : 4 ≤ (2 * sumRange 4 D) := by
    have hMul : 4 * sumRange 4 D ≤ (2 * sumRange 4 D) * sumRange 4 D := by
      simpa [Int.mul_assoc] using hQuad
    exact cancel_pos_mul_right hM1 hMul
  omega

/-! ## 6. Sharp Premise-Failure Counterexamples -/

/-- Indefinite spectral weights `w_bad = (1, 1, 1, -2)` violating `w_3 ≥ 0` on `{0, 1}²`. -/
def badNegModeW2 : Nat → Int
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => -2
  | _ => 0

/-- Positive off-diagonal weights `w_pos = (1, 0, 0, 1)` violating `F(0, 3) ≤ 0` on `{0, 1}²`. -/
def badPosOffW2 : Nat → Int
  | 0 => 1
  | 3 => 1
  | _ => 0

/--
**Theorem 5 (Sharp Premise-Failure Counterexamples to Delsarte–Cohn–Elkies Packing Bounds)**:
1. **Negative Fourier Mode Failure**: `badNegModeW2 = (1, 1, 1, -2)` satisfies `F_bad(x, x) = 1` and
   spatial sign barrier `F_bad(x, y) = -3 ≤ 0` on distinct points of `antipodalDesign2 = {00, 11}`,
   yet `w_0 · |C| = 1 · 2 = 2 > 1 = F_diag` (`w_0 |C|² = 4 > 2 = F_diag |C|`) because `w_3 = -2 < 0`!
2. **Positive Off-Diagonal Kernel Failure**: `badPosOffW2 = (1, 0, 0, 1)` satisfies `w_r ≥ 0` for all `r < 4`
   and `F_pos(x, x) = 2`, yet `F_pos(0, 3) = +2 > 0` allows `antipodalDesign2 = {00, 11}` (or the full cube)
   to achieve spatial energy `8 > 4 = F_diag · |C|`!
-/
theorem negative_fourier_mode_and_positive_off_diagonal_packing_failures :
    (bochnerKernel 4 badNegModeW2 walsh2 0 0 = 1 ∧
     bochnerKernel 4 badNegModeW2 walsh2 3 3 = 1 ∧
     bochnerKernel 4 badNegModeW2 walsh2 0 3 = -3 ∧
     badNegModeW2 3 < 0 ∧
     badNegModeW2 0 * sumRange 4 antipodalDesign2 > bochnerKernel 4 badNegModeW2 walsh2 0 0) ∧
    ((∀ r : Fin 4, 0 ≤ badPosOffW2 r.val) ∧
     bochnerKernel 4 badPosOffW2 walsh2 0 0 = 2 ∧
     bochnerKernel 4 badPosOffW2 walsh2 0 3 = 2 ∧
     sumRange 4 (fun x => sumRange 4 (fun y =>
       antipodalDesign2 x * antipodalDesign2 y * bochnerKernel 4 badPosOffW2 walsh2 x y)) >
       2 * sumRange 4 antipodalDesign2) := by
  decide

end CommonGround.UniversalAffineQueryCompression.DelsarteCohnElkiesDuality
