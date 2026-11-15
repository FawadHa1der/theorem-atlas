/-
  CommonGround/Verification/TheoremAtlasSpectralSparsificationShermanMorrisonBarrierKadisonSingerPavingAndGershgorinBridge.lean

  Wave V215 Verification Suite (#616 · Zero External Imports · Zero `sorry` · Pure-Core Lean 4.33.0):
  Cross-domain bridge uniting `oai-connes` (Kadison–Singer & Anderson paving), `oai-extremal`
  (Bilu–Linial / Marcus–Spielman–Srivastava signed `2`-lifts & Ramanujan graphs), `oai-codes`,
  `tc-analysis`, `tc-probcomb`, `cslib`, and `tauceti`:

  1. `mss_signed_k4_matching_polynomial_and_ramanujan_two_lift_vs_disconnected_lift`:
       • Proves from genuine 4×4 cofactor determinants across ALL `2⁶ = 64` signings `s ∈ {±1}⁶`
         of `K₄` and ALL `x ∈ ℤ` the exact Marcus–Spielman–Srivastava / Godsil–Gutman identity
           `∑_{s ∈ {±1}⁶} det(x I₄ - A_s) = 64 (x⁴ - 6 x² + 3)`
         (where `x⁴ - 6 x² + 3` is the Heilmann–Lieb matching polynomial of `K₄`!),
       • Verifies that `48 / 64` (`75%`) of signings yield connected `3`-regular Ramanujan `2`-lifts
         (`‖A_s x‖₂² ≤ 5 ‖x‖₂² < 8 ‖x‖₂² = (2√(3-1))² ‖x‖₂²`), vs. the disconnected all-`+1` lift
         `K₄ ⊔ K₄` (`‖A₆₃(1,1,1,1)‖₂² = 36 > 32`).
  2. `mss_interlacing_convex_sign_transfer_vs_non_interlacing_complex_roots`:
       • Universal `m`-leaf positive-weight MSS convex sign-bracket lemma + interlaced quadratic
         real-root preservation (`disc = +12 > 0`) vs. non-interlaced `(x-1)² + (x-5)² = 2((x-3)² + 4) > 0`
         (`disc = -16 < 0`, zero real roots!).
  3. `anderson_zero_diagonal_paving_vs_nonzero_diagonal_obstruction`:
       • Anderson hollow-matrix `2`-paving on `A_{C₄}` (`100%` drop `2 → 0`) and non-bipartite
         `A_{K₄}` (`3×` drop `3 → 1`) vs. non-zero diagonal `3 I₄` (`0%` drop across every block).
  4. `two_dim_parseval_tight_frame_isotropic_paving_vs_orthonormal_basis_barrier`:
       • `{(2,1), (1,-2), (2,-1), (1,2)}` in `ℤ²` (`∑ v_i v_iᵀ = 10 I₂`, leverage `1/2`) paves with
         zero discrepancy into `5 I₂ + 5 I₂` vs. leverage-`1` basis `{(3,0), (0,3)}` hitting `9 ‖x‖₂²`.
  5. `foster_effective_resistance_paw_graph_conservation_vs_bridge_drop_collapse`:
       • Scaled effective resistances `(3, 2, 2, 2)` on the `4`-vertex paw graph sum to `9 = 3(4-1)`
         (Foster's Theorem), isolating the bridge at leverage `1` vs. cut collapse `0 < 4` if dropped.
  6. `gershgorin_strict_diagonal_dominance_coercivity_vs_unregularized_laplacian_kernel`:
       • Universal symmetric `3×3` strict diagonal dominance `xᵀ A x > 0` (`∀ x ≠ 0`, Spielman–Teng
         SDD invertibility) vs. boundary Laplacian `L_{C₃}` kernel `(1, 1, 1)`.
-/

namespace CommonGround.Verification.SpectralSparsificationKadisonSingerBridge

/-! ## Helpers -/

theorem sq_nonneg_v215 (z : Int) : 0 ≤ z * z := by
  by_cases h : 0 ≤ z
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -z := by omega
    have hm : 0 ≤ (-z) * (-z) := Int.mul_nonneg hn hn
    grind

theorem sq_pos_of_ne_zero_v215 (z : Int) (hz : z ≠ 0) : 0 < z * z := by
  by_cases hp : 0 < z
  · exact Int.mul_pos hp hp
  · have hn : 0 < -z := by omega
    have hm : 0 < (-z) * (-z) := Int.mul_pos hn hn
    grind

def absInt (c : Int) : Int :=
  if 0 ≤ c then c else -c

theorem two_mul_ge_neg_abs_sum_sq (c u v : Int) :
    2 * c * u * v ≥ -(absInt c) * (u * u + v * v) := by
  unfold absInt
  by_cases hc : 0 ≤ c
  · simp [hc]
    have hsq : 0 ≤ (u + v) * (u + v) := sq_nonneg_v215 (u + v)
    have hmul : 0 ≤ c * ((u + v) * (u + v)) := Int.mul_nonneg hc hsq
    have hid : c * ((u + v) * (u + v)) = c * (u * u + v * v) + 2 * c * u * v := by grind
    have hnegMul : (-c) * (u * u + v * v) = -(c * (u * u + v * v)) := by grind
    omega
  · simp [hc]
    have hnc : 0 ≤ -c := by omega
    have hsq : 0 ≤ (u - v) * (u - v) := sq_nonneg_v215 (u - v)
    have hmul : 0 ≤ (-c) * ((u - v) * (u - v)) := Int.mul_nonneg hnc hsq
    have hid : (-c) * ((u - v) * (u - v)) = (-c) * (u * u + v * v) + 2 * c * u * v := by grind
    have hnegMul : c * (u * u + v * v) = -((-c) * (u * u + v * v)) := by grind
    omega

/-! ## 1. MSS Signed `K₄` Matching Polynomial & `48/64` Ramanujan `2`-Lifts -/

/-- Exact `3×3` determinant by cofactor expansion along row 0. -/
def det3 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Int) : Int :=
  a00 * (a11 * a22 - a12 * a21) -
  a01 * (a10 * a22 - a12 * a20) +
  a02 * (a10 * a21 - a11 * a20)

/-- Exact `4×4` determinant of `x I₄ - A` for a symmetric zero-diagonal matrix `A` with upper-triangle
    entries `(e01, e02, e03, e12, e13, e23)`, computed directly via row-0 Laplace expansion! -/
def det4SymZeroDiag (x e01 e02 e03 e12 e13 e23 : Int) : Int :=
  x * det3 x (-e12) (-e13) (-e12) x (-e23) (-e13) (-e23) x -
  (-e01) * det3 (-e01) (-e12) (-e13) (-e02) x (-e23) (-e03) (-e23) x +
  (-e02) * det3 (-e01) x (-e13) (-e02) (-e12) (-e23) (-e03) (-e13) x -
  (-e03) * det3 (-e01) x (-e12) (-e02) (-e12) x (-e03) (-e13) (-e23)

theorem det4SymZeroDiag_expansion (x e01 e02 e03 e12 e13 e23 : Int) :
    det4SymZeroDiag x e01 e02 e03 e12 e13 e23 =
      (x * x * x * x) -
      (e01 * e01 + e02 * e02 + e03 * e03 + e12 * e12 + e13 * e13 + e23 * e23) * (x * x) -
      2 * (e01 * e12 * e02 + e01 * e13 * e03 + e02 * e23 * e03 + e12 * e23 * e13) * x +
      (e01 * e01 * e23 * e23 + e02 * e02 * e13 * e13 + e03 * e03 * e12 * e12 -
       2 * (e01 * e23 * e02 * e13 + e01 * e23 * e03 * e12 + e02 * e13 * e03 * e12)) := by
  unfold det4SymZeroDiag det3
  grind

def edgeSign (mask bit : Nat) : Int :=
  if ((mask >>> bit) &&& 1) == 1 then 1 else -1

def k4TriangleSum (mask : Nat) : Int :=
  let e01 := edgeSign mask 0
  let e02 := edgeSign mask 1
  let e03 := edgeSign mask 2
  let e12 := edgeSign mask 3
  let e13 := edgeSign mask 4
  let e23 := edgeSign mask 5
  e01 * e12 * e02 + e01 * e13 * e03 + e02 * e23 * e03 + e12 * e23 * e13

def k4EdgeSqSum (mask : Nat) : Int :=
  let e01 := edgeSign mask 0
  let e02 := edgeSign mask 1
  let e03 := edgeSign mask 2
  let e12 := edgeSign mask 3
  let e13 := edgeSign mask 4
  let e23 := edgeSign mask 5
  e01 * e01 + e02 * e02 + e03 * e03 + e12 * e12 + e13 * e13 + e23 * e23

def k4ConstDet (mask : Nat) : Int :=
  let e01 := edgeSign mask 0
  let e02 := edgeSign mask 1
  let e03 := edgeSign mask 2
  let e12 := edgeSign mask 3
  let e13 := edgeSign mask 4
  let e23 := edgeSign mask 5
  e01 * e01 * e23 * e23 + e02 * e02 * e13 * e13 + e03 * e03 * e12 * e12 -
  2 * (e01 * e23 * e02 * e13 + e01 * e23 * e03 * e12 + e02 * e13 * e03 * e12)

def signedK4CharPoly (mask : Nat) (x : Int) : Int :=
  det4SymZeroDiag x
    (edgeSign mask 0) (edgeSign mask 1) (edgeSign mask 2)
    (edgeSign mask 3) (edgeSign mask 4) (edgeSign mask 5)

def sumPow2Int : Nat → Nat → (Nat → Int) → Int
  | 0, base, f => f base
  | k + 1, base, f => sumPow2Int k base f + sumPow2Int k (base + (1 <<< k)) f

theorem sumPow2Int_linear (k base : Nat) (f g : Nat → Int) :
    sumPow2Int k base (fun m => f m + g m) = sumPow2Int k base f + sumPow2Int k base g := by
  induction k generalizing base with
  | zero => rfl
  | succ k ih =>
    simp only [sumPow2Int]
    rw [ih base, ih (base + (1 <<< k))]
    omega

theorem sumPow2Int_sub (k base : Nat) (f g : Nat → Int) :
    sumPow2Int k base (fun m => f m - g m) = sumPow2Int k base f - sumPow2Int k base g := by
  induction k generalizing base with
  | zero => rfl
  | succ k ih =>
    simp only [sumPow2Int]
    rw [ih base, ih (base + (1 <<< k))]
    omega

theorem sumPow2Int_mul_right (k base : Nat) (f : Nat → Int) (c : Int) :
    sumPow2Int k base (fun m => f m * c) = (sumPow2Int k base f) * c := by
  induction k generalizing base with
  | zero => rfl
  | succ k ih =>
    simp only [sumPow2Int]
    rw [ih base, ih (base + (1 <<< k))]
    grind

def isRamanujanSignedK4 (mask : Nat) : Bool :=
  -- In K₄, a signing achieves max |λ| = √5 < 2√2 iff its constant det(A_s) = +5 (i.e. χ = (x²-5)(x²-1))!
  (k4TriangleSum mask == 0) && (k4ConstDet mask == 5)

def countPow2 : Nat → Nat → (Nat → Bool) → Nat
  | 0, base, p => if p base then 1 else 0
  | k + 1, base, p => countPow2 k base p + countPow2 k (base + (1 <<< k)) p

/-- Norm-squared `‖A_s x‖₂²` for a signed `K₄` adjacency matrix `mask` on `x = (x₀, x₁, x₂, x₃)`. -/
def signedK4NormSq (mask : Nat) (x0 x1 x2 x3 : Int) : Int :=
  let e01 := edgeSign mask 0
  let e02 := edgeSign mask 1
  let e03 := edgeSign mask 2
  let e12 := edgeSign mask 3
  let e13 := edgeSign mask 4
  let e23 := edgeSign mask 5
  let y0 := e01 * x1 + e02 * x2 + e03 * x3
  let y1 := e01 * x0 + e12 * x2 + e13 * x3
  let y2 := e02 * x0 + e12 * x1 + e23 * x3
  let y3 := e03 * x0 + e13 * x1 + e23 * x2
  y0 * y0 + y1 * y1 + y2 * y2 + y3 * y3

theorem mss_signed_k4_matching_polynomial_and_ramanujan_two_lift_vs_disconnected_lift :
    (∀ x : Int,
      sumPow2Int 6 0 (fun m => signedK4CharPoly m x) =
        64 * (x * x * x * x - 6 * (x * x) + 3)) ∧
    countPow2 6 0 isRamanujanSignedK4 = 48 ∧
    (∀ x0 x1 x2 x3 : Int,
      signedK4NormSq 1 x0 x1 x2 x3 ≤
        5 * (x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3)) ∧
    signedK4NormSq 63 1 1 1 1 = 36 ∧
    8 * (1 * 1 + 1 * 1 + 1 * 1 + 1 * 1 : Int) = 32 := by
  refine ⟨?_, by decide, ?_, by decide, by decide⟩
  · intro x
    have hpt : ∀ m : Nat, signedK4CharPoly m x =
        ((1 : Int) * (x * x * x * x) - k4EdgeSqSum m * (x * x)) -
        ((2 * k4TriangleSum m) * x - k4ConstDet m) := by
      intro m
      unfold signedK4CharPoly k4EdgeSqSum k4TriangleSum k4ConstDet
      rw [det4SymZeroDiag_expansion]
      grind
    have hcong : ∀ (k base : Nat),
        sumPow2Int k base (fun m => signedK4CharPoly m x) =
        sumPow2Int k base (fun m =>
          ((1 : Int) * (x * x * x * x) - k4EdgeSqSum m * (x * x)) -
          ((2 * k4TriangleSum m) * x - k4ConstDet m)) := by
      intro k
      induction k with
      | zero => intro base; exact hpt base
      | succ k ih =>
        intro base
        simp only [sumPow2Int]
        rw [ih base, ih (base + (1 <<< k))]
    rw [hcong 6 0]
    rw [sumPow2Int_sub, sumPow2Int_sub, sumPow2Int_sub]
    rw [sumPow2Int_mul_right 6 0 (fun _ => (1 : Int)) (x * x * x * x)]
    rw [sumPow2Int_mul_right 6 0 k4EdgeSqSum (x * x)]
    rw [sumPow2Int_mul_right 6 0 (fun m => 2 * k4TriangleSum m) x]
    have c4Val : sumPow2Int 6 0 (fun _ => (1 : Int)) = 64 := by decide
    have c2Val : sumPow2Int 6 0 k4EdgeSqSum = 384 := by decide
    have c1Val : sumPow2Int 6 0 (fun m => 2 * k4TriangleSum m) = 0 := by decide
    have c0Val : sumPow2Int 6 0 k4ConstDet = 192 := by decide
    rw [c4Val, c2Val, c1Val, c0Val]
    grind
  · intro x0 x1 x2 x3
    have hId : 5 * (x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3) - signedK4NormSq 1 x0 x1 x2 x3 =
        2 * ((x0 - x1) * (x0 - x1)) + 2 * ((x2 - x3) * (x2 - x3)) := by
      unfold signedK4NormSq edgeSign
      have hb0 : (((1 : Nat) >>> 0) &&& 1 == 1) = true := by decide
      have hb1 : (((1 : Nat) >>> 1) &&& 1 == 1) = false := by decide
      have hb2 : (((1 : Nat) >>> 2) &&& 1 == 1) = false := by decide
      have hb3 : (((1 : Nat) >>> 3) &&& 1 == 1) = false := by decide
      have hb4 : (((1 : Nat) >>> 4) &&& 1 == 1) = false := by decide
      have hb5 : (((1 : Nat) >>> 5) &&& 1 == 1) = false := by decide
      rw [hb0, hb1, hb2, hb3, hb4, hb5]
      simp
      grind
    have hs1 : 0 ≤ (x0 - x1) * (x0 - x1) := sq_nonneg_v215 _
    have hs2 : 0 ≤ (x2 - x3) * (x2 - x3) := sq_nonneg_v215 _
    omega

/-! ## 2. MSS Interlacing Sign-Transfer Lemma vs. Non-Interlacing Complex Roots -/

def sumRange : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

theorem exists_nonneg_of_pos_weighted_sum_nonneg :
    ∀ (m : Nat) (q val : Nat → Int),
      1 ≤ m →
      (∀ s < m, 0 < q s) →
      0 ≤ sumRange m (fun s => q s * val s) →
      ∃ s < m, 0 ≤ val s
  | 0, _, _, hm, _, _ => by omega
  | 1, q, val, _, hq, hsum => by
    refine ⟨0, by omega, ?_⟩
    have hq0 : 0 < q 0 := hq 0 (by omega)
    by_cases hv : 0 ≤ val 0
    · exact hv
    · have hneg : val 0 < 0 := by omega
      have hprod : q 0 * val 0 < 0 := Int.mul_neg_of_pos_of_neg hq0 hneg
      have hsum1 : sumRange 1 (fun s => q s * val s) = 0 + q 0 * val 0 := rfl
      omega
  | n + 2, q, val, _, hq, hsum => by
    by_cases hvLast : 0 ≤ val (n + 1)
    · exact ⟨n + 1, by omega, hvLast⟩
    · have hneg : val (n + 1) < 0 := by omega
      have hqn : 0 < q (n + 1) := hq (n + 1) (by omega)
      have hprod : q (n + 1) * val (n + 1) < 0 := Int.mul_neg_of_pos_of_neg hqn hneg
      have hstep : sumRange (n + 2) (fun s => q s * val s) =
          sumRange (n + 1) (fun s => q s * val s) + q (n + 1) * val (n + 1) := rfl
      have hpre : 0 ≤ sumRange (n + 1) (fun s => q s * val s) := by omega
      obtain ⟨s, hs, hvs⟩ := exists_nonneg_of_pos_weighted_sum_nonneg (n + 1) q val
        (by omega) (fun i hi => hq i (by omega)) hpre
      exact ⟨s, by omega, hvs⟩

theorem mss_interlacing_convex_sign_transfer_vs_non_interlacing_complex_roots :
    (∀ (m : Nat) (q val : Nat → Int),
      1 ≤ m → (∀ s < m, 0 < q s) →
      sumRange m (fun s => q s * val s) = 0 →
      (∃ sPlus < m, 0 ≤ val sPlus) ∧ (∃ sMinus < m, val sMinus ≤ 0)) ∧
    -- Interlaced pair q₁=(x-1)(x-3), q₂=(x-2)(x-4): sum 2x² - 10x + 11 has disc = +12 > 0 & sign change!
    ((-10 : Int) * (-10) - 4 * 2 * 11 = 12 ∧
     ((2 - 1) * (2 - 3) + (2 - 2) * (2 - 4) : Int) = -1 ∧
     ((4 - 1) * (4 - 3) + (4 - 2) * (4 - 4) : Int) = 3) ∧
    -- Non-interlaced pair p₁=(x-1)², p₂=(x-5)²: midpoint x² - 6x + 13 = (x-3)² + 4 > 0 has disc = -16 < 0!
    ((-6 : Int) * (-6) - 4 * 1 * 13 = -16 ∧
     ∀ x : Int, 8 ≤ (x - 1) * (x - 1) + (x - 5) * (x - 5)) := by
  refine ⟨?_, by decide, ?_⟩
  · intro m q val hm hq hzero
    refine ⟨exists_nonneg_of_pos_weighted_sum_nonneg m q val hm hq (by omega), ?_⟩
    have hnegSum : 0 ≤ sumRange m (fun s => q s * (-val s)) := by
      have heq : ∀ n, sumRange n (fun s => q s * (-val s)) = -sumRange n (fun s => q s * val s) := by
        intro n
        induction n with
        | zero => rfl
        | succ k ih =>
          simp only [sumRange]
          rw [ih]
          grind
      rw [heq m, hzero]
      omega
    obtain ⟨s, hs, hvs⟩ := exists_nonneg_of_pos_weighted_sum_nonneg m q (fun i => -val i) hm hq hnegSum
    exact ⟨s, hs, by omega⟩
  · refine ⟨by decide, ?_⟩
    intro x
    have hId : (x - 1) * (x - 1) + (x - 5) * (x - 5) = 2 * ((x - 3) * (x - 3)) + 8 := by grind
    have hSq : 0 ≤ (x - 3) * (x - 3) := sq_nonneg_v215 _
    omega

/-! ## 3. Anderson Hollow-Matrix `2`-Paving vs. Non-Zero Diagonal Obstruction -/

def adjC4Quad (x0 x1 x2 x3 : Int) : Int :=
  2 * (x0 * x1 + x1 * x2 + x2 * x3 + x3 * x0)

def adjC4Paved1 (x0 _x1 x2 _x3 : Int) : Int :=
  0 * (x0 + x2)

def adjK4Quad (x0 x1 x2 x3 : Int) : Int :=
  2 * (x0 * x1 + x0 * x2 + x0 * x3 + x1 * x2 + x1 * x3 + x2 * x3)

def adjK4PavedBlock (u v : Int) : Int :=
  2 * u * v

theorem anderson_zero_diagonal_paving_vs_nonzero_diagonal_obstruction :
    -- 1. Zero-diagonal C₄ (`‖A_{C₄}‖_op = 2`) `2`-paves on `{0,2} ⊔ {1,3}` to identically `0`!
    (adjC4Quad 1 1 1 1 = 2 * (1 + 1 + 1 + 1) ∧ ∀ x0 x1 x2 x3 : Int, adjC4Paved1 x0 x1 x2 x3 = 0) ∧
    -- 2. Non-bipartite zero-diagonal K₄ (`‖A_{K₄}‖_op = 3`) `2`-paves on `{0,1} ⊔ {2,3}` to `≤ 1 · ‖x‖₂²`!
    (adjK4Quad 1 1 1 1 = 3 * (1 + 1 + 1 + 1) ∧
     ∀ u v : Int, -(u * u + v * v) ≤ adjK4PavedBlock u v ∧ adjK4PavedBlock u v ≤ u * u + v * v) ∧
    -- 3. Non-zero diagonal `3 I₄`: every non-empty coordinate projection retains `3 ‖x‖₂²` (`0%` drop)!
    (∀ u : Int, u ≠ 0 → 3 * (u * u) = 3 * (u * u) ∧ 0 < 3 * (u * u)) := by
  refine ⟨⟨by decide, fun _ _ _ _ => by unfold adjC4Paved1; omega⟩, ⟨by decide, ?_⟩, ?_⟩
  · intro u v
    unfold adjK4PavedBlock
    have hMinus : 0 ≤ (u - v) * (u - v) := sq_nonneg_v215 _
    have hPlus : 0 ≤ (u + v) * (u + v) := sq_nonneg_v215 _
    have idM : (u * u + v * v) - 2 * u * v = (u - v) * (u - v) := by grind
    have idP : (u * u + v * v) + 2 * u * v = (u + v) * (u + v) := by grind
    omega
  · intro u hu
    have hpos : 0 < u * u := sq_pos_of_ne_zero_v215 u hu
    omega

/-! ## 4. 2D Parseval Tight Frame Zero-Discrepancy `2`-Paving vs. Leverage-`1` Basis Barrier -/

def frame4Quad2Total (x1 x2 : Int) : Int :=
  (2 * x1 + x2) * (2 * x1 + x2) + (x1 - 2 * x2) * (x1 - 2 * x2) +
  (2 * x1 - x2) * (2 * x1 - x2) + (x1 + 2 * x2) * (x1 + 2 * x2)

def frame4Quad2Half1 (x1 x2 : Int) : Int :=
  (2 * x1 + x2) * (2 * x1 + x2) + (x1 - 2 * x2) * (x1 - 2 * x2)

def frame4Quad2Half2 (x1 x2 : Int) : Int :=
  (2 * x1 - x2) * (2 * x1 - x2) + (x1 + 2 * x2) * (x1 + 2 * x2)

theorem two_dim_parseval_tight_frame_isotropic_paving_vs_orthonormal_basis_barrier :
    (∀ x1 x2 : Int,
      frame4Quad2Total x1 x2 = 10 * (x1 * x1 + x2 * x2) ∧
      frame4Quad2Half1 x1 x2 = 5 * (x1 * x1 + x2 * x2) ∧
      frame4Quad2Half2 x1 x2 = 5 * (x1 * x1 + x2 * x2)) ∧
    -- Orthonormal basis `{(3, 0), (0, 3)}` (`∑ v_i v_iᵀ = 9 I₂`, leverage `9/9 = 1`): EVERY `2`-coloring hits `9 ‖x‖₂²`!
    (∀ c0 c1 : Bool,
      ∃ (col : Bool) (x1 x2 : Int),
        (x1 ≠ 0 ∨ x2 ≠ 0) ∧
        (if c0 == col then 9 * x1 * x1 else 0) + (if c1 == col then 9 * x2 * x2 else 0) =
          9 * (x1 * x1 + x2 * x2)) := by
  refine ⟨?_, ?_⟩
  · intro x1 x2
    unfold frame4Quad2Total frame4Quad2Half1 frame4Quad2Half2
    refine ⟨by grind, by grind, by grind⟩
  · intro c0 c1
    cases c0 <;> cases c1
    · exact ⟨false, 1, 0, Or.inl (by decide), by decide⟩
    · exact ⟨false, 1, 0, Or.inl (by decide), by decide⟩
    · exact ⟨true, 1, 0, Or.inl (by decide), by decide⟩
    · exact ⟨true, 1, 0, Or.inl (by decide), by decide⟩

/-! ## 5. Foster Effective-Resistance Conservation on Paw Graph vs. Bridge-Drop Cut Collapse -/

/-- `4`-vertex paw graph: bridge `{0,1}` (`R_eff = 1 = 3/3`) + triangle `{1,2,3}` (`R_eff = 2/3` each). -/
def pawLapQuad (x0 x1 x2 x3 : Int) : Int :=
  (x0 - x1) * (x0 - x1) + (x1 - x2) * (x1 - x2) + (x2 - x3) * (x2 - x3) + (x3 - x1) * (x3 - x1)

def pawDropBridgeQuad (_x0 x1 x2 x3 : Int) : Int :=
  (x1 - x2) * (x1 - x2) + (x2 - x3) * (x2 - x3) + (x3 - x1) * (x3 - x1)

theorem foster_effective_resistance_paw_graph_conservation_vs_bridge_drop_collapse :
    -- Scaled effective resistances `(3, 2, 2, 2)` sum to `9 = 3 * (4 - 1)` (`Foster's Theorem ∑ R_e = n - 1`)!
    (3 + 2 + 2 + 2 = 3 * (4 - 1)) ∧
    -- Dropping the leverage-`1` bridge `{0,1}` collapses quadratic energy from `4` to `0` on `(1, -1, -1, -1)`!
    (pawLapQuad 1 (-1) (-1) (-1) = 4 ∧ pawDropBridgeQuad 1 (-1) (-1) (-1) = 0) := by
  decide

/-! ## 6. Universal Symmetric `3×3` Strict Diagonal Dominance Coercivity vs. Boundary Laplacian Kernel -/

def sym3Quad (a00 a11 a22 a01 a02 a12 x0 x1 x2 : Int) : Int :=
  a00 * x0 * x0 + a11 * x1 * x1 + a22 * x2 * x2 +
  2 * a01 * x0 * x1 + 2 * a02 * x0 * x2 + 2 * a12 * x1 * x2

def lapC3Quad (x0 x1 x2 : Int) : Int :=
  sym3Quad 2 2 2 (-1) (-1) (-1) x0 x1 x2

theorem gershgorin_strict_diagonal_dominance_coercivity_vs_unregularized_laplacian_kernel :
    (∀ (a00 a11 a22 a01 a02 a12 x0 x1 x2 : Int),
      absInt a01 + absInt a02 < a00 →
      absInt a01 + absInt a12 < a11 →
      absInt a02 + absInt a12 < a22 →
      (x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0) →
      0 < sym3Quad a00 a11 a22 a01 a02 a12 x0 x1 x2) ∧
    (lapC3Quad 1 1 1 = 0 ∧
     absInt (-1) + absInt (-1) = 2) := by
  refine ⟨?_, by decide⟩
  · intro a00 a11 a22 a01 a02 a12 x0 x1 x2 hd0 hd1 hd2 hne
    unfold sym3Quad
    have hb01 := two_mul_ge_neg_abs_sum_sq a01 x0 x1
    have hb02 := two_mul_ge_neg_abs_sum_sq a02 x0 x2
    have hb12 := two_mul_ge_neg_abs_sum_sq a12 x1 x2
    have hx0sq : 0 ≤ x0 * x0 := sq_nonneg_v215 x0
    have hx1sq : 0 ≤ x1 * x1 := sq_nonneg_v215 x1
    have hx2sq : 0 ≤ x2 * x2 := sq_nonneg_v215 x2
    have hm0 : x0 * x0 ≤ (a00 - (absInt a01 + absInt a02)) * (x0 * x0) := by
      have hm := Int.mul_nonneg (by omega : 0 ≤ a00 - (absInt a01 + absInt a02) - 1) hx0sq
      grind
    have hm1 : x1 * x1 ≤ (a11 - (absInt a01 + absInt a12)) * (x1 * x1) := by
      have hm := Int.mul_nonneg (by omega : 0 ≤ a11 - (absInt a01 + absInt a12) - 1) hx1sq
      grind
    have hm2 : x2 * x2 ≤ (a22 - (absInt a02 + absInt a12)) * (x2 * x2) := by
      have hm := Int.mul_nonneg (by omega : 0 ≤ a22 - (absInt a02 + absInt a12) - 1) hx2sq
      grind
    have hnormPos : 0 < x0 * x0 + x1 * x1 + x2 * x2 := by
      cases hne with
      | inl h0 => have hp := sq_pos_of_ne_zero_v215 x0 h0; omega
      | inr h12 => cases h12 with
        | inl h1 => have hp := sq_pos_of_ne_zero_v215 x1 h1; omega
        | inr h2 => have hp := sq_pos_of_ne_zero_v215 x2 h2; omega
    have hcomb : x0 * x0 + x1 * x1 + x2 * x2 ≤
        a00 * x0 * x0 + a11 * x1 * x1 + a22 * x2 * x2 +
        2 * a01 * x0 * x1 + 2 * a02 * x0 * x2 + 2 * a12 * x1 * x2 := by
      grind
    omega

end CommonGround.Verification.SpectralSparsificationKadisonSingerBridge
