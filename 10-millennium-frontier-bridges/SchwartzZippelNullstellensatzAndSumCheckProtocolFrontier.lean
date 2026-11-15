/-!
# Combinatorial Nullstellensatz, `LFKN` / `ZK-STARK` Sum-Check Soundness, Reed–Muller Error-Locator Uniqueness & Croot–Lev–Pach Slice-Rank Polynomial Method (`0` Imports, `0` Sorry)

This standalone pure-core Lean 4.33.0 frontier module unifies **Folder `10`**
(Algebraic Complexity, Coding & Proof-System Barriers), **Folder `02`** (Moment
& Interpolation Compression), and **Folder `07`** (Interactive Samplers & Error
Correction):

1. **Alon's (`1999`) Combinatorial Nullstellensatz Coefficient Extraction vs. Grid Annihilator `x(x-1)(x-2)`**
   (`combinatorial_nullstellensatz_grid_nonvanishing_vs_degree_exceeding_grid_annihilation`):
   - *Universal `(1, 1)` Grid Extraction*: For any `P(x, y) = c00 + c10 x + c01 y + c11 x y`
     and any `x0 ≠ x1, y0 ≠ y1`, alternating Möbius difference equals `c11 (x1 - x0)(y1 - y0)`,
     so `c11 ≠ 0` forbids `P` from vanishing on `{x0, x1} × {y0, y1}`.
   - *Universal `(2, 1)` Six-Point Grid Extraction*: For `P(x, y) = q0(x) + y(a0 + a1 x + a2 x^2)`
     on `{0, 1, 2} × {y0, y1}` (`y0 ≠ y1`), second-difference extraction isolates `2 a2 (y1 - y0)`,
     forbidding simultaneous vanishing whenever `a2 ≠ 0`.
   - *Premise-Failure Counterexample (`deg_x = |S_x| = 3`)*: `P(x, y) = x(x - 1)(x - 2)` has
     monic top coefficient `1 ≠ 0` yet vanishes at EVERY point of `{0, 1, 2} × ℤ`.

2. **Lund–Fortnow–Karloff–Nisan (`LFKN`) / `ZK-STARK` Sum-Check Soundness vs. Unbounded-Degree Forgery**
   (`sum_check_protocol_completeness_and_low_degree_soundness_vs_high_degree_forgery`):
   - *Exact Completeness*: Honest univariate marginals `s1(X) = g(X,0) + g(X,1)` and
     `s2(Y) = g(r1, Y)` pass every round check identically for all `g` and all challenges `(r1, r2)`.
   - *Universal Quadratic Root-Bound Soundness*: Via the exact Vandermonde identity
     `(r2 - r1) Δ(r0) - (r2 - r0) Δ(r1) + (r1 - r0) Δ(r2) = d2 (r1 - r0)(r2 - r0)(r2 - r1)`,
     any degree-`≤ 2` round-1 polynomial `s1_tilde` claiming a false sum `H ≠ S_true` (`Δ(0) + Δ(1) ≠ 0`)
     can agree with `s1` on AT MOST `2` distinct integer challenges (`¬ (Δ r0 = 0 ∧ Δ r1 = 0 ∧ Δ r2 = 0)`
     for all `r0 < r1 < r2`)!
   - *Premise-Failure Counterexample*: Without the low-degree cap, a degree-`4` forgery
     `s1_cheat(X) = s1(X) + (X - 2)(X - 3)(X - 4)` claims false sum `H = S_true - 30 ≠ S_true`
     on `{0, 1}` yet agrees 100% with honest `s1(r)` at every challenge `r ∈ {2, 3, 4}`!

3. **Berlekamp–Welch / Reed–Solomon Unique Decoding (`2e < d`) vs. Half-Distance Ambiguity (`2e = d`)**
   (`reed_solomon_unique_decoding_radius_vs_half_distance_ambiguity`):
   - *Universal Unique Decoding (`n = 4, k = 2, d = 3, e ≤ 1`)*: Any two degree-`≤ 1` codewords
     `a0 + a1 x` and `b0 + b1 x` each within Hamming distance `≤ 1` of received `y` on `{0, 1, 2, 3}`
     must coincide (`a0 = b0 ∧ a1 = b1`), accompanied by an explicit Berlekamp–Welch key equation
     `E(x)(a0 + a1 x) = N(x)` locating spike error at `x = 2`.
   - *Premise-Failure Counterexample (`e = 2`, `2e = 4 > d = 3`)*: Received word `(0, 0, 3, 4)`
     sits at exact Hamming distance `2` from BOTH `(0, 0, 0, 0)` (`P = 0`) and `(1, 2, 3, 4)` (`Q = 1 + x`).

4. **Croot–Lev–Pach / Ellenberg–Gijswijt Slice-Rank Determinant Obstruction (`det₃ = 0` vs. `d₀ d₁ d₂ ≠ 0`)**
   (`croot_lev_pach_slice_rank_diagonal_obstruction_vs_rank_deficient_drop`):
   - *Universal `3 × 3` Slice-Rank Lower Bound*: Every `2`-term bilinear / slice decomposition
     `M_{i,j} = u1_i v1_j + u2_i v2_j` has `det₃(M) = 0` identically, whereas `diag(d0, d1, d2)`
     has `det₃ = d0 d1 d2 ≠ 0` whenever `d0, d1, d2 ≠ 0` — hence NO `2`-slice representation exists!
   - *Premise-Failure Counterexample*: Zeroing a single diagonal entry `diag(1, 1, 0)` drops
     `det₃ = 0` and admits an exact `2`-slice representation.
-/

namespace CommonGround.Frontier.SchwartzZippelNullstellensatzAndSumCheck

/-- Evaluate bivariate degree-`(1, 1)` polynomial `c00 + c10*x + c01*y + c11*x*y`. -/
def evalBilin (c00 c10 c01 c11 x y : Int) : Int :=
  c00 + c10 * x + c01 * y + c11 * x * y

/-- Evaluate bivariate degree-`(2, 1)` polynomial `(b0 + b1*x + b2*x^2) + y*(a0 + a1*x + a2*x^2)`. -/
def evalDeg21 (b0 b1 b2 a0 a1 a2 x y : Int) : Int :=
  (b0 + b1 * x + b2 * x * x) + y * (a0 + a1 * x + a2 * x * x)

/-- Theorem 1: Alon's Combinatorial Nullstellensatz Grid Coefficient Extraction (`(1,1)` & `(2,1)`)
    vs. Fermat/Grid Annihilator `x(x - 1)(x - 2)` when `deg_x = |S_x|`. -/
theorem combinatorial_nullstellensatz_grid_nonvanishing_vs_degree_exceeding_grid_annihilation :
    -- (1) Universal `(1, 1)` Combinatorial Nullstellensatz on `{x0, x1} × {y0, y1}`:
    (∀ c00 c10 c01 c11 x0 x1 y0 y1 : Int,
      evalBilin c00 c10 c01 c11 x1 y1 - evalBilin c00 c10 c01 c11 x0 y1 -
        evalBilin c00 c10 c01 c11 x1 y0 + evalBilin c00 c10 c01 c11 x0 y0 =
        c11 * (x1 - x0) * (y1 - y0) ∧
      (c11 ≠ 0 → x0 ≠ x1 → y0 ≠ y1 →
        ¬ (evalBilin c00 c10 c01 c11 x0 y0 = 0 ∧
           evalBilin c00 c10 c01 c11 x1 y0 = 0 ∧
           evalBilin c00 c10 c01 c11 x0 y1 = 0 ∧
           evalBilin c00 c10 c01 c11 x1 y1 = 0))) ∧
    -- (2) Universal `(2, 1)` Combinatorial Nullstellensatz on `{0, 1, 2} × {y0, y1}`:
    (∀ b0 b1 b2 a0 a1 a2 y0 y1 : Int,
      (evalDeg21 b0 b1 b2 a0 a1 a2 2 y1 - 2 * evalDeg21 b0 b1 b2 a0 a1 a2 1 y1 + evalDeg21 b0 b1 b2 a0 a1 a2 0 y1) -
      (evalDeg21 b0 b1 b2 a0 a1 a2 2 y0 - 2 * evalDeg21 b0 b1 b2 a0 a1 a2 1 y0 + evalDeg21 b0 b1 b2 a0 a1 a2 0 y0) =
        2 * a2 * (y1 - y0) ∧
      (a2 ≠ 0 → y0 ≠ y1 →
        ¬ (evalDeg21 b0 b1 b2 a0 a1 a2 0 y0 = 0 ∧
           evalDeg21 b0 b1 b2 a0 a1 a2 1 y0 = 0 ∧
           evalDeg21 b0 b1 b2 a0 a1 a2 2 y0 = 0 ∧
           evalDeg21 b0 b1 b2 a0 a1 a2 0 y1 = 0 ∧
           evalDeg21 b0 b1 b2 a0 a1 a2 1 y1 = 0 ∧
           evalDeg21 b0 b1 b2 a0 a1 a2 2 y1 = 0))) ∧
    -- (3) Premise-Failure Counterexample (`deg_x = 3 = |{0, 1, 2}|`):
    --     Monic `P(x, y) = x(x - 1)(x - 2)` has nonzero top coefficient `1 ≠ 0` yet vanishes on ALL `{0, 1, 2} × ℤ`!
    ((1 : Int) ≠ 0 ∧
     ∀ y : Int,
       (0 : Int) * (0 - 1) * (0 - 2) + 0 * y = 0 ∧
       (1 : Int) * (1 - 1) * (1 - 2) + 0 * y = 0 ∧
       (2 : Int) * (2 - 1) * (2 - 2) + 0 * y = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c00 c10 c01 c11 x0 x1 y0 y1
    have hId :
        evalBilin c00 c10 c01 c11 x1 y1 - evalBilin c00 c10 c01 c11 x0 y1 -
          evalBilin c00 c10 c01 c11 x1 y0 + evalBilin c00 c10 c01 c11 x0 y0 =
          c11 * (x1 - x0) * (y1 - y0) := by unfold evalBilin; grind
    refine ⟨hId, ?_⟩
    intro hc11 hx hy ⟨z00, z10, z01, z11⟩
    rw [z00, z10, z01, z11] at hId
    have hDx : x1 - x0 ≠ 0 := by omega
    have hDy : y1 - y0 ≠ 0 := by omega
    have hProdNe : c11 * (x1 - x0) * (y1 - y0) ≠ 0 :=
      Int.mul_ne_zero (Int.mul_ne_zero hc11 hDx) hDy
    exact hProdNe hId.symm
  · intro b0 b1 b2 a0 a1 a2 y0 y1
    have hId :
        (evalDeg21 b0 b1 b2 a0 a1 a2 2 y1 - 2 * evalDeg21 b0 b1 b2 a0 a1 a2 1 y1 + evalDeg21 b0 b1 b2 a0 a1 a2 0 y1) -
        (evalDeg21 b0 b1 b2 a0 a1 a2 2 y0 - 2 * evalDeg21 b0 b1 b2 a0 a1 a2 1 y0 + evalDeg21 b0 b1 b2 a0 a1 a2 0 y0) =
          2 * a2 * (y1 - y0) := by unfold evalDeg21; grind
    refine ⟨hId, ?_⟩
    intro ha2 hy ⟨z00, z10, z20, z01, z11, z21⟩
    rw [z00, z10, z20, z01, z11, z21] at hId
    have h2a2 : 2 * a2 ≠ 0 := by omega
    have hDy : y1 - y0 ≠ 0 := by omega
    have hProdNe : 2 * a2 * (y1 - y0) ≠ 0 := Int.mul_ne_zero h2a2 hDy
    exact hProdNe hId.symm
  · refine ⟨by decide, ?_⟩
    intro y
    omega

/-- Evaluate univariate quadratic `d0 + d1 * x + d2 * x^2`. -/
def evalQuad (d0 d1 d2 x : Int) : Int :=
  d0 + d1 * x + d2 * x * x

/-- Theorem 2: `LFKN` / `ZK-STARK` Sum-Check Completeness & Degree-`≤ 2` Soundness (`≤ 2` Bad Challenges)
    vs. High-Degree Lagrange Forgery (`100%` Challenge Evasion Without Degree Cap). -/
theorem sum_check_protocol_completeness_and_low_degree_soundness_vs_high_degree_forgery :
    -- (1) Universal 2-Round Boolean Sum-Check Completeness for ANY `g : Int → Int → Int`:
    (∀ (g : Int → Int → Int) (r1 r2 : Int),
      let s1 := fun X => g X 0 + g X 1
      let s2 := fun Y => g r1 Y
      s1 0 + s1 1 = (g 0 0 + g 0 1 + g 1 0 + g 1 1) ∧
      s2 0 + s2 1 = s1 r1 ∧
      s2 r2 = g r1 r2) ∧
    -- (2) Universal Quadratic Error-Polynomial Soundness: if `Δ(X) = d0 + d1*X + d2*X^2` has
    --     nonzero Boolean sum discrepancy `Δ(0) + Δ(1) ≠ 0`, then `Δ` CANNOT vanish at ANY `3`
    --     distinct challenges `r0 < r1 < r2`!
    (∀ d0 d1 d2 r0 r1 r2 : Int,
      (r2 - r1) * evalQuad d0 d1 d2 r0 - (r2 - r0) * evalQuad d0 d1 d2 r1 +
        (r1 - r0) * evalQuad d0 d1 d2 r2 =
        d2 * (r1 - r0) * (r2 - r0) * (r2 - r1) ∧
      (evalQuad d0 d1 d2 0 + evalQuad d0 d1 d2 1 ≠ 0 →
        r0 < r1 → r1 < r2 →
        ¬ (evalQuad d0 d1 d2 r0 = 0 ∧ evalQuad d0 d1 d2 r1 = 0 ∧ evalQuad d0 d1 d2 r2 = 0))) ∧
    -- (3) Premise-Failure Counterexample (Omitted Degree Cap):
    --     Cubic error `Δ_cheat(X) = (X - 2)*(X - 3)*(X - 4)` shifts claimed sum on `{0, 1}` by `-30 ≠ 0`
    --     yet vanishes IDENTICALLY at every verifier challenge `r ∈ {2, 3, 4}`!
    (let deltaCheat := fun X : Int => (X - 2) * (X - 3) * (X - 4)
     deltaCheat 0 + deltaCheat 1 = -30 ∧
     deltaCheat 2 = 0 ∧ deltaCheat 3 = 0 ∧ deltaCheat 4 = 0) := by
  refine ⟨?_, ?_, by decide⟩
  · intro g r1 r2
    dsimp only
    refine ⟨by omega, rfl, rfl⟩
  · intro d0 d1 d2 r0 r1 r2
    have hVand :
        (r2 - r1) * evalQuad d0 d1 d2 r0 - (r2 - r0) * evalQuad d0 d1 d2 r1 +
          (r1 - r0) * evalQuad d0 d1 d2 r2 =
          d2 * (r1 - r0) * (r2 - r0) * (r2 - r1) := by unfold evalQuad; grind
    refine ⟨hVand, ?_⟩
    intro hSumNe h01 h12 ⟨z0, z1, z2⟩
    rw [z0, z1, z2] at hVand
    -- First deduce `d2 = 0` from `d2 * (r1 - r0) * (r2 - r0) * (r2 - r1) = 0`:
    have hd2 : d2 = 0 := by
      by_cases hd2Eq : d2 = 0
      · exact hd2Eq
      · exfalso
        have p1 : d2 * (r1 - r0) ≠ 0 := Int.mul_ne_zero hd2Eq (by omega)
        have p2 : d2 * (r1 - r0) * (r2 - r0) ≠ 0 := Int.mul_ne_zero p1 (by omega)
        have p3 : d2 * (r1 - r0) * (r2 - r0) * (r2 - r1) ≠ 0 := Int.mul_ne_zero p2 (by omega)
        omega
    -- Next deduce `d1 = 0` and `d0 = 0` from `evalQuad d0 d1 0 r0 = 0` and `evalQuad d0 d1 0 r1 = 0`:
    unfold evalQuad at z0 z1 hSumNe
    rw [hd2] at z0 z1 hSumNe
    have hDiffLin : d1 * (r1 - r0) = 0 := by grind
    have hd1 : d1 = 0 := by
      by_cases hd1Eq : d1 = 0
      · exact hd1Eq
      · exfalso
        exact (Int.mul_ne_zero hd1Eq (by omega)) hDiffLin
    rw [hd1] at z0 hSumNe
    omega

/-- Hamming distance on `4` evaluation points `{0, 1, 2, 3}` between `(u0, u1, u2, u3)` and `(v0, v1, v2, v3)`. -/
def hamming4 (u0 u1 u2 u3 v0 v1 v2 v3 : Int) : Nat :=
  (if u0 = v0 then 0 else 1) +
  (if u1 = v1 then 0 else 1) +
  (if u2 = v2 then 0 else 1) +
  (if u3 = v3 then 0 else 1)

/-- Theorem 3: Reed–Solomon / Berlekamp–Welch Unique Decoding (`n = 4, k = 2, d = 3, e ≤ 1`)
    vs. Beyond-Radius (`e = 2`) Dual-Codeword Tie. -/
theorem reed_solomon_unique_decoding_radius_vs_half_distance_ambiguity :
    -- (1) Universal Unique Decoding Within Radius `e ≤ 1` on `{0, 1, 2, 3}`:
    --     any two affine message polynomials `a0 + a1*x` and `b0 + b1*x` at Hamming distance `≤ 1`
    --     from ANY received word `(y0, y1, y2, y3)` are identical (`a0 = b0 ∧ a1 = b1`)!
    (∀ a0 a1 b0 b1 y0 y1 y2 y3 : Int,
      hamming4 a0 (a0 + a1) (a0 + 2 * a1) (a0 + 3 * a1) y0 y1 y2 y3 ≤ 1 →
      hamming4 b0 (b0 + b1) (b0 + 2 * b1) (b0 + 3 * b1) y0 y1 y2 y3 ≤ 1 →
      a0 = b0 ∧ a1 = b1) ∧
    -- (2) Explicit Berlekamp–Welch Key Equation Witness for `P(x) = 3 + 2x` corrupted at `x = 2` (`7 ↦ 99`):
    --     Error locator `E(x) = x - 2` and `N(x) = (x - 2)*(3 + 2x)` satisfy `E(x_i) * y_i = N(x_i)` at ALL 4 nodes!
    (let y : Fin 4 → Int := fun i => match i.val with | 0 => 3 | 1 => 5 | 2 => 99 | _ => 9
     let E := fun x : Int => x - 2
     let N := fun x : Int => (x - 2) * (3 + 2 * x)
     (∀ i : Fin 4, E (Int.ofNat i.val) * y i = N (Int.ofNat i.val)) ∧ E 2 = 0 ∧ E 0 ≠ 0 ∧ E 1 ≠ 0 ∧ E 3 ≠ 0) ∧
    -- (3) Premise-Failure Counterexample (`e = 2` errors, `2e = 4 > d = 3`):
    --     Received `(0, 0, 3, 4)` is at exact Hamming distance `2` from BOTH `P(x) = 0` (`(0,0,0,0)`) AND `Q(x) = 1 + x` (`(1,2,3,4)`)!
    (hamming4 0 0 0 0 0 0 3 4 = 2 ∧
     hamming4 1 2 3 4 0 0 3 4 = 2 ∧
     (0 : Int) ≠ 1) := by
  refine ⟨?_, by decide, by decide⟩
  intro a0 a1 b0 b1 y0 y1 y2 y3 hA hB
  unfold hamming4 at hA hB
  have t0 : (if a0 = b0 then 0 else 1) ≤ (if a0 = y0 then 0 else 1) + (if b0 = y0 then 0 else 1) := by
    split <;> split <;> split <;> omega
  have t1 : (if a0 + a1 = b0 + b1 then 0 else 1) ≤ (if a0 + a1 = y1 then 0 else 1) + (if b0 + b1 = y1 then 0 else 1) := by
    split <;> split <;> split <;> omega
  have t2 : (if a0 + 2 * a1 = b0 + 2 * b1 then 0 else 1) ≤ (if a0 + 2 * a1 = y2 then 0 else 1) + (if b0 + 2 * b1 = y2 then 0 else 1) := by
    split <;> split <;> split <;> omega
  have t3 : (if a0 + 3 * a1 = b0 + 3 * b1 then 0 else 1) ≤ (if a0 + 3 * a1 = y3 then 0 else 1) + (if b0 + 3 * b1 = y3 then 0 else 1) := by
    split <;> split <;> split <;> omega
  have hTri :
      (if a0 = b0 then 0 else 1) +
      (if a0 + a1 = b0 + b1 then 0 else 1) +
      (if a0 + 2 * a1 = b0 + 2 * b1 then 0 else 1) +
      (if a0 + 3 * a1 = b0 + 3 * b1 then 0 else 1) ≤ 2 := by omega
  clear hA hB t0 t1 t2 t3
  split at hTri <;> split at hTri <;> split at hTri <;> split at hTri <;> omega

/-- Exact `3 × 3` determinant over `Int`. -/
def det3 (M : Fin 3 → Fin 3 → Int) : Int :=
  let i0 : Fin 3 := ⟨0, by decide⟩
  let i1 : Fin 3 := ⟨1, by decide⟩
  let i2 : Fin 3 := ⟨2, by decide⟩
  M i0 i0 * (M i1 i1 * M i2 i2 - M i1 i2 * M i2 i1) -
  M i0 i1 * (M i1 i0 * M i2 i2 - M i1 i2 * M i2 i0) +
  M i0 i2 * (M i1 i0 * M i2 i1 - M i1 i1 * M i2 i0)

/-- Theorem 4: Croot–Lev–Pach / Ellenberg–Gijswijt Slice-Rank Determinant Obstruction
    (`det₃` Vanishes on All `2`-Slice Tensors vs. Nonzero `d₀ d₁ d₂ ≠ 0` Diagonal) vs. Rank-Deficient Diagonal Drop. -/
theorem croot_lev_pach_slice_rank_diagonal_obstruction_vs_rank_deficient_drop :
    -- (1) Universal Vanishing of `det₃` on Every Sum of Two Outer Products `u1 ⊗ v1 + u2 ⊗ v2`:
    (∀ u1 u2 v1 v2 : Fin 3 → Int,
      det3 (fun i j => u1 i * v1 j + u2 i * v2 j) = 0) ∧
    -- (2) Universal Slice-Rank `= 3` Lower Bound on Every Full-Support `3 × 3` Diagonal Matrix:
    (∀ d0 d1 d2 : Int,
      d0 ≠ 0 → d1 ≠ 0 → d2 ≠ 0 →
      let diagM : Fin 3 → Fin 3 → Int := fun i j =>
        if i = j then
          match i.val with
          | 0 => d0
          | 1 => d1
          | _ => d2
        else 0
      det3 diagM = d0 * d1 * d2 ∧
      ¬ ∃ u1 u2 v1 v2 : Fin 3 → Int, ∀ i j : Fin 3, diagM i j = u1 i * v1 j + u2 i * v2 j) ∧
    -- (3) Premise-Failure Counterexample: dropping `d2 = 0` (`diag(1, 1, 0)`) admits an exact `2`-slice decomposition!
    (∃ u1 u2 v1 v2 : Fin 3 → Int,
      ∀ i j : Fin 3,
        (if i = j ∧ i.val < 2 then (1 : Int) else 0) = u1 i * v1 j + u2 i * v2 j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u1 u2 v1 v2
    unfold det3
    grind
  · intro d0 d1 d2 hd0 hd1 hd2
    dsimp only
    have hDetDiag :
        det3 (fun i j : Fin 3 =>
          if i = j then match i.val with | 0 => d0 | 1 => d1 | _ => d2 else 0) =
          d0 * d1 * d2 := by unfold det3; dsimp only; grind
    refine ⟨hDetDiag, ?_⟩
    intro ⟨u1, u2, v1, v2, hEq⟩
    have hFunEq :
        (fun i j : Fin 3 =>
          if i = j then match i.val with | 0 => d0 | 1 => d1 | _ => d2 else 0) =
          (fun i j : Fin 3 => u1 i * v1 j + u2 i * v2 j) := by
      funext i j
      exact hEq i j
    have hZero :
        det3 (fun i j : Fin 3 => u1 i * v1 j + u2 i * v2 j) = 0 := by unfold det3; grind
    rw [hFunEq] at hDetDiag
    rw [hZero] at hDetDiag
    have hProdNe : d0 * d1 * d2 ≠ 0 :=
      Int.mul_ne_zero (Int.mul_ne_zero hd0 hd1) hd2
    exact hProdNe hDetDiag.symm
  · refine ⟨(fun i : Fin 3 => if i.val = 0 then 1 else 0),
            (fun i : Fin 3 => if i.val = 1 then 1 else 0),
            (fun i : Fin 3 => if i.val = 0 then 1 else 0),
            (fun i : Fin 3 => if i.val = 1 then 1 else 0), ?_⟩
    decide

end CommonGround.Frontier.SchwartzZippelNullstellensatzAndSumCheck
