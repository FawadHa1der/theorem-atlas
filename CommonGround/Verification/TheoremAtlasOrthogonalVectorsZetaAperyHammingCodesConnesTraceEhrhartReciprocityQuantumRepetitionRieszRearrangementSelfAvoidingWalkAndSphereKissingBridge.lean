/-
  Verification Suite #608 (V207):
  9-Repository Specialized Frontier Synthesis — Orthogonal Vectors (`eth`),
  Zeta Apéry Irrationality Exclusion (`zeta23`), Hamming `[7, 4, 3]` Codes (`oai-codes`),
  Connes Cyclic Trace (`oai-connes`), Ehrhart–Macdonald Reciprocity (`oai-ehrhart`),
  Quantum Repetition Stabilizers (`oai-qrep`), Riesz Rearrangement (`oai-riesz`),
  Self-Avoiding Walk Loop Deficit (`oai-saw`), and `D₄` 24-Sphere Kissing Shell (`oai-sphere`)
  ============================================================================================

  Pure-Core Lean 4.33.0 (`0` external imports, `0` `sorry`, `0` `admit`).
  Every cross-domain mechanism is paired with both a constructive positive witness and an
  explicit premise-failure counterexample.
-/

namespace CommonGround.Verification.Tier4NineFrontierBridges

/-! ## 1. `eth`: Williams Boolean Polynomial Indicator for Orthogonal Vectors vs. Non-Boolean False Root -/

def bitAt (mask k : Nat) : Int :=
  if ((mask >>> k) &&& 1) == 1 then 1 else 0

def dot4 (u v : Nat → Int) : Int :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3

def ovPoly4 (u v : Nat → Int) : Int :=
  (1 - u 0 * v 0) * (1 - u 1 * v 1) * (1 - u 2 * v 2) * (1 - u 3 * v 3)

def checkAllBooleanOv4 : Bool :=
  (List.range 16).all fun mu =>
    (List.range 16).all fun mv =>
      let u := bitAt mu
      let v := bitAt mv
      ovPoly4 u v == (if dot4 u v == 0 then 1 else 0)

def nonBoolU : Nat → Int
  | 0 => 2 | 1 => 2 | _ => 0

def nonBoolV : Nat → Int
  | 0 => 1 | 1 => 1 | _ => 0

/-- **`eth` Bridge**: Across all `16 × 16 = 256` pairs in `{0, 1}⁴`, `∏_{k<4} (1 - u_k v_k)` equals `1`
    iff `⟨u, v⟩ = 0` and `0` otherwise; but on non-idempotent `{0, 1, 2}⁴` inputs `u = (2, 2, 0, 0)`,
    `v = (1, 1, 0, 0)`, `⟨u, v⟩ = 4 ≠ 0` while `∏ (1 - u_k v_k) = (-1)(-1) = +1` (false OV root)! -/
theorem eth_orthogonal_vectors_polynomial_indicator_vs_nonboolean_root_bridge :
    checkAllBooleanOv4 = true ∧
    dot4 nonBoolU nonBoolV = 4 ∧
    ovPoly4 nonBoolU nonBoolV = 1 := by
  decide

/-! ## 2. `zeta23`: Telescoping Series Acceleration & Dirichlet–Apéry Irrationality Gap Exclusion -/

/-- Exact cross-multiplied telescoping identity:
    `S_N = ∑_{n=1}^N 1/(n(n+1)) = N/(N+1)` encoded division-free via induction on partial numerators:
    `N/(N+1) + 1/((N+1)(N+2)) = (N+1)/(N+2)`, i.e., `N * (N + 2) + 1 = (N + 1)²`. -/
theorem telescoping_step_numerator_identity (N : Int) :
    N * (N + 2) + 1 = (N + 1) * (N + 1) := by
  have h1 : N * (N + 2) + 1 = N * N + 2 * N + 1 := by
    simp only [Int.mul_add]
    omega
  have h2 : (N + 1) * (N + 1) = N * N + 2 * N + 1 := by
    simp only [Int.add_mul, Int.mul_add]
    omega
  rw [h1, h2]

/-- **Dirichlet–Apéry Integer Linear-Form Irrationality Criterion** vs. **Slow-Growth Premise Failure**:
    1. If an Apéry integer linear form `L = A * p - B * q` is nonzero (`L ≠ 0`) yet strictly bounded inside
       `(-1, 1)`, no integer solution `(p, q)` can exist (`False`)!
    2. Premise Failure: if `|A * p - B * q|` only reaches `1` (`|3 * 1 - 1 * 2| = 1`), rationality (`p/q = 1/2`)
       is NOT excluded! -/
theorem zeta23_telescoping_apery_acceleration_and_liouville_irrationality_gap_bridge :
    (∀ A B p q : Int, A * p - B * q ≠ 0 → -1 < A * p - B * q → A * p - B * q < 1 → False) ∧
    ((3 : Int) * 1 - 1 * 2 = 1 ∧ (3 : Int) * 1 - 1 * 2 ≠ 0) := by
  constructor
  · intro A B p q hne hgt hlt
    omega
  · decide

/-! ## 3. `oai-codes`: `[7, 4, 3]` Hamming Parity-Check Code vs. 2-Bit Error Syndrome Aliasing -/

def bBit (m k : Nat) : Nat := (m >>> k) &&& 1

def hamming74Encode (m : Nat) : Nat → Nat
  | 0 => bBit m 0
  | 1 => bBit m 1
  | 2 => bBit m 2
  | 3 => bBit m 3
  | 4 => (bBit m 0 + bBit m 1 + bBit m 2) % 2
  | 5 => (bBit m 0 + bBit m 1 + bBit m 3) % 2
  | 6 => (bBit m 0 + bBit m 2 + bBit m 3) % 2
  | _ => 0

def hammingWeight7 (c : Nat → Nat) : Nat :=
  c 0 + c 1 + c 2 + c 3 + c 4 + c 5 + c 6

def hamming74Syndrome (c : Nat → Nat) : Nat :=
  let s0 := (c 0 + c 1 + c 2 + c 4) % 2
  let s1 := (c 0 + c 1 + c 3 + c 5) % 2
  let s2 := (c 0 + c 2 + c 3 + c 6) % 2
  s0 + 2 * s1 + 4 * s2

def singleBitError7 (pos : Nat) : Nat → Nat :=
  fun j => if j == pos then 1 else 0

def doubleBitError01 : Nat → Nat :=
  fun j => if j == 0 || j == 1 then 1 else 0

def verifyHamming74Code : Bool :=
  let zeroSyndromeAll16 := (List.range 16).all fun m => hamming74Syndrome (hamming74Encode m) == 0
  let minDistAtLeast3 := (List.range 15).all fun k => hammingWeight7 (hamming74Encode (k + 1)) >= 3
  let syndromes := (List.range 7).map fun pos => hamming74Syndrome (singleBitError7 pos)
  let distinctNonzero := syndromes.all (fun s => s >= 1 && s <= 7) &&
    (List.range 7).all fun i => (List.range 7).all fun j =>
      if i == j then true else hamming74Syndrome (singleBitError7 i) != hamming74Syndrome (singleBitError7 j)
  zeroSyndromeAll16 && minDistAtLeast3 && distinctNonzero

/-- **`oai-codes` Bridge**: Every nonzero codeword of `[7, 4, 3]` Hamming has weight `≥ 3` and `0` syndrome,
    and all `7` single-bit errors yield distinct syndromes in `{1..7}`; whereas a `2`-bit error on `{0, 1}`
    aliases the exact single-bit syndrome of parity bit `6` (`7 ⊕ 3 = 4`), causing miscorrection! -/
theorem codes_hamming_7_4_3_minimum_distance_and_syndrome_decoding_vs_double_error_bridge :
    verifyHamming74Code = true ∧
    hamming74Syndrome doubleBitError01 = hamming74Syndrome (singleBitError7 6) ∧
    hamming74Syndrome doubleBitError01 = 4 := by
  decide

/-! ## 4. `oai-connes`: Cyclic Trace `[A, B]` Vanishing vs. Non-Tracial Weighted State Anomaly -/

structure Mat2Int where
  a00 : Int
  a01 : Int
  a10 : Int
  a11 : Int
  deriving DecidableEq, Repr

def mul2 (A B : Mat2Int) : Mat2Int :=
  { a00 := A.a00 * B.a00 + A.a01 * B.a10
    a01 := A.a00 * B.a01 + A.a01 * B.a11
    a10 := A.a10 * B.a00 + A.a11 * B.a10
    a11 := A.a10 * B.a01 + A.a11 * B.a11 }

def comm2 (A B : Mat2Int) : Mat2Int :=
  let AB := mul2 A B
  let BA := mul2 B A
  { a00 := AB.a00 - BA.a00
    a01 := AB.a01 - BA.a01
    a10 := AB.a10 - BA.a10
    a11 := AB.a11 - BA.a11 }

def tr2 (X : Mat2Int) : Int := X.a00 + X.a11

def weightedTr2 (w0 w1 : Int) (X : Mat2Int) : Int := w0 * X.a00 + w1 * X.a11

/-- **`oai-connes` Bridge**: `Tr([A, B]) = 0` holds universally for all `A, B ∈ M₂(ℤ)` (0-dimensional
    Hochschild–Connes cycle), whereas a non-tracial KMS weight `(1, 2)` has `φ([E₀₁, E₁₀]) = -1 ≠ 0`! -/
theorem connes_cyclic_trace_commutator_vanishing_vs_weighted_shift_anomaly_bridge :
    (∀ A B : Mat2Int, tr2 (comm2 A B) = 0) ∧
    weightedTr2 1 2 (comm2 ⟨0, 1, 0, 0⟩ ⟨0, 0, 1, 0⟩) = -1 := by
  constructor
  · intro A B
    unfold tr2 comm2 mul2
    dsimp
    have hc1 : B.a00 * A.a00 = A.a00 * B.a00 := Int.mul_comm _ _
    have hc2 : B.a01 * A.a10 = A.a10 * B.a01 := Int.mul_comm _ _
    have hc3 : B.a10 * A.a01 = A.a01 * B.a10 := Int.mul_comm _ _
    have hc4 : B.a11 * A.a11 = A.a11 * B.a11 := Int.mul_comm _ _
    rw [hc1, hc2, hc3, hc4]
    omega
  · decide

/-! ## 5. `oai-ehrhart`: Ehrhart–Macdonald `(-1)³` Cube Reciprocity vs. Half-Integral Period-2 Defect -/

def ehrhartCube3 (t : Int) : Int := (t + 1) * (t + 1) * (t + 1)
def interiorCube3 (t : Int) : Int := (t - 1) * (t - 1) * (t - 1)

def halfPolytopeCount (t : Nat) : Int := Int.ofNat (t / 2 + 1)

/-- **`oai-ehrhart` Bridge**: Unit 3-cube satisfies exact Ehrhart–Macdonald reciprocity
    `(-1)³ L_{[0,1]³}(-t) = (t - 1)³ = L_{(0,1)³}(t)` for all `t : Int`; whereas non-integral `[0, 1/2]`
    has `L(1) = 1, L(2) = 2, L(3) = 2`, which NO degree-1 polynomial `a t + b` can interpolate! -/
theorem ehrhart_macdonald_cube_reciprocity_vs_half_integral_quasipolynomial_bridge :
    (∀ t : Int, - ehrhartCube3 (-t) = interiorCube3 t) ∧
    halfPolytopeCount 1 = 1 ∧ halfPolytopeCount 2 = 2 ∧ halfPolytopeCount 3 = 2 ∧
    (∀ a b : Int, ¬ (a * 1 + b = 1 ∧ a * 2 + b = 2 ∧ a * 3 + b = 2)) := by
  refine ⟨?_, by decide, by decide, by decide, ?_⟩
  · intro t
    unfold ehrhartCube3 interiorCube3
    have hneg : (-t + 1) = -(t - 1) := by omega
    rw [hneg, Int.neg_mul_neg]
    have h3 : (t - 1) * (t - 1) * -(t - 1) = -((t - 1) * (t - 1) * (t - 1)) := by
      simp only [Int.mul_neg]
    rw [h3]
    omega
  · intro a b h
    omega

/-! ## 6. `oai-qrep`: 3-Qubit Bit-Flip Stabilizer Decoding vs. Undetected Phase-Flip Logical Error -/

def stabZ0Z1 (ψ : Nat → Int) : Nat → Int :=
  fun x => if (((x >>> 2) &&& 1) ^^^ ((x >>> 1) &&& 1)) == 0 then ψ x else - ψ x

def stabZ1Z2 (ψ : Nat → Int) : Nat → Int :=
  fun x => if (((x >>> 1) &&& 1) ^^^ (x &&& 1)) == 0 then ψ x else - ψ x

def flipX (bit : Nat) (ψ : Nat → Int) : Nat → Int :=
  fun x => ψ (x ^^^ (1 <<< bit))

def phaseZ0 (ψ : Nat → Int) : Nat → Int :=
  fun x => if ((x >>> 2) &&& 1) == 0 then ψ x else - ψ x

def plusLogical : Nat → Int
  | 0 => 1 | 7 => 1 | _ => 0

def minusLogical : Nat → Int
  | 0 => 1 | 7 => -1 | _ => 0

def eqState8 (φ ψ : Nat → Int) : Bool :=
  (List.range 8).all fun x => φ x == ψ x

def negState8 (ψ : Nat → Int) : Nat → Int := fun x => - ψ x

def dotState8 (φ ψ : Nat → Int) : Int :=
  (List.range 8).foldl (fun acc x => acc + φ x * ψ x) 0

/-- **`oai-qrep` Bridge**: `Z₀Z₁` and `Z₁Z₂` stabilize `|+_L⟩` and assign distinct `±1` syndromes
    `(+1,-1), (-1,-1), (-1,+1)` to all 3 single-qubit bit flips `X₀, X₁, X₂`; whereas single-qubit
    phase flip `Z₀` maps `|+_L⟩ ↦ |-_L⟩` (`⟨+_L | -_L⟩ = 0`) while triggering `(+1, +1)` trivial syndrome! -/
theorem qrep_three_qubit_bitflip_syndrome_table_vs_undetected_phase_flip_bridge :
    -- Code state stabilized:
    (eqState8 (stabZ0Z1 plusLogical) plusLogical = true ∧
     eqState8 (stabZ1Z2 plusLogical) plusLogical = true) ∧
    -- Distinct nonzero syndromes on X_2 (q0), X_1 (q1), X_0 (q2):
    (eqState8 (stabZ0Z1 (flipX 2 plusLogical)) (negState8 (flipX 2 plusLogical)) = true ∧
     eqState8 (stabZ1Z2 (flipX 2 plusLogical)) (flipX 2 plusLogical) = true) ∧
    (eqState8 (stabZ0Z1 (flipX 1 plusLogical)) (negState8 (flipX 1 plusLogical)) = true ∧
     eqState8 (stabZ1Z2 (flipX 1 plusLogical)) (negState8 (flipX 1 plusLogical)) = true) ∧
    (eqState8 (stabZ0Z1 (flipX 0 plusLogical)) (flipX 0 plusLogical) = true ∧
     eqState8 (stabZ1Z2 (flipX 0 plusLogical)) (negState8 (flipX 0 plusLogical)) = true) ∧
    -- Premise failure: Z₀ flips |+_L⟩ to orthogonal |-_L⟩ with UNDETECTED (+1, +1) syndrome!
    (eqState8 (phaseZ0 plusLogical) minusLogical = true ∧
     dotState8 plusLogical (phaseZ0 plusLogical) = 0 ∧
     eqState8 (stabZ0Z1 (phaseZ0 plusLogical)) (phaseZ0 plusLogical) = true ∧
     eqState8 (stabZ1Z2 (phaseZ0 plusLogical)) (phaseZ0 plusLogical) = true) := by
  decide

/-! ## 7. `oai-riesz`: Hardy–Littlewood & Riesz Convolution Rearrangement vs. Indefinite Kernel Failure -/

def quadConvZ4 (K f : Nat → Int) : Int :=
  (List.range 4).foldl (fun acc x =>
    acc + (List.range 4).foldl (fun inAcc y => inAcc + f x * K ((x + 4 - y) % 4) * f y) 0) 0

def attractiveKernelZ4 : Nat → Int
  | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 1 | _ => 0

def indefiniteKernelZ4 : Nat → Int
  | 0 => -1 | 1 => 1 | 2 => 0 | 3 => 1 | _ => 0

def splitProfileZ4 : Nat → Int
  | 0 => 1 | 2 => 1 | _ => 0

def rearrangedProfileZ4 : Nat → Int
  | 0 => 2 | _ => 0

/-- **`oai-riesz` Bridge**: Universal 2-point rearrangement `a₀ ≥ a₁, b₀ ≥ b₁ ⟹ a₀ b₁ + a₁ b₀ ≤ a₀ b₀ + a₁ b₁`
    and non-negative symmetric-decreasing Riesz energy increase (`4 → 8` on `ℤ/4ℤ`), contrasted with
    indefinite kernel `K(0) = -1, K(±1) = +1` where concentration drops energy from `-2` down to `-4`! -/
theorem riesz_rearrangement_pairing_and_convolution_vs_indefinite_kernel_bridge :
    (∀ a0 a1 b0 b1 : Int, a1 ≤ a0 → b1 ≤ b0 → a0 * b1 + a1 * b0 ≤ a0 * b0 + a1 * b1) ∧
    (quadConvZ4 attractiveKernelZ4 splitProfileZ4 = 4 ∧
     quadConvZ4 attractiveKernelZ4 rearrangedProfileZ4 = 8) ∧
    (quadConvZ4 indefiniteKernelZ4 splitProfileZ4 = -2 ∧
     quadConvZ4 indefiniteKernelZ4 rearrangedProfileZ4 = -4) := by
  refine ⟨?_, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
  intro a0 a1 b0 b1 ha hb
  have hprod : 0 ≤ (a0 - a1) * (b0 - b1) := Int.mul_nonneg (by omega) (by omega)
  have hexp : (a0 - a1) * (b0 - b1) = a0 * b0 - a0 * b1 - a1 * b0 + a1 * b1 := by
    simp only [Int.sub_mul, Int.mul_sub]
    omega
  omega

/-! ## 8. `oai-saw`: Self-Avoiding Walk Submultiplicativity vs. 4-Step Non-Backtracking Loop Deficit -/

def stepsZ2 : List (Int × Int) := [(1, 0), (-1, 0), (0, 1), (0, -1)]

def extendSaw : Nat → (Int × Int) → List (Int × Int) → Nat
  | 0, _, _ => 1
  | n + 1, cur, visited =>
      stepsZ2.foldl (fun acc st =>
        let nxt := (cur.1 + st.1, cur.2 + st.2)
        if visited.contains nxt then acc
        else acc + extendSaw n nxt (nxt :: visited)) 0

def sawCount (n : Nat) : Nat := extendSaw n (0, 0) [(0, 0)]

def extendNbw : Nat → (Int × Int) → Option (Int × Int) → Nat
  | 0, _, _ => 1
  | n + 1, cur, prev =>
      stepsZ2.foldl (fun acc st =>
        let nxt := (cur.1 + st.1, cur.2 + st.2)
        if prev == some nxt then acc
        else acc + extendNbw n nxt (some cur)) 0

def nbwCount (n : Nat) : Nat := extendNbw n (0, 0) none

/-- **`oai-saw` Bridge**: Exact `ℤ²` SAW counts `c₁ = 4, c₂ = 12, c₃ = 36, c₄ = 100` obey submultiplicativity
    `c₃ ≤ c₁ c₂` (`36 ≤ 48`) and `c₄ ≤ c₂²` (`100 ≤ 144`), whereas non-backtracking walks overcount `n = 4`
    by `108 - 100 = 8` oriented unit-square self-intersections! -/
theorem saw_self_avoiding_walk_submultiplicativity_and_square_loop_deficit_bridge :
    sawCount 1 = 4 ∧ sawCount 2 = 12 ∧ sawCount 3 = 36 ∧ sawCount 4 = 100 ∧
    sawCount 3 ≤ sawCount 1 * sawCount 2 ∧
    sawCount 4 ≤ sawCount 2 * sawCount 2 ∧
    nbwCount 4 = 108 ∧
    nbwCount 4 - sawCount 4 = 8 := by
  decide

/-! ## 9. `oai-sphere`: `D₄` Checkerboard `24`-Sphere Kissing Shell vs. Odd-Parity Coset Collapse -/

def coords3 : List Int := [-1, 0, 1]

def countD4KissingShell : Nat :=
  coords3.foldl (fun acc x0 =>
    coords3.foldl (fun acc1 x1 =>
      coords3.foldl (fun acc2 x2 =>
        coords3.foldl (fun acc3 x3 =>
          let nsq := x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3
          if (x0 + x1 + x2 + x3) % 2 == 0 && nsq == 2 then acc3 + 1 else acc3) acc2) acc1) acc) 0

def countZ4UnitKissing : Nat :=
  coords3.foldl (fun acc x0 =>
    coords3.foldl (fun acc1 x1 =>
      coords3.foldl (fun acc2 x2 =>
        coords3.foldl (fun acc3 x3 =>
          if x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3 == 1 then acc3 + 1 else acc3) acc2) acc1) acc) 0

theorem int_sq_nonneg_and_pos (z : Int) :
    0 ≤ z * z ∧ (z ≠ 0 → 1 ≤ z * z) ∧ (z * z = 1 → z = 1 ∨ z = -1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Decidable.byCases
      (fun h : 0 ≤ z => Int.mul_nonneg h h)
      (fun h : ¬ 0 ≤ z => by
        have hn : 0 ≤ -z := by omega
        have hm : (-z) * (-z) = z * z := Int.neg_mul_neg z z
        rw [← hm]
        exact Int.mul_nonneg hn hn)
  · intro hne
    exact Decidable.byCases
      (fun hp : 1 ≤ z => by
        have hmul : 1 * 1 ≤ z * z := Int.mul_le_mul hp hp (by decide) (by omega)
        omega)
      (fun hnp : ¬ 1 ≤ z => by
        have hn : 1 ≤ -z := by omega
        have hm : (-z) * (-z) = z * z := Int.neg_mul_neg z z
        have hmul : 1 * 1 ≤ (-z) * (-z) := Int.mul_le_mul hn hn (by decide) (by omega)
        omega)
  · intro hsq1
    exact Decidable.byCases
      (fun hle1 : z ≤ 1 =>
        Decidable.byCases
          (fun hge_neg1 : -1 ≤ z => by
            have hcases : z = -1 ∨ z = 0 ∨ z = 1 := by omega
            rcases hcases with rfl | rfl | rfl <;> omega)
          (fun hlt_neg1 : ¬ -1 ≤ z => by
            have hn : 2 ≤ -z := by omega
            have hm : (-z) * (-z) = z * z := Int.neg_mul_neg z z
            have hmul : 2 * 2 ≤ (-z) * (-z) := Int.mul_le_mul hn hn (by decide) (by omega)
            omega))
      (fun hgt1 : ¬ z ≤ 1 => by
        have hp : 2 ≤ z := by omega
        have hmul : 2 * 2 ≤ z * z := Int.mul_le_mul hp hp (by decide) (by omega)
        omega)

/-- Universal `D₄` minimum squared norm over **all** `ℤ⁴`: every nonzero even-sum lattice vector satisfies `‖x‖₂² ≥ 2`! -/
theorem d4_universal_min_norm_sq_ge_two
    (x0 x1 x2 x3 : Int)
    (hne : x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0)
    (heven : (x0 + x1 + x2 + x3) % 2 = 0) :
    2 ≤ x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3 := by
  have ⟨nn0, p0, s0⟩ := int_sq_nonneg_and_pos x0
  have ⟨nn1, p1, s1⟩ := int_sq_nonneg_and_pos x1
  have ⟨nn2, p2, s2⟩ := int_sq_nonneg_and_pos x2
  have ⟨nn3, p3, s3⟩ := int_sq_nonneg_and_pos x3
  exact Decidable.byContradiction fun hlt2 => by
    rcases hne with h0 | h1 | h2 | h3
    · have ge1 : 1 ≤ x0 * x0 := p0 h0
      have eq1 : x0 * x0 = 1 ∧ x1 * x1 = 0 ∧ x2 * x2 = 0 ∧ x3 * x3 = 0 := by omega
      have z1 : x1 = 0 := Decidable.byContradiction fun c => by have := p1 c; omega
      have z2 : x2 = 0 := Decidable.byContradiction fun c => by have := p2 c; omega
      have z3 : x3 = 0 := Decidable.byContradiction fun c => by have := p3 c; omega
      rcases s0 eq1.1 with rfl | rfl <;> subst z1 z2 z3 <;> omega
    · have ge1 : 1 ≤ x1 * x1 := p1 h1
      have eq1 : x1 * x1 = 1 ∧ x0 * x0 = 0 ∧ x2 * x2 = 0 ∧ x3 * x3 = 0 := by omega
      have z0 : x0 = 0 := Decidable.byContradiction fun c => by have := p0 c; omega
      have z2 : x2 = 0 := Decidable.byContradiction fun c => by have := p2 c; omega
      have z3 : x3 = 0 := Decidable.byContradiction fun c => by have := p3 c; omega
      rcases s1 eq1.1 with rfl | rfl <;> subst z0 z2 z3 <;> omega
    · have ge1 : 1 ≤ x2 * x2 := p2 h2
      have eq1 : x2 * x2 = 1 ∧ x0 * x0 = 0 ∧ x1 * x1 = 0 ∧ x3 * x3 = 0 := by omega
      have z0 : x0 = 0 := Decidable.byContradiction fun c => by have := p0 c; omega
      have z1 : x1 = 0 := Decidable.byContradiction fun c => by have := p1 c; omega
      have z3 : x3 = 0 := Decidable.byContradiction fun c => by have := p3 c; omega
      rcases s2 eq1.1 with rfl | rfl <;> subst z0 z1 z3 <;> omega
    · have ge1 : 1 ≤ x3 * x3 := p3 h3
      have eq1 : x3 * x3 = 1 ∧ x0 * x0 = 0 ∧ x1 * x1 = 0 ∧ x2 * x2 = 0 := by omega
      have z0 : x0 = 0 := Decidable.byContradiction fun c => by have := p0 c; omega
      have z1 : x1 = 0 := Decidable.byContradiction fun c => by have := p1 c; omega
      have z2 : x2 = 0 := Decidable.byContradiction fun c => by have := p2 c; omega
      rcases s3 eq1.1 with rfl | rfl <;> subst z0 z1 z2 <;> omega

/-- **`oai-sphere` Bridge**:
    1. Every nonzero `x ∈ D₄` (`∑ x_i ≡ 0 mod 2`) across **all** `ℤ⁴` has `‖x‖₂² ≥ 2`, with **24** kissing spheres
       at `‖x‖₂² = 2` (`3×` the `8` kissing neighbors of `ℤ⁴`)!
    2. Universal Obtuse Spherical Code Bound: if `0 ≤ M * d - M * (M - 1)` with `M ≥ 1` (from `0 ≤ ‖∑ v_i‖²`
       when `‖v_i‖² = d` and `⟨v_i, v_j⟩ ≤ -1` for `i ≠ j`), then `M ≤ d + 1`!
    3. Premise Failure: dropping even parity admits `(1, 0, 0, 0)` with `‖x‖₂² = 1 < 2`! -/
theorem sphere_d4_checkerboard_kissing_24_and_welch_simplex_cap_vs_odd_parity_defect_bridge :
    countD4KissingShell = 24 ∧
    countZ4UnitKissing = 8 ∧
    (∀ x0 x1 x2 x3 : Int,
      (x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0) →
      (x0 + x1 + x2 + x3) % 2 = 0 →
      2 ≤ x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3) ∧
    (∀ M d : Int, 0 < M → 0 ≤ M * d - M * (M - 1) → M ≤ d + 1) ∧
    ((1 : Int) * 1 + 0 * 0 + 0 * 0 + 0 * 0 = 1 ∧ ((1 : Int) + 0 + 0 + 0) % 2 ≠ 0) := by
  refine ⟨by decide, by decide, d4_universal_min_norm_sq_ge_two, ?_, ⟨by decide, by decide⟩⟩
  intro M d hM hgram
  have hfac : M * d - M * (M - 1) = M * (d + 1 - M) := by
    simp only [Int.mul_sub, Int.mul_add, Int.mul_one]
    omega
  rw [hfac] at hgram
  exact Decidable.byContradiction fun hlt => by
    have hneg : d + 1 - M < 0 := by omega
    have hprod_neg : M * (d + 1 - M) < 0 := Int.mul_neg_of_pos_of_neg hM hneg
    omega

end CommonGround.Verification.Tier4NineFrontierBridges
