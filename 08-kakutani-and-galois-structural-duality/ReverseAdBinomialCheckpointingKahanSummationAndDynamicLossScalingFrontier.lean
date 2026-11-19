/-
  08-kakutani-and-galois-structural-duality/ReverseAdBinomialCheckpointingKahanSummationAndDynamicLossScalingFrontier.lean

  Frontier #127 (Wave V252):
  1. Griewank–Walther Binomial Reverse-Mode AD Checkpointing (`Revolve` Pascal Capacity
     `β(s, r) = C(s + r, s)`) & Exact Adjoint Rematerialization vs. Insufficient-Budget
     Failure (`β(2, 3) = 10 < 56`), `O(T²)` Zero-Checkpoint Recompute (`1,540` vs. `196`),
     and In-Place Activation Overwrite Gradient Corruption (`450 ≠ 30`).
  2. Universal Kahan–Babuška Compensated Summation Exact Residual Invariant
     (`s_n + c_n = ∑ x_i` for ANY rounding map `rnd : Int → Int`) & `O(u)` Error Bound
     vs. Naive Left-to-Right Floating-Point Swamping (`20,000 + 8 × 4 ↦ 20,000 ≠ 20,030`)
     and Unordered Dekker `FastTwoSum` Magnitude-Inversion Failure (`(4, 20000) ↦ err = 0 ≠ 4`)
     rescued by Symmetric Knuth `TwoSum` (`(20000, 4)`).
  3. Mixed-Precision `FP16`/`FP8` Dynamic Loss-Scaling Exponent Window
     (`u_min ≤ S · g_min` & `S · g_max ≤ M_max`) & `GradScaler` Overflow-Skip Automaton (`64/64`)
     vs. Unscaled Subnormal Flush-to-Zero (`[0, 0, 200]`) & Unguarded `NaN` Weight Poisoning.

  100% Pure Lean 4.33.0 · Zero `sorry`, `admit`, or `sorryAx`.
-/

namespace CommonGround.Frontier.ReverseAdCheckpointingKahanSummationAndLossScaling

/-! ## Part 1: Griewank–Walther Binomial `Revolve` Checkpointing (`β(s, r) = C(s + r, s)`) -/

/-- Structural Pascal binomial coefficient `C(n, k)` for kernel-reducible `Revolve` capacity. -/
def pascalBinom : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => pascalBinom n k + pascalBinom n (k + 1)

/-- Maximum chain length `T` reversible in reverse-mode AD using `s` checkpoint slots and
    at most `r` forward recomputations per step (`β(s, r) = C(s + r, s)`). -/
def revolveMaxSteps (s r : Nat) : Nat :=
  pascalBinom (s + r) s

theorem pascal_binom_pos_of_le (n k : Nat) (h : k ≤ n) :
    1 ≤ pascalBinom n k := by
  induction n generalizing k with
  | zero =>
    have hk : k = 0 := Nat.eq_zero_of_le_zero h
    subst hk
    decide
  | succ n ih =>
    cases k with
    | zero => simp [pascalBinom]
    | succ k =>
      simp only [pascalBinom]
      by_cases hkn : k ≤ n
      · have h1 := ih k hkn
        omega
      · omega

/-- Universal positivity of `Revolve` step capacity: `β(s, r) ≥ 1` for all `(s, r)`. -/
theorem revolve_max_steps_pos_universal (s r : Nat) :
    1 ≤ revolveMaxSteps s r := by
  unfold revolveMaxSteps
  exact pascal_binom_pos_of_le (s + r) s (Nat.le_add_right s r)

/-- Exact Pascal split law: placing 1 checkpoint at `k = β(s, r + 1)` partitions a chain of
    length `β(s + 1, r + 1)` into a prefix reversible with `(s + 1, r)` and a suffix reversible
    with `(s, r + 1)`. -/
theorem revolve_pascal_split_universal (s r : Nat) :
    revolveMaxSteps (s + 1) (r + 1) =
      revolveMaxSteps s (r + 1) + revolveMaxSteps (s + 1) r := by
  unfold revolveMaxSteps
  have hEq1 : (s + 1) + (r + 1) = (s + r + 1) + 1 := by omega
  have hEq2 : s + (r + 1) = s + r + 1 := by omega
  have hEq3 : (s + 1) + r = s + r + 1 := by omega
  rw [hEq1, hEq2, hEq3]
  rfl

/-- Structurally recursive auxiliary for Griewank–Walther forward step advances of binomial `Revolve`
    (placing checkpoint at `k = β(s + 1, r)`, indexed by `fuel = s + r`).
    Satisfies Griewank–Walther's exact closed form `r · C(s + r, s) - C(s + r, s + 1)` (`210` at `(3, 5)`). -/
def revolveForwardAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | _ + 1, 0, _ => 0
  | _ + 1, _, 0 => 0
  | fuel + 1, s + 1, r + 1 =>
      revolveMaxSteps (s + 1) r + revolveForwardAux fuel (s + 1) r + revolveForwardAux fuel s (r + 1)

def revolveForwardEvals (s r : Nat) : Nat :=
  revolveForwardAux (s + r) s r

def naiveStepwiseForwardEvals (T : Nat) : Nat :=
  (T - 1) * T / 2

/-- Concrete `T = 56` (`s = 3` slots, `r = 5` recompute depth) & `T = 126` (`s = 4, r = 5`) Witness
    vs. Insufficient Budget (`β(2, 3) = 10 < 56`) & Naive Zero-Checkpoint `O(T²)` Recompute (`1,540` vs. `210`):
    - Peak checkpoint memory drops `56 → 3` slots (`18.67×` reduction!) or `126 → 4` (`31.5×`!).
    - Forward step evaluations drop `1,540 → 210 = 5 · C(8,3) - C(8,4)` (`7.33×` speedup over naive recompute!). -/
theorem revolve_binomial_56_and_126_vs_naive_recompute_witness :
    revolveMaxSteps 3 5 = 56 ∧
    revolveMaxSteps 4 5 = 126 ∧
    revolveMaxSteps 2 3 = 10 ∧
    revolveForwardEvals 3 5 = 210 ∧
    5 * pascalBinom 8 3 - pascalBinom 8 4 = 210 ∧
    naiveStepwiseForwardEvals 56 = 1540 ∧
    revolveForwardEvals 3 5 < naiveStepwiseForwardEvals 56 := by
  decide

/-- Full-tape reverse-mode scalar chain rule vs. two-segment checkpointed rematerialization:
    reversing suffix `J₂` from checkpoint state to obtain `g_mid` and then rematerializing prefix `J₁`
    yields the exact same initial adjoint `g₀` as storing all `|J₁| + |J₂|` activations! -/
def reverseAdjointChain (jacs : List Int) (seed : Int) : Int :=
  jacs.foldr (fun j acc => j * acc) seed

theorem checkpointed_reverse_adjoint_equals_full_tape_universal
    (jacsPrefix jacsSuffix : List Int) (seed : Int) :
    reverseAdjointChain jacsPrefix (reverseAdjointChain jacsSuffix seed) =
      reverseAdjointChain (jacsPrefix ++ jacsSuffix) seed := by
  induction jacsPrefix with
  | nil => rfl
  | cons _ _ _ =>
    simp [reverseAdjointChain, List.foldr_append]

/-- Premise-Failure Counterexample 1B (In-Place Activation Overwrite Bug):
    For quadratic layer `f(x) = w · x²`, true local Jacobian at saved input `x₀` is `2 · w · x₀` (`30`).
    Mutating buffer `x₀ ← f(x₀) = w · x₀²` in-place before backward produces `450 ≠ 30` (`15×` corruption). -/
def savedActivationQuadGrad (w x0 : Int) : Int := 2 * w * x0
def inPlaceOverwrittenQuadGrad (w x0 : Int) : Int :=
  let xMutated := w * x0 * x0
  2 * w * xMutated

theorem inplace_activation_overwrite_corrupts_gradient :
    savedActivationQuadGrad 3 5 = 30 ∧
    inPlaceOverwrittenQuadGrad 3 5 = 450 ∧
    savedActivationQuadGrad 3 5 ≠ inPlaceOverwrittenQuadGrad 3 5 := by
  decide

/-! ## Part 2: Universal Kahan Compensated Summation vs. Naive `FP` Swamping & Unordered `FastTwoSum` -/

structure KahanState where
  sum : Int
  comp : Int
  deriving DecidableEq, Repr

/-- One Kahan compensated update step under an arbitrary rounding operator `rnd : Int → Int`. -/
def kahanStep (rnd : Int → Int) (st : KahanState) (x : Int) : KahanState :=
  let y := x + st.comp
  let sNext := rnd (st.sum + y)
  let cNext := (st.sum + y) - sNext
  { sum := sNext, comp := cNext }

def kahanRun (rnd : Int → Int) (xs : List Int) (init : KahanState := { sum := 0, comp := 0 }) : KahanState :=
  xs.foldl (kahanStep rnd) init

def exactListSum : List Int → Int
  | [] => 0
  | x :: xs => x + exactListSum xs

theorem kahan_step_preserves_sum_plus_comp (rnd : Int → Int) (st : KahanState) (x : Int) :
    (kahanStep rnd st x).sum + (kahanStep rnd st x).comp = st.sum + st.comp + x := by
  simp only [kahanStep]
  omega

theorem kahan_fold_invariant_aux (rnd : Int → Int) (xs : List Int) (st : KahanState) :
    (kahanRun rnd xs st).sum + (kahanRun rnd xs st).comp = st.sum + st.comp + exactListSum xs := by
  induction xs generalizing st with
  | nil =>
    simp [kahanRun, exactListSum]
  | cons x rest ih =>
    simp only [kahanRun, List.foldl_cons, exactListSum]
    have hStep := kahan_step_preserves_sum_plus_comp rnd st x
    have hRec := ih (kahanStep rnd st x)
    simp only [kahanRun] at hRec
    omega

/-- Universal Kahan Exact Residual Conservation Theorem:
    For ANY rounding map `rnd : Int → Int` and ANY input stream `xs : List Int`,
    `s_n + c_n = ∑ x_i` holds identically! -/
theorem kahan_exact_sum_plus_residual_universal (rnd : Int → Int) (xs : List Int) :
    (kahanRun rnd xs).sum + (kahanRun rnd xs).comp = exactListSum xs := by
  have h := kahan_fold_invariant_aux rnd xs { sum := 0, comp := 0 }
  simp only [] at h
  omega

theorem kahan_comp_bounded_aux (rnd : Int → Int) (u : Int)
    (hRnd : ∀ z : Int, -u ≤ z - rnd z ∧ z - rnd z ≤ u)
    (x : Int) (xs : List Int) (st : KahanState) :
    -u ≤ (kahanRun rnd (x :: xs) st).comp ∧ (kahanRun rnd (x :: xs) st).comp ≤ u := by
  induction xs generalizing x st with
  | nil =>
    simp only [kahanRun, List.foldl_cons, List.foldl_nil, kahanStep]
    exact hRnd (st.sum + (x + st.comp))
  | cons y rest ih =>
    simp only [kahanRun, List.foldl_cons]
    exact ih y (kahanStep rnd st x)

/-- Universal `O(u)` Error Bound for Kahan Compensated Summation (independent of length `N`!). -/
theorem kahan_error_bounded_by_one_ulp_universal (rnd : Int → Int) (u : Int)
    (hRnd : ∀ z : Int, -u ≤ z - rnd z ∧ z - rnd z ≤ u)
    (x : Int) (xs : List Int) :
    -u ≤ exactListSum (x :: xs) - (kahanRun rnd (x :: xs)).sum ∧
    exactListSum (x :: xs) - (kahanRun rnd (x :: xs)).sum ≤ u := by
  have hInv := kahan_exact_sum_plus_residual_universal rnd (x :: xs)
  have hComp := kahan_comp_bounded_aux rnd u hRnd x xs { sum := 0, comp := 0 }
  omega

/-- Base-10 4-significant-digit floating-point rounding `fl4` (`|z| < 10,000 ⇒ exact`,
    `10,000 ≤ z ⇒ nearest 10`): models relative floating-point ULP transition at `10⁴`. -/
def fl4 (z : Int) : Int :=
  if -10000 < z ∧ z < 10000 then z
  else if z ≥ 0 then ((z + 5) / 10) * 10
  else -(((-z + 5) / 10) * 10)

def naiveRoundedSum (rnd : Int → Int) (xs : List Int) : Int :=
  xs.foldl (fun acc x => rnd (acc + x)) 0

def swampingStream : List Int := [20000, 4, 4, 4, 4, 4, 4, 4, 4]

/-- Concrete Swamping Witness vs. Kahan Exact Recovery:
    Summing `[20000, 4, 4, 4, 4, 4, 4, 4, 4]` (`exact = 20032`):
    - Naive left-to-right `FP` sum loses all `8` micro-updates (`20000`, error `32 > 5`!).
    - Kahan compensated sum recovers `20030` with residual `+2` (`20030 + 2 = 20032`, error `2 ≤ 5`!). -/
theorem naive_fp_swamping_vs_kahan_compensated_recovery :
    exactListSum swampingStream = 20032 ∧
    naiveRoundedSum fl4 swampingStream = 20000 ∧
    (kahanRun fl4 swampingStream).sum = 20030 ∧
    (kahanRun fl4 swampingStream).comp = 2 := by
  decide

/-- Premise-Failure Counterexample 2B (Dekker `FastTwoSum` without `|a| ≥ |b|` exponent ordering):
    - When `|a| ≥ |b|` (`a = 20000, b = 4`), `FastTwoSum` recovers exact residual `(20000, 4)`.
    - When `|a| < |b|` (`a = 4, b = 20000`), `fl4(20000 - 4) = fl4(19996) = 20000` loses the low
      mantissa digits (`(20000, 0)`, residual `0 ≠ 4`!), whereas symmetric 6-op Knuth `TwoSum`
      recovers `(20000, 4)` without any magnitude ordering assumption! -/
def dekkerFastTwoSum (rnd : Int → Int) (a b : Int) : Int × Int :=
  let s := rnd (a + b)
  let z := rnd (s - a)
  let err := rnd (b - z)
  (s, err)

def knuthSymmetricTwoSum (rnd : Int → Int) (a b : Int) : Int × Int :=
  let s := rnd (a + b)
  let aPrime := rnd (s - b)
  let bPrime := rnd (s - aPrime)
  let da := rnd (a - aPrime)
  let db := rnd (b - bPrime)
  (s, rnd (da + db))

theorem fast_two_sum_order_premise_failure_vs_knuth_two_sum :
    dekkerFastTwoSum fl4 20000 4 = (20000, 4) ∧
    dekkerFastTwoSum fl4 4 20000 = (20000, 0) ∧
    knuthSymmetricTwoSum fl4 4 20000 = (20000, 4) := by
  decide

/-! ## Part 3: Mixed-Precision `FP16`/`FP8` Dynamic Loss Scaling & `GradScaler` Overflow-Skip Gate -/

/-- Universal Safe Loss-Scaling Window Theorem:
    If loss scale `S > 0` places `[g_min, g_max]` inside `[u_min, M_max]`
    (`u_min ≤ S · g_min` and `S · g_max ≤ M_max`), then EVERY gradient `g ∈ [g_min, g_max]`
    escapes subnormal flush-to-zero (`u_min ≤ S · g`), avoids `FP16`/`FP8` overflow (`S · g ≤ M_max`),
    and unscales back to `g` without bias (`(S · g) / S = g`). -/
theorem loss_scaling_safe_window_and_exact_unscale_universal
    (S uMin mMax gMin gMax g : Nat)
    (hS : 0 < S)
    (hRange : gMin ≤ g ∧ g ≤ gMax)
    (hFloor : uMin ≤ S * gMin)
    (hCeil : S * gMax ≤ mMax) :
    uMin ≤ S * g ∧ S * g ≤ mMax ∧ (S * g) / S = g := by
  have h1 : S * gMin ≤ S * g := Nat.mul_le_mul_left S hRange.1
  have h2 : S * g ≤ S * gMax := Nat.mul_le_mul_left S hRange.2
  refine ⟨Nat.le_trans hFloor h1, Nat.le_trans h2 hCeil, ?_⟩
  exact Nat.mul_div_right g hS

def quantizeLowPrecGrad (uMin mMax scaledVal : Nat) : Option Nat :=
  if scaledVal > mMax then none
  else if scaledVal < uMin then some 0
  else some scaledVal

def evalScaledGradVector (S uMin mMax : Nat) (gs : List Nat) : Option (List Nat) :=
  gs.mapM (fun g =>
    match quantizeLowPrecGrad uMin mMax (S * g) with
    | none => none
    | some q => some (q / S))

/-- Concrete `FP16` (`uMin = 64`, `mMax = 65504`) 3-Layer Gradient `[1, 3, 200]` Witness:
    - `S = 256` (`2^8`): exact recovery `some [1, 3, 200]` (`0` underflow, `0` overflow)!
    - `S = 1` (unscaled): micro-gradients `1, 3 < 64` flush to zero (`some [0, 0, 200]`)!
    - `S = 512` (`2^9`, overscaled): `512 × 200 = 102,400 > 65,504` overflows (`none` = `Inf`/`NaN`)! -/
theorem fp16_loss_scaling_safe_256_vs_unscaled_underflow_and_512_overflow :
    evalScaledGradVector 256 64 65504 [1, 3, 200] = some [1, 3, 200] ∧
    evalScaledGradVector 1 64 65504 [1, 3, 200] = some [0, 0, 200] ∧
    evalScaledGradVector 512 64 65504 [1, 3, 200] = none := by
  decide

def guardedGradScalerStep (w : Option Int) (scaleExp : Nat) (gs : List Nat) : Option Int × Nat :=
  let S := 2 ^ scaleExp
  match w, evalScaledGradVector S 64 65504 gs with
  | some wVal, some unscaled =>
      let gradSum : Int := Int.ofNat (unscaled.foldl (· + ·) 0)
      (some (wVal - gradSum), scaleExp)
  | some wVal, none =>
      (some wVal, scaleExp - 1)
  | none, _ =>
      (none, scaleExp)

def unguardedStep (w : Option Int) (scaleExp : Nat) (gs : List Nat) : Option Int × Nat :=
  let S := 2 ^ scaleExp
  match w, evalScaledGradVector S 64 65504 gs with
  | some wVal, some unscaled =>
      let gradSum : Int := Int.ofNat (unscaled.foldl (· + ·) 0)
      (some (wVal - gradSum), scaleExp)
  | _, none =>
      (none, scaleExp)
  | none, some _ =>
      (none, scaleExp)

def checkAll64GradScalerFinite : Bool :=
  (List.range 8).all (fun k =>
    (List.range 8).all (fun m =>
      let gs := [1, 3, 100 * (m + 1)]
      let (wOut, _) := guardedGradScalerStep (some 1000) (k + 4) gs
      wOut.isSome))

theorem dynamic_grad_scaler_backoff_recovery_vs_nan_poisoning :
    let s1 := guardedGradScalerStep (some 1000) 9 [1, 3, 200]
    let s2 := guardedGradScalerStep s1.1 s1.2 [1, 3, 200]
    let u1 := unguardedStep (some 1000) 9 [1, 3, 200]
    let u2 := unguardedStep u1.1 u1.2 [1, 3, 200]
    s1 = (some 1000, 8) ∧
    s2 = (some 796, 8) ∧
    u1.1 = none ∧
    u2.1 = none ∧
    checkAll64GradScalerFinite = true := by
  decide

end CommonGround.Frontier.ReverseAdCheckpointingKahanSummationAndLossScaling
