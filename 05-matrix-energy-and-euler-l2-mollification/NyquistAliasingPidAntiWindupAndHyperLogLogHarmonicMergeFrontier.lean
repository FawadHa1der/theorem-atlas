/-
  05-matrix-energy-and-euler-l2-mollification/NyquistAliasingPidAntiWindupAndHyperLogLogHarmonicMergeFrontier.lean

  Milestone Wave V262 · Frontier Module #137 (HISTORIC 800th ZERO-SORRY .lean FILE PAIR!):
  Exact Algebraic, Harmonic & Control-Theoretic Formalization of:
  1. Nyquist–Shannon Discrete Sampling Phase-Fold Identity (`k*f + k*(N-f) = k*N`), Super-Nyquist
     Aliasing Indistinguishability (`sampledCos8 (8 - f) = sampledCos8 f`, `f = 7` ≡ `f = 1` across
     all `8` samples!) vs. Bandlimited Sub-Nyquist Injectivity (`2*f ≤ 8`) (`euler` ↔ `tc-analysis`).
  2. Discrete PI/PID Integral-Action Zero Steady-State Disturbance Error (`I + Ki*(r - y) = I ∧ Ki > 0 ⟹ y = r`)
     vs. Proportional-Only Nonzero Steady-State Offset (`e_ss = 5 ≠ 0`) & Unclamped Actuator Saturation
     Integral Windup (`u = +10` during `-5` error reversal vs. Clamped Anti-Windup `u = 0`) (`tc-analysis` ↔ `cslib`).
  3. Flajolet–Martin / HyperLogLog Register `max`-Semilattice Exact Union (Idempotent, Commutative,
     Associative) & Harmonic Mean Outlier Immunity (`2 < 3` on `[1, 1, 1, 20]`) vs. Arithmetic Mean
     Single-Hash Cardinality Explosion (`262,145`) (`cslib` ↔ `tc-probcomb`).

  Toolchain: leanprover/lean4:v4.33.0 (pure core Lean 4, zero sorry).
-/

namespace NyquistAliasingPidAntiWindupAndHyperLogLogHarmonicMergeFrontier

-- ============================================================================
-- PART I: NYQUIST–SHANNON ALIASING FOLD-BACK VS. SUB-NYQUIST INJECTIVITY
-- ============================================================================

/--
  **Theorem 1a (Universal Nyquist Phase-Fold Reflection Identity)**:
  For any sampling rate `N`, sample index `k`, and frequency `f ≤ N`, the sum of discrete phases
  `k * f` and `k * (N - f)` is an exact integer multiple `k * N` of the sampling period.
-/
theorem nyquist_folded_phase_sum_universal (k f N : Nat) (hLe : f ≤ N) :
    k * f + k * (N - f) = k * N := by
  rw [← Nat.left_distrib]
  have hSub : f + (N - f) = N := by omega
  rw [hSub]

/-- Exact integer-scaled 8-point cosine lookup `round(100 * cos(2π m / 8))` on `Fin 8`. -/
def cos8Scaled : Fin 8 → Int
  | ⟨0, _⟩ => 100
  | ⟨1, _⟩ => 71
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => -71
  | ⟨4, _⟩ => -100
  | ⟨5, _⟩ => -71
  | ⟨6, _⟩ => 0
  | ⟨7, _⟩ => 71

/-- Sampled cosine sequence at discrete frequency `freq` over `N = 8` samples per period. -/
def sampledCos8 (freq : Nat) (k : Fin 8) : Int :=
  cos8Scaled ⟨(k.val * freq) % 8, Nat.mod_lt _ (by decide)⟩

/--
  **Theorem 1b (Super-Nyquist Aliasing Indistinguishability vs. Sub-Nyquist Bandlimited Injectivity)**:
  1. Every frequency `f : Fin 8` and its folded image `8 - f` generate the **exact same** 8 samples.
  2. Super-Nyquist `f = 7 > 4` is sample-by-sample identical to `f = 1 < 4`.
  3. Restricted to the Nyquist band `f₁, f₂ : Fin 5` (`{0, 1, 2, 3, 4}`, `2 * f ≤ 8`), the 8-sample
     signature map is strictly injective (`sampledCos8 f₁ = sampledCos8 f₂ ⟹ f₁ = f₂`).
-/
theorem nyquist_aliasing_indistinguishability_vs_bandlimited_injectivity8 :
    (∀ f : Fin 8, ∀ k : Fin 8, sampledCos8 (8 - f.val) k = sampledCos8 f.val k) ∧
    (∀ k : Fin 8, sampledCos8 7 k = sampledCos8 1 k) ∧
    (∀ f₁ f₂ : Fin 5, (∀ k : Fin 8, sampledCos8 f₁.val k = sampledCos8 f₂.val k) → f₁ = f₂) := by
  decide

-- ============================================================================
-- PART II: PI/PID INTEGRAL ZERO STEADY-STATE ERROR VS. P-OFFSET & WINDUP
-- ============================================================================

/--
  **Theorem 2a (Universal Integral-Action Zero Steady-State Error Under Unknown Disturbance)**:
  For any setpoint `r`, equilibrium output `yEq`, integrator state `iEq`, and positive integral gain
  `1 ≤ Ki`, if the integrator reaches steady state (`iEq + Ki * (r - yEq) = iEq`), then `yEq = r`
  identically — eliminating steady-state offset regardless of any constant load disturbance `d`.
-/
theorem pi_integral_equilibrium_zero_error_universal
    (r yEq iEq Ki : Int) (hKi : 1 ≤ Ki)
    (hIntFix : iEq + Ki * (r - yEq) = iEq) :
    yEq = r := by
  have hProdZero : Ki * (r - yEq) = 0 := by omega
  by_cases hLt : yEq < r
  · have hPosErr : 0 < r - yEq := by omega
    have hPosProd : 0 < Ki * (r - yEq) := Int.mul_pos (by omega) hPosErr
    omega
  · by_cases hGt : r < yEq
    · have hPosNeg : 0 < yEq - r := by omega
      have hPosProd : 0 < Ki * (yEq - r) := Int.mul_pos (by omega) hPosNeg
      have hFlip : Ki * (yEq - r) = -(Ki * (r - yEq)) := by
        rw [Int.mul_sub, Int.mul_sub]
        omega
      omega
    · omega

/-- Symmetric actuator / integrator saturation clamp `[lo, hi]`. -/
def clampInt (lo hi x : Int) : Int :=
  if x < lo then lo else if hi < x then hi else x

/-- Unclamped PI controller step (`Kp = 1, Ki = 1`, actuator saturated to `[-10, 10]`, integrator unclamped!):
    returns `(newIntegrator, saturatedActuator)`. -/
def unclampedPiStep (iState err : Int) : Int × Int :=
  let iNext := iState + err
  (iNext, clampInt (-10) 10 (err + iNext))

/-- Clamped anti-windup PI controller step (`Kp = 1, Ki = 1`, both integrator & actuator clamped to `[-10, 10]`):
    prevents integrator windup during actuator saturation! -/
def antiWindupPiStep (iState err : Int) : Int × Int :=
  let iNext := clampInt (-10) 10 (iState + err)
  (iNext, clampInt (-10) 10 (err + iNext))

def runPiTrace (stepFn : Int → Int → Int × Int) (errs : List Int) : Int × Int :=
  errs.foldl (fun st e => stepFn st.1 e) (0, 0)

/--
  **Theorem 2b (Proportional-Only Offset `5 ≠ 0` & Unclamped Windup `+10` Overshoot vs. Anti-Windup `0`)**:
  - Under disturbance `d = 10` at `r = 0, Kp = 1` with `Ki = 0` (P-only), `yEq = -5` (`yEq = (0 - yEq) - 10`),
    leaving permanent steady-state offset `r - yEq = 5 ≠ 0`.
  - After 4 saturated launch steps `[20, 20, 20, 20]` followed by reversal `err = -5`:
    * Unclamped PI stays **pinned at `+10` full positive saturation** (`(75, 10)`) despite negative error `-5`!
    * Clamped anti-windup PI immediately desaturates to `0` (`(5, 0)`)!
-/
theorem proportional_offset_and_unclamped_windup_vs_anti_windup :
    ((-5 : Int) = 1 * (0 - (-5)) - 10 ∧ (0 : Int) - (-5) = 5) ∧
    runPiTrace unclampedPiStep [20, 20, 20, 20, -5] = (75, 10) ∧
    runPiTrace antiWindupPiStep [20, 20, 20, 20, -5] = (5, 0) := by
  decide

-- ============================================================================
-- PART III: HYPERLOGLOG MAX-SEMILATTICE UNION & HARMONIC OUTLIER IMMUNITY
-- ============================================================================

/-- Pointwise HyperLogLog register merge `(A ⊔ B)[j] = max(A[j], B[j])`. -/
def hllMerge {m : Nat} (A B : Fin m → Nat) (j : Fin m) : Nat :=
  max (A j) (B j)

/--
  **Theorem 3a (Universal HyperLogLog Register Join-Semilattice Laws)**:
  Pointwise `max` register merging is universally idempotent (duplicate stream replay adds `0`
  error), commutative, and associative across arbitrary register count `m`.
-/
theorem hll_register_merge_semilattice_universal {m : Nat} (A B C : Fin m → Nat) (j : Fin m) :
    hllMerge A A j = A j ∧
    hllMerge A B j = hllMerge B A j ∧
    hllMerge (hllMerge A B) C j = hllMerge A (hllMerge B C) j := by
  dsimp [hllMerge]
  refine ⟨by omega, by omega, by omega⟩

/-- Arithmetic-mean 4-register power-of-two estimator `(2^{r₀} + 2^{r₁} + 2^{r₂} + 2^{r₃}) / 4`. -/
def fmArithmeticMean4 (r₀ r₁ r₂ r₃ : Nat) : Nat :=
  (2 ^ r₀ + 2 ^ r₁ + 2 ^ r₂ + 2 ^ r₃) / 4

/-- Exact integer-scaled HyperLogLog harmonic-mean floor `⌊4 / ∑ 2^{-r_i}⌋` when `r_i ≤ 20`:
    computes `(4 * 2^{20}) / ∑ 2^{20 - r_i}`. -/
def hllHarmonicFloor4 (r₀ r₁ r₂ r₃ : Nat) : Nat :=
  (4 * (2 ^ 20)) / (2 ^ (20 - r₀) + 2 ^ (20 - r₁) + 2 ^ (20 - r₂) + 2 ^ (20 - r₃))

/--
  **Theorem 3b (HyperLogLog Harmonic Outlier Immunity `< 3` vs. Arithmetic `262,145` Explosion)**:
  When 3 registers observe `r = 1` (`2^1 = 2`) and 1 register hits a freak `20`-zero hash (`2^{20} = 1,048,576`):
  - Arithmetic mean explodes to `262,145` (`> 131,000×` true scale!),
  - HyperLogLog harmonic floor evaluates to `2` (`< 3`), completely suppressing the single-hash outlier!
-/
theorem hll_harmonic_outlier_immunity_vs_arithmetic_explosion :
    hllHarmonicFloor4 1 1 1 20 = 2 ∧
    fmArithmeticMean4 1 1 1 20 = 262145 ∧
    hllHarmonicFloor4 1 1 1 20 < 3 ∧
    100000 * hllHarmonicFloor4 1 1 1 20 < fmArithmeticMean4 1 1 1 20 := by
  decide

end NyquistAliasingPidAntiWindupAndHyperLogLogHarmonicMergeFrontier
