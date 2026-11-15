/-
  Discovery 08 — Frontier Cross-Atlas Synthesis (Pure Core Lean 4.33.0, Zero Sorry):
  `HenselNewtonValuationAndTropicalDuality.lean`

  Unifies Arithmetic Galois / Hensel Deformation Lifting (`flt`, `tc-numtheory`, `oai-sat`)
  with Tropical Legendre–Fenchel Valuation Duality (`08/TropicalFenchelSinkhornAndParityDuality.lean`):

  1. **Universal Horner 3-Jet Taylor Identity (`horner_second_order_taylor_identity`)**:
     Proves by structural Horner recursion—without binomial tables or external imports—that
     every degree-`n` integer polynomial satisfies the exact second-order identity
       `f(x + h) = f(x) + f'(x) · h + h² · R_f(x, h)`
     over `ℤ`.
  2. **Unramified Hensel–Newton Quadratic Precision Doubling (`hensel_newton_quadratic_precision_doubling`
     & `iterated_quadratic_exponent_doubling`)**:
     When `f(x) = q · M` and `u · f'(x) = 1 + k · M`, one Newton step `x' = x - u · f(x)`
     satisfies `M ∣ (x' - x)` and **`M² ∣ f(x')`**, doubling valuation precision at every
     step (`2^t · r` digits in `t` steps: `1024×` at `t = 10` vs. linear contraction `11×`).
  3. **Generalized Ramified Hensel Lifting vs. Sharp `2 v_p(f'(x₀))` Obstruction
     (`generalized_ramified_hensel_step` & `ramified_threshold_sharpness_witness_and_mod8_failure`)**:
     When `f'(x) = D · d₀` vanishes modulo `D = p^δ` (`gcd(d₀, D K) = 1`) and
     `f(x) = D² · K · q` (`v_p(f(x)) = 2δ + r > 2δ`), the divided-by-`D` step
     `x_ram = x - u · D · K · q` advances precision from `D² K` to `D² K²` (`2δ + 2r`).
     Conversely, right on the critical boundary `v_2(f(1)) = 2 = 2 v_2(f'(1))` (`g(x) = x² - 5`,
     `4 ∣ g(1)`, `g'(1) = 2`), **no integer `x ∈ ℤ` satisfies `8 ∣ (x² - 5)`**!
  4. **Ultrametric Isosceles Pinning & Tropical Newton-Polygon Slope Quantization
     (`ultrametric_isolated_minimizer_pins_sum_valuation` & `tropical_newton_bend_slope_quantization`)**:
     Connects Folder `08` Legendre–Fenchel lower-envelope duality directly to ultrametric
     root valuations: whenever `i ↦ V(i) + i · s` has a unique minimizer `k`, ultrametric
     tie-breaking pins `val(∑ term_i) = V(k) + k · s`, forbidding zero; hence every root
     valuation `s` must sit at a tropical bend corner where two distinct monomials `i < j`
     tie, quantizing the root slope via `(j - i) · s = V(i) - V(j)`.
-/

namespace CommonGround.HenselNewtonValuationAndTropicalDuality

/-! ## Part 1: Universal Horner 3-Jet Taylor Expansion over `ℤ` -/

/-- Shifts a polynomial coefficient stream `c₀, c₁, c₂, …` to `c₁, c₂, c₃, …`. -/
def shiftCoeffs (c : Nat → Int) : Nat → Int :=
  fun i => c (i + 1)

/-- Horner evaluation `f(x) = c₀ + x (c₁ + x (c₂ + …))` of the first `n` coefficients. -/
def hornerVal : Nat → (Nat → Int) → Int → Int
  | 0, _, _ => 0
  | n + 1, c, x => c 0 + x * hornerVal n (shiftCoeffs c) x

/-- Formal derivative `f'(x)` evaluated simultaneously via Horner's product rule `(x g)' = g + x g'`. -/
def hornerDeriv : Nat → (Nat → Int) → Int → Int
  | 0, _, _ => 0
  | n + 1, c, x => hornerVal n (shiftCoeffs c) x + x * hornerDeriv n (shiftCoeffs c) x

/-- Exact integer second-order divided-difference remainder `R_f(x, h)` in `f(x+h) = f(x) + f'(x)h + h² R_f(x,h)`. -/
def hornerRem2 : Nat → (Nat → Int) → Int → Int → Int
  | 0, _, _, _ => 0
  | n + 1, c, x, h =>
      hornerDeriv n (shiftCoeffs c) x + (x + h) * hornerRem2 n (shiftCoeffs c) x h

/-- Pure-core integer ring step identity underlying Horner's 3-jet recursion. -/
theorem horner_jet_step_ring (c0 x h V D R : Int) :
    c0 + (x + h) * (V + D * h + (h * h) * R) =
      (c0 + x * V) + (V + x * D) * h + (h * h) * (D + (x + h) * R) := by
  have hExpand1 :
      (x + h) * (V + D * h + (h * h) * R) =
        (x + h) * (V + D * h) + (x + h) * ((h * h) * R) := by
    rw [Int.mul_add]
  have hExpand2 :
      (x + h) * (V + D * h) = x * V + x * (D * h) + (h * V + h * (D * h)) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
  have hMid : (V + x * D) * h = h * V + x * (D * h) := by
    rw [Int.add_mul, Int.mul_comm V h, Int.mul_assoc x D h]
  have hRem1 : (h * h) * (D + (x + h) * R) = (h * h) * D + (h * h) * ((x + h) * R) := by
    rw [Int.mul_add]
  have hRemD : (h * h) * D = h * (D * h) := by
    rw [Int.mul_assoc, Int.mul_comm h D]
  have hRemR : (h * h) * ((x + h) * R) = (x + h) * ((h * h) * R) := by
    rw [← Int.mul_assoc, Int.mul_comm (h * h) (x + h), Int.mul_assoc]
  rw [hExpand1, hExpand2, hMid, hRem1, hRemD, hRemR]
  omega

/-- **Theorem 1 (Universal Horner 3-Jet Taylor Identity)**:
    Every degree-`n` integer polynomial satisfies `f(x + h) = f(x) + f'(x) · h + h² · R_f(x, h)`
    identically over `ℤ`. -/
theorem horner_second_order_taylor_identity
    (n : Nat) (c : Nat → Int) (x h : Int) :
    hornerVal n c (x + h) =
      hornerVal n c x + hornerDeriv n c x * h + (h * h) * hornerRem2 n c x h := by
  induction n generalizing c with
  | zero =>
      simp [hornerVal, hornerDeriv, hornerRem2]
  | succ m ih =>
      simp only [hornerVal, hornerDeriv, hornerRem2]
      rw [ih (shiftCoeffs c)]
      exact horner_jet_step_ring (c 0) x h
        (hornerVal m (shiftCoeffs c) x)
        (hornerDeriv m (shiftCoeffs c) x)
        (hornerRem2 m (shiftCoeffs c) x h)

/-! ## Part 2: Unramified Hensel–Newton Quadratic Precision Doubling -/

/-- Pure-core integer factorization for the unramified Newton step `h = -u · (q · M)`
    under `u · D = 1 + k · M`. -/
theorem newton_unramified_residual_factorization (q M u D k R : Int)
    (hInv : u * D = 1 + k * M) :
    q * M + D * ((-u * q) * M) + (((-u * q) * M) * ((-u * q) * M)) * R =
      (-(q * k) + (u * q) * (u * q) * R) * (M * M) := by
  have hDu : D * ((-u * q) * M) = -(q * (u * D) * M) := by
    have h1 : D * ((-u * q) * M) = (D * (-u * q)) * M := (Int.mul_assoc _ _ _).symm
    have h2 : D * (-u * q) = -(q * (u * D)) := by
      have ha : D * (-u * q) = -(D * (u * q)) := by
        calc
          D * (-u * q) = D * (-(u * q)) := by rw [Int.neg_mul]
          _ = -(D * (u * q)) := Int.mul_neg D (u * q)
      have hb : D * (u * q) = q * (u * D) := by
        calc
          D * (u * q) = (D * u) * q := (Int.mul_assoc D u q).symm
          _ = q * (D * u) := Int.mul_comm (D * u) q
          _ = q * (u * D) := by rw [Int.mul_comm D u]
      rw [ha, hb]
    rw [h1, h2, Int.neg_mul]
  have hLin : q * M + D * ((-u * q) * M) = -(q * k) * (M * M) := by
    rw [hDu, hInv]
    have hq : q * (1 + k * M) * M = q * M + (q * k) * (M * M) := by
      calc
        q * (1 + k * M) * M = (q * 1 + q * (k * M)) * M := by rw [Int.mul_add]
        _ = (q + (q * k) * M) * M := by rw [Int.mul_one, Int.mul_assoc q k M]
        _ = q * M + ((q * k) * M) * M := Int.add_mul q ((q * k) * M) M
        _ = q * M + (q * k) * (M * M) := by rw [Int.mul_assoc (q * k) M M]
    rw [hq, Int.neg_mul]
    omega
  have hQuad :
      (((-u * q) * M) * ((-u * q) * M)) * R = ((u * q) * (u * q) * R) * (M * M) := by
    have hNegSq : (-u * q) * (-u * q) = (u * q) * (u * q) := by
      rw [Int.neg_mul, Int.neg_mul_neg]
    calc
      (((-u * q) * M) * ((-u * q) * M)) * R
          = (((-u * q) * (-u * q)) * (M * M)) * R := by
              have hSwap : ((-u * q) * M) * ((-u * q) * M) = ((-u * q) * (-u * q)) * (M * M) := by
                calc
                  ((-u * q) * M) * ((-u * q) * M)
                      = (-u * q) * (M * ((-u * q) * M)) := Int.mul_assoc _ _ _
                  _ = (-u * q) * ((M * (-u * q)) * M) := by rw [Int.mul_assoc M (-u * q) M]
                  _ = (-u * q) * (((-u * q) * M) * M) := by rw [Int.mul_comm M (-u * q)]
                  _ = (-u * q) * ((-u * q) * (M * M)) := by rw [Int.mul_assoc (-u * q) M M]
                  _ = ((-u * q) * (-u * q)) * (M * M) := (Int.mul_assoc _ _ _).symm
              rw [hSwap]
      _ = (((u * q) * (u * q)) * (M * M)) * R := by rw [hNegSq]
      _ = ((u * q) * (u * q)) * ((M * M) * R) := Int.mul_assoc _ _ _
      _ = ((u * q) * (u * q)) * (R * (M * M)) := by rw [Int.mul_comm (M * M) R]
      _ = ((u * q) * (u * q) * R) * (M * M) := (Int.mul_assoc _ _ _).symm
  rw [hLin, hQuad, ← Int.add_mul]

/-- **Theorem 2 (Unramified Hensel–Newton Quadratic Precision Doubling)**:
    If `f(x) = q · M` (`M ∣ f(x)`) and `u · f'(x) = 1 + k · M` (`f'(x)` invertible mod `M`),
    then the single Newton update `x' = x - u · f(x)` satisfies:
    1. Congruence Lift: `x' - x = (-u · q) · M` (`x' ≡ x (mod M)`), and
    2. Quadratic Precision Doubling: `M² ∣ f(x')` via an explicit integer witness! -/
theorem hensel_newton_quadratic_precision_doubling
    (n : Nat) (c : Nat → Int) (x M q u k : Int)
    (hRootMod : hornerVal n c x = q * M)
    (hDerivUnit : u * hornerDeriv n c x = 1 + k * M) :
    let xNext := x - u * hornerVal n c x
    let stepCoeff := -u * q
    (xNext - x = stepCoeff * M) ∧
    (hornerVal n c xNext =
      (-(q * k) + (u * q) * (u * q) * hornerRem2 n c x (stepCoeff * M)) * (M * M)) := by
  dsimp only
  have hStep : x - u * hornerVal n c x - x = (-u * q) * M := by
    rw [hRootMod]
    have hMul : u * (q * M) = (u * q) * M := (Int.mul_assoc u q M).symm
    have hNeg : -((u * q) * M) = (-u * q) * M := by
      rw [Int.neg_mul, Int.neg_mul]
    omega
  refine ⟨hStep, ?_⟩
  have hShiftEq : x - u * hornerVal n c x = x + ((-u * q) * M) := by omega
  rw [hShiftEq, horner_second_order_taylor_identity n c x ((-u * q) * M), hRootMod]
  exact newton_unramified_residual_factorization q M u (hornerDeriv n c x) k
    (hornerRem2 n c x ((-u * q) * M)) hDerivUnit

/-- Precision exponent `r_t` after `t` quadratic Newton doublings (`r_{t+1} = 2 r_t`). -/
def quadraticPrecisionExp (r0 : Nat) : Nat → Nat
  | 0 => r0
  | t + 1 => 2 * quadraticPrecisionExp r0 t

/-- **Theorem 3 (Exponential `2^t` Precision Doubling vs. Linear Contraction)**:
    Starting from valuation accuracy `r₀`, `t` Hensel–Newton steps achieve accuracy `(2^t) · r₀`
    (`1024 · r₀` after `10` steps, strictly exceeding `93×` a `10`-step linear contraction `(10 + 1) · r₀`). -/
theorem iterated_quadratic_exponent_doubling (r0 t : Nat) :
    quadraticPrecisionExp r0 t = (2 ^ t) * r0 ∧
    quadraticPrecisionExp 1 10 = 1024 ∧
    quadraticPrecisionExp 1 10 > 93 * (10 + 1) := by
  refine ⟨?_, by decide, by decide⟩
  induction t with
  | zero =>
      simp [quadraticPrecisionExp]
  | succ m ih =>
      simp only [quadraticPrecisionExp, ih]
      have hPow : 2 ^ (m + 1) = 2 * (2 ^ m) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hPow, Nat.mul_assoc]

/-! ## Part 3: Generalized Ramified Hensel Lifting vs. Sharp `2 v_p(f'(x₀))` Obstruction -/

/-- Pure-core factorization for Generalized Ramified Hensel Lifting when `f'(x) = D · d₀`
    and `f(x) = (D · D · K) · q`. -/
theorem newton_ramified_residual_factorization (D K q d0 u k R : Int)
    (hInv : u * d0 = 1 + k * (D * K)) :
    (D * D * K) * q + (D * d0) * ((-u * q) * (D * K)) +
        (((-u * q) * (D * K)) * ((-u * q) * (D * K))) * R =
      (-(q * k * D) + (u * q) * (u * q) * R) * (D * D * K * K) := by
  have h1 :
      (D * d0) * ((-u * q) * (D * K)) = -(q * (u * d0)) * (D * D * K) := by
    calc
      (D * d0) * ((-u * q) * (D * K))
          = (d0 * (-u * q)) * (D * (D * K)) := by
              calc
                (D * d0) * ((-u * q) * (D * K))
                    = D * (d0 * ((-u * q) * (D * K))) := Int.mul_assoc _ _ _
                _ = D * ((d0 * (-u * q)) * (D * K)) := by rw [Int.mul_assoc d0 (-u * q) (D * K)]
                _ = (D * (d0 * (-u * q))) * (D * K) := (Int.mul_assoc _ _ _).symm
                _ = ((d0 * (-u * q)) * D) * (D * K) := by rw [Int.mul_comm D (d0 * (-u * q))]
                _ = (d0 * (-u * q)) * (D * (D * K)) := Int.mul_assoc _ _ _
      _ = (-(q * (u * d0))) * (D * D * K) := by
            have hd : d0 * (-u * q) = -(q * (u * d0)) := by
              calc
                d0 * (-u * q) = d0 * (-(u * q)) := by rw [Int.neg_mul]
                _ = -(d0 * (u * q)) := Int.mul_neg d0 (u * q)
                _ = -((d0 * u) * q) := by rw [Int.mul_assoc d0 u q]
                _ = -(q * (d0 * u)) := by rw [Int.mul_comm (d0 * u) q]
                _ = -(q * (u * d0)) := by rw [Int.mul_comm d0 u]
            have hDDK : D * (D * K) = D * D * K := (Int.mul_assoc D D K).symm
            rw [hd, hDDK]
  have hLin :
      (D * D * K) * q + (D * d0) * ((-u * q) * (D * K)) =
        (-(q * k * D)) * (D * D * K * K) := by
    rw [h1, hInv, Int.mul_comm (D * D * K) q]
    have hSub :
        q * (D * D * K) + (-(q * (1 + k * (D * K)))) * (D * D * K) =
          (q - q * (1 + k * (D * K))) * (D * D * K) := by
      rw [Int.sub_eq_add_neg, Int.add_mul, Int.neg_mul]
    have hInner : q - q * (1 + k * (D * K)) = -(q * k * D) * K := by
      calc
        q - q * (1 + k * (D * K))
            = q - (q * 1 + q * (k * (D * K))) := by rw [Int.mul_add]
        _ = -(q * (k * (D * K))) := by rw [Int.mul_one]; omega
        _ = -((q * k * D) * K) := by
              have hAssoc : q * (k * (D * K)) = (q * k * D) * K := by
                calc
                  q * (k * (D * K)) = (q * k) * (D * K) := (Int.mul_assoc q k (D * K)).symm
                  _ = (q * k * D) * K := (Int.mul_assoc (q * k) D K).symm
              rw [hAssoc]
        _ = -(q * k * D) * K := (Int.neg_mul (q * k * D) K).symm
    rw [hSub, hInner, Int.mul_assoc (-(q * k * D)) K (D * D * K), Int.mul_comm K (D * D * K)]
  have hQuad :
      (((-u * q) * (D * K)) * ((-u * q) * (D * K))) * R =
        ((u * q) * (u * q) * R) * (D * D * K * K) := by
    have hDK2 : (D * K) * (D * K) = D * D * K * K := by
      calc
        (D * K) * (D * K) = D * (K * (D * K)) := Int.mul_assoc D K (D * K)
        _ = D * ((K * D) * K) := by rw [Int.mul_assoc K D K]
        _ = D * ((D * K) * K) := by rw [Int.mul_comm K D]
        _ = (D * (D * K)) * K := (Int.mul_assoc D (D * K) K).symm
        _ = (D * D * K) * K := by rw [Int.mul_assoc D D K]
    have hNegSq : (-u * q) * (-u * q) = (u * q) * (u * q) := by
      rw [Int.neg_mul, Int.neg_mul_neg]
    calc
      (((-u * q) * (D * K)) * ((-u * q) * (D * K))) * R
          = (((-u * q) * (-u * q)) * ((D * K) * (D * K))) * R := by
              have hSwap :
                  ((-u * q) * (D * K)) * ((-u * q) * (D * K)) =
                    ((-u * q) * (-u * q)) * ((D * K) * (D * K)) := by
                calc
                  ((-u * q) * (D * K)) * ((-u * q) * (D * K))
                      = (-u * q) * ((D * K) * ((-u * q) * (D * K))) := Int.mul_assoc _ _ _
                  _ = (-u * q) * (((D * K) * (-u * q)) * (D * K)) := by
                        rw [Int.mul_assoc (D * K) (-u * q) (D * K)]
                  _ = (-u * q) * (((-u * q) * (D * K)) * (D * K)) := by
                        rw [Int.mul_comm (D * K) (-u * q)]
                  _ = (-u * q) * ((-u * q) * ((D * K) * (D * K))) := by
                        rw [Int.mul_assoc (-u * q) (D * K) (D * K)]
                  _ = ((-u * q) * (-u * q)) * ((D * K) * (D * K)) := (Int.mul_assoc _ _ _).symm
              rw [hSwap]
      _ = (((u * q) * (u * q)) * (D * D * K * K)) * R := by rw [hNegSq, hDK2]
      _ = ((u * q) * (u * q)) * ((D * D * K * K) * R) := Int.mul_assoc _ _ _
      _ = ((u * q) * (u * q)) * (R * (D * D * K * K)) := by rw [Int.mul_comm (D * D * K * K) R]
      _ = ((u * q) * (u * q) * R) * (D * D * K * K) := (Int.mul_assoc _ _ _).symm
  rw [hLin, hQuad, ← Int.add_mul]

/-- **Theorem 4 (Generalized Ramified Hensel Lifting above `2 v_p(f'(x₀))`)**:
    When `f'(x)` is divisible by `D = p^δ` (`f'(x) = D · d₀` with `u · d₀ = 1 + k · D · K`)
    and `f(x) = (D² · K) · q` lies strictly deeper than `D²` (`K = p^r`), the divided-by-`D`
    step `x_ram = x + (-u · q) · (D · K)` lifts precision from `D² · K` to **`D² · K²`**! -/
theorem generalized_ramified_hensel_step
    (n : Nat) (c : Nat → Int) (x D K q d0 u k : Int)
    (hVal : hornerVal n c x = (D * D * K) * q)
    (hDeriv : hornerDeriv n c x = D * d0)
    (hUnit : u * d0 = 1 + k * (D * K)) :
    let hStep := (-u * q) * (D * K)
    let xRam := x + hStep
    (xRam - x = (-u * q) * (D * K)) ∧
    (hornerVal n c xRam =
      (-(q * k * D) + (u * q) * (u * q) * hornerRem2 n c x hStep) * (D * D * K * K)) := by
  dsimp only
  refine ⟨by omega, ?_⟩
  rw [horner_second_order_taylor_identity n c x ((-u * q) * (D * K)), hVal, hDeriv]
  exact newton_ramified_residual_factorization D K q d0 u k
    (hornerRem2 n c x ((-u * q) * (D * K))) hUnit

/-- **Theorem 5 (Sharpness of the `2 v_p(f'(x₀))` Ramification Barrier — 1-Bit Separation)**:
    - **Above Threshold (`v_2(f(1)) = 3 = 2·1 + 1 > 2 v_2(f'(1))`)**:
      For `f(x) = x² - 9` (`c = (-9, 0, 1)`) at `x₀ = 1`, `f(1) = -8` (`D = 2, K = 2, q = -1`)
      and `f'(1) = 2`, so ramified lifting produces `x_ram = 3` with `f(3) = 0` (`16 ∣ f(3)`).
    - **On the Boundary (`v_2(g(1)) = 2 = 2 v_2(g'(1))` — Premise Failure!)**:
      Just 1 bit lower, for `g(x) = x² - 5` (`c = (-5, 0, 1)`) at `x₀ = 1`, `4 ∣ g(1) = -4`
      holds while `g'(1) = 2`, yet **no integer `x ∈ ℤ` satisfies `8 ∣ (x² - 5)`**! -/
theorem ramified_threshold_sharpness_witness_and_mod8_failure :
    let cLift : Nat → Int := fun i => if i = 0 then -9 else if i = 1 then 0 else if i = 2 then 1 else 0
    let cFail : Nat → Int := fun i => if i = 0 then -5 else if i = 1 then 0 else if i = 2 then 1 else 0
    (hornerVal 3 cLift 1 = -8 ∧ hornerDeriv 3 cLift 1 = 2 ∧ hornerVal 3 cLift 3 = 0) ∧
    (hornerVal 3 cFail 1 = -4 ∧ hornerDeriv 3 cFail 1 = 2 ∧
      ∀ x : Int, ¬ ∃ m : Int, hornerVal 3 cFail x = 8 * m) := by
  dsimp only
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, ?_⟩⟩
  intro x ⟨m, hm⟩
  have hEval :
      hornerVal 3 (fun i => if i = 0 then -5 else if i = 1 then 0 else if i = 2 then 1 else 0) x =
        -5 + x * x := by
    simp [hornerVal, shiftCoeffs]
  rw [hEval] at hm
  have hDecomp : ∃ q r : Int, x = 8 * q + r ∧ 0 ≤ r ∧ r < 8 :=
    ⟨x / 8, x % 8, by omega, by omega, by omega⟩
  rcases hDecomp with ⟨q, r, rfl, hr0, hr8⟩
  have hSq : (8 * q + r) * (8 * q + r) = 8 * (8 * (q * q) + 2 * (q * r)) + r * r := by
    calc
      (8 * q + r) * (8 * q + r)
          = (8 * q) * (8 * q) + (8 * q) * r + (r * (8 * q) + r * r) := by
              rw [Int.add_mul, Int.mul_add, Int.mul_add]
      _ = 64 * (q * q) + 16 * (q * r) + r * r := by
            have h64 : (8 * q) * (8 * q) = 64 * (q * q) := by
              calc
                (8 * q) * (8 * q) = 8 * (q * (8 * q)) := Int.mul_assoc 8 q (8 * q)
                _ = 8 * ((q * 8) * q) := by rw [Int.mul_assoc q 8 q]
                _ = 8 * ((8 * q) * q) := by rw [Int.mul_comm q 8]
                _ = (8 * 8) * (q * q) := by
                      rw [← Int.mul_assoc 8 (8 * q) q, ← Int.mul_assoc 8 8 q, Int.mul_assoc (8 * 8) q q]
                _ = 64 * (q * q) := rfl
            have h8a : (8 * q) * r = 8 * (q * r) := Int.mul_assoc 8 q r
            have h8b : r * (8 * q) = 8 * (q * r) := by
              rw [Int.mul_comm r (8 * q), Int.mul_assoc 8 q r]
            rw [h64, h8a, h8b]
            omega
      _ = 8 * (8 * (q * q) + 2 * (q * r)) + r * r := by
            have hDist : 8 * (8 * (q * q) + 2 * (q * r)) = 64 * (q * q) + 16 * (q * r) := by
              rw [Int.mul_add, ← Int.mul_assoc 8 8 (q * q), ← Int.mul_assoc 8 2 (q * r)]
              rfl
            rw [hDist]
  rw [hSq] at hm
  have hrCases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
  rcases hrCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-! ## Part 4: Ultrametric Isosceles Pinning & Tropical Newton-Polygon Slope Quantization -/

/-- Prefix sum `∑_{i < m} term(i)` over an abstract commutative additive operation `op` with unit `z`. -/
def prefixOp {α : Type} (op : α → α → α) (z : α) : Nat → (Nat → α) → α
  | 0, _ => z
  | m + 1, term => op (prefixOp op z m term) (term m)

/-- Ultrametric lower bound on prefix sums: if every active summand has valuation `≥ L` and
    `val z ≥ L`, then `val (prefixOp m term) ≥ L`. -/
theorem ultrametric_prefix_ge
    {α : Type} (op : α → α → α) (z : α) (val : α → Int)
    (hMin : ∀ (a b : α) (L : Int), L ≤ val a → L ≤ val b → L ≤ val (op a b))
    (m : Nat) (term : Nat → α) (L : Int)
    (hz : L ≤ val z)
    (hTerms : ∀ i : Nat, i < m → L ≤ val (term i)) :
    L ≤ val (prefixOp op z m term) := by
  induction m with
  | zero =>
      simpa [prefixOp] using hz
  | succ j ih =>
      simp only [prefixOp]
      apply hMin _ _ L
      · exact ih (fun i hi => hTerms i (by omega))
      · exact hTerms j (by omega)

/-- **Theorem 6 (Ultrametric Isolated-Minimizer Valuation Pinning)**:
    Under the ultrametric triangle law (`min(val a, val b) ≤ val(a ⊕ b)`) and strict isosceles
    tie-breaking (`val a < val b → val(a ⊕ b) = val a`, `val b < val a → val(a ⊕ b) = val b`),
    whenever an index `k < m` is the **strictly unique** minimizer of `i ↦ val(term i)` with value `M`
    (`M + 1 ≤ val(term i)` for all `i ≠ k`, and `M + 1 ≤ val z`), the valuation of the entire sum
    is pinned identically at `M` (`val(∑_{i < m} term i) = M`)—hence `∑_{i < m} term i ≠ z`! -/
theorem ultrametric_isolated_minimizer_pins_sum_valuation
    {α : Type} (op : α → α → α) (z : α) (val : α → Int)
    (hMin : ∀ (a b : α) (L : Int), L ≤ val a → L ≤ val b → L ≤ val (op a b))
    (hTieL : ∀ a b : α, val a < val b → val (op a b) = val a)
    (hTieR : ∀ a b : α, val b < val a → val (op a b) = val b)
    (m : Nat) (term : Nat → α) (k : Nat) (M : Int)
    (hkLt : k < m)
    (hz : M + 1 ≤ val z)
    (hkVal : val (term k) = M)
    (hStrict : ∀ i : Nat, i < m → i ≠ k → M + 1 ≤ val (term i)) :
    val (prefixOp op z m term) = M ∧ prefixOp op z m term ≠ z := by
  have hPin : val (prefixOp op z m term) = M := by
    induction m with
    | zero => omega
    | succ j ih =>
        simp only [prefixOp]
        by_cases hkj : k = j
        · subst hkj
          have hPrefGe : M + 1 ≤ val (prefixOp op z k term) := by
            apply ultrametric_prefix_ge op z val hMin k term (M + 1) hz
            intro i hi
            exact hStrict i (by omega) (by omega)
          have hLt : val (term k) < val (prefixOp op z k term) := by omega
          rw [hTieR (prefixOp op z k term) (term k) hLt, hkVal]
        · have hkLtJ : k < j := by omega
          have hPrefEq : val (prefixOp op z j term) = M :=
            ih hkLtJ (fun i hi hne => hStrict i (by omega) hne)
          have hLastGe : M + 1 ≤ val (term j) :=
            hStrict j (by omega) (fun heq => hkj heq.symm)
          have hLt : val (prefixOp op z j term) < val (term j) := by omega
          rw [hTieL (prefixOp op z j term) (term j) hLt, hPrefEq]
  refine ⟨hPin, ?_⟩
  intro hEqZ
  rw [hEqZ] at hPin
  omega

/-- **Theorem 7 (Tropical Newton-Polygon Bend & Root-Slope Quantization)**:
    1. **Slope Quantization Law**: Whenever two distinct active monomials `i < j` tie at the
       tropical Legendre–Fenchel minimum `V(i) + i · s = V(j) + j · s = M` (`V(r) + r · s ≥ M`
       for all `r < m`), the root valuation `s` satisfies the exact Newton-polygon edge equation
       `(j - i) · s = V(i) - V(j)`.
    2. **3-Term Tropical Bend vs. Non-Corner Isolation Witness**:
       For `V = (3, 1, 0)` (modeling `p³ + p x + x²`):
       - Bend slopes `s = 2` (`i = 0, j = 1` tie at `3`) and `s = 1` (`i = 1, j = 2` tie at `2`)
         satisfy `(1 - 0)·2 = 3 - 1` and `(2 - 1)·1 = 1 - 0`;
       - At non-corner slope `s = 0` (`V(r) + r·0 = (3, 1, 0)`), `k = 2` is the unique minimizer
         (`0 < 1 < 3`), forbidding ultrametric cancellation! -/
theorem tropical_newton_bend_slope_quantization
    (V : Nat → Int) (i j : Nat) (s M : Int)
    (hij : i < j)
    (hTieI : V i + (i : Int) * s = M)
    (hTieJ : V j + (j : Int) * s = M) :
    ((j : Int) - (i : Int)) * s = V i - V j ∧
    (let V3 : Nat → Int := fun r => if r = 0 then 3 else if r = 1 then 1 else 0
     (V3 0 + 0 * 2 = 3 ∧ V3 1 + 1 * 2 = 3 ∧ V3 2 + 2 * 2 = 4) ∧
     (V3 1 + 1 * 1 = 2 ∧ V3 2 + 2 * 1 = 2 ∧ V3 0 + 0 * 1 = 3) ∧
     (V3 2 + 2 * 0 = 0 ∧ ∀ r : Nat, r < 3 → r ≠ 2 → 0 + 1 ≤ V3 r + (r : Int) * 0)) := by
  have hDiff : ((j : Int) - (i : Int)) * s = V i - V j := by
    have hSub : ((j : Int) - (i : Int)) * s = (j : Int) * s - (i : Int) * s :=
      Int.sub_mul (j : Int) (i : Int) s
    let _ := hij
    omega
  refine ⟨hDiff, ?_⟩
  dsimp only
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, ⟨by decide, ?_⟩⟩
  intro r hrLT hrNe
  have hrCases : r = 0 ∨ r = 1 := by omega
  rcases hrCases with rfl | rfl <;> decide

end CommonGround.HenselNewtonValuationAndTropicalDuality
