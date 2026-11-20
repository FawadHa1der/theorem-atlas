/-
  05-matrix-energy-and-euler-l2-mollification/MillerRabinCarmichaelGrayCodeBijectionAndSmithWsptExchangeFrontier.lean

  Milestone Wave V285 (`Frontier #160`, `140` Exact Finite Micro-Labs Milestone & `Suite #686`!):
  1. Miller–Rabin (`1976`/`1980`) Non-Trivial Square-Root Primality Witness vs. Fermat Carmichael `561`:
     Universal prime square-root rigidity (`p ∣ (x - 1) * (x + 1) → x = 1 ∨ x = p - 1`),
     universal non-trivial square-root strict factor extraction (`1 < gcd(x - 1, n) < n ∧ gcd ∣ n`),
     universal Korselt-CRT lift for `561 = 3 * 11 * 17` (`x % 3 = 1 ∧ x % 11 = 1 ∧ x % 17 = 1 → x % 561 = 1`),
     and exact Carmichael `561` witness where Fermat's test falsely certifies `561` on all coprime
     residues (`2, 4, 5, 7, 8, 10, 13, 14, 16, 19`) while Miller–Rabin base `2` exposes
     `67^2 ≡ 1 (mod 561)` and factors `gcd(66, 561) = 33`, `gcd(68, 561) = 17`.
  2. Frank Gray (`1953`) Reflected Binary Gray Code Unbounded Bijection & Unit-Hamming Step:
     Universal unbounded-`Nat` prefix-XOR bijection (`grayDecode (grayEncode n) = n` and
     `grayEncode (grayDecode g) = g`), universal inductive single-bit transition
     (`∀ n : Nat, ∃ k : Nat, grayEncode n ^^^ grayEncode (n + 1) = 2 ^ k`), and CDC asynchronous
     FIFO witness contrasting `1`-bit Gray transition `4 → 12` (`popcount = 1`) against `4`-bit
     binary ripple-carry metastability glitch `0111 → 1000` (`7 ^^^ 8 = 15`, `popcount = 4`).
  3. Wayne Smith (`1956`) `WSPT` Weighted Shortest Processing Time Exchange Optimality (`w_i / p_i`):
     Universal arbitrary-length schedule swap identity
     `scheduleWeightedCost t (pre ++ (w1,p1)::(w2,p2)::suf) + w1*p2 = scheduleWeightedCost t (pre ++ (w2,p2)::(w1,p1)::suf) + w2*p1`,
     exact `IFF` optimality criterion `w2 * p1 ≤ w1 * p2`, and unweighted `SPT` priority-inversion
     counterexample (`502` vs. `305` on `2` jobs; `862` vs. `589` on `3` jobs).
-/

namespace MillerRabinGrayCodeAndSmithWsptFrontier

/-! ## Part 1: Miller–Rabin (`1976`/`1980`) Square-Root Factor Split vs. Carmichael `561` -/

/-- Structural binary modular exponentiation (`fuel` bit-steps, reduces natively inside `decide`). -/
def powModFuel : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, mod => if mod = 0 then 0 else 1 % mod
  | fuel + 1, base, exp, mod =>
    if mod = 0 then 0
    else if exp = 0 then 1 % mod
    else
      let half := powModFuel fuel base (exp / 2) mod
      let sq := (half * half) % mod
      if exp % 2 = 1 then (sq * (base % mod)) % mod else sq

/-- Fast modular exponentiation `base ^ exp % mod` (supports exponents up to `2^16`). -/
def powMod (base exp mod : Nat) : Nat :=
  powModFuel 16 base exp mod

/-- **Theorem 1a (Universal Prime Square-Root Rigidity)**:
    For ANY modulus `p ≥ 2` satisfying Euclid's prime property (`p ∣ a * b → p ∣ a ∨ p ∣ b`)
    and ANY residue `1 ≤ x < p`, `p ∣ (x - 1) * (x + 1)` forces `x = 1 ∨ x = p - 1`. -/
theorem prime_square_root_of_one_rigidity
    (p x : Nat) (hp : 2 ≤ p)
    (hPrime : ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b)
    (hxLo : 1 ≤ x) (hxHi : x < p)
    (hSq : p ∣ (x - 1) * (x + 1)) :
    x = 1 ∨ x = p - 1 := by
  rcases hPrime (x - 1) (x + 1) hSq with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    cases k with
    | zero => omega
    | succ k' =>
      have hGe : p * (k' + 1) ≥ p * 1 := Nat.mul_le_mul_left p (by omega)
      omega
  · right
    cases k with
    | zero => omega
    | succ k' =>
      cases k' with
      | zero => omega
      | succ k'' =>
        have hGe : p * (k'' + 1 + 1) ≥ p * 2 := Nat.mul_le_mul_left p (by omega)
        omega

/-- **Theorem 1b (Universal Non-Trivial Square-Root Strict Factor Extraction)**:
    For ANY modulus `n ≥ 2` and ANY non-trivial square root `1 < x < n - 1` of `1 mod n`
    (`n ∣ (x - 1) * (x + 1)`), `g = Nat.gcd (x - 1) n` is a strict divisor of `n`
    (`1 < g ∧ g < n ∧ g ∣ n`), immediately certifying compositeness and factoring `n`. -/
theorem nontrivial_sqrt_extracts_strict_factor
    (n x : Nat) (hn : 2 ≤ n) (hxLo : 1 < x) (hxHi : x + 1 < n)
    (hSq : n ∣ (x - 1) * (x + 1)) :
    1 < Nat.gcd (x - 1) n ∧ Nat.gcd (x - 1) n < n ∧ Nat.gcd (x - 1) n ∣ n := by
  have hDvdN : Nat.gcd (x - 1) n ∣ n := Nat.gcd_dvd_right (x - 1) n
  have hDvdX : Nat.gcd (x - 1) n ∣ x - 1 := Nat.gcd_dvd_left (x - 1) n
  have hLeX : Nat.gcd (x - 1) n ≤ x - 1 := Nat.le_of_dvd (by omega) hDvdX
  have hLtN : Nat.gcd (x - 1) n < n := by omega
  have hNe0 : Nat.gcd (x - 1) n ≠ 0 := by
    intro h0
    rw [h0] at hDvdN
    rcases hDvdN with ⟨k, hk⟩
    omega
  have hNe1 : Nat.gcd (x - 1) n ≠ 1 := by
    intro h1
    have hCop : Nat.Coprime n (x - 1) := by
      unfold Nat.Coprime
      rw [Nat.gcd_comm]
      exact h1
    have hDvdXp1 : n ∣ x + 1 := hCop.dvd_of_dvd_mul_left hSq
    have hLeXp1 : n ≤ x + 1 := Nat.le_of_dvd (by omega) hDvdXp1
    omega
  exact ⟨by omega, hLtN, hDvdN⟩

/-- **Theorem 1c (Universal Korselt-CRT Congruence Lift for Carmichael `561 = 3 * 11 * 17`)**:
    Because `2 ∣ 560`, `10 ∣ 560`, and `16 ∣ 560`, any `x` congruent to `1` modulo `3`, `11`,
    and `17` is automatically congruent to `1` modulo `561`, causing Fermat's test to pass on
    EVERY coprime base `a` (`320 / 320` bases)! -/
theorem korselt_561_crt_lift (x : Nat)
    (h3 : x % 3 = 1) (h11 : x % 11 = 1) (h17 : x % 17 = 1) :
    x % 561 = 1 := by
  omega

/-- **Theorem 1d (Carmichael `561` Korselt Residue Check vs. Miller–Rabin Base-`2` Split)**:
    1. Every nonzero residue mod `3`, `11`, and `17` satisfies `r^560 ≡ 1`, and concrete coprime
       bases `[2, 4, 5, 7, 8, 10, 13, 14, 16, 19]` all satisfy Fermat's `a^560 % 561 = 1`.
    2. Miller–Rabin on `560 = 2^4 * 35` with base `a = 2` computes `2^35 ≡ 263`, `263^2 ≡ 166`,
       `166^2 ≡ 67`, `67^2 ≡ 1 (mod 561)`, exposing non-trivial square root `67 ∉ {1, 560}` and
       immediately extracting factors `gcd(66, 561) = 33`, `gcd(68, 561) = 17` (`33 * 17 = 561`). -/
theorem carmichael_561_fermat_false_positive_vs_miller_rabin_witness :
    (∀ r : Fin 3, r.val ≠ 0 → powMod r.val 560 3 = 1) ∧
    (∀ r : Fin 11, r.val ≠ 0 → powMod r.val 560 11 = 1) ∧
    (∀ r : Fin 17, r.val ≠ 0 → powMod r.val 560 17 = 1) ∧
    ([2, 4, 5, 7, 8, 10, 13, 14, 16, 19].all (fun a => powMod a 560 561 == 1) = true) ∧
    powMod 2 35 561 = 263 ∧
    (263 * 263) % 561 = 166 ∧
    (166 * 166) % 561 = 67 ∧
    (67 * 67) % 561 = 1 ∧
    Nat.gcd (67 - 1) 561 = 33 ∧
    Nat.gcd (67 + 1) 561 = 17 ∧
    33 * 17 = 561 := by
  decide

/-! ## Part 2: Frank Gray (`1953`) Reflected Binary Gray Code Bijection & Unit-Hamming Step -/

/-- Frank Gray (`1953`) reflected binary encoder `G(n) = n ^^^ (n / 2)`. -/
def grayEncode (n : Nat) : Nat := n ^^^ (n / 2)

/-- Structurally recursive prefix-XOR Gray decoder step `G⁻¹_k(g)`. -/
def grayDecodeStep : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, g => g ^^^ grayDecodeStep k (g / 2)

/-- Unbounded prefix-XOR Gray decoder `G⁻¹(g) = grayDecodeStep g g`. -/
def grayDecode (g : Nat) : Nat := grayDecodeStep g g

private theorem div_two_xor (a b : Nat) : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_div_two]

private theorem grayDecodeStep_zero : ∀ k : Nat, grayDecodeStep k 0 = 0
  | 0 => rfl
  | k + 1 => by
    simp only [grayDecodeStep, Nat.zero_div, grayDecodeStep_zero k, Nat.xor_zero]

private theorem grayDecodeStep_decode_encode :
    ∀ (k n : Nat), n ≤ k → grayDecodeStep k (grayEncode n) = n
  | 0, n, h => by
    have hn : n = 0 := by omega
    subst hn; rfl
  | k + 1, n, h => by
    have hSub : n / 2 ≤ k := by omega
    have hDiv : grayEncode n / 2 = grayEncode (n / 2) := by
      unfold grayEncode; rw [div_two_xor]
    simp only [grayDecodeStep, hDiv]
    rw [grayDecodeStep_decode_encode k (n / 2) hSub]
    unfold grayEncode
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

private theorem grayDecodeStep_encode_decode :
    ∀ (k g : Nat), g ≤ k → grayEncode (grayDecodeStep k g) = g
  | 0, g, h => by
    have hg : g = 0 := by omega
    subst hg; rfl
  | k + 1, g, h => by
    have hSub : g / 2 ≤ k := by omega
    have hRec := grayDecodeStep_encode_decode k (g / 2) hSub
    simp only [grayDecodeStep]
    have hHalf : (g ^^^ grayDecodeStep k (g / 2)) / 2 = grayDecodeStep k (g / 2) := by
      rw [div_two_xor]
      unfold grayEncode at hRec
      calc
        g / 2 ^^^ grayDecodeStep k (g / 2) / 2
            = (grayDecodeStep k (g / 2) ^^^ grayDecodeStep k (g / 2) / 2) ^^^ grayDecodeStep k (g / 2) / 2 := by
              rw [hRec]
        _ = grayDecodeStep k (g / 2) := by
              rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    unfold grayEncode
    rw [hHalf, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

private theorem grayDecodeStep_eq_of_ge :
    ∀ (k1 k2 g : Nat), g ≤ k1 → g ≤ k2 → grayDecodeStep k1 g = grayDecodeStep k2 g
  | 0, k2, g, h1, _ => by
    have hg : g = 0 := by omega
    subst hg
    simp only [grayDecodeStep, grayDecodeStep_zero]
  | k1 + 1, 0, g, _, h2 => by
    have hg : g = 0 := by omega
    subst hg
    simp only [grayDecodeStep, grayDecodeStep_zero, Nat.zero_div, Nat.xor_zero]
  | k1 + 1, k2 + 1, g, h1, h2 => by
    simp only [grayDecodeStep]
    rw [grayDecodeStep_eq_of_ge k1 k2 (g / 2) (by omega) (by omega)]

/-- **Theorem 2a (Universal Unbounded-`Nat` Gray Right Inverse: `grayEncode (grayDecode g) = g`)**:
    For EVERY natural number `g : Nat`, `grayEncode (grayDecode g) = g`. -/
theorem gray_encode_decode_universal (g : Nat) :
    grayEncode (grayDecode g) = g :=
  grayDecodeStep_encode_decode g g (Nat.le_refl g)

/-- **Theorem 2b (Universal Unbounded-`Nat` Gray Left Inverse: `grayDecode (grayEncode n) = n`)**:
    For EVERY natural number `n : Nat`, `grayDecode (grayEncode n) = n` — certifying an exact
    bijection on all of `Nat`! -/
theorem gray_decode_encode_universal (n : Nat) :
    grayDecode (grayEncode n) = n := by
  unfold grayDecode
  have hEq := grayDecodeStep_eq_of_ge (grayEncode n) (grayEncode n + n) (grayEncode n)
    (Nat.le_refl _) (by omega)
  have hDec := grayDecodeStep_decode_encode (grayEncode n + n) n (by omega)
  omega

private theorem gray_even_step (m : Nat) :
    grayEncode (2 * m) ^^^ grayEncode (2 * m + 1) = 1 := by
  have hA : (2 * m) / 2 = m := by omega
  have hB : (2 * m + 1) / 2 = m := by omega
  unfold grayEncode
  rw [hA, hB]
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
    simp [Nat.testBit_zero]
    omega
  | succ j =>
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
    rw [Nat.testBit_succ (2 * m) j, Nat.testBit_succ (2 * m + 1) j, hA, hB]
    have hOne : (1 : Nat).testBit (j + 1) = false := by simp [Nat.testBit_succ]
    rw [hOne]
    cases (m.testBit j) <;> cases (m.testBit (j + 1)) <;> rfl

private theorem gray_odd_step (m : Nat) :
    grayEncode (2 * m + 1) ^^^ grayEncode (2 * m + 2) =
      2 * (grayEncode m ^^^ grayEncode (m + 1)) := by
  have hA : (2 * m + 1) / 2 = m := by omega
  have hB : (2 * m + 2) / 2 = m + 1 := by omega
  unfold grayEncode
  rw [hA, hB]
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
    simp [Nat.testBit_zero]
    omega
  | succ j =>
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
    rw [Nat.testBit_succ (2 * m + 1) j, Nat.testBit_succ (2 * m + 2) j, hA, hB]
    rw [Nat.testBit_succ (2 * _) j]
    have hC : (2 * (m ^^^ m / 2 ^^^ (m + 1 ^^^ (m + 1) / 2))) / 2 =
        m ^^^ m / 2 ^^^ (m + 1 ^^^ (m + 1) / 2) := by omega
    rw [hC, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
    rw [Nat.testBit_succ m j, Nat.testBit_succ (m + 1) j]

private theorem gray_unit_step_fuel :
    ∀ (fuel n : Nat), n ≤ fuel → ∃ k : Nat, grayEncode n ^^^ grayEncode (n + 1) = 2 ^ k
  | 0, n, h => by
    have hn : n = 0 := by omega
    subst hn
    exact ⟨0, rfl⟩
  | fuel + 1, n, h => by
    by_cases hEven : n % 2 = 0
    · refine ⟨0, ?_⟩
      have hn : n = 2 * (n / 2) := by omega
      rw [hn]
      exact gray_even_step (n / 2)
    · let m := n / 2
      have hmLe : m ≤ fuel := by omega
      obtain ⟨k, hk⟩ := gray_unit_step_fuel fuel m hmLe
      refine ⟨k + 1, ?_⟩
      have hn : n = 2 * m + 1 := by omega
      have hn1 : n + 1 = 2 * m + 2 := by omega
      rw [hn1, hn, gray_odd_step m, hk, Nat.pow_succ, Nat.mul_comm]

/-- **Theorem 2c (Universal Gray Unit-Hamming Step)**:
    For EVERY `n : Nat`, consecutive Gray codewords `grayEncode n` and `grayEncode (n + 1)`
    differ in EXACTLY ONE bit (`∃ k, grayEncode n ^^^ grayEncode (n + 1) = 2 ^ k`)! -/
theorem gray_consecutive_single_bit_flip (n : Nat) :
    ∃ k : Nat, grayEncode n ^^^ grayEncode (n + 1) = 2 ^ k :=
  gray_unit_step_fuel n n (Nat.le_refl n)

/-- 4-bit Hamming weight (`popcount4`) for asynchronous FIFO CDC pointer transitions. -/
def popcount4 (x : Nat) : Nat :=
  (x % 2) + ((x / 2) % 2) + ((x / 4) % 2) + ((x / 8) % 2)

/-- **Theorem 2d (CDC Async FIFO Witness: Gray `1`-Bit Transition vs. Binary `4`-Bit Glitch)**:
    Across all `16` cyclic 4-bit pointer increments, Gray code flips strictly `1` bit (`popcount = 1`),
    whereas standard binary `7 → 8` (`0111 → 1000`) flips all `4` bits (`7 ^^^ 8 = 15`, `popcount = 4`)
    creating `14` phantom metastability states on asynchronous clock-domain crossings. -/
theorem gray_cdc_fifo_single_bit_vs_binary_four_bit_glitch_witness :
    (∀ i : Fin 16, popcount4 (grayEncode i.val ^^^ grayEncode ((i.val + 1) % 16)) = 1) ∧
    grayEncode 7 = 4 ∧
    grayEncode 8 = 12 ∧
    popcount4 (grayEncode 7 ^^^ grayEncode 8) = 1 ∧
    (7 ^^^ 8) = 15 ∧
    popcount4 (7 ^^^ 8) = 4 := by
  decide

/-! ## Part 3: Wayne Smith (`1956`) `WSPT` Weighted Shortest Processing Time Exchange -/

/-- Weighted completion cost of running job `(w1, p1)` followed immediately by `(w2, p2)` at time `t`. -/
def wsptPairCost (t w1 p1 w2 p2 : Nat) : Nat :=
  w1 * (t + p1) + w2 * (t + p1 + p2)

/-- Total weighted completion time of an arbitrary job schedule `List (weight × duration)` starting at `t`. -/
def scheduleWeightedCost (t : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (w, p) :: rest => w * (t + p) + scheduleWeightedCost (t + p) rest

/-- **Theorem 3a (Universal Smith `WSPT` Adjacent-Pair Exact Difference Identity)**:
    For ALL start times `t` and ALL jobs `(w1, p1), (w2, p2)`:
    `wsptPairCost t w1 p1 w2 p2 + w1 * p2 = wsptPairCost t w2 p2 w1 p1 + w2 * p1`. -/
theorem smith_wspt_adjacent_pair_identity (t w1 p1 w2 p2 : Nat) :
    wsptPairCost t w1 p1 w2 p2 + w1 * p2 =
      wsptPairCost t w2 p2 w1 p1 + w2 * p1 := by
  simp only [wsptPairCost, Nat.mul_add]
  omega

/-- **Theorem 3b (Universal Arbitrary-Length Schedule Adjacent-Swap Exchange Identity)**:
    Swapping adjacent jobs `(w1, p1)` and `(w2, p2)` inside ANY surrounding schedule `pre ++ ... ++ suf`
    leaves every prefix and suffix completion time invariant and shifts total weighted latency by
    EXACTLY `w2 * p1 - w1 * p2` (`IFF` optimality criterion: `w2 * p1 ≤ w1 * p2`)! -/
theorem smith_wspt_arbitrary_schedule_exchange_identity
    (pre suf : List (Nat × Nat)) (t w1 p1 w2 p2 : Nat) :
    scheduleWeightedCost t (pre ++ (w1, p1) :: (w2, p2) :: suf) + w1 * p2 =
      scheduleWeightedCost t (pre ++ (w2, p2) :: (w1, p1) :: suf) + w2 * p1 := by
  induction pre generalizing t with
  | nil =>
    simp only [List.nil_append, scheduleWeightedCost]
    have hTime : t + p1 + p2 = t + p2 + p1 := by omega
    rw [hTime]
    simp only [Nat.mul_add]
    omega
  | cons job rest ih =>
    rcases job with ⟨w0, p0⟩
    simp only [List.cons_append, scheduleWeightedCost]
    have hSub := ih (t + p0)
    omega

/-- **Theorem 3c (Exact `WSPT` Adjacent-Optimality `IFF` Across Arbitrary Schedules)**:
    Placing `(w1, p1)` before `(w2, p2)` in `pre ++ ... ++ suf` achieves lower-or-equal total
    weighted completion cost IF AND ONLY IF Smith's ratio holds (`w2 * p1 ≤ w1 * p2`, i.e. `w1/p1 ≥ w2/p2`). -/
theorem smith_wspt_arbitrary_schedule_optimality_iff
    (pre suf : List (Nat × Nat)) (t w1 p1 w2 p2 : Nat) :
    scheduleWeightedCost t (pre ++ (w1, p1) :: (w2, p2) :: suf) ≤
      scheduleWeightedCost t (pre ++ (w2, p2) :: (w1, p1) :: suf) ↔
      w2 * p1 ≤ w1 * p2 := by
  have hId := smith_wspt_arbitrary_schedule_exchange_identity pre suf t w1 p1 w2 p2
  omega

/-- **Theorem 3d (Premise-Failure Counterexample: Unweighted `SPT` Priority-Inversion Blowup)**:
    Ordering by shortest duration alone (`p_A = 2 < p_B = 3`) puts low-weight job `A = (1, 2)`
    ahead of urgent job `B = (100, 3)`, inflating weighted latency from `305` to `502` (`+197` penalty),
    and on 3 jobs `[(1, 2), (100, 3), (40, 4)]` from `589` (`WSPT`) to `862` (`SPT`, `+273` penalty). -/
theorem smith_wspt_vs_unweighted_spt_counterexamples :
    scheduleWeightedCost 0 [(100, 3), (1, 2)] = 305 ∧
    scheduleWeightedCost 0 [(1, 2), (100, 3)] = 502 ∧
    scheduleWeightedCost 0 [(100, 3), (40, 4), (1, 2)] = 589 ∧
    scheduleWeightedCost 0 [(1, 2), (100, 3), (40, 4)] = 862 := by
  decide

end MillerRabinGrayCodeAndSmithWsptFrontier
