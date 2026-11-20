/-
  CommonGround/Verification/TheoremAtlasMillerRabinGrayCodeAndSmithWsptBridge.lean

  Milestone Wave V285 · Suite #686, 140 Exact Finite Micro-Labs & 160 Frontier Modules:
  Cross-Domain Kernel Bridge Unifying:
  - Miller–Rabin (`1976`/`1980`) Non-Trivial Square-Root Factor Split (`1 < gcd(x - 1, n) < n`)
    vs. Carmichael `561 = 3 * 11 * 17` Korselt-CRT Fermat False Positive (`a^560 ≡ 1 mod 561`
    for all coprime bases vs. Miller–Rabin `67^2 ≡ 1 mod 561`, `gcd(66, 561) = 33`) (`tc-numtheory` ↔ `cslib`)
  - Frank Gray (`1953`) Reflected Binary Gray Code Unbounded Bijection (`grayDecode (grayEncode n) = n`,
    `grayEncode (grayDecode g) = g`) & Universal Unit-Hamming Step (`∃ k, g(n) ^^^ g(n+1) = 2^k`)
    vs. Binary `0111 → 1000` `4`-Bit CDC Async FIFO Metastability Glitch (`oai-codes` ↔ `cslib`)
  - Wayne Smith (`1956`) `WSPT` Weighted Shortest Processing Time Arbitrary-Schedule Exchange `IFF`
    (`cost(pre ++ j1::j2::suf) ≤ cost(pre ++ j2::j1::suf) ↔ w2 * p1 ≤ w1 * p2`) vs. Unweighted `SPT`
    Priority Inversion (`502` vs. `305`; `862` vs. `589`) (`econlib` ↔ `cslib` ↔ `apsp3sum`)

  Toolchain: leanprover/lean4:v4.33.0 (zero sorry).
-/

namespace CommonGround.Verification.TheoremAtlasMillerRabinGrayCodeAndSmithWsptBridge

def powModFuel : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, mod => if mod = 0 then 0 else 1 % mod
  | fuel + 1, base, exp, mod =>
    if mod = 0 then 0
    else if exp = 0 then 1 % mod
    else
      let half := powModFuel fuel base (exp / 2) mod
      let sq := (half * half) % mod
      if exp % 2 = 1 then (sq * (base % mod)) % mod else sq

def powMod (base exp mod : Nat) : Nat :=
  powModFuel 16 base exp mod

def grayEncode (n : Nat) : Nat := n ^^^ (n / 2)

def grayDecodeStep : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, g => g ^^^ grayDecodeStep k (g / 2)

def grayDecode (g : Nat) : Nat := grayDecodeStep g g

def popcount4 (x : Nat) : Nat :=
  (x % 2) + ((x / 2) % 2) + ((x / 4) % 2) + ((x / 8) % 2)

def scheduleWeightedCost (t : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (w, p) :: rest => w * (t + p) + scheduleWeightedCost (t + p) rest

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
    subst hn; exact ⟨0, rfl⟩
  | fuel + 1, n, h => by
    by_cases hEven : n % 2 = 0
    · refine ⟨0, ?_⟩
      have hn : n = 2 * (n / 2) := by omega
      rw [hn]; exact gray_even_step (n / 2)
    · let m := n / 2
      have hmLe : m ≤ fuel := by omega
      obtain ⟨k, hk⟩ := gray_unit_step_fuel fuel m hmLe
      refine ⟨k + 1, ?_⟩
      have hn : n = 2 * m + 1 := by omega
      have hn1 : n + 1 = 2 * m + 2 := by omega
      rw [hn1, hn, gray_odd_step m, hk, Nat.pow_succ, Nat.mul_comm]

/--
  **Bridge 1 (`tc-numtheory` ↔ `cslib`)**:
  Universal Miller–Rabin non-trivial square-root factor split (`1 < gcd(x - 1, n) < n ∧ gcd ∣ n`)
  paired with the Carmichael `561 = 3 * 11 * 17` premise-failure witness where Fermat passes
  `2^560 % 561 = 1` while Miller–Rabin exposes `67^2 % 561 = 1` and factors `gcd(66, 561) = 33`.
-/
theorem miller_rabin_sqrt_factor_split_vs_carmichael_561_bridge
    (n x : Nat) (hn : 2 ≤ n) (hxLo : 1 < x) (hxHi : x + 1 < n)
    (hSq : n ∣ (x - 1) * (x + 1)) :
    (1 < Nat.gcd (x - 1) n ∧ Nat.gcd (x - 1) n < n ∧ Nat.gcd (x - 1) n ∣ n) ∧
    (powMod 2 560 561 = 1 ∧ powMod 2 35 561 = 263 ∧ (67 * 67) % 561 = 1 ∧
      Nat.gcd (67 - 1) 561 = 33 ∧ Nat.gcd (67 + 1) 561 = 17) := by
  refine ⟨?_, by decide⟩
  have hDvdN : Nat.gcd (x - 1) n ∣ n := Nat.gcd_dvd_right (x - 1) n
  have hDvdX : Nat.gcd (x - 1) n ∣ x - 1 := Nat.gcd_dvd_left (x - 1) n
  have hLeX : Nat.gcd (x - 1) n ≤ x - 1 := Nat.le_of_dvd (by omega) hDvdX
  have hNe0 : Nat.gcd (x - 1) n ≠ 0 := by
    intro h0; rw [h0] at hDvdN; rcases hDvdN with ⟨k, hk⟩; omega
  have hNe1 : Nat.gcd (x - 1) n ≠ 1 := by
    intro h1
    have hCop : Nat.Coprime n (x - 1) := by unfold Nat.Coprime; rw [Nat.gcd_comm]; exact h1
    have hLeXp1 : n ≤ x + 1 := Nat.le_of_dvd (by omega) (hCop.dvd_of_dvd_mul_left hSq)
    omega
  exact ⟨by omega, by omega, hDvdN⟩

/--
  **Bridge 2 (`oai-codes` ↔ `cslib`)**:
  Universal Frank Gray (`1953`) unbounded-`Nat` prefix-XOR bijection (`grayDecode (grayEncode n) = n`)
  and single-bit consecutive transition (`∃ k, grayEncode n ^^^ grayEncode (n + 1) = 2 ^ k`) vs.
  binary `0111 → 1000` `4`-bit CDC async FIFO metastability glitch (`popcount4 (7 ^^^ 8) = 4`).
-/
theorem gray_code_unbounded_bijection_and_unit_step_vs_binary_glitch_bridge (n : Nat) :
    (grayDecode (grayEncode n) = n ∧ ∃ k : Nat, grayEncode n ^^^ grayEncode (n + 1) = 2 ^ k) ∧
    (popcount4 (grayEncode 7 ^^^ grayEncode 8) = 1 ∧ popcount4 (7 ^^^ 8) = 4) := by
  refine ⟨⟨?_, gray_unit_step_fuel n n (Nat.le_refl n)⟩, by decide⟩
  unfold grayDecode
  have hEq := grayDecodeStep_eq_of_ge (grayEncode n) (grayEncode n + n) (grayEncode n)
    (Nat.le_refl _) (by omega)
  have hDec := grayDecodeStep_decode_encode (grayEncode n + n) n (by omega)
  omega

/--
  **Bridge 3 (`econlib` ↔ `cslib` ↔ `apsp3sum`)**:
  Universal Wayne Smith (`1956`) `WSPT` arbitrary-schedule adjacent-exchange optimality `IFF`
  (`scheduleWeightedCost t (pre ++ j1::j2::suf) ≤ scheduleWeightedCost t (pre ++ j2::j1::suf) ↔ w2 * p1 ≤ w1 * p2`)
  paired with unweighted `SPT` priority-inversion counterexamples (`305 < 502`, `589 < 862`).
-/
theorem smith_wspt_exchange_iff_vs_unweighted_spt_inversion_bridge
    (pre suf : List (Nat × Nat)) (t w1 p1 w2 p2 : Nat) :
    (scheduleWeightedCost t (pre ++ (w1, p1) :: (w2, p2) :: suf) ≤
      scheduleWeightedCost t (pre ++ (w2, p2) :: (w1, p1) :: suf) ↔
      w2 * p1 ≤ w1 * p2) ∧
    (scheduleWeightedCost 0 [(100, 3), (1, 2)] = 305 ∧
      scheduleWeightedCost 0 [(1, 2), (100, 3)] = 502 ∧
      scheduleWeightedCost 0 [(100, 3), (40, 4), (1, 2)] = 589 ∧
      scheduleWeightedCost 0 [(1, 2), (100, 3), (40, 4)] = 862) := by
  refine ⟨?_, by decide⟩
  have hId :
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
  omega

/--
  **Master Triad Theorem (`Suite #686`, `140` Labs & `160` Frontier Modules Milestone)**:
  Simultaneously certifies Miller–Rabin non-trivial square-root factor splitting (`1 < gcd < n`),
  Frank Gray unbounded prefix-XOR bijection + single-bit Hamming transition (`2^k`), and
  Wayne Smith `WSPT` arbitrary-schedule adjacent-exchange optimality `IFF`.
-/
theorem master_miller_rabin_gray_code_and_smith_wspt_bridge
    (n x g : Nat) (pre suf : List (Nat × Nat)) (t w1 p1 w2 p2 : Nat)
    (hn : 2 ≤ n) (hxLo : 1 < x) (hxHi : x + 1 < n)
    (hSq : n ∣ (x - 1) * (x + 1)) :
    (1 < Nat.gcd (x - 1) n ∧ Nat.gcd (x - 1) n < n ∧ Nat.gcd (x - 1) n ∣ n) ∧
    (grayDecode (grayEncode g) = g ∧ ∃ k : Nat, grayEncode g ^^^ grayEncode (g + 1) = 2 ^ k) ∧
    (scheduleWeightedCost t (pre ++ (w1, p1) :: (w2, p2) :: suf) ≤
      scheduleWeightedCost t (pre ++ (w2, p2) :: (w1, p1) :: suf) ↔
      w2 * p1 ≤ w1 * p2) := by
  exact ⟨(miller_rabin_sqrt_factor_split_vs_carmichael_561_bridge n x hn hxLo hxHi hSq).1,
         (gray_code_unbounded_bijection_and_unit_step_vs_binary_glitch_bridge g).1,
         (smith_wspt_exchange_iff_vs_unweighted_spt_inversion_bridge pre suf t w1 p1 w2 p2).1⟩

end CommonGround.Verification.TheoremAtlasMillerRabinGrayCodeAndSmithWsptBridge
