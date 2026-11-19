/-
Copyright (c) 2026 Common Ground Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace CommonGround.Frontier.MoeDualBiasNetworkCodingAndShamirSharing

/-!
# Wave V242 Frontier (#117): Loss-Free Dual-Bias `MoE` Capacity Routing, Butterfly Linear Network Coding & Shamir Secret Sharing

Unifies **Sparse Mixture-of-Experts (`MoE`) Optimization (`04`+`08`)**, **Algebraic Network Information
Flow (`09`+`02`)**, and **Information-Theoretic Threshold Cryptography (`02`+`03`+`10`)** through a
single structural principle: **capacity bottlenecks that defeat greedy or unmixed routing (`66.7%` `MoE`
token drop, `1`-bit store-and-forward collision, `x = 0` coordinate collapse) are resolved losslessly
by dual Lagrange bias potentials and finite-field linear/polynomial mixing**.
-/

/-- Pure-core finite sum over `Fin n` valued in `Int`. -/
def finSumInt : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f =>
      finSumInt n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) +
        f ⟨n, Nat.lt_succ_self n⟩

/-- Pure-core finite sum over `Fin n` valued in `Nat`. -/
def finSumNat : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f =>
      finSumNat n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) +
        f ⟨n, Nat.lt_succ_self n⟩

theorem finSumInt_add (n : Nat) (f g : Fin n → Int) :
    finSumInt n (fun i => f i + g i) = finSumInt n f + finSumInt n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [finSumInt]
      rw [ih]
      omega

theorem finSumInt_mul_const (n : Nat) (f : Fin n → Int) (c : Int) :
    finSumInt n (fun i => f i * c) = finSumInt n f * c := by
  induction n with
  | zero => simp [finSumInt]
  | succ k ih =>
      simp only [finSumInt]
      rw [ih, Int.add_mul]

theorem finSumInt_le_finSumInt (n : Nat) (f g : Fin n → Int)
    (h : ∀ i : Fin n, f i ≤ g i) :
    finSumInt n f ≤ finSumInt n g := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ k ih =>
      simp only [finSumInt]
      have h1 := ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                    (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
                    (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      have h2 := h ⟨k, Nat.lt_succ_self k⟩
      omega

theorem finSumInt_swap (M E : Nat) (F : Fin M → Fin E → Int) :
    finSumInt M (fun i => finSumInt E (fun e => F i e)) =
      finSumInt E (fun e => finSumInt M (fun i => F i e)) := by
  induction M with
  | zero =>
      have hz : ∀ k : Nat, finSumInt k (fun _ => (0 : Int)) = 0 := by
        intro k
        induction k with
        | zero => rfl
        | succ m ihm => simp [finSumInt, ihm]
      exact (hz E).symm
  | succ m ih =>
      simp only [finSumInt]
      rw [ih, ← finSumInt_add]

/-! ## Part I: Loss-Free Dual-Bias `MoE` Routing Optimality vs. Token-Drop Collapse (`04`+`08`) -/

/-- Total true affinity `∑_{i, e} A(i, e) · S(i, e)` of an `M`-token, `E`-expert routing matrix `A`. -/
def moeTrueAffinity (M E : Nat) (A S : Fin M → Fin E → Int) : Int :=
  finSumInt M (fun i => finSumInt E (fun e => A i e * S i e))

/-- Total biased routing score `∑_{i, e} A(i, e) · (S(i, e) + b(e))`. -/
def moeBiasedAffinity (M E : Nat) (A S : Fin M → Fin E → Int) (b : Fin E → Int) : Int :=
  finSumInt M (fun i => finSumInt E (fun e => A i e * (S i e + b e)))

/-- Exact decomposition: `moeBiasedAffinity(A) = moeTrueAffinity(A) + ∑_e (∑_i A(i,e)) · b(e)`. -/
theorem moe_biased_affinity_decomposition (M E : Nat)
    (A S : Fin M → Fin E → Int) (b : Fin E → Int) :
    moeBiasedAffinity M E A S b =
      moeTrueAffinity M E A S +
        finSumInt E (fun e => finSumInt M (fun i => A i e) * b e) := by
  unfold moeBiasedAffinity moeTrueAffinity
  have h_row : ∀ i : Fin M,
      finSumInt E (fun e => A i e * (S i e + b e)) =
        finSumInt E (fun e => A i e * S i e) + finSumInt E (fun e => A i e * b e) := by
    intro i
    have h_dist : (fun e : Fin E => A i e * (S i e + b e)) =
        (fun e : Fin E => A i e * S i e + A i e * b e) := by
      funext e
      exact Int.mul_add (A i e) (S i e) (b e)
    rw [h_dist, finSumInt_add]
  have h_fn : (fun i : Fin M => finSumInt E (fun e => A i e * (S i e + b e))) =
      (fun i : Fin M => finSumInt E (fun e => A i e * S i e) + finSumInt E (fun e => A i e * b e)) := by
    funext i
    exact h_row i
  rw [h_fn, finSumInt_add, finSumInt_swap M E (fun i e => A i e * b e)]
  have h_col : (fun e : Fin E => finSumInt M (fun i => A i e * b e)) =
      (fun e : Fin E => finSumInt M (fun i => A i e) * b e) := by
    funext e
    exact finSumInt_mul_const M (fun i => A i e) (b e)
  rw [h_col]

/-- **Universal Loss-Free Dual-Bias `MoE` Global Optimality (`04`+`08`, `DeepSeek-V3` Mechanism)**:
    If `A` and `B` satisfy the exact same expert capacity loads `∑_i A(i,e) = C(e) = ∑_i B(i,e)`
    and for every token `i`, `A` maximizes the biased score `S(i, e) + b(e)` row-wise
    (`∑_e B(i,e)(S(i,e)+b(e)) ≤ ∑_e A(i,e)(S(i,e)+b(e))`), then `A` **globally maximizes true
    expert affinity `moeTrueAffinity`** (`moeTrueAffinity B ≤ moeTrueAffinity A`) — the routing
    biases `b(e)` cancel identically without polluting training gradients! -/
theorem dual_bias_balanced_moe_maximizes_true_affinity (M E : Nat)
    (A B S : Fin M → Fin E → Int) (C b : Fin E → Int)
    (hCapA : ∀ e : Fin E, finSumInt M (fun i => A i e) = C e)
    (hCapB : ∀ e : Fin E, finSumInt M (fun i => B i e) = C e)
    (hRowOpt : ∀ i : Fin M,
      finSumInt E (fun e => B i e * (S i e + b e)) ≤
        finSumInt E (fun e => A i e * (S i e + b e))) :
    moeTrueAffinity M E B S ≤ moeTrueAffinity M E A S := by
  have hBiasedLe : moeBiasedAffinity M E B S b ≤ moeBiasedAffinity M E A S b :=
    finSumInt_le_finSumInt M _ _ hRowOpt
  rw [moe_biased_affinity_decomposition, moe_biased_affinity_decomposition] at hBiasedLe
  have hBiasEq :
      finSumInt E (fun e => finSumInt M (fun i => B i e) * b e) =
        finSumInt E (fun e => finSumInt M (fun i => A i e) * b e) := by
    have hfn : (fun e : Fin E => finSumInt M (fun i => B i e) * b e) =
        (fun e : Fin E => finSumInt M (fun i => A i e) * b e) := by
      funext e
      rw [hCapB e, hCapA e]
    rw [hfn]
  omega

/-- Concrete `6`-token, `3`-expert (`capacity C = 2`) affinity matrix where all `6` tokens rank
    Expert `0` highest (`10`), while tokens `0..1`, `2..3`, `4..5` have distinct secondary skills. -/
def moeScoresHetero6x3 (i : Fin 6) (e : Fin 3) : Int :=
  let rows : List (List Int) := [
    [10, 6, 1],
    [10, 6, 1],
    [10, 9, 3],
    [10, 9, 3],
    [10, 5, 6],
    [10, 5, 6]
  ]
  (rows.getD i.val []).getD e.val 0

/-- Unbiased greedy argmax (`b = (0, 0, 0)`) sends all `6` tokens to Expert `0`, overflowing `C = 2`
    by `4` dropped tokens (`4/6 = 66.7%` token drop; served affinity = `20`). -/
def moeGreedyUnbalanced (_i : Fin 6) (e : Fin 3) : Int :=
  if e.val == 0 then 1 else 0

/-- Exact dual biases `b = (0, 2, 5)`:
    - Tokens `0,1`: `S + b = [10, 8, 6]` -> Expert `0` (`10`)
    - Tokens `2,3`: `S + b = [10, 11, 8]` -> Expert `1` (`11`)
    - Tokens `4,5`: `S + b = [10, 7, 11]` -> Expert `2` (`11`)! -/
def moeDualBias3 (e : Fin 3) : Int :=
  [0, 2, 5].getD e.val 0

def moeBalancedOpt6x3 (i : Fin 6) (e : Fin 3) : Int :=
  if i.val / 2 == e.val then 1 else 0

/-- Concrete witness & premise-failure contrast:
    1) Unbiased argmax sends `6 > 2` tokens to Expert `0` (`4` tokens dropped, served affinity `20`),
    2) Dual-bias `b = (0, 2, 5)` routes `(2, 2, 2)` tokens (`0` drops!) with optimal true affinity `50` (`10+10+9+9+6+6 = 50`). -/
theorem moe_6x3_token_drop_vs_loss_free_dual_bias_witness :
    finSumInt 6 (fun i => moeGreedyUnbalanced i ⟨0, by decide⟩) = 6 ∧
    (∀ e : Fin 3, finSumInt 6 (fun i => moeBalancedOpt6x3 i e) = 2) ∧
    moeTrueAffinity 6 3 moeBalancedOpt6x3 moeScoresHetero6x3 = 50 ∧
    (∀ i : Fin 6, ∀ e : Fin 3,
      moeScoresHetero6x3 i e + moeDualBias3 e ≤
        finSumInt 3 (fun e' => moeBalancedOpt6x3 i e' * (moeScoresHetero6x3 i e' + moeDualBias3 e'))) := by
  decide

/-! ## Part II: Ahlswede–Cai–Li–Yeung Butterfly Linear Network Coding vs. Store-and-Forward Bottleneck (`09`+`02`) -/

/-- Butterfly network with two source bits `(b₁, b₂) ∈ Fin 2 × Fin 2`:
    - Receiver `R₁` observes direct side-link `b₁` plus shared bottleneck bit `e_mid`.
    - Receiver `R₂` observes direct side-link `b₂` plus shared bottleneck bit `e_mid`.
    Under `𝔽₂` linear network coding, the bottleneck router transmits XOR `e_mid = (b₁ + b₂) % 2`. -/
def butterflyXorMid (b₁ b₂ : Fin 2) : Fin 2 :=
  ⟨(b₁.val + b₂.val) % 2, Nat.mod_lt _ (by decide)⟩

def butterflyDecodeR1 (b₁ eMid : Fin 2) : Fin 2 × Fin 2 :=
  (b₁, ⟨(b₁.val + eMid.val) % 2, Nat.mod_lt _ (by decide)⟩)

def butterflyDecodeR2 (b₂ eMid : Fin 2) : Fin 2 × Fin 2 :=
  (⟨(b₂.val + eMid.val) % 2, Nat.mod_lt _ (by decide)⟩, b₂)

/-- **Positive Witness (`butterfly_linear_network_coding_achieves_2bit_multicast`)**:
    Transmitting a single XOR parity bit `e_mid = (b₁ + b₂) mod 2` across the shared bottleneck
    allows BOTH receivers `R₁` and `R₂` to recover `(b₁, b₂)` losslessly for all `4` input pairs
    (`2` bits/tick simultaneous multicast throughput)! -/
theorem butterfly_linear_network_coding_achieves_2bit_multicast :
    ∀ b₁ b₂ : Fin 2,
      butterflyDecodeR1 b₁ (butterflyXorMid b₁ b₂) = (b₁, b₂) ∧
      butterflyDecodeR2 b₂ (butterflyXorMid b₁ b₂) = (b₁, b₂) := by
  decide

/-- **Premise-Failure Counterexample (`butterfly_store_and_forward_routing_bottleneck_impossibility`)**:
    Under pure store-and-forward routing (forwarding either `e_mid = b₁` or `e_mid = b₂` without
    algebraic mixing), NO decoder `(dec₁, dec₂)` can simultaneously deliver `(b₁, b₂)` to both
    receivers: forwarding `b₁` makes `(1, 0)` and `(1, 1)` indistinguishable at `R₁`,
    while forwarding `b₂` makes `(0, 1)` and `(1, 1)` indistinguishable at `R₂`! -/
theorem butterfly_store_and_forward_routing_bottleneck_impossibility :
    (∀ dec₁ : Fin 2 → Fin 2 → Fin 2 × Fin 2,
      ¬ (∀ b₁ b₂ : Fin 2, dec₁ b₁ b₁ = (b₁, b₂))) ∧
    (∀ dec₂ : Fin 2 → Fin 2 → Fin 2 × Fin 2,
      ¬ (∀ b₁ b₂ : Fin 2, dec₂ b₂ b₂ = (b₁, b₂))) := by
  constructor
  · intro dec₁ hAll
    have h0 := hAll ⟨1, by decide⟩ ⟨0, by decide⟩
    have h1 := hAll ⟨1, by decide⟩ ⟨1, by decide⟩
    rw [h0] at h1
    injection h1 with _ hEq
    exact absurd (congrArg Fin.val hEq) (by decide)
  · intro dec₂ hAll
    have h0 := hAll ⟨0, by decide⟩ ⟨1, by decide⟩
    have h1 := hAll ⟨1, by decide⟩ ⟨1, by decide⟩
    rw [h0] at h1
    injection h1 with hEq _
    exact absurd (congrArg Fin.val hEq) (by decide)

/-! ## Part III: Shamir `(2, n)` Polynomial Secret Sharing over `𝔽_p` (`𝔽₇` / `𝔽₁₇`) vs. `x = 0` Coordinate Leak (`02`+`03`+`10`) -/

/-- Universal `(2, n)` Shamir share evaluation modulo `p > 0`: `P_{s, r}(x) = (s + r · x) mod p`. -/
def shamirEvalMod (p : Nat) (hp : 0 < p) (s r x : Fin p) : Fin p :=
  ⟨(s.val + r.val * x.val) % p, Nat.mod_lt _ hp⟩

/-- **Universal `Fin p` Zero-Coordinate Total Secret Leak (`shamir_zero_coordinate_universal_leak`)**:
    For ANY prime/modulus `p > 0`, evaluating a `(2, n)` Shamir polynomial at `x = 0` (`0`-indexed
    participant ID bug) annihilates the random slope `r · 0 = 0` and outputs `P_{s, r}(0) = s`
    identically for EVERY random mask `r : Fin p`! -/
theorem shamir_zero_coordinate_universal_leak (p : Nat) (hp : 0 < p) (s r : Fin p) :
    shamirEvalMod p hp s r ⟨0, hp⟩ = s := by
  apply Fin.ext
  simp only [shamirEvalMod, Nat.mul_zero, Nat.add_zero]
  exact Nat.mod_eq_of_lt s.isLt

/-- `(2, n)` Shamir share evaluation over `𝔽₁₇` and `𝔽₇`. -/
def shamirEval17 (s r x : Fin 17) : Fin 17 :=
  ⟨(s.val + r.val * x.val) % 17, Nat.mod_lt _ (by decide)⟩

def shamirEval7 (s r x : Fin 7) : Fin 7 :=
  ⟨(s.val + r.val * x.val) % 7, Nat.mod_lt _ (by decide)⟩

/-- Exact O(1) multiplicative inverse table in `𝔽₁₇` (`a · inv17(a) ≡ 1 mod 17` for `1 ≤ a ≤ 16`). -/
def modInv17 (a : Nat) : Nat :=
  [0, 1, 9, 6, 13, 7, 3, 5, 15, 2, 12, 14, 10, 4, 11, 8, 16].getD (a % 17) 0

/-- Lagrange interpolation at `0` from two shares `(x₁, y₁)` and `(x₂, y₂)` over `𝔽₁₇`:
    `s = (x₂ · y₁ - x₁ · y₂) · (x₂ - x₁)⁻¹ mod 17`. -/
def shamirReconstruct2of17 (x₁ y₁ x₂ y₂ : Fin 17) : Fin 17 :=
  let num := (x₂.val * y₁.val + 289 - x₁.val * y₂.val) % 17
  let den := (x₂.val + 17 - x₁.val) % 17
  ⟨(num * modInv17 den) % 17, Nat.mod_lt _ (by decide)⟩

/-- Count of random slopes `r ∈ Fin 7` producing share `y` at coordinate `x` for secret `s` over `𝔽₇`. -/
def shamirSlopeHitCount7 (s x y : Fin 7) : Nat :=
  finSumNat 7 (fun r => if shamirEval7 s r x == y then 1 else 0)

/-- **Positive Witness 1 (`shamir_2_of_n_exact_lagrange_reconstruction_17`)**:
    For distinct nonzero public coordinates `x₁ = 1, x₂ = 2` (and `x₁ = 3, x₂ = 11`),
    Lagrange interpolation recovers EVERY secret `s ∈ Fin 17` across ALL `17` random slopes `r ∈ Fin 17`! -/
theorem shamir_2_of_n_exact_lagrange_reconstruction_17 :
    (∀ s r : Fin 17,
      shamirReconstruct2of17 ⟨1, by decide⟩ (shamirEval17 s r ⟨1, by decide⟩)
                             ⟨2, by decide⟩ (shamirEval17 s r ⟨2, by decide⟩) = s) ∧
    (∀ s r : Fin 17,
      shamirReconstruct2of17 ⟨3, by decide⟩ (shamirEval17 s r ⟨3, by decide⟩)
                             ⟨11, by decide⟩ (shamirEval17 s r ⟨11, by decide⟩) = s) := by
  decide

/-- **Positive Witness 2 (`shamir_single_share_perfect_uniformity_7`)**:
    At EVERY nonzero evaluation coordinate `x ∈ Fin 7` (`x ≠ 0`), EVERY secret `s ∈ Fin 7` and
    EVERY observed share value `y ∈ Fin 7` has **exact slope multiplicity `1`** (`Pr[Y_x = y | S = s] = 1/7`
    independent of `s`, proving `I(S; Y_x) = 0` information-theoretic zero leakage)! -/
theorem shamir_single_share_perfect_uniformity_7 :
    ∀ x : Fin 7, x.val ≠ 0 →
      ∀ s y : Fin 7, shamirSlopeHitCount7 s x y = 1 := by
  decide

/-- **Premise-Failure Counterexample (`shamir_zero_coordinate_evaluation_total_leak_counterexample`)**:
    At `x = 0`, `P_{s, r}(0)` annihilates the random mask `r · 0 = 0`, producing `y = s` with
    multiplicity `7` (`100%` probability) and `0` for `y ≠ s`, leaking the entire secret from `1` share! -/
theorem shamir_zero_coordinate_evaluation_total_leak_counterexample :
    (∀ s r : Fin 7, shamirEval7 s r ⟨0, by decide⟩ = s) ∧
    shamirSlopeHitCount7 ⟨5, by decide⟩ ⟨0, by decide⟩ ⟨5, by decide⟩ = 7 ∧
    shamirSlopeHitCount7 ⟨5, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩ = 0 := by
  decide

end CommonGround.Frontier.MoeDualBiasNetworkCodingAndShamirSharing
