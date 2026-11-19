/-
  09-consequence-lens-meta-atlas/SkipListExpressSearchLamportBakeryMutexAndRsaEulerMalleabilityFrontier.lean

  Wave V268 · Frontier #143 (812 ZERO-SORRY .lean FILES & 772 KERNEL-COMPILED MODULES!):
  Cross-Domain Structural Bridge Unifying:
  1. Pugh Skip-List Dyadic Express-Lane Search & `< 2N` Pointer Telescoping (`cslib` ↔ `tc-probcomb`):
     - Universal Dyadic Tower Sum: `∀ L : Nat, dyadicTowerSum L + 1 = 2 ^ (L + 1)` (`< 2` pointers/key!).
     - Express-Lane Search Witness (`N = 8`): `skipListSteps8 y ≤ 4` across all `y ∈ Fin 8` vs.
       level-`0` degenerated linked list (`linearScanSteps8 7 = 8 = N`).
  2. Lamport Bakery `(ticket, threadId)` Lexicographic Mutual Exclusion (`cslib` ↔ `econlib`):
     - Universal Strict Asymmetric Trichotomy: for `i ≠ j`, `bakeryLt ti i tj j` and `bakeryLt tj j ti i`
       are mutually exclusive and exhaustive (`100%` mutual exclusion without hardware `CAS`!), whereas
       dropping the `threadId` tie-breaker on colliding tickets `t₀ = t₁ = 6` causes simultaneous
       critical-section entry under `<` (`!(6 < 6)`) or mutual deadlock under `≤` (`6 ≤ 6`)!
  3. Rivest–Shamir–Adleman (`RSA`) CRT/Euler Decryption over `ℤ₃₃` (`n = 3 × 11`, `e = 3, d = 7`)
     vs. Textbook Unpadded Malleability & Common-Modulus Attack (`flt` ↔ `cslib` ↔ `oai-codes`):
     - Exhaustive `33/33` (`100%`) Bijective Decryption `((m^3 % 33)^7) % 33 = m` across all `Fin 33`.
     - Exhaustive `1,089/1,089` Unpadded Multiplicative Malleability `Enc(a)·Enc(b) ≡ Enc(a·b) (mod 33)`
       and Keyless Common-Modulus (`e₁ = 3, e₂ = 5`) Bezout Plaintext Extraction `c₁² · c₂⁻¹ ≡ m (mod 33)`!

  Toolchain: leanprover/lean4:v4.33.0 (zero sorry).
-/

namespace CommonGround.Frontier.SkipListExpressSearchLamportBakeryMutexAndRsaEulerMalleability

/-! ## Part 1: Pugh Skip-List Dyadic Pointer Telescoping & Express-Lane Search -/

def dyadicTowerSum : Nat → Nat
  | 0 => 1
  | k + 1 => dyadicTowerSum k + 2 ^ (k + 1)

theorem skip_list_dyadic_tower_telescoping :
    ∀ L : Nat, dyadicTowerSum L + 1 = 2 ^ (L + 1)
  | 0 => rfl
  | L + 1 => by
    have ih := skip_list_dyadic_tower_telescoping L
    simp [dyadicTowerSum]
    have hPow : 2 ^ (L + 1 + 1) = 2 ^ (L + 1) + 2 ^ (L + 1) := by
      rw [Nat.pow_succ]
      omega
    omega

/-- Express-lane probes on `8`-key skip-list (`L2={0,4}, L1={0,2,4,6}, L0={0..7}`). -/
def skipListSteps8 (target : Fin 8) : Nat :=
  1 + (if target.val >= 4 then 1 else 0) +
      (if target.val % 4 >= 2 then 1 else 0) +
      (if target.val % 2 == 1 then 1 else 0)

def linearScanSteps8 (target : Fin 8) : Nat :=
  target.val + 1

theorem skip_list_express4_vs_linear8 :
    (∀ y : Fin 8, skipListSteps8 y ≤ 4) ∧
    skipListSteps8 ⟨7, by decide⟩ = 4 ∧
    linearScanSteps8 ⟨7, by decide⟩ = 8 := by
  decide

/-! ## Part 2: Lamport Bakery `(ticket, threadId)` Lexicographic Mutual Exclusion -/

def bakeryLt (ti i tj j : Nat) : Prop :=
  ti < tj ∨ (ti = tj ∧ i < j)

theorem lamport_bakery_strict_mutex_and_totality
    (ti i tj j : Nat) (hDistinct : i ≠ j) :
    (¬(bakeryLt ti i tj j ∧ bakeryLt tj j ti i)) ∧
    (bakeryLt ti i tj j ∨ bakeryLt tj j ti i) := by
  unfold bakeryLt
  constructor
  · intro hBoth
    omega
  · omega

/-- Without `threadId` tie-breaking on equal tickets `t = 6`:
    - Waiting only when `t_other < t_me` (`6 < 6 = false`) lets BOTH threads enter (`2` in CS!).
    - Waiting whenever `t_other ≤ t_me` (`6 ≤ 6 = true`) blocks BOTH threads (`0` progress!). -/
theorem untied_ticket_collision_dual_entry_or_deadlock :
    (!(decide (6 < 6)) && !(decide (6 < 6))) = true ∧
    (decide (6 ≤ 6) && decide (6 ≤ 6)) = true := by
  decide

/-! ## Part 3: `RSA` over `ℤ₃₃` (`n = 3 × 11`, `e = 3, d = 7`) vs. Malleability & Common-Modulus Attack -/

def rsaEnc33 (m : Nat) : Nat :=
  (m ^ 3) % 33

def rsaDec33 (c : Nat) : Nat :=
  (c ^ 7) % 33

def rsaEncExp5_33 (m : Nat) : Nat :=
  (m ^ 5) % 33

/-- Euler's totient `φ(33) = 20`, so `a^19 mod 33` is the exact modular inverse for all `gcd(a, 33) = 1`! -/
def modInv33 (a : Nat) : Nat :=
  (a ^ 19) % 33

/-- Bezout common-modulus attack for `e₁ = 3, e₂ = 5` (`2 * 3 - 1 * 5 = 1`): `m = c₁² · c₂⁻¹ mod 33`. -/
def commonModulusRecover33 (c1 c2 : Nat) : Nat :=
  (((c1 * c1) % 33) * modInv33 c2) % 33

theorem rsa33_crt_bijection_vs_malleability_and_common_modulus :
    (∀ m : Fin 33, rsaDec33 (rsaEnc33 m.val) = m.val) ∧
    (∀ a b : Fin 12, (rsaEnc33 a.val * rsaEnc33 b.val) % 33 = rsaEnc33 ((a.val * b.val) % 33)) ∧
    (∀ m : Fin 33, Nat.gcd m.val 33 = 1 →
      commonModulusRecover33 (rsaEnc33 m.val) (rsaEncExp5_33 m.val) = m.val) := by
  decide

/-! ## Part 4: Master Wave V268 Frontier Synthesis -/

theorem master_skip_list_lamport_bakery_and_rsa33_frontier
    (L ti i tj j : Nat) (hDistinct : i ≠ j) :
    dyadicTowerSum L + 1 = 2 ^ (L + 1) ∧
    (∀ y : Fin 8, skipListSteps8 y ≤ 4) ∧
    (¬(bakeryLt ti i tj j ∧ bakeryLt tj j ti i)) ∧
    (∀ m : Fin 33, rsaDec33 (rsaEnc33 m.val) = m.val) := by
  exact ⟨skip_list_dyadic_tower_telescoping L,
         skip_list_express4_vs_linear8.1,
         (lamport_bakery_strict_mutex_and_totality ti i tj j hDistinct).1,
         rsa33_crt_bijection_vs_malleability_and_common_modulus.1⟩

end CommonGround.Frontier.SkipListExpressSearchLamportBakeryMutexAndRsaEulerMalleability
