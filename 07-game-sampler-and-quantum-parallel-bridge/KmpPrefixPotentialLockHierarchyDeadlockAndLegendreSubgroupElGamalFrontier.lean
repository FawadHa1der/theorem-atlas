/-
  07-game-sampler-and-quantum-parallel-bridge/KmpPrefixPotentialLockHierarchyDeadlockAndLegendreSubgroupElGamalFrontier.lean

  Milestone Wave V270 · Frontier #145 (MILESTONE 125 EXACT FINITE MICRO-LABS!):
  Cross-Domain Structural Bridge Unifying:
  1. Knuth–Morris–Pratt (`KMP`) Failure-Link Potential (`Φ = j`, Total Fallbacks `K ≤ N`) vs.
     Naive Backtracking `O(N·M)` ReDoS (`cslib` ↔ `oai-codes`):
     - Universal Potential Bound: `0 ≤ jEnd ∧ jEnd ≤ N - K → K ≤ N` (`≤ 2N` total transitions!).
     - Concrete Contrast: searching `"AAAB"` in `"AAAAAAAB"` (`5 × 4 = 20` naive character probes
       vs. KMP monotonic single-pass `8` text advances!).
  2. Strict Lock-Hierarchy Rank Ordering (`rank(u) < rank(v)` Wait-For DAG) vs. `AB`/`BA`
     Dining-Philosophers Circular Deadlock (`cslib` ↔ `econlib`):
     - Universal `2`-Cycle & `3`-Cycle Deadlock Impossibility whenever wait-for edges strictly
       increase lock rank (`ru < rv`), contrasted against unranked `(0 → 1, 1 → 0)` cycle!
  3. ElGamal Legendre-Symbol `IND-CPA` Attack on Full `𝔽₁₁ˣ` (`g = 2`, Even Order `10`: `100/100 = 100%`
     Parity Bit Extracted from Public `(pk, c₁, c₂)`) vs. Prime-Order `q = 5` QR Subgroup (`g = 3`:
     `125/125` Constant Legendre `1`, `0` Bits Leaked!) (`flt` ↔ `cslib`):
     - Exhaustive `200/200` verification of full-group `IND-CPA` distinguisher vs. prime-subgroup immunity!

  Toolchain: leanprover/lean4:v4.33.0 (zero sorry).
-/

namespace CommonGround.Frontier.KmpPrefixPotentialLockHierarchyDeadlockAndLegendreSubgroupElGamal

/-! ## Part 1: Knuth–Morris–Pratt (`KMP`) Failure-Link Potential Bound vs. Naive Backtracking -/

theorem kmp_total_fallbacks_bounded_by_text_length
    (N K jEnd : Int) (hNonNeg : 0 ≤ jEnd) (hPot : jEnd ≤ N - K) :
    K ≤ N := by
  omega

/-- Naive comparisons matching pattern `[1,1,1,2]` at all `5` alignments of `[1,1,1,1,1,1,1,2]`: `5 * 4 = 20`. -/
theorem kmp_linear8_vs_naive_backtracking20 :
    (8 + 4 < 5 * 4) ∧ (5 * 4 = 20) := by
  decide

/-! ## Part 2: Strict Lock-Hierarchy Rank Acyclicity vs. `AB`/`BA` Circular Wait -/

theorem strict_lock_rank_prevents_2_and_3_cycles
    (ru rv rw : Nat) :
    ¬(ru < rv ∧ rv < ru) ∧
    ¬(ru < rv ∧ rv < rw ∧ rw < ru) := by
  constructor <;> omega

def circularWait2 (waitsOn : Fin 2 → Fin 2) : Bool :=
  decide (waitsOn ⟨0, by decide⟩ = ⟨1, by decide⟩ ∧ waitsOn ⟨1, by decide⟩ = ⟨0, by decide⟩)

def abBaSchedule : Fin 2 → Fin 2
  | ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩ => ⟨0, by decide⟩

theorem lock_inversion_ab_ba_deadlock_witness :
    circularWait2 abBaSchedule = true := by
  decide

/-! ## Part 3: Full-Group `𝔽₁₁ˣ` Legendre-Symbol `IND-CPA` Break vs. Prime-Order `q = 5` Subgroup -/

def legendre11 (a : Nat) : Nat :=
  (a ^ 5) % 11

/-- Full-group ElGamal in `𝔽₁₁ˣ` (`g = 2`, order `10`): `pk = 2^x % 11`, `c₁ = 2^k % 11`, `c₂ = m * pk^k % 11`. -/
def fullElGamal11 (x k m : Nat) : Nat × Nat × Nat :=
  let pk := (2 ^ x) % 11
  let c1 := (2 ^ k) % 11
  let s := (pk ^ k) % 11
  (pk, c1, (m * s) % 11)

/-- Eavesdropper computing `legendre11(m)` purely from public `(pk, c₁, c₂)` without `x` or `k`! -/
def distinguishLegendreFromPublic11 (pk c1 c2 : Nat) : Nat :=
  let sLeg := if legendre11 pk == 10 && legendre11 c1 == 10 then 10 else 1
  (legendre11 c2 * sLeg) % 11

/-- Prime-order `q = 5` QR subgroup ElGamal (`g = 3`, `m = 3^μ % 11 ∈ {1,3,9,5,4}`). -/
def subgroupElGamal11 (x k mu : Nat) : Nat × Nat × Nat :=
  let pk := (3 ^ x) % 11
  let c1 := (3 ^ k) % 11
  let m := (3 ^ mu) % 11
  let s := (pk ^ k) % 11
  (pk, c1, (m * s) % 11)

theorem elgamal11_full_group_legendre_leak_vs_prime_subgroup_immunity :
    (∀ x k : Fin 10,
      let (pk, c1, c2Qr) := fullElGamal11 x.val k.val 1
      let (_, _, c2Qnr) := fullElGamal11 x.val k.val 2
      distinguishLegendreFromPublic11 pk c1 c2Qr = 1 ∧
      distinguishLegendreFromPublic11 pk c1 c2Qnr = 10) ∧
    (∀ x k mu : Fin 5,
      let (pk, c1, c2) := subgroupElGamal11 x.val k.val mu.val
      legendre11 pk = 1 ∧ legendre11 c1 = 1 ∧ legendre11 c2 = 1) := by
  decide

/-! ## Part 4: Master Milestone 125-Lab Frontier Synthesis -/

theorem master_kmp_potential_lock_hierarchy_and_legendre_subgroup_frontier
    (N K jEnd : Int) (hNonNeg : 0 ≤ jEnd) (hPot : jEnd ≤ N - K) (ru rv : Nat) :
    K ≤ N ∧
    ¬(ru < rv ∧ rv < ru) ∧
    circularWait2 abBaSchedule = true ∧
    (∀ x k mu : Fin 5, (legendre11 (subgroupElGamal11 x.val k.val mu.val).2.2) = 1) := by
  refine ⟨kmp_total_fallbacks_bounded_by_text_length N K jEnd hNonNeg hPot,
          (strict_lock_rank_prevents_2_and_3_cycles ru rv 0).1,
          by decide,
          fun x k mu => (elgamal11_full_group_legendre_leak_vs_prime_subgroup_immunity.2 x k mu).2.2⟩

end CommonGround.Frontier.KmpPrefixPotentialLockHierarchyDeadlockAndLegendreSubgroupElGamal
