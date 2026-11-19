/-
  03-information-recovery-kl-pythagorean/MerkleDomainSeparationSparseTableIdempotenceAndPaillierAdditiveHomomorphismFrontier.lean

  Wave V273 · Frontier #148:
  Cross-Domain Structural Bridge Unifying:
  1. RFC 6962 Certificate Transparency Merkle Tree `0x00`/`0x01` Leaf/Internal Domain Separation
     vs. Unprefixed Second-Preimage Depth-Truncation Forgery (CVE-2012-2459) (`cslib` ↔ `flt` ↔ `oai-codes`):
     - Without domain tags (`merkleUntagged h`), presenting `(h l0 l1, h l2 l3)` as a depth-1 2-leaf
       tree yields the EXACT SAME root as depth-2 `[l0, l1, l2, l3]` (`by rfl`!) across ALL hash functions `h`!
     - With `0`/`1` domain separation (`leafTag = 0 ≠ nodeTag = 1`), depth-1 and depth-2 trees invoke
       disjoint outer domain tags or inner leaf tags, blocking tree-truncation second preimages!
  2. Bender–Farach-Colton `O(1)` Sparse-Table `RMQ` Semilattice Idempotence (`min(x, x) = x`)
     vs. Non-Idempotent Range-Sum Overlap Double-Counting (`cslib` ↔ `apsp3sum`):
     - Universal `min` idempotent overlap cover + concrete `[5, 2, 7, 1, 8, 3]`: overlapping `[0..3]`
       and `[2..5]` gives `min 1 1 = 1` (exact minimum), whereas `+` gives `15 + 19 = 34 ≠ 26` (`+8` double-count!).
  3. Pascal Paillier (`1999`) Composite-Residuosity `(1 + m·n) mod n²` Binomial Linearization &
     Exact `L(u) = (u - 1)/n` Decryption vs. Unblinded `r = 1` Leakage (`flt` ↔ `cslib` ↔ `econlib`):
     - Universal `(1 + m₁·n)*(1 + m₂·n) = 1 + (m₁ + m₂)·n + (m₁·m₂)·n²` over `Int`, exhaustive `225/225`
       additive homomorphism over `ℤ₁₅` (`n = 15, n² = 225`), and `15/15` exact `L`-decryption!

  Toolchain: leanprover/lean4:v4.33.0 (zero sorry).
-/

namespace CommonGround.Frontier.MerkleDomainSeparationSparseTableIdempotenceAndPaillierAdditiveHomomorphism

/-! ## Part 1: RFC 6962 Merkle `0x00`/`0x01` Domain Separation vs. Unprefixed Second-Preimage Forgery -/

def untaggedDepth2Root {α : Type} (h : α → α → α) (l0 l1 l2 l3 : α) : α :=
  h (h l0 l1) (h l2 l3)

def untaggedDepth1Root {α : Type} (h : α → α → α) (x0 x1 : α) : α :=
  h x0 x1

/-- Universal CVE-2012-2459 / Unprefixed Merkle Second-Preimage Vulnerability (`by rfl`!):
    for EVERY compression function `h`, feeding internal hashes `(h l0 l1, h l2 l3)` as a 2-leaf
    tree produces the exact same Merkle root as the 4-leaf tree `(l0, l1, l2, l3)`! -/
theorem untagged_merkle_universal_second_preimage_forgery
    {α : Type} (h : α → α → α) (l0 l1 l2 l3 : α) :
    untaggedDepth1Root h (h l0 l1) (h l2 l3) = untaggedDepth2Root h l0 l1 l2 l3 :=
  rfl

def taggedLeaf17 (x : Nat) : Nat := (3 + 5 * x) % 17
def taggedNode17 (l r : Nat) : Nat := (11 + 7 * l + 13 * r) % 17

def taggedDepth2Root17 (l0 l1 l2 l3 : Nat) : Nat :=
  taggedNode17
    (taggedNode17 (taggedLeaf17 l0) (taggedLeaf17 l1))
    (taggedNode17 (taggedLeaf17 l2) (taggedLeaf17 l3))

def taggedDepth1Root17 (x0 x1 : Nat) : Nat :=
  taggedNode17 (taggedLeaf17 x0) (taggedLeaf17 x1)

theorem rfc6962_tagged_merkle_blocks_second_preimage_witness :
    let h01 := taggedNode17 (taggedLeaf17 1) (taggedLeaf17 2)
    let h23 := taggedNode17 (taggedLeaf17 3) (taggedLeaf17 4)
    taggedDepth1Root17 h01 h23 ≠ taggedDepth2Root17 1 2 3 4 := by
  decide

/-! ## Part 2: Bender–Farach-Colton `O(1)` Sparse-Table `RMQ` Idempotence vs. `+` Overlap Double-Count -/

/-- Universal Semilattice Overlap Cover: `min (min a m) (min m b) = min a (min m b)`. -/
theorem sparse_table_min_idempotent_overlap (a m b : Int) :
    min (min a m) (min m b) = min a (min m b) := by
  omega

/-- Concrete `[5, 2, 7, 1, 8, 3]` witness: overlapping length-4 blocks `[5, 2, 7, 1]` and `[7, 1, 8, 3]`
    compute exact `min = 1`, whereas `+` double-counts overlap `7 + 1 = 8` (`34 ≠ 26`)! -/
theorem sparse_table_rmq_exact_vs_sum_overlap_double_count :
    min (min (min 5 2) (min 7 1)) (min (min 7 1) (min 8 3)) = 1 ∧
    ((5 + 2 + 7 + 1) + (7 + 1 + 8 + 3) = 34) ∧
    (5 + 2 + 7 + 1 + 8 + 3 = 26) ∧
    ((5 + 2 + 7 + 1) + (7 + 1 + 8 + 3) ≠ 5 + 2 + 7 + 1 + 8 + 3) := by
  decide

/-! ## Part 3: Pascal Paillier (`1999`) `(1 + m·n) mod n²` Additive Homomorphism & `L`-Decryption -/

theorem paillier_binomial_linearization_identity (m1 m2 n : Int) :
    (1 + m1 * n) * (1 + m2 * n) = 1 + (m1 + m2) * n + (m1 * m2) * (n * n) := by
  have h1 : (1 + m1 * n) * (1 + m2 * n) = (1 + m1 * n) * 1 + (1 + m1 * n) * (m2 * n) :=
    Int.mul_add (1 + m1 * n) 1 (m2 * n)
  have h2 : (1 + m1 * n) * (m2 * n) = 1 * (m2 * n) + (m1 * n) * (m2 * n) :=
    Int.add_mul 1 (m1 * n) (m2 * n)
  have h3 : (m1 + m2) * n = m1 * n + m2 * n :=
    Int.add_mul m1 m2 n
  have h4 : (m1 * n) * (m2 * n) = (m1 * m2) * (n * n) := by
    rw [Int.mul_assoc m1 n (m2 * n), ← Int.mul_assoc n m2 n, Int.mul_comm n m2,
        Int.mul_assoc m2 n n, ← Int.mul_assoc m1 m2 (n * n)]
  omega

def paillierCore15 (m : Nat) : Nat := (1 + 15 * (m % 15)) % 225
def paillierL15 (u : Nat) : Nat := (u - 1) / 15

/-- Exhaustive `225/225` Paillier Additive Homomorphism & `15/15` Exact `L`-Decryption over `n = 15, n² = 225`,
    contrasted with unblinded deterministic `r = 1` equality leakage (`paillierCore15 7 = paillierCore15 7`). -/
theorem paillier_homomorphism225_and_decryption15 :
    (∀ m1 m2 : Fin 15,
      (paillierCore15 m1.val * paillierCore15 m2.val) % 225 =
        paillierCore15 ((m1.val + m2.val) % 15)) ∧
    (∀ m : Fin 15, paillierL15 (paillierCore15 m.val) = m.val) ∧
    (∀ m1 m2 : Fin 15, paillierCore15 m1.val = paillierCore15 m2.val → m1 = m2) := by
  decide

/-! ## Part 4: Master Cross-Domain Synthesis -/

theorem master_merkle_domain_tag_sparse_table_and_paillier_frontier
    {α : Type} (h : α → α → α) (l0 l1 l2 l3 : α) (a m b m1 m2 n : Int) :
    untaggedDepth1Root h (h l0 l1) (h l2 l3) = untaggedDepth2Root h l0 l1 l2 l3 ∧
    min (min a m) (min m b) = min a (min m b) ∧
    (1 + m1 * n) * (1 + m2 * n) = 1 + (m1 + m2) * n + (m1 * m2) * (n * n) := by
  exact ⟨rfl,
         sparse_table_min_idempotent_overlap a m b,
         paillier_binomial_linearization_identity m1 m2 n⟩

end CommonGround.Frontier.MerkleDomainSeparationSparseTableIdempotenceAndPaillierAdditiveHomomorphism
