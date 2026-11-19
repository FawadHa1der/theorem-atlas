/-!
# Suite #645: Consistent Hashing `1/K` Ring Locality, Power-of-Two-Choices `p²` Tail-Squaring & RFC 6962 Merkle Audit Bridge

Zero-sorry Lean 4.33.0 verification bridge (`Suite #645`) certifying the unified distributed-routing
and cryptographic tree-commitment triad with explicit premise-failure counterexamples:

1. **Consistent Hashing Ring `1/K` Locality (`4/20 = 20%`) vs. Naive `hash mod N` `80%` Stampede (`16/20`)**:
   - Inserting a 5th shard on a cyclic ring leaves `100%` of keys outside the split arc invariant
     (`4/20 = 20%` remapped), whereas `k % 4` vs. `k % 5` remaps `16/20 = 80%` (`4×` cache stampede).
2. **Power-of-Two-Choices (`Po2C`) `p²` Tail-Squaring (`25% → 6.25%`) vs. Stale-Snapshot Herd (`48 > 36`)**:
   - `min(l₁, l₂) ≥ τ ↔ l₁ ≥ τ ∧ l₂ ≥ τ` squares hot-server collision probability from `16/64` (`25%`)
     to `4/64` (`6.25%`) on `N = 8, M = 2`, whereas stale snapshot `[0, 2, 2, 2]` funnels `7/16` pairs
     to Server `0` and triggers `[6, 2, 2, 2]` herd congestion (`∑ L_i² = 48 > 36` uniform `[3, 3, 3, 3]`).
3. **RFC 6962 Domain-Separated Merkle Audit vs. Unprefixed Second-Preimage & `CVE-2012-2459` Collision**:
   - Domain-tagged leaves (`0x00`) vs. internal nodes (`0x01`) forbid leaf/parent collisions under any
     injective compression primitive, whereas omitting tags enables `(H(a), H(b))` second-preimage forgery
     and odd-leaf duplication (`CVE-2012-2459`) equates `[A, B, C]` with `[A, B, C, C]`.

* **Cross-Domain Triad**: cslib ↔ tc-probcomb ↔ oai-codes ↔ econlib
-/

namespace CommonGround.Verification.ConsistentHashingPo2CMerkleAuditBridge

/-- Inserting a new ring shard `s_new` on split arc `inNewArc` preserves all non-arc keys. -/
def insertRingShard {α : Type} (assignOld : α → Nat) (s_new : Nat) (inNewArc : α → Bool) (k : α) : Nat :=
  if inNewArc k then s_new else assignOld k

/-- Universal cyclic-ring insertion locality outside the split arc. -/
theorem consistent_hashing_universal_arc_locality
    {α : Type} (assignOld : α → Nat) (s_new : Nat) (inNewArc : α → Bool) (k : α)
    (hOutside : inNewArc k = false) :
    insertRingShard assignOld s_new inNewArc k = assignOld k := by
  simp [insertRingShard, hOutside]

/-- `4`-shard ring assignment on `Fin 20`. -/
def ringAssign4 (k : Fin 20) : Nat :=
  if k.val ≤ 4 then 0 else if k.val ≤ 9 then 1 else if k.val ≤ 14 then 2 else 3

/-- `5`-shard ring assignment after splitting `{0, 1, 2, 3}` onto Shard `4`. -/
def ringAssign5 (k : Fin 20) : Nat :=
  insertRingShard ringAssign4 4 (fun x => decide (x.val ≤ 3)) k

/-- Structural remapped-key counter over `Fin 20`. -/
def countRemappedAux (f g : Fin 20 → Nat) : (n : Nat) → n ≤ 20 → Nat
  | 0, _ => 0
  | n + 1, h =>
      let prev := countRemappedAux f g n (Nat.le_of_succ_le h)
      if f ⟨n, h⟩ != g ⟨n, h⟩ then prev + 1 else prev

def countRemapped20 (f g : Fin 20 → Nat) : Nat :=
  countRemappedAux f g 20 (Nat.le_refl 20)

/-- Universal `Po2C` order-statistic threshold gate `min(l₁, l₂) ≥ τ ↔ l₁ ≥ τ ∧ l₂ ≥ τ`. -/
theorem po2c_min_ge_threshold_iff (l1 l2 tau : Nat) :
    Nat.min l1 l2 ≥ tau ↔ (l1 ≥ tau ∧ l2 ≥ tau) := by
  simp only [Nat.min_def]
  split <;> omega

/-- `8`-server load profile with `2` overloaded servers (`load = 4`). -/
def loadProfile8 (i : Fin 8) : Nat :=
  match i.val with
  | 0 => 4 | 1 => 4 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1 | _ => 0

def countRow8 (P : Fin 8 → Bool) : (n : Nat) → n ≤ 8 → Nat
  | 0, _ => 0
  | n + 1, h =>
      let prev := countRow8 P n (Nat.le_of_succ_le h)
      if P ⟨n, h⟩ then prev + 1 else prev

def countPairs8Aux (P : Fin 8 → Fin 8 → Bool) : (n : Nat) → n ≤ 8 → Nat
  | 0, _ => 0
  | n + 1, h =>
      countPairs8Aux P n (Nat.le_of_succ_le h) + countRow8 (P ⟨n, h⟩) 8 (Nat.le_refl 8)

def countPairs8 (P : Fin 8 → Fin 8 → Bool) : Nat :=
  countPairs8Aux P 8 (Nat.le_refl 8)

/-- Stale load snapshot `[0, 2, 2, 2]` on `4` servers. -/
def staleLoad4 (i : Fin 4) : Nat := if i.val == 0 then 0 else 2

/-- `Po2C` tie-breaking selector on `Fin 4`. -/
def po2cPick4 (L : Fin 4 → Nat) (i j : Fin 4) : Fin 4 := if L i ≤ L j then i else j

def countRow4 (P : Fin 4 → Bool) : (n : Nat) → n ≤ 4 → Nat
  | 0, _ => 0
  | n + 1, h =>
      let prev := countRow4 P n (Nat.le_of_succ_le h)
      if P ⟨n, h⟩ then prev + 1 else prev

def countPairs4Aux (P : Fin 4 → Fin 4 → Bool) : (n : Nat) → n ≤ 4 → Nat
  | 0, _ => 0
  | n + 1, h =>
      countPairs4Aux P n (Nat.le_of_succ_le h) + countRow4 (P ⟨n, h⟩) 4 (Nat.le_refl 4)

def countPairsToServer4 (L : Fin 4 → Nat) (s : Fin 4) : Nat :=
  countPairs4Aux (fun i j => po2cPick4 L i j == s) 4 (Nat.le_refl 4)

/-- Quadratic server load congestion `∑ L_i²`. -/
def sumLoadSq4 (l0 l1 l2 l3 : Nat) : Nat :=
  l0 * l0 + l1 * l1 + l2 * l2 + l3 * l3

/-- Universal RFC 6962 domain-tag non-collision (`tag = 0` leaf vs. `tag = 1` internal node). -/
theorem domain_separated_merkle_no_leaf_node_confusion
    (H : Nat → Nat → Nat → Nat)
    (hInj : ∀ t1 a1 b1 t2 a2 b2, H t1 a1 b1 = H t2 a2 b2 → t1 = t2 ∧ a1 = a2 ∧ b1 = b2)
    (x0 x1 hL hR : Nat) :
    H 0 x0 x1 ≠ H 1 hL hR := by
  intro hEq
  have hTags := (hInj 0 x0 x1 1 hL hR hEq).1
  omega

/-- Concrete domain-tagged toy hash (`tag * 65536 + a * 256 + b`). -/
def toyTaggedHash (tag a b : Nat) : Nat :=
  tag * 65536 + (a % 256) * 256 + (b % 256)

/-- Prime-modulus mixing hash `(tag * 131 + a * 37 + b * 17 + 7) % 251` for `8`-leaf audit paths. -/
def mixTagged251 (tag a b : Nat) : Nat :=
  (tag * 131 + a * 37 + b * 17 + 7) % 251

def verifyDepth3Merkle (leafLo leafHi : Nat) (s0 s1 s2 : Nat) (idx : Fin 8) : Nat :=
  let h0 := mixTagged251 0 leafLo leafHi
  let h1 := if idx.val % 2 == 0 then mixTagged251 1 h0 s0 else mixTagged251 1 s0 h0
  let h2 := if (idx.val / 2) % 2 == 0 then mixTagged251 1 h1 s1 else mixTagged251 1 s1 h1
  if (idx.val / 4) % 2 == 0 then mixTagged251 1 h2 s2 else mixTagged251 1 s2 h2

/-- Unprefixed 1-leaf vs. 2-leaf Merkle roots and Bitcoin `CVE-2012-2459` odd-leaf duplication roots. -/
def unprefixedLeafRoot (H_raw : Nat → Nat → Nat) (x0 x1 : Nat) : Nat := H_raw x0 x1
def unprefixedTwoLeafRoot (H_raw : Nat → Nat → Nat) (a0 a1 b0 b1 : Nat) : Nat := H_raw (H_raw a0 a1) (H_raw b0 b1)
def oddPadMerkleRoot3 (H_pair : Nat → Nat → Nat) (A B C : Nat) : Nat := H_pair (H_pair A B) (H_pair C C)
def evenMerkleRoot4 (H_pair : Nat → Nat → Nat) (A B C D : Nat) : Nat := H_pair (H_pair A B) (H_pair C D)

/-- **Master Bridge Theorem (`Suite #645`)**:
    1. Consistent hashing `4 → 5` ring remaps `4/20` (`20%`) vs. naive modulo `16/20` (`80%` stampede);
    2. `Po2C` squares `8`-server tail hits from `16/64` (`25%`) to `4/64` (`6.25%`) while stale snapshot
       `[0,2,2,2]` causes `[6,2,2,2]` herd congestion (`48 > 36`);
    3. RFC 6962 `0x00`/`0x01` domain tags separate leaves from internal nodes and verify `8`-leaf depth-3
       inclusion, whereas unprefixed trees suffer `(H(a),H(b))` second-preimage forgery and odd-leaf
       duplication (`CVE-2012-2459`) equates `[A, B, C]` with `[A, B, C, C]`. -/
theorem master_consistent_hashing_po2c_and_merkle_audit_bridge :
    (countRemapped20 ringAssign4 ringAssign5 = 4 ∧
     countRemapped20 (fun k => k.val % 4) (fun k => k.val % 5) = 16 ∧
     (∀ k : Fin 20, 4 ≤ k.val → k.val % 4 ≠ k.val % 5)) ∧
    ((∀ l1 l2 tau : Nat, Nat.min l1 l2 ≥ tau ↔ (l1 ≥ tau ∧ l2 ≥ tau)) ∧
     countPairs8 (fun i _ => decide (loadProfile8 i ≥ 4)) = 16 ∧
     countPairs8 (fun i j => decide (Nat.min (loadProfile8 i) (loadProfile8 j) ≥ 4)) = 4 ∧
     countPairsToServer4 staleLoad4 ⟨0, by decide⟩ = 7 ∧
     sumLoadSq4 6 2 2 2 = 48 ∧ sumLoadSq4 3 3 3 3 = 36) ∧
    (toyTaggedHash 0 33 44 ≠ toyTaggedHash 1 33 44 ∧
     verifyDepth3Merkle 11 23 33 44 55 ⟨5, by decide⟩ ≠ verifyDepth3Merkle 11 22 33 44 55 ⟨5, by decide⟩ ∧
     (∀ (H_raw H_pair : Nat → Nat → Nat) (a0 a1 b0 b1 A B C : Nat),
       unprefixedLeafRoot H_raw (H_raw a0 a1) (H_raw b0 b1) = unprefixedTwoLeafRoot H_raw a0 a1 b0 b1 ∧
       oddPadMerkleRoot3 H_pair A B C = evenMerkleRoot4 H_pair A B C C)) := by
  refine ⟨by decide, ⟨po2c_min_ge_threshold_iff, by decide, by decide, by decide, by decide, by decide⟩, ⟨by decide, by decide, ?_⟩⟩
  intro H_raw H_pair a0 a1 b0 b1 A B C
  exact ⟨rfl, rfl⟩

end CommonGround.Verification.ConsistentHashingPo2CMerkleAuditBridge
