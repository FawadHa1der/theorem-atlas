/-
  10-millennium-frontier-bridges/LamportPaxosSynodQuorumTreapHeapBstUniquenessAndReedMullerLocalDecodingFrontier.lean

  Wave V263 · Frontier Module #138:
  Exact Algebraic, Distributed & Probabilistic Formalization of:
  1. Lamport Single-Decree Paxos Synod Ballot-Quorum Safety Invariant (`Q₁ ∩ Q₂ ≠ ∅` + Phase-2a
     highest-ballot adoption preserves chosen decree `v₁`) & `Fin 5` Majority Pigeonhole (`≥ 3` of `5`)
     vs. Disjoint `2`-of-`4` Split-Quorum (`{0,1} ∩ {2,3} = ∅`) Dual-Decree Fork (`cslib` ↔ `econlib`).
  2. Seidel–Aragon Randomized Treap (`Cartesian Tree`) Unique Min-Priority Root Theorem (`r₁ = r₂`,
     making tree shape 100% insertion-order invariant, depth `≤ 3` on sorted `[0..7]`) vs. Plain
     Unprioritized BST Sorted-Insertion `O(N)` Spine (`depth = 7`) (`cslib` ↔ `tc-probcomb`).
  3. Walsh–Hadamard / First-Order Reed–Muller `RM(1, 3)` `2`-Query XOR Linearity & `7`-Ray Smooth
     Majority Self-Correction (`100%` `512/512` recovery under any single-coordinate corruption) vs.
     Fixed-Offset `r = 1` Targeted Adversary (`7/8 = 87.5%` inverted!) (`oai-codes` ↔ `tc-probcomb`).

  Toolchain: leanprover/lean4:v4.33.0 (pure core Lean 4, zero sorry).
-/

namespace LamportPaxosSynodQuorumTreapHeapBstUniquenessAndReedMullerLocalDecodingFrontier

-- ============================================================================
-- PART I: LAMPORT PAXOS SYNOD QUORUM SAFETY VS. SPLIT-QUORUM FORK
-- ============================================================================

/--
  **Theorem 1a (Universal Paxos Synod Quorum-Witness Inductive Safety Step)**:
  If quorum `Q₁` (where ballot `b₁` was accepted) and Phase-1b quorum `Q₂` (for higher ballot `b₂`)
  share an honest witness `w`, and `maxRep < b₂` is the highest ballot reported across `Q₂`
  (`repBallot a ≤ maxRep` for all `a ∈ Q₂`, with `b₁ ≤ repBallot w`), then under the inductive
  hypothesis `∀ b ∈ [b₁, b₂), proposedVal b = v₁`, Phase-2a MUST propose `proposedVal maxRep = v₁`.
-/
theorem paxos_quorum_witness_safety_universal
    {N : Nat} (Q₁ Q₂ : Fin N → Bool) (w : Fin N)
    (hInter : Q₁ w = true ∧ Q₂ w = true)
    (b₁ b₂ maxRep : Nat) (repBallot : Fin N → Nat) (proposedVal : Nat → Nat) (v₁ : Nat)
    (hWRep : Q₁ w = true → b₁ ≤ repBallot w)
    (hQ2Max : ∀ a : Fin N, Q₂ a = true → repBallot a ≤ maxRep)
    (hLt : maxRep < b₂)
    (hInd : ∀ b : Nat, b₁ ≤ b → b < b₂ → proposedVal b = v₁) :
    proposedVal maxRep = v₁ := by
  have hLo : b₁ ≤ repBallot w := hWRep hInter.1
  have hHi : repBallot w ≤ maxRep := hQ2Max w hInter.2
  exact hInd maxRep (by omega) hLt

/-- Membership of acceptor `a : Fin 5` in 5-bit quorum mask `q : Fin 32`. -/
def inQuorum5 (q : Fin 32) (a : Fin 5) : Bool :=
  ((q.val >>> a.val) &&& 1) == 1

def popcount5 (q : Fin 32) : Nat :=
  (if inQuorum5 q ⟨0, by decide⟩ then 1 else 0) +
  (if inQuorum5 q ⟨1, by decide⟩ then 1 else 0) +
  (if inQuorum5 q ⟨2, by decide⟩ then 1 else 0) +
  (if inQuorum5 q ⟨3, by decide⟩ then 1 else 0) +
  (if inQuorum5 q ⟨4, by decide⟩ then 1 else 0)

def inQuorum4 (q : Fin 16) (a : Fin 4) : Bool :=
  ((q.val >>> a.val) &&& 1) == 1

def popcount4 (q : Fin 16) : Nat :=
  (if inQuorum4 q ⟨0, by decide⟩ then 1 else 0) +
  (if inQuorum4 q ⟨1, by decide⟩ then 1 else 0) +
  (if inQuorum4 q ⟨2, by decide⟩ then 1 else 0) +
  (if inQuorum4 q ⟨3, by decide⟩ then 1 else 0)

/--
  **Theorem 1b (`5`-Node Majority Quorum Intersection vs. `2`-of-`4` Disjoint Split-Brain Fork)**:
  - Across all `32 × 32 = 1,024` subset pairs on `5` acceptors, every pair of strict majorities
    (`≥ 3` of `5`) shares at least one common acceptor `w : Fin 5`.
  - **Premise-Failure Counterexample**: Relaxing to `N / 2` (`2`-of-`4` acceptors) admits `q₁ = 0b0011`
    (`{0,1}`) and `q₂ = 0b1100` (`{2,3}`) with **zero** intersection, allowing conflicting decrees!
-/
theorem paxos_majority5_intersection_vs_even4_disjoint_fork :
    (∀ q₁ q₂ : Fin 32, 3 ≤ popcount5 q₁ → 3 ≤ popcount5 q₂ →
      ∃ w : Fin 5, inQuorum5 q₁ w = true ∧ inQuorum5 q₂ w = true) ∧
    popcount4 ⟨3, by decide⟩ = 2 ∧
    popcount4 ⟨12, by decide⟩ = 2 ∧
    (∀ w : Fin 4, ¬(inQuorum4 ⟨3, by decide⟩ w = true ∧ inQuorum4 ⟨12, by decide⟩ w = true)) := by
  decide

-- ============================================================================
-- PART II: SEIDEL–ARAGON TREAP ROOT UNIQUENESS VS. SORTED BST O(N) SPINE
-- ============================================================================

/--
  **Theorem 2a (Universal Treap / Cartesian Tree Min-Priority Root Uniqueness)**:
  In any non-empty key domain `Fin n` with priority map `prio`, at most one element can satisfy
  strict min-heap dominance `∀ x ≠ r, prio r < prio x` — uniquely fixing the Treap root (and recursively
  every left `< r` and right `> r` subtree) independently of key arrival order!
-/
theorem treap_unique_min_priority_root_universal
    {n : Nat} (prio : Fin n → Nat) (r₁ r₂ : Fin n)
    (hMin₁ : ∀ x : Fin n, x ≠ r₁ → prio r₁ < prio x)
    (hMin₂ : ∀ x : Fin n, x ≠ r₂ → prio r₂ < prio x) :
    r₁ = r₂ := by
  by_cases hEq : r₁ = r₂
  · exact hEq
  · have h12 : prio r₁ < prio r₂ := hMin₁ r₂ (Ne.symm hEq)
    have h21 : prio r₂ < prio r₁ := hMin₂ r₁ hEq
    omega

/-- Tree pointer depth over `Fin 8` (root `p x == x` has depth `0`). -/
def treeDepth8 : Nat → (Fin 8 → Fin 8) → Fin 8 → Nat
  | 0, _, _ => 0
  | fuel + 1, parent, x =>
    if parent x == x then 0 else 1 + treeDepth8 fuel parent (parent x)

/-- Plain BST parent map when sorted keys `[0, 1, 2, 3, 4, 5, 6, 7]` arrive in ascending order
    (root `0`, `x + 1`'s parent is `x` ↦ linear right spine of depth `7`!). -/
def sortedBstSpineParent8 (x : Fin 8) : Fin 8 :=
  if h : 0 < x.val then ⟨x.val - 1, by omega⟩ else x

/-- Canonical Treap parent map on keys `[0..7]` with distinct priorities `[50, 20, 60, 10, 70, 30, 80, 40]`:
    unique root `3` (`prio 10`), left child `1` (`prio 20`, children `0, 2`), right child `5` (`prio 30`,
    left `4`, right `7` (`prio 40`, left `6`)) — max depth `3` regardless of arrival order! -/
def treapCartesianParent8 : Fin 8 → Fin 8
  | ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩ => ⟨3, by decide⟩
  | ⟨2, _⟩ => ⟨1, by decide⟩
  | ⟨3, _⟩ => ⟨3, by decide⟩
  | ⟨4, _⟩ => ⟨5, by decide⟩
  | ⟨5, _⟩ => ⟨3, by decide⟩
  | ⟨6, _⟩ => ⟨7, by decide⟩
  | ⟨7, _⟩ => ⟨5, by decide⟩

def treapPrio8 : Fin 8 → Nat
  | ⟨0, _⟩ => 50
  | ⟨1, _⟩ => 20
  | ⟨2, _⟩ => 60
  | ⟨3, _⟩ => 10
  | ⟨4, _⟩ => 70
  | ⟨5, _⟩ => 30
  | ⟨6, _⟩ => 80
  | ⟨7, _⟩ => 40

/--
  **Theorem 2b (Treap Heap-Invariance & Depth `≤ 3` on Sorted Keys vs. Plain BST Spine `7`)**:
  Verifies every non-root node `x ≠ 3` has strictly larger priority than its Treap parent, every node
  in `Fin 8` has Treap depth `≤ 3`, while plain sorted-insertion BST reaches depth `7` at key `7`!
-/
theorem treap_balanced_depth3_vs_sorted_bst_spine7 :
    (∀ x : Fin 8, x ≠ ⟨3, by decide⟩ → treapPrio8 (treapCartesianParent8 x) < treapPrio8 x) ∧
    (∀ x : Fin 8, treeDepth8 8 treapCartesianParent8 x ≤ 3) ∧
    treeDepth8 8 sortedBstSpineParent8 ⟨7, by decide⟩ = 7 := by
  decide

-- ============================================================================
-- PART III: HADAMARD RM(1,3) SMOOTH 2-QUERY SELF-CORRECTION VS. FIXED OFFSET
-- ============================================================================

def parity3 (v : Nat) : Bool :=
  (((v &&& 1) + ((v >>> 1) &&& 1) + ((v >>> 2) &&& 1)) % 2) == 1

/-- Walsh–Hadamard / `RM(1, 3)` linear evaluation `⟨a, x⟩ mod 2` over `𝔽₂³` (`Fin 8`). -/
def hadamard3 (a x : Fin 8) : Bool :=
  parity3 (a.val &&& x.val)

/-- Adversarially corrupted oracle flipping codeword `a` at coordinate `e : Fin 8`. -/
def corruptHadamard3 (a e y : Fin 8) : Bool :=
  if y == e then !(hadamard3 a y) else hadamard3 a y

/-- Local `2`-query XOR probe `oracle(x ⊕ r) ⊕ oracle(r)`. -/
def localXorProbe3 (oracle : Fin 8 → Bool) (x r : Fin 8) : Bool :=
  Bool.xor (oracle ⟨(x.val ^^^ r.val) % 8, Nat.mod_lt _ (by decide)⟩) (oracle r)

/-- Smooth `7`-ray majority self-corrector polling all non-zero shifts `r ∈ {1..7}` (`≥ 4` of `7`). -/
def smoothMajDecode3 (oracle : Fin 8 → Bool) (x : Fin 8) : Bool :=
  let votes :=
    (if localXorProbe3 oracle x ⟨1, by decide⟩ then 1 else 0) +
    (if localXorProbe3 oracle x ⟨2, by decide⟩ then 1 else 0) +
    (if localXorProbe3 oracle x ⟨3, by decide⟩ then 1 else 0) +
    (if localXorProbe3 oracle x ⟨4, by decide⟩ then 1 else 0) +
    (if localXorProbe3 oracle x ⟨5, by decide⟩ then 1 else 0) +
    (if localXorProbe3 oracle x ⟨6, by decide⟩ then 1 else 0) +
    (if localXorProbe3 oracle x ⟨7, by decide⟩ then 1 else 0)
  decide (4 ≤ votes)

/--
  **Theorem 3 (Hadamard `RM(1,3)` `100%` Smooth `2`-Query Self-Correction vs. Fixed-Offset `87.5%` Flip)**:
  1. Uncorrupted `2`-query linearity holds across all `512` `(a, x, r)` triples.
  2. Smooth `7`-ray majority recovers `hadamard3 a x` across **all `512` `(a, e, x)` single-error triples**
     (`100%` recovery — even when target `x = e` itself is corrupted!).
  3. **Premise-Failure Counterexample**: Fixing deterministic offset `r = 1` under single-bit error `e = 1`
     inverts the decoded bit on **every non-zero coordinate `x ≠ 0`** (`7/8 = 87.5%` corruption)!
-/
theorem hadamard_rm13_smooth_local_decoding_vs_fixed_offset :
    (∀ a x r : Fin 8, localXorProbe3 (hadamard3 a) x r = hadamard3 a x) ∧
    (∀ a e x : Fin 8, smoothMajDecode3 (corruptHadamard3 a e) x = hadamard3 a x) ∧
    (∀ a x : Fin 8, x.val ≠ 0 →
      localXorProbe3 (corruptHadamard3 a ⟨1, by decide⟩) x ⟨1, by decide⟩ = !(hadamard3 a x)) := by
  decide

end LamportPaxosSynodQuorumTreapHeapBstUniquenessAndReedMullerLocalDecodingFrontier
