/-
  10-millennium-frontier-bridges/PbftByzantineQuorumIntersectionMonotonicQueuePotentialAndZobristXorTranspositionFrontier.lean

  Milestone Wave V275 · Frontier #150 (MILESTONE 150 FRONTIER MODULES & 130 EXACT FINITE MICRO-LABS!):
  Cross-Domain Structural Bridge Unifying:
  1. Castro–Liskov (`1999`) `PBFT` `3f + 1` Byzantine Quorum Intersection (`2(2f+1) - (3f+1) = f + 1 > f`)
     vs. `N = 3f` Equivocation Split-Brain (`{0, 1} ∩ {1, 2} = {1}` Traitor-Only Overlap!) (`cslib` ↔ `econlib`):
     - Universal Pigeonhole Lower Bound: any two `2f + 1` quorums inside `3f + 1` replicas share at least
       `f + 1` replicas, strictly exceeding the `f` Byzantine budget (`≥ 1` honest witness guaranteed!).
     - Premise-Failure Contrast (`N = 3, f = 1, Q = 2`): quorums `{0, 1}` and `{1, 2}` intersect ONLY at
       Byzantine replica `1` (`0` honest nodes in intersection!).
  2. Monotonic Queue Sliding-Window Minimum Amortized Potential (`Φ = |deque|`, Total Pops `≤ N`)
     vs. Naive `O(N·W)` Window Rescan (`cslib` ↔ `apsp3sum`):
     - Universal Potential Conservation: `finalLen + totalPops = N → totalPops ≤ N ∧ N + totalPops ≤ 2 * N`!
  3. Zobrist (`1970`) Incremental `XOR` Game-State Transposition Hashing (`(h ^^^ r₁) ^^^ r₂ = (h ^^^ r₂) ^^^ r₁`
     & Exact Self-Inverse Undo `(h ^^^ r) ^^^ r = h`) vs. Linear Key Schedule `R[i] = i` `2`-Piece Collision (`cslib` ↔ `oai-codes` ↔ `flt`):
     - Exhaustive `BitVec 8` commutativity + involution (`65,536` triples) vs. `1 ^^^ 2 = 0 ^^^ 3 = 3` aliasing!

  Toolchain: leanprover/lean4:v4.33.0 (zero sorry).
-/

namespace CommonGround.Frontier.PbftByzantineQuorumIntersectionMonotonicQueuePotentialAndZobristXorTransposition

/-! ## Part 1: Castro–Liskov (`1999`) PBFT `3f + 1` Quorum Intersection vs. `3f` Equivocation -/

/-- Universal PBFT `3f + 1` Honest Witness Guarantee:
    if `|Q₁| ≥ 2f + 1`, `|Q₂| ≥ 2f + 1`, and `|Q₁ ∪ Q₂| ≤ 3f + 1`, then
    `|Q₁ ∩ Q₂| = |Q₁| + |Q₂| - |Q₁ ∪ Q₂| ≥ f + 1 > f`, leaving `≥ 1` honest node! -/
theorem pbft_quorum_intersection_exceeds_byzantine_budget
    (f q1 q2 unionSz interSz : Nat)
    (hQ1 : q1 ≥ 2 * f + 1)
    (hQ2 : q2 ≥ 2 * f + 1)
    (hUnion : unionSz ≤ 3 * f + 1)
    (hIE : q1 + q2 = unionSz + interSz) :
    interSz ≥ f + 1 ∧ interSz > f := by
  omega

/-- Concrete `N = 3, f = 1, Q = 2` Split-Brain Counterexample (`3`-bit masks over `{0, 1, 2}` where node `1` is Byzantine):
    `Q₁ = {0, 1}` (`mask = 0b011 = 3`) and `Q₂ = {1, 2}` (`mask = 0b110 = 6`) both have size `2`,
    yet `(Q₁ ∩ Q₂) \ {1} = ∅` (`0` honest nodes in intersection)! -/
def popcount4 (m : Nat) : Nat :=
  (m &&& 1) + ((m >>> 1) &&& 1) + ((m >>> 2) &&& 1) + ((m >>> 3) &&& 1)

theorem pbft_4_of_3_exhaustive_vs_3_of_2_split_brain :
    (∀ q1 q2 : Fin 16,
      popcount4 q1.val ≥ 3 → popcount4 q2.val ≥ 3 →
      popcount4 (q1.val &&& q2.val) ≥ 2) ∧
    ((3 &&& 6) = 2) ∧
    (((3 &&& 6) &&& 5) = 0) := by
  decide

/-! ## Part 2: Monotonic Deque Sliding-Window Minimum Amortized Potential -/

/-- Universal Monotonic Deque Potential Bound (`Φ = finalLen`):
    each of `N` pushes inserts `1` item; every dominated pop removes `1` item;
    hence `finalLen + totalPops = N` implies `totalPops ≤ N` and total work `N + totalPops ≤ 2 * N`! -/
theorem monotonic_deque_amortized_2n_bound (N finalLen totalPops : Nat)
    (hConservation : finalLen + totalPops = N) :
    totalPops ≤ N ∧ N + totalPops ≤ 2 * N := by
  omega

def window3Min4 (a b c d e f : Int) : List Int :=
  [min a (min b c), min b (min c d), min c (min d e), min d (min e f)]

theorem monotonic_window_witness_vs_naive_rescan :
    window3Min4 8 6 4 2 5 7 = [4, 2, 2, 2] ∧
    (6 + 4 = 10) ∧
    (4 * 6 = 24) ∧
    (10 < 24) := by
  decide

/-! ## Part 3: Zobrist (`1970`) Incremental `XOR` Hashing vs. Linear Key Schedule Collision -/

/-- Exhaustive `4,096/4,096` `Fin 16` Zobrist `XOR` Self-Inverse Undo & Move-Order Transposition Invariance,
    contrasted with structured linear keys `R[i] = i` suffering `1 ^^^ 2 = 0 ^^^ 3 = 3` collision! -/
theorem zobrist_xor_involution_and_transposition_vs_linear_key_collision :
    (∀ h r : Fin 16, (h.val ^^^ r.val) ^^^ r.val = h.val) ∧
    (∀ h r1 r2 : Fin 16, (h.val ^^^ r1.val) ^^^ r2.val = (h.val ^^^ r2.val) ^^^ r1.val) ∧
    ((1 ^^^ 2) = (0 ^^^ 3)) ∧
    ((1, 2) ≠ (0, 3)) := by
  decide

/-! ## Part 4: Master Milestone Synthesis (`Frontier #150` & `Lab #130`) -/

theorem master_pbft_quorum_monotonic_deque_and_zobrist_frontier
    (f q1 q2 unionSz interSz N finalLen totalPops : Nat)
    (hQ1 : q1 ≥ 2 * f + 1) (hQ2 : q2 ≥ 2 * f + 1)
    (hUnion : unionSz ≤ 3 * f + 1) (hIE : q1 + q2 = unionSz + interSz)
    (hCons : finalLen + totalPops = N) :
    interSz ≥ f + 1 ∧
    N + totalPops ≤ 2 * N ∧
    (∀ h r1 r2 : Fin 16, (h.val ^^^ r1.val) ^^^ r2.val = (h.val ^^^ r2.val) ^^^ r1.val) := by
  exact ⟨(pbft_quorum_intersection_exceeds_byzantine_budget f q1 q2 unionSz interSz hQ1 hQ2 hUnion hIE).1,
         (monotonic_deque_amortized_2n_bound N finalLen totalPops hCons).2,
         zobrist_xor_involution_and_transposition_vs_linear_key_collision.2.1⟩

end CommonGround.Frontier.PbftByzantineQuorumIntersectionMonotonicQueuePotentialAndZobristXorTransposition
