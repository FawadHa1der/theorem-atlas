/-
Copyright (c) 2026 Common Ground Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Frontier #123: Conflict-Serializability (`DSG` Acyclicity) & `SI` Write-Skew vs. `SSI`, Lamport vs. Fidge–Mattern Vector Clocks (`a → b ⟺ V(a) < V(b)`), and Amdahl Ceiling vs. Gunther `USL` Retrograde Scalability Collapse

This pure Lean 4.33.0 module (zero external dependencies, zero `sorry`) formalizes
three foundational theorems across database transaction isolation, distributed
causality, and parallel/cluster scalability—each paired with an explicit
premise-failure counterexample exposing a classic production failure mode:

1. **Conflict-Serializability (`DSG` Acyclicity ⟺ Serial Equivalence) & Snapshot Isolation (`SI`) Write-Skew vs. `SSI`**:
   - **Positive Witnesses**:
     * Exhaustive verification across all `2⁶ = 64` irreflexive `3`-transaction Direct
       Serialization Graphs (`DSG`) (`dsg_acyclicity_iff_topological_serial_order_universal`):
       `hasCycle3 g = false ↔ existsTopoOrder3 g = true`.
     * Exhaustive schedule verification across all `6³ = 216` `3`-operation multi-key
       schedules (`conflict_serializability_schedule_equivalence_216`): a schedule's
       induced conflict graph is acyclic iff at least one of the `3! = 6` serial
       transaction permutations preserves the order of every `WR`/`RW`/`WW` conflict.
     * Snapshot Isolation's First-Committer-Wins (`W₁ ∩ W₂ = ∅`) blocks classic `WW`
       Lost Updates (`siAllowsCommit 0b01 0b01 = false`).
   - **Premise-Failure Counterexample (Write Skew `RW`-Cycle Escaping `SI`, Caught by `SSI`)**:
     * Under invariant `x + y ≥ 100` starting from `(100, 100)`, `T₁` reads `{x, y}` and
       sets `x := 0` (`W₁ = {x}`), while `T₂` concurrently reads `{x, y}` and sets
       `y := 0` (`W₂ = {y}`). Because `W₁ ∩ W₂ = ∅`, **Snapshot Isolation lets both
       commit**, yielding `(0, 0)` with `0 + 0 = 0 < 100`!
     * **Serializable Snapshot Isolation (`SSI`, Cahill–Röhm–Fekete)** detects the
       bidirectional `rw`-antidependency `2`-cycle (`T₁ -rw(y)-> T₂` and `T₂ -rw(x)-> T₁`)
       and aborts `T₂`, restoring exact serializability without read locks.

2. **Lamport Scalar Logical Clocks (`a → b ⟹ L(a) < L(b)`) vs. Fidge–Mattern Vector Clocks (`a → b ⟺ V(a) < V(b)`)**:
   - **Positive Witnesses**:
     * Exhaustive verification across all `2⁴ = 16` distributed message topologies and
       all `6 × 6 = 36` event pairs (`576` total pairs) on a `3`-process execution
       (`lamport_forward_and_vector_clock_exact_iff_576`):
       1. Scalar Lamport clocks satisfy forward causal monotonicity (`a →⁺ b ⟹ L(a) < L(b)`).
       2. Fidge–Mattern `3`-slot Vector Clocks satisfy the **exact bidirectional poset
          isomorphism** (`a →⁺ b ⟺ V(a) < V(b)` across all `576/576` pairs).
   - **Premise-Failure Counterexample (Lamport Converse Failure & `LWW` Silent Data Loss)**:
     * Scalar `L(a) < L(b)` does **not** imply `a →⁺ b`: concurrent writes `e₀` on `P₀`
       (`L = 1`) and `e₅` on `P₂` (`L = 2`) satisfy `L(e₀) < L(e₅)` despite `e₀ ∥ e₅`,
       causing Last-Writer-Wins (`LWW`) registers to silently drop `e₀`, whereas Vector
       Clocks report `V(e₀) = (1, 0, 0) ∥ (0, 0, 2) = V(e₅)` (`vecConcurrent = true`).

3. **Amdahl's Law (`β = 0`) Monotonic Ceiling vs. Gunther's Universal Scalability Law (`USL`, `β > 0`) Retrograde Collapse**:
   - **Positive Witnesses**:
     * Universal arithmetic ceiling (`amdahl_ceiling_cross_mul`) and universal step
       monotonicity (`amdahl_step_monotonic_cross_mul`) for all `α_bp ≤ 10,000` and all
       worker counts `N ≥ 1` when coherency cross-talk `β = 0`.
   - **Premise-Failure Counterexample (`USL` Quadratic Coherency Cross-Talk `β > 0`)**:
     * With contention `α = 10%` (`1,000` bp) and cache/quorum coherency penalty
       `β = 0.25%` (`25` bp), throughput peaks uniquely at `N* = √((1 - α + β)/β) = 19`
       nodes (`5.198×`) and then **collapses retrogradely**: `64` nodes (`3.682×`) run
       slower than `6` nodes (`3.809×`), and `100` nodes (`2.805×`) run slower than
       `4` nodes (`3.007×`), whereas Amdahl (`β = 0`) falsely predicts `9.174×`!
-/

namespace CommonGround.Frontier.SerializabilityVectorClockAndUSLScalability

/-! ## Part 1: Conflict-Serializability (`DSG` Acyclicity) & `SI` Write-Skew vs. `SSI` -/

/-- Binary-tree enumeration over all `2^k` `k`-bit masks (recursion depth `k`). -/
def allMasks : Nat → (Nat → Bool) → Bool
  | 0, f => f 0
  | k + 1, f => allMasks k (fun m => f (2 * m)) && allMasks k (fun m => f (2 * m + 1))

/-- Extract directed edge `u → v` (`u ≠ v`, `u, v ∈ {0, 1, 2}`) from a `6`-bit `DSG` mask:
bit 0: `0→1`, bit 1: `1→0`, bit 2: `0→2`, bit 3: `2→0`, bit 4: `1→2`, bit 5: `2→1`. -/
def dsgEdge (g u v : Nat) : Bool :=
  if u == 0 && v == 1 then (g &&& 1) != 0
  else if u == 1 && v == 0 then (g &&& 2) != 0
  else if u == 0 && v == 2 then (g &&& 4) != 0
  else if u == 2 && v == 0 then (g &&& 8) != 0
  else if u == 1 && v == 2 then (g &&& 16) != 0
  else if u == 2 && v == 1 then (g &&& 32) != 0
  else false

/-- Set the directed edge bit `u → v` (`u ≠ v`) in a `6`-bit `DSG` mask. -/
def dsgBit (u v : Nat) : Nat :=
  if u == 0 && v == 1 then 1
  else if u == 1 && v == 0 then 2
  else if u == 0 && v == 2 then 4
  else if u == 2 && v == 0 then 8
  else if u == 1 && v == 2 then 16
  else if u == 2 && v == 1 then 32
  else 0

/-- Whether a `3`-transaction Direct Serialization Graph `g` contains a directed `2`-cycle or `3`-cycle. -/
def hasCycle3 (g : Nat) : Bool :=
  (dsgEdge g 0 1 && dsgEdge g 1 0) ||
  (dsgEdge g 0 2 && dsgEdge g 2 0) ||
  (dsgEdge g 1 2 && dsgEdge g 2 1) ||
  (dsgEdge g 0 1 && dsgEdge g 1 2 && dsgEdge g 2 0) ||
  (dsgEdge g 0 2 && dsgEdge g 2 1 && dsgEdge g 1 0)

/-- Position (`0`, `1`, or `2`) of transaction `t` in serial order `(p0, p1, p2)`. -/
def permPos3 (p0 p1 _p2 t : Nat) : Nat :=
  if t == p0 then 0 else if t == p1 then 1 else 2

/-- Whether serial permutation `(p0, p1, p2)` respects all directed conflict edges of `g`. -/
def validTopoOrder3 (g p0 p1 p2 : Nat) : Bool :=
  let pairs := [(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)]
  pairs.all fun (u, v) =>
    !dsgEdge g u v || decide (permPos3 p0 p1 p2 u < permPos3 p0 p1 p2 v)

/-- Whether at least one of the `3! = 6` serial permutations is a valid topological sort of `g`. -/
def existsTopoOrder3 (g : Nat) : Bool :=
  let perms := [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]
  perms.any fun (p0, p1, p2) => validTopoOrder3 g p0 p1 p2

/-- Positive Theorem 1a: Across all `2⁶ = 64` `3`-transaction Direct Serialization Graphs,
`DSG` acyclicity holds if and only if a conflict-preserving serial order exists. -/
theorem dsg_acyclicity_iff_topological_serial_order_universal :
    (allMasks 6 fun g => (hasCycle3 g == false) == existsTopoOrder3 g) = true := by
  decide

/-- Build the `6`-bit `DSG` conflict mask of a concrete schedule `[(txn, isWrite, key), ...]`:
for every earlier op `(t₁, w₁, k₁)` and later op `(t₂, w₂, k₂)` with `t₁ ≠ t₂`, `k₁ = k₂`,
and `(w₁ || w₂)`, add directed conflict edge `t₁ → t₂`. -/
def scheduleDSG : List (Nat × Bool × Nat) → Nat
  | [] => 0
  | (t1, w1, k1) :: rest =>
      let headEdges := rest.foldl (fun acc (t2, w2, k2) =>
        if t1 != t2 && k1 == k2 && (w1 || w2) then acc ||| dsgBit t1 t2 else acc) 0
      headEdges ||| scheduleDSG rest

/-- Check directly on a schedule `s` whether serial transaction order `(p0, p1, p2)`
orders every conflicting operation pair identically to `s`. -/
def scheduleMatchesSerialPerm (p0 p1 p2 : Nat) : List (Nat × Bool × Nat) → Bool
  | [] => true
  | (t1, w1, k1) :: rest =>
      let okHead := rest.all fun (t2, w2, k2) =>
        if t1 != t2 && k1 == k2 && (w1 || w2) then
          decide (permPos3 p0 p1 p2 t1 < permPos3 p0 p1 p2 t2)
        else
          true
      okHead && scheduleMatchesSerialPerm p0 p1 p2 rest

def scheduleConflictSerializable (s : List (Nat × Bool × Nat)) : Bool :=
  let perms := [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]
  perms.any fun (p0, p1, p2) => scheduleMatchesSerialPerm p0 p1 p2 s

/-- Exhaustive check across `6³ = 216` interleaved `4`-operation schedules that
`hasCycle3 (scheduleDSG s) == false` iff `scheduleConflictSerializable s == true`. -/
def checkScheduleSerializability216 : Bool :=
  let ops := [
    (0, false, 0), (0, true, 0),
    (1, false, 0), (1, true, 1),
    (2, false, 1), (2, true, 0)
  ]
  ops.all fun o1 =>
    ops.all fun o2 =>
      ops.all fun o3 =>
        let s := [o1, o2, o3, (1, true, 0)]
        (hasCycle3 (scheduleDSG s) == false) == scheduleConflictSerializable s

/-- Positive Theorem 1b: Across all `216` multi-key read/write schedule interleavings,
conflict-serializability coincides identically with `DSG` acyclicity. -/
theorem conflict_serializability_schedule_equivalence_216 :
    checkScheduleSerializability216 = true := by
  decide

/-- Snapshot Isolation (`SI`) First-Committer-Wins rule: two concurrent transactions
with write-set bitmasks `w1, w2` both commit iff their write sets are disjoint (`w1 &&& w2 == 0`). -/
def siAllowsBothCommit (w1 w2 : Nat) : Bool :=
  (w1 &&& w2) == 0

/-- Whether `T_A` (read mask `rA`) has an outgoing `rw`-antidependency to concurrent `T_B` (write mask `wB`). -/
def hasRwAntidependency (rA wB : Nat) : Bool :=
  (rA &&& wB) != 0

/-- Serializable Snapshot Isolation (`SSI`) guard: rejects concurrent commit if either
First-Committer-Wins fails (`w1 ∩ w2 ≠ ∅`) OR a `2`-consecutive `rw`-antidependency cycle forms. -/
def ssiAbortsConcurrentPair (r1 w1 r2 w2 : Nat) : Bool :=
  !siAllowsBothCommit w1 w2 || (hasRwAntidependency r1 w2 && hasRwAntidependency r2 w1)

/-- Premise-Failure Theorem 1c (`SI` Write-Skew Invariant Breach vs. `SSI` Resolution):
Starting from `(x₀, y₀) = (100, 100)` with integrity constraint `x + y ≥ 100`:
1. **Lost Update (`WW` overlap on `x`, bit `0b01`)**: `SI` rejects concurrent commit (`false`).
2. **Write Skew (`R₁ = {x,y} = 0b11, W₁ = {x} = 0b01` setting `x := 0`; `R₂ = {x,y} = 0b11, W₂ = {y} = 0b10` setting `y := 0`)**:
   - `SI` sees disjoint write sets (`0b01 &&& 0b10 = 0`) and **allows both to commit** (`true`),
     producing `(x, y) = (0, 0)` which violates `x + y ≥ 100` (`0 + 0 < 100`)!
   - Both serial schedules (`T₁; T₂` or `T₂; T₁`, where the second sees `100` total and cannot withdraw `100`)
     preserve `x + y = 100 ≥ 100`.
   - `SSI` detects `T₁ -rw(y)-> T₂` and `T₂ -rw(x)-> T₁` (`ssiAbortsConcurrentPair = true`), blocking the anomaly! -/
theorem snapshot_isolation_write_skew_vs_ssi_guard_counterexample :
    -- 1. SI blocks WW lost update on key x (0b01):
    siAllowsBothCommit 0b01 0b01 = false ∧
    -- 2. SI permits Write Skew because write sets {x}=0b01 and {y}=0b10 are disjoint:
    siAllowsBothCommit 0b01 0b10 = true ∧
    -- 3. Resulting concurrent SI state (0, 0) violates x + y >= 100, whereas initial/serial state (100, 0) satisfies it:
    (decide (0 + 0 ≥ 100) = false ∧ decide (100 + 0 ≥ 100) = true) ∧
    -- 4. Schedule [R1(x), R2(y), W1(y), W2(x)] has a 2-cycle in DSG (non-serializable):
    hasCycle3 (scheduleDSG [(0, false, 0), (1, false, 1), (0, true, 1), (1, true, 0)]) = true ∧
    -- 5. SSI detects the bidirectional rw-antidependency cycle and aborts:
    ssiAbortsConcurrentPair 0b11 0b01 0b11 0b10 = true := by
  decide

/-! ## Part 2: Lamport Clocks (`a → b ⟹ L(a) < L(b)`) vs. Vector Clocks (`a → b ⟺ V(a) < V(b)`) -/

/-- Direct causal edge on `6` distributed events (`P₀: 0→1`, `P₁: 2→3`, `P₂: 4→5`) under
`4`-bit message topology `m`:
- bit 0 (`1`): `0 → 2` (`P₀` step 1 to `P₁` step 1)
- bit 1 (`2`): `2 → 4` (`P₁` step 1 to `P₂` step 1)
- bit 2 (`4`): `0 → 5` (`P₀` step 1 to `P₂` step 2)
- bit 3 (`8`): `4 → 3` (`P₂` step 1 to `P₁` step 2) -/
def directCausalEdge (m a b : Nat) : Bool :=
  (a == 0 && b == 1) ||
  (a == 2 && b == 3) ||
  (a == 4 && b == 5) ||
  (((m &&& 1) != 0) && a == 0 && b == 2) ||
  (((m &&& 2) != 0) && a == 2 && b == 4) ||
  (((m &&& 4) != 0) && a == 0 && b == 5) ||
  (((m &&& 8) != 0) && a == 4 && b == 3)

/-- Bounded `k`-hop causal reachability (`a →⁺ b`) in message topology `m`. -/
def causalReach : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => false
  | k + 1, m, a, b =>
      directCausalEdge m a b ||
      [0, 1, 2, 3, 4, 5].any fun mid => directCausalEdge m a mid && causalReach k m mid b

def happensBefore (m a b : Nat) : Bool :=
  causalReach 6 m a b

/-- Scalar Lamport timestamp `L(e)` for each event `e ∈ {0..5}` in topological order `[0, 1, 2, 4, 3, 5]`. -/
def lamportClock (m e : Nat) : Nat :=
  let l0 := 1
  let l1 := l0 + 1
  let l2 := (if (m &&& 1) != 0 then l0 else 0) + 1
  let l4 := (if (m &&& 2) != 0 then l2 else 0) + 1
  let l3Base := if (m &&& 8) != 0 then Nat.max l2 l4 else l2
  let l3 := l3Base + 1
  let l5Base := if (m &&& 4) != 0 then Nat.max l4 l0 else l4
  let l5 := l5Base + 1
  match e with
  | 0 => l0
  | 1 => l1
  | 2 => l2
  | 3 => l3
  | 4 => l4
  | _ => l5

/-- Componentwise maximum of `3`-process vector timestamps. -/
def vecMax (u v : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (Nat.max u.1 v.1, Nat.max u.2.1 v.2.1, Nat.max u.2.2 v.2.2)

/-- Strict Fidge–Mattern vector order `u < v`: componentwise `≤` and strictly `<` in `≥ 1` slot. -/
def vecStrictLt (u v : Nat × Nat × Nat) : Bool :=
  decide (u.1 ≤ v.1 ∧ u.2.1 ≤ v.2.1 ∧ u.2.2 ≤ v.2.2 ∧
          (u.1 < v.1 ∨ u.2.1 < v.2.1 ∨ u.2.2 < v.2.2))

/-- Exact concurrency detection on vector timestamps: neither `u ≤ v` nor `v ≤ u` (`u ≠ v` incomparable). -/
def vecConcurrent (u v : Nat × Nat × Nat) : Bool :=
  u != v && !vecStrictLt u v && !vecStrictLt v u

/-- Fidge–Mattern `3`-slot Vector Clock `V(e)` for each event `e ∈ {0..5}` under topology `m`. -/
def vectorClock (m e : Nat) : Nat × Nat × Nat :=
  let v0 := (1, 0, 0)
  let v1 := (2, 0, 0)
  let v2In := if (m &&& 1) != 0 then v0 else (0, 0, 0)
  let v2 := (v2In.1, v2In.2.1 + 1, v2In.2.2)
  let v4In := if (m &&& 2) != 0 then v2 else (0, 0, 0)
  let v4 := (v4In.1, v4In.2.1, v4In.2.2 + 1)
  let v3In := if (m &&& 8) != 0 then vecMax v2 v4 else v2
  let v3 := (v3In.1, v3In.2.1 + 1, v3In.2.2)
  let v5In := if (m &&& 4) != 0 then vecMax v4 v0 else v4
  let v5 := (v5In.1, v5In.2.1, v5In.2.2 + 1)
  match e with
  | 0 => v0
  | 1 => v1
  | 2 => v2
  | 3 => v3
  | 4 => v4
  | _ => v5

/-- Exhaustive check across all `16` message topologies × `36` event pairs (`576` pairs). -/
def checkLamportAndVectorClocks576 : Bool :=
  allMasks 4 fun m =>
    let evs := [0, 1, 2, 3, 4, 5]
    evs.all fun a =>
      evs.all fun b =>
        let hb := happensBefore m a b
        let lamportForwardOk := !hb || decide (lamportClock m a < lamportClock m b)
        let vectorExactIffOk := hb == vecStrictLt (vectorClock m a) (vectorClock m b)
        lamportForwardOk && vectorExactIffOk

/-- Positive Theorem 2a: Across all `16 × 36 = 576` distributed event pairs, Lamport clocks
are strictly monotone along causal chains (`a →⁺ b ⟹ L(a) < L(b)`) and Fidge–Mattern Vector
Clocks decide causality **exactly** (`a →⁺ b ⟺ V(a) < V(b)`). -/
theorem lamport_forward_and_vector_clock_exact_iff_576 :
    checkLamportAndVectorClocks576 = true := by
  decide

/-- Premise-Failure Theorem 2b (Scalar Lamport Converse Failure & `LWW` Silent Data Loss):
In topology `m = 1` (message `0 → 2` only, `P₂` independent), event `0` on `P₀` has
`L(0) = 1` and event `5` on `P₂` has `L(5) = 2`, so `L(0) < L(5)` even though `0 ↛⁺ 5`
and `5 ↛⁺ 0` (`0 ∥ 5`)! Vector clocks assign `V(0) = (1, 0, 0)` and `V(5) = (0, 0, 2)`,
certifying `vecConcurrent V(0) V(5) = true` so concurrent writes are merged rather than lost. -/
theorem lamport_converse_failure_vs_vector_concurrency_detection :
    lamportClock 1 0 = 1 ∧
    lamportClock 1 5 = 2 ∧
    lamportClock 1 0 < lamportClock 1 5 ∧
    happensBefore 1 0 5 = false ∧
    happensBefore 1 5 0 = false ∧
    vectorClock 1 0 = (1, 0, 0) ∧
    vectorClock 1 5 = (0, 0, 2) ∧
    vecConcurrent (vectorClock 1 0) (vectorClock 1 5) = true := by
  decide

/-! ## Part 3: Amdahl's Law (`β = 0`) vs. Gunther's Universal Scalability Law (`USL`, `β > 0`) -/

/-- Positive Theorem 3a (Universal Amdahl Asymptotic Ceiling):
For any serial/contention fraction `alphaBp ≤ 10,000` (in basis points, `10,000 = 100%`)
and any positive worker count `N = n + 1`, cross-multiplied throughput satisfies
`C(N) ≤ 10,000 / alphaBp`, i.e., `alphaBp * (n + 1) ≤ 10,000 + alphaBp * n`. -/
theorem amdahl_ceiling_cross_mul (alphaBp n : Nat) (hAlpha : alphaBp ≤ 10000) :
    alphaBp * (n + 1) ≤ 10000 + alphaBp * n := by
  rw [Nat.mul_succ]
  omega

/-- Positive Theorem 3b (Universal Amdahl Step-Monotonicity when Coherency `β = 0`):
When cross-talk `β = 0`, adding workers **never** reduces throughput: for all `alphaBp ≤ 10,000`
and all `n : Nat`, `C(n + 1) ≤ C(n + 2)` in exact cross-multiplied rational form. -/
theorem amdahl_step_monotonic_cross_mul (alphaBp n : Nat) (hAlpha : alphaBp ≤ 10000) :
    (n + 1) * (10000 + alphaBp * (n + 1)) ≤ (n + 2) * (10000 + alphaBp * n) := by
  have hceil := amdahl_ceiling_cross_mul alphaBp n hAlpha
  have hL : (n + 1) * (10000 + alphaBp * (n + 1)) =
      (n + 1) * (10000 + alphaBp * n) + alphaBp * (n + 1) := by
    rw [Nat.mul_succ alphaBp n, ← Nat.add_assoc, Nat.mul_add, Nat.mul_comm (n + 1) alphaBp, ← Nat.mul_succ alphaBp n]
  have hR : (n + 2) * (10000 + alphaBp * n) =
      (n + 1) * (10000 + alphaBp * n) + (10000 + alphaBp * n) := by
    rw [Nat.succ_mul (n + 1)]
  omega

/-- Gunther's Universal Scalability Law (`USL`) relative throughput (in milli-units, `1,000 = 1.000×`)
for contention `alphaBp` (basis points), coherency cross-talk `betaBp` (basis points), and `N ≥ 1` nodes:
`C(N) = N / (1 + α(N - 1) + β N(N - 1))`. -/
def uslMilliThroughput (alphaBp betaBp N : Nat) : Nat :=
  if N == 0 then 0
  else (1000 * 10000 * N) / (10000 + alphaBp * (N - 1) + betaBp * N * (N - 1))

/-- Exhaustive check across `N ∈ [1, 128]` that `N* = 19` (`√((10000 - 1000 + 25)/25) = √361 = 19`)
uniquely maximizes `USL` throughput for `(α = 10%, β = 0.25%)`. -/
def checkUslGlobalPeakAt19 : Bool :=
  let peak := uslMilliThroughput 1000 25 19
  (List.range 128).all fun k =>
    let N := k + 1
    if N == 19 then uslMilliThroughput 1000 25 N == peak
    else decide (uslMilliThroughput 1000 25 N < peak)

/-- Premise-Failure Theorem 3c (`USL` Retrograde Throughput Collapse under Coherency `β > 0`):
With contention `α = 10%` (`1,000` bp) and quadratic cache/quorum coherency `β = 0.25%` (`25` bp):
1. Throughput attains a strict global maximum over `N ∈ [1, 128]` at `N* = 19` (`5,198` = `5.198×`,
   strictly beating `N = 18` at `5,194` and `N = 20` at `5,194`).
2. Scaling out to `N = 64` collapses throughput to **`3,682`** (`3.682×`), strictly **slower than
   `6` nodes** (`3,809` = `3.809×`)!
3. Scaling out to `N = 100` collapses throughput to **`2,805`** (`2.805×`), strictly **slower than
   `4` nodes** (`3,007` = `3.007×`), whereas Amdahl's Law (`β = 0`) falsely predicts **`9,174`** (`9.174×`)! -/
theorem usl_retrograde_throughput_collapse_counterexample :
    checkUslGlobalPeakAt19 = true ∧
    uslMilliThroughput 1000 25 18 = 5194 ∧
    uslMilliThroughput 1000 25 19 = 5198 ∧
    uslMilliThroughput 1000 25 20 = 5194 ∧
    (uslMilliThroughput 1000 25 64 = 3682 ∧
     uslMilliThroughput 1000 25 6 = 3809 ∧
     uslMilliThroughput 1000 25 64 < uslMilliThroughput 1000 25 6) ∧
    (uslMilliThroughput 1000 25 100 = 2805 ∧
     uslMilliThroughput 1000 25 4 = 3007 ∧
     uslMilliThroughput 1000 25 100 < uslMilliThroughput 1000 25 4 ∧
     uslMilliThroughput 1000 0 100 = 9174) := by
  decide

end CommonGround.Frontier.SerializabilityVectorClockAndUSLScalability
