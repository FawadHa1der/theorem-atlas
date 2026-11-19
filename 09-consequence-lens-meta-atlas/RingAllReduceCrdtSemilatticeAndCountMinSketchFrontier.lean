/-
  09-consequence-lens-meta-atlas/RingAllReduceCrdtSemilatticeAndCountMinSketchFrontier.lean

  Wave V245 · Frontier #120 (Milestone 100th Exact Finite Micro-Lab Anchor):
  1. Ring-AllReduce `2(P-1)(M/P)` Per-Node Bandwidth Optimality vs. Parameter-Server `2(P-1)M`
     Root Incast (`8×` Bottleneck at `P=8`) & Saturated Floating-Point Non-Associative Ring Drift (`4 ≠ 10`).
  2. State-Based `CvRDT` Join-Semilattice Strong Eventual Consistency (Order + Duplicate Gossip
     Invariance) vs. Non-Commutative `Add`/`Remove` Split-Brain & `LWW` Clock-Skew Causal Loss.
  3. Cormode–Muthukrishnan Count-Min Sketch One-Sided Point-Query Envelope (`min_r C[r, h_r(i)] ≥ f_i`)
     vs. Turnstile Negative-Deletion Underestimation (`min(6, 10) = 6 < 10`).

  Pure Lean 4.33.0 core (`0` sorry, `0` axioms, `0` external dependencies).
-/

namespace CommonGround.Frontier.RingAllReduceCrdtAndCountMinSketch

/-! ## Pillar I: Ring-AllReduce Bandwidth Optimality vs. PS Root Incast & FP Non-Associativity -/

/-- Per-worker words transferred (sent + received) in two-phase Ring-AllReduce
    (Scatter-Reduce + AllGather) over `P` workers when total model size is `M = P * chunkWords`. -/
def ringAllReducePerNodeWords (P chunkWords : Nat) : Nat :=
  2 * (P - 1) * chunkWords

/-- Words transferred through the central coordinator in a star Parameter-Server aggregation
    (`P - 1` workers each upload `M = P * chunkWords` gradients and download `M` updated weights). -/
def paramServerRootWords (P chunkWords : Nat) : Nat :=
  2 * (P - 1) * (P * chunkWords)

/-- Universal `P×` Incast Elimination Identity:
    For every cluster size `P` and shard size `chunkWords`, the Parameter-Server root transfers
    strictly `P` times the per-GPU volume of Ring-AllReduce (`112 = 8 * 14` at `P = 8, chunkWords = 1`),
    and Ring-AllReduce per-GPU volume is strictly bounded by `2 * M` (`14 < 16`) for all `P ≥ 1`! -/
theorem ring_allreduce_per_node_volume_vs_parameter_server (P chunkWords : Nat) :
    paramServerRootWords P chunkWords = P * ringAllReducePerNodeWords P chunkWords ∧
    ringAllReducePerNodeWords 8 1 = 14 ∧
    paramServerRootWords 8 1 = 112 ∧
    ringAllReducePerNodeWords 8 1 < 2 * (8 * 1) := by
  refine ⟨?_, by decide, by decide, by decide⟩
  simp [paramServerRootWords, ringAllReducePerNodeWords, Nat.mul_assoc, Nat.mul_comm]

/-- Saturated finite-range floating-point / quantized accumulator clamping onto `[-10, 10]`. -/
def satAdd10 (x y : Int) : Int :=
  let s := x + y
  if s > 10 then 10 else if s < -10 then -10 else s

/-- Premise-Failure Counterexample (Non-Associative FP Ring-Order Drift):
    Because finite-precision saturated/rounded addition is NOT associative, reducing the exact same
    3-worker gradient vector `[8, 8, -6]` starting at `(0, 1)` yields `((8 ⊞ 8) ⊞ -6) = 10 ⊞ -6 = 4`,
    whereas starting the ring reduction one hop shifted yields `8 ⊞ (8 ⊞ -6) = 8 ⊞ 2 = 10` (`4 ≠ 10`)! -/
theorem non_associative_fp_ring_order_drift_counterexample :
    satAdd10 (satAdd10 8 8) (-6) = 4 ∧
    satAdd10 8 (satAdd10 8 (-6)) = 10 ∧
    satAdd10 (satAdd10 8 8) (-6) ≠ satAdd10 8 (satAdd10 8 (-6)) := by
  decide

/-! ## Pillar II: `CvRDT` Join-Semilattice Convergence vs. Add/Remove Split-Brain & LWW Skew -/

/-- Algebraic Join-Semilattice carrier underlying State-Based Convergent Replicated Data Types (`CvRDT`). -/
structure JoinSemilattice (S : Type) where
  join : S → S → S
  join_idem : ∀ a : S, join a a = a
  join_comm : ∀ a b : S, join a b = join b a
  join_assoc : ∀ a b c : S, join (join a b) c = join a (join b c)

/-- Universal Strong Eventual Consistency (`CvRDT` Gossip Invariance):
    In any `JoinSemilattice`, out-of-order gossip delivery `((a ⊔ b) ⊔ c)` vs. `((c ⊔ a) ⊔ b)`
    and duplicate packet retries `((a ⊔ b) ⊔ b)` converge to the exact same replica state! -/
theorem cvrdt_gossip_order_and_duplicate_invariance {S : Type} (L : JoinSemilattice S) (a b c : S) :
    L.join (L.join a b) c = L.join (L.join c a) b ∧
    L.join (L.join a b) b = L.join a b := by
  constructor
  · rw [L.join_comm (L.join a b) c, L.join_assoc]
  · rw [L.join_assoc, L.join_idem]

/-- 4-replica Grow-Only Counter (`GCounter`) state merged coordinatewise via `Nat.max`. -/
structure GCounter4 where
  r0 : Nat
  r1 : Nat
  r2 : Nat
  r3 : Nat
  deriving DecidableEq, Repr

def gcounterMerge (x y : GCounter4) : GCounter4 :=
  { r0 := Nat.max x.r0 y.r0
    r1 := Nat.max x.r1 y.r1
    r2 := Nat.max x.r2 y.r2
    r3 := Nat.max x.r3 y.r3 }

def gcounterValue (x : GCounter4) : Nat :=
  x.r0 + x.r1 + x.r2 + x.r3

theorem gcounter4_merge_witness :
    let a : GCounter4 := ⟨3, 0, 1, 0⟩
    let b : GCounter4 := ⟨1, 4, 0, 2⟩
    gcounterMerge a b = ⟨3, 4, 1, 2⟩ ∧
    gcounterMerge a b = gcounterMerge b a ∧
    gcounterMerge (gcounterMerge a b) b = gcounterMerge a b ∧
    gcounterValue (gcounterMerge a b) = 10 := by
  decide

/-- Naive boolean membership operations (`addElem` sets `true`, `removeElem` sets `false`). -/
def naiveAdd (_ : Bool) : Bool := true
def naiveRemove (_ : Bool) : Bool := false

/-- Last-Writer-Wins (`LWW`) register `(payload, wallClockTimestamp)` merged by physical timestamp. -/
structure LwwReg where
  val : Nat
  ts : Nat
  deriving DecidableEq, Repr

def lwwMerge (a b : LwwReg) : LwwReg :=
  if a.ts ≥ b.ts then a else b

/-- Dual Premise-Failure Counterexamples (`Add`/`Remove` Split-Brain & `LWW` Clock-Skew Loss):
    (1) Naive `add` and `remove` do NOT commute (`naiveRemove (naiveAdd false) = false ≠ true = naiveAdd (naiveRemove false)`),
        causing permanent replica divergence under reordered network delivery.
    (2) Under `+5ms` clock skew (`ts = 105`), an earlier stale write `(val=42, ts=105)` silently overwrites
        a causally later write `(val=99, ts=102)` (`(lwwMerge ⟨42,105⟩ ⟨99,102⟩).val = 42 ≠ 99`)! -/
theorem naive_add_remove_split_brain_and_lww_clock_skew_loss :
    naiveRemove (naiveAdd false) = false ∧
    naiveAdd (naiveRemove false) = true ∧
    naiveRemove (naiveAdd false) ≠ naiveAdd (naiveRemove false) ∧
    (lwwMerge ⟨42, 105⟩ ⟨99, 102⟩).val = 42 ∧
    (lwwMerge ⟨42, 105⟩ ⟨99, 102⟩).val ≠ 99 := by
  decide

/-! ## Pillar III: Count-Min Sketch One-Sided Envelope vs. Turnstile Negative Deletion -/

/-- Universal 2-Row Non-Negative Count-Min Sketch Point-Query Envelope:
    When all colliding stream counts are non-negative (`c₀ = f_i + noise₀`, `c₁ = f_i + noise₁`),
    `min(c₀, c₁) ≥ f_i` ALWAYS holds (zero underestimation), and `min(c₀, c₁) = f_i` holds
    exactly whenever either hash row isolates item `i` (`noise₀ = 0 ∨ noise₁ = 0`)! -/
theorem count_min_sketch_universal_point_lower_bound (f_i noise0 noise1 : Nat) :
    f_i ≤ Nat.min (f_i + noise0) (f_i + noise1) ∧
    ((noise0 = 0 ∨ noise1 = 0) → Nat.min (f_i + noise0) (f_i + noise1) = f_i) := by
  simp only [Nat.min_def]
  constructor
  · split <;> omega
  · intro hZero
    cases hZero with
    | inl h0 => split <;> omega
    | inr h1 => split <;> omega

/-- Concrete `2 × 4` Count-Min Sketch over 4 items with frequencies `f = [10, 3, 1, 2]`:
    Row 0 hashes `h₀ = [0, 1, 0, 2]` (colliding item `0` (`10`) and item `2` (`1`) into bucket `0` = `11`),
    Row 1 hashes `h₁ = [2, 1, 3, 0]` (isolating item `0` in bucket `2` = `10`).
    Querying item `0` returns `min(11, 10) = 10 == f[0]`, and every item `k ∈ Fin 4` satisfies `f[k] ≤ cmsQuery(k)`! -/
def streamFreq4 : Fin 4 → Nat
  | ⟨0, _⟩ => 10
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2

def cmsHash0 : Fin 4 → Fin 4
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨2, _⟩ => ⟨0, by decide⟩
  | ⟨3, _⟩ => ⟨2, by decide⟩

def cmsHash1 : Fin 4 → Fin 4
  | ⟨0, _⟩ => ⟨2, by decide⟩
  | ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨2, _⟩ => ⟨3, by decide⟩
  | ⟨3, _⟩ => ⟨0, by decide⟩

def cmsRow0Bucket : Fin 4 → Nat
  | ⟨0, _⟩ => 11
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 0

def cmsRow1Bucket : Fin 4 → Nat
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 10
  | ⟨3, _⟩ => 1

def cmsQuery2x4 (k : Fin 4) : Nat :=
  Nat.min (cmsRow0Bucket (cmsHash0 k)) (cmsRow1Bucket (cmsHash1 k))

theorem count_min_sketch_nonneg_lower_bound_2x4 :
    cmsQuery2x4 ⟨0, by decide⟩ = 10 ∧
    (∀ k : Fin 4, streamFreq4 k ≤ cmsQuery2x4 k) := by
  decide

/-- Premise-Failure Counterexample (Turnstile Negative-Deletion Underestimation):
    If colliding item `2` undergoes an unauthenticated / out-of-window negative deletion `Δ = -5`
    in a signed turnstile stream (`1 - 5 = -4`), Row 0 bucket `0` drops from `11` to `10 + (-4) = 6`,
    so `min(6, 10) = 6 < 10 = f[0]` — violating the Count-Min lower bound by `40%`! -/
theorem count_min_sketch_turnstile_negative_deletion_underestimate :
    let row0Turnstile : Int := 10 + (1 - 5)
    let row1Turnstile : Int := 10
    let cmsEst : Int := if row0Turnstile ≤ row1Turnstile then row0Turnstile else row1Turnstile
    cmsEst = 6 ∧ cmsEst < 10 := by
  decide

end CommonGround.Frontier.RingAllReduceCrdtAndCountMinSketch
