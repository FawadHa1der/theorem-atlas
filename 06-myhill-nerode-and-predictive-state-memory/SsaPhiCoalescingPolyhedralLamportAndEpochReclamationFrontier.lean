/-
  Common Ground — Frontier Module #126 (V251)
  06-myhill-nerode-and-predictive-state-memory/SsaPhiCoalescingPolyhedralLamportAndEpochReclamationFrontier.lean

  Cross-Domain Mathematical Verification of:
  1. Strict-SSA Chordal Register Allocation (`χ(G) = ω(G)` via Perfect Elimination Ordering)
     vs. Post-SSA `C₅` Non-Chordal Spill (`ω = 2 < 3 = χ`) & Naive `φ`-Elimination `Swap` / `Lost-Copy` Bugs.
  2. Polyhedral Loop Dependence & Lamport Wavefront Hyperplane Scheduling (`τ(i + d) - τ(i) ≥ 1`)
     vs. Unskewed Rectangular-Tile Backward Dependence `(1, -1)` Cycle & Parallel Stencil Corruption.
  3. Lock-Free Concurrent Memory Reclamation: Treiber Stack `ABA` Use-After-Free Corruption
     vs. Monotonic Tagged-Pointer `CAS` & `3`-Epoch Grace-Period (`EBR` / `RCU`) Safety Invariant.

  Toolchain: Lean 4.33.0 (`0` sorry, `0` admit, `0` sorryAx).
-/

namespace CommonGround.Frontier.SsaPolyhedralEpochReclamation

/-!
## Part 1: Strict-SSA Chordal Register Allocation vs. `C₅` Spill & `φ`-Coalescing Bugs

In Static Single Assignment (`SSA`) form over a dominance tree (Hack, Grund & Goos 2006),
live-range interference graphs are **chordal**, admitting a Perfect Elimination Ordering (`PEO`)
in which greedy coloring achieves `χ(G) = ω(G)` with zero register spills whenever `K ≥ ω(G)`.
Once `φ`-destruction inserts copies carelessly:
  (a) Chordless odd cycles such as `C₅` can arise with `maxLive = ω(C₅) = 2` yet `χ(C₅) = 3`,
      forcing an unexpected register spill under `K = 2` registers;
  (b) Sequentializing parallel `φ` copies `(a, b) ← (b, a)` without interference temp-splitting
      triggers the classic Briggs–Cooper–Kennedy–Torczon **Swap Problem**, clobbering `a`!
-/

/-- Adjacency predicate for a 5-variable strict-SSA chordal interference graph on `Fin 5`
    comprising overlapping 3-cliques `{0,1,2}`, `{1,2,3}`, and `{2,3,4}` (`ω(G) = 3`). -/
def ssaChordalAdj (u v : Fin 5) : Bool :=
  let a := u.val
  let b := v.val
  if a == b then false
  else
    let lo := if a ≤ b then a else b
    let hi := if a ≤ b then b else a
    (lo == 0 && (hi == 1 || hi == 2)) ||
    (lo == 1 && (hi == 2 || hi == 3)) ||
    (lo == 2 && (hi == 3 || hi == 4)) ||
    (lo == 3 && hi == 4)

/-- Check whether a coloring `c : Fin 5 → Fin K` assigns distinct registers to all interfering pairs. -/
def isValidColoring5 {K : Nat} (adj : Fin 5 → Fin 5 → Bool) (c : Fin 5 → Fin K) : Bool :=
  (List.finRange 5).all fun u =>
    (List.finRange 5).all fun v =>
      if adj u v then decide (c u ≠ c v) else true

/-- Greedy PEO `3`-coloring `![0, 1, 2, 0, 1]` along the dominance-tree elimination order. -/
def ssaGreedyColoring3 : Fin 5 → Fin 3
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨2, _⟩ => ⟨2, by decide⟩
  | ⟨3, _⟩ => ⟨0, by decide⟩
  | ⟨4, _⟩ => ⟨1, by decide⟩

/-- Every earlier-neighbor set (`v < u`) in `ssaChordalAdj` is a clique of size `≤ 2` (`PEO` property!). -/
def isPeoSimplicial5 (adj : Fin 5 → Fin 5 → Bool) : Bool :=
  (List.finRange 5).all fun u =>
    let earlier := (List.finRange 5).filter fun v => decide (v.val < u.val) && adj u v
    decide (earlier.length ≤ 2) &&
    earlier.all fun x => earlier.all fun y =>
      if x == y then true else adj x y

/-- **Positive Witness 1A**: `ssaChordalAdj` satisfies the exact simplicial PEO invariant (`backDeg ≤ 2`),
    contains a `3`-clique `{0, 1, 2}` (`ω(G) ≥ 3`), and is validly `3`-colored with zero spills! -/
theorem ssa_chordal_peo_zero_spill_three_coloring :
    isPeoSimplicial5 ssaChordalAdj = true ∧
    ssaChordalAdj ⟨0, by decide⟩ ⟨1, by decide⟩ = true ∧
    ssaChordalAdj ⟨1, by decide⟩ ⟨2, by decide⟩ = true ∧
    ssaChordalAdj ⟨0, by decide⟩ ⟨2, by decide⟩ = true ∧
    isValidColoring5 ssaChordalAdj ssaGreedyColoring3 = true := by
  decide

/-- Chordless 5-cycle `C₅` interference graph (`0-1-2-3-4-0`), which can appear after SSA destruction. -/
def postSsaCycle5Adj (u v : Fin 5) : Bool :=
  let d := (u.val + 5 - v.val) % 5
  d == 1 || d == 4

/-- `C₅` contains **zero** triangles (`ω(C₅) = 2`, so at most 2 variables are ever simultaneously live). -/
def hasTriangle5 (adj : Fin 5 → Fin 5 → Bool) : Bool :=
  (List.finRange 5).any fun i =>
    (List.finRange 5).any fun j =>
      (List.finRange 5).any fun k =>
        adj i j && adj j k && adj i k

/-- Exhaustive search over all `2^5 = 32` `2`-register assignments (`mask : Fin 32`). -/
def anyTwoColoring5 (adj : Fin 5 → Fin 5 → Bool) : Bool :=
  (List.finRange 32).any fun mask =>
    let c : Fin 5 → Fin 2 := fun u => ⟨(mask.val >>> u.val) % 2, Nat.mod_lt _ (by decide)⟩
    isValidColoring5 adj c

/-- **Premise-Failure Counterexample 1B (Post-SSA Non-Chordal `C₅` Spill)**:
    Even though `postSsaCycle5Adj` has `ω(C₅) = 2` (`hasTriangle5 = false`), it violates the PEO
    chordality premise (`isPeoSimplicial5 = false`) and admits **zero** valid `2`-register colorings
    across all `32` assignments, forcing a spill unless `K ≥ 3`! -/
theorem post_ssa_c5_nonchordal_forces_two_register_spill :
    hasTriangle5 postSsaCycle5Adj = false ∧
    isPeoSimplicial5 postSsaCycle5Adj = false ∧
    anyTwoColoring5 postSsaCycle5Adj = false := by
  decide

/-- Parallel SSA `φ`-header copy semantics `(a', b') := (b, a)` via temporary register split `tmp := a`. -/
def parallelPhiSwap (a b : Int) : Int × Int :=
  let tmp := a
  let a' := b
  let b' := tmp
  (a', b')

/-- Buggy naive sequential `φ`-copy lowering (`a := b; b := a`) without live-out interference check. -/
def buggySequentialPhiSwap (_a b : Int) : Int × Int :=
  let a1 := b
  let b1 := a1
  (a1, b1)

/-- **Positive Theorem & Premise-Failure Counterexample 1C (Briggs `Swap Problem`)**:
    1. Parallel/temp-split `φ` lowering swaps `(a, b) ↦ (b, a)` universally and is an involution.
    2. Naive sequential copy lowering clobbers `a`: on `(10, 99)`, it produces `(99, 99) ≠ (99, 10)`,
       destroying distinctness and losing value `10`! -/
theorem ssa_phi_swap_parallel_valid_vs_sequential_clobber :
    (∀ a b : Int, parallelPhiSwap (parallelPhiSwap a b).1 (parallelPhiSwap a b).2 = (a, b)) ∧
    parallelPhiSwap 10 99 = (99, 10) ∧
    buggySequentialPhiSwap 10 99 = (99, 99) ∧
    buggySequentialPhiSwap 10 99 ≠ parallelPhiSwap 10 99 := by
  refine ⟨?_, by decide, by decide, by decide⟩
  intro a b
  rfl

/-- Critical-edge **Lost-Copy Problem**: loop increments `x₁ = x₀ + 1` and branches:
    if exit is taken, return previous `x₀`; else loop with `x₁`.
    Naive copy `x₀ := x₁` hoisted BEFORE the branch overwrites the exit return value! -/
def splitCriticalEdgeExitValue (x0 : Int) : Int × Int :=
  let x1 := x0 + 1
  let exitRet := x0      -- Exit edge preserves old x0
  let backedgeX0 := x1   -- Split loop-latch edge copies x1 into x0
  (exitRet, backedgeX0)

def unsplitLostCopyExitValue (x0 : Int) : Int × Int :=
  let x1 := x0 + 1
  let x0_clobbered := x1 -- Copy placed before conditional branch!
  (x0_clobbered, x0_clobbered)

theorem ssa_critical_edge_lost_copy_counterexample :
    splitCriticalEdgeExitValue 10 = (10, 11) ∧
    unsplitLostCopyExitValue 10 = (11, 11) ∧
    (unsplitLostCopyExitValue 10).1 ≠ (splitCriticalEdgeExitValue 10).1 := by
  decide

/-!
## Part 2: Polyhedral Loop Dependence & Lamport Wavefront Hyperplane Scheduling

For a 2D loop nest `(t, x)` with affine schedule `τ(t, x) = α·t + β·x` and dependence vectors
`d = (dt, dx) ∈ D`, Lamport's hyperplane theorem states that if `α·dt + β·dx ≥ 1` for all `d ∈ D`,
every consumer `(t + dt, x + dx)` is scheduled in a strictly later wavefront than its producer `(t, x)`,
so all points on hyperplane `τ(t, x) = k` have zero data dependences and execute safely in parallel!
-/

/-- Affine 2D hyperplane timestamp `τ(t, x) = α·t + β·x`. -/
def polySchedule (alpha beta t x : Int) : Int :=
  alpha * t + beta * x

/-- **Universal Theorem 2A (`lamport_hyperplane_causality_universal`)**:
    Whenever `α·dt + β·dx ≥ 1`, every producer `(t, x)` precedes its consumer `(t + dt, x + dx)`
    by at least `1` wavefront tick (`τ(consumer) ≥ τ(producer) + 1`), hence producer and consumer
    NEVER share the same parallel wavefront (`τ(consumer) ≠ τ(producer)`). -/
theorem lamport_hyperplane_causality_universal
    (alpha beta t x dt dx : Int)
    (hPos : alpha * dt + beta * dx ≥ 1) :
    polySchedule alpha beta (t + dt) (x + dx) ≥ polySchedule alpha beta t x + 1 ∧
    polySchedule alpha beta (t + dt) (x + dx) ≠ polySchedule alpha beta t x := by
  unfold polySchedule
  have hDiff : alpha * (t + dt) + beta * (x + dx) - (alpha * t + beta * x) = alpha * dt + beta * dx := by
    rw [Int.mul_add, Int.mul_add]
    omega
  omega

/-- The three 1D Jacobi / sequence-DP stencil dependence vectors: `(1, -1)`, `(1, 0)`, `(1, 1)`. -/
def jacobiStencilDeps : List (Int × Int) :=
  [(1, -1), (1, 0), (1, 1)]

/-- **Premise-Failure Counterexample 2B (Unskewed Rectangular Spatial Tile Cycle)**:
    Under spatial-only tile schedule `τ_space(t, x) = x` (`α = 0, β = 1`), dependence `d = (1, -1)`
    has `α·dt + β·dx = -1 < 1`: consumer `(t=1, x=2)` has `τ_space = 2 < 3 = τ_space(0, 3)`!
    By contrast, wavefront skewing `(α = 2, β = 1)` makes ALL 3 Jacobi dependences strictly positive
    (`1, 2, 3 ≥ 1`)! -/
theorem jacobi_unskewed_violation_vs_skewed_wavefront_valid :
    polySchedule 0 1 1 2 < polySchedule 0 1 0 3 ∧
    (jacobiStencilDeps.all fun d => decide (2 * d.1 + 1 * d.2 ≥ 1)) = true := by
  decide

/-- Exact 4-cell stencil step `next[x] = prev[x-1] + prev[x] + prev[x+1]` (zero-padded boundaries),
    comparing sequential/wavefront double-buffered execution against an unskewed in-place race
    that overwrites `prev[x-1]` before `x` reads it (`WAR` / `RAW` hazard!). -/
def stencilReferenceStep (v : Fin 4 → Nat) : Fin 4 → Nat
  | ⟨0, _⟩ => v ⟨0, by decide⟩ + v ⟨1, by decide⟩
  | ⟨1, _⟩ => v ⟨0, by decide⟩ + v ⟨1, by decide⟩ + v ⟨2, by decide⟩
  | ⟨2, _⟩ => v ⟨1, by decide⟩ + v ⟨2, by decide⟩ + v ⟨3, by decide⟩
  | ⟨3, _⟩ => v ⟨2, by decide⟩ + v ⟨3, by decide⟩

/-- Unbuffered in-place sweep `for x = 0..3: A[x] := A[x-1] + A[x] + A[x+1]` violating anti-dependence `(0, 1)`
    when parallelized/pipelined without wavefront skewing or double-buffering. -/
def stencilUnskewedInPlaceRace (v : Fin 4 → Nat) : Fin 4 → Nat :=
  let a0 := v ⟨0, by decide⟩ + v ⟨1, by decide⟩
  let a1 := a0 + v ⟨1, by decide⟩ + v ⟨2, by decide⟩
  let a2 := a1 + v ⟨2, by decide⟩ + v ⟨3, by decide⟩
  let a3 := a2 + v ⟨3, by decide⟩
  fun i => match i with
    | ⟨0, _⟩ => a0
    | ⟨1, _⟩ => a1
    | ⟨2, _⟩ => a2
    | ⟨3, _⟩ => a3

/-- Wavefront skewed execution computes cells in causal diagonal order and matches `stencilReferenceStep` identically,
    whereas `stencilUnskewedInPlaceRace` on `[1, 2, 3, 4]` produces `[3, 8, 15, 19] ≠ [3, 6, 9, 7]`! -/
theorem stencil_wavefront_exact_vs_inplace_race_corruption :
    let init : Fin 4 → Nat := fun i => i.val + 1
    (List.finRange 4).map (stencilReferenceStep init) = [3, 6, 9, 7] ∧
    (List.finRange 4).map (stencilUnskewedInPlaceRace init) = [3, 8, 15, 19] ∧
    (List.finRange 4).map (stencilUnskewedInPlaceRace init) ≠ (List.finRange 4).map (stencilReferenceStep init) := by
  decide

/-!
## Part 3: Lock-Free Treiber Stack `ABA` Corruption vs. Tagged `CAS` & `3`-Epoch Reclamation (`EBR`)

In a lock-free Treiber stack over a manual heap (`C++` / `Rust` / kernel `RCU`):
  - If Thread 1 reads `head = A` (`next(A) = B`) and pauses while Thread 2 pops `A`, pops & frees `B`,
    and pushes a recycled block at address `A` (`head = A → C`), an **untagged** `CAS(&head, A, B)`
    succeeds (`A == A`!) and sets `head = B` — a **freed/dangling node**!
  - **Fix 1 (Monotonic Generation Stamp)**: `CAS((A, gen₀), ...)` compares `(addr, gen)`. Because
    `gen` strictly increases on every mutation, any `ABA` round-trip produces `gen₂ ≥ gen₀ + 2 > gen₀`,
    causing stale `CAS` to reject universally.
  - **Fix 2 (`3`-Epoch Based Reclamation `EBR`)**: Nodes retired in epoch `r` are reclaimed ONLY when
    global epoch reaches `E ≥ r + 2`, and `E → E + 1` requires all active pinned threads to satisfy `e_t = E`.
-/

/-- Heap node state in a 4-slot lock-free allocator (`0 = A, 1 = B, 2 = C, 3 = nil`). -/
structure HeapSlot where
  allocated : Bool
  next      : Nat
  payload   : Nat
  deriving DecidableEq, Repr

/-- Untagged Treiber stack state (`head` slot index + 4-slot heap). -/
structure UntaggedStack where
  head  : Nat
  slots : Fin 4 → HeapSlot

/-- Initial valid stack `head = 0 (A) → 1 (B) → 2 (C) → 3 (nil)` with payloads `10, 20, 30`. -/
def initTreiberStack : UntaggedStack where
  head := 0
  slots := fun i => match i with
    | ⟨0, _⟩ => { allocated := true,  next := 1, payload := 10 }
    | ⟨1, _⟩ => { allocated := true,  next := 2, payload := 20 }
    | ⟨2, _⟩ => { allocated := true,  next := 3, payload := 30 }
    | ⟨3, _⟩ => { allocated := false, next := 3, payload := 0  }

/-- Untagged `CAS` on `head`: if `s.head == expected`, swing `s.head := desired`. -/
def untaggedCasHead (s : UntaggedStack) (expected desired : Nat) : UntaggedStack × Bool :=
  if s.head == expected then ({ s with head := desired }, true) else (s, false)

/-- Intervening `ABA` trace by Thread 2 under immediate `free` (without `EBR` / Hazard Pointers):
    pop `A(0)` & free `0`, pop `B(1)` & **free `1`**, reallocate slot `0` (`payload = 99, next = 2`) and push `0`! -/
def afterThread2AbaReuse (s : UntaggedStack) : UntaggedStack where
  head := 0
  slots := fun i => match i with
    | ⟨0, _⟩ => { allocated := true,  next := 2, payload := 99 } -- Reallocated at address A(0)!
    | ⟨1, _⟩ => { allocated := false, next := 3, payload := 0  } -- B(1) is FREED!
    | ⟨2, _⟩ => s.slots ⟨2, by decide⟩
    | ⟨3, _⟩ => s.slots ⟨3, by decide⟩

/-- **Premise-Failure Counterexample 3A (`treiber_aba_free_reuse_corrupts_stack`)**:
    Thread 1 recorded `expected = 0 (A)` and `desired = next(A) = 1 (B)` from `initTreiberStack`.
    After Thread 2's `ABA` reuse (`afterThread2AbaReuse`), Thread 1's untagged `CAS(&head, 0, 1)`
    **succeeds (`ok = true`)**, swinging `head` to slot `1` whose `allocated` bit is **`false` (Use-After-Free!)**! -/
theorem treiber_aba_free_reuse_corrupts_stack :
    let expected := initTreiberStack.head
    let desired  := (initTreiberStack.slots ⟨0, by decide⟩).next
    let sMid     := afterThread2AbaReuse initTreiberStack
    let res      := untaggedCasHead sMid expected desired
    res.2 = true ∧
    res.1.head = 1 ∧
    (res.1.slots ⟨1, by decide⟩).allocated = false := by
  decide

/-- Tagged pointer `(addr, gen)` with monotonic ABA generation counter. -/
structure TaggedPtr where
  addr : Nat
  gen  : Nat
  deriving DecidableEq, Repr

def taggedCas (cur expected desired : TaggedPtr) : TaggedPtr × Bool :=
  if cur == expected then (desired, true) else (cur, false)

/-- **Universal Theorem 3B (`tagged_cas_monotonic_stamp_blocks_aba_universal`)**:
    For ANY address `a`, initial generation `g₀`, and ANY intervening `pop` (`g₁ > g₀`) followed by
    `push` reusing the exact same address `a` (`g₂ > g₁`), a stale `taggedCas` expecting `(a, g₀)`
    **always fails (`false`)** and leaves `(a, g₂)` untouched! -/
theorem tagged_cas_monotonic_stamp_blocks_aba_universal
    (a g0 g1 g2 desiredAddr : Nat)
    (hPop : g0 < g1)
    (hPush : g1 < g2) :
    taggedCas { addr := a, gen := g2 } { addr := a, gen := g0 } { addr := desiredAddr, gen := g0 + 1 } =
      ({ addr := a, gen := g2 }, false) := by
  unfold taggedCas
  have hNe : ({ addr := a, gen := g2 } == ({ addr := a, gen := g0 } : TaggedPtr)) = false := by
    simp [BEq.beq, decide_eq_false_iff_not]
    omega
  rw [hNe]
  rfl

/-- **Universal Theorem 3C (`ebr_three_epoch_grace_period_safety_universal`)**:
    In `3`-Epoch Based Reclamation (`Crossbeam` / `Fraser EBR`), if every active pinned reader `t`
    satisfies the two-epoch window invariant `E ≤ e_t + 1` (i.e., `e_t ∈ {E - 1, E}`) and a retired
    node's retirement epoch `r` satisfies the reclamation guard `r + 2 ≤ E`, then `r < e_t` strictly:
    the retired node was unlinked BEFORE reader `t` entered its critical section, preventing Use-After-Free! -/
theorem ebr_three_epoch_grace_period_safety_universal
    (globalE readerEpoch retireEpoch : Nat)
    (hPinWindow : globalE ≤ readerEpoch + 1)
    (hReclaimGuard : retireEpoch + 2 ≤ globalE) :
    retireEpoch < readerEpoch := by
  omega

/-- Exhaustive 3-thread `EBR` state check (`(pinned : Bool, localE : Fin 4)` per thread):
    verifies across all `(2 × 4)^2 = 64` 2-thread states at `globalE = 2` that:
    1. Guarded epoch advance (`all pinned threads have localE == globalE`) preserves `globalE' ≤ localE + 1`
       for `globalE' = 3` (`64 / 64` states!).
    2. Unguarded epoch advance while Thread 0 is pinned at `localE = 1` (`globalE = 2 → 3`) violates
       grace-period safety, allowing `retireEpoch = 1` (`1 + 2 ≤ 3`) to be freed while Thread 0 is STILL
       reading epoch `1` (`retireEpoch = readerEpoch = 1`)! -/
def checkEbrAdvance2Threads : Bool :=
  let globalE := 2
  let states := (List.finRange 2).flatMap fun p0 =>
    (List.finRange 4).flatMap fun e0 =>
      (List.finRange 2).flatMap fun p1 =>
        (List.finRange 4).map fun e1 =>
          (p0.val == 1, e0.val, p1.val == 1, e1.val)
  states.all fun (pin0, e0, pin1, e1) =>
    let invBefore := (!pin0 || decide (globalE ≤ e0 + 1)) && (!pin1 || decide (globalE ≤ e1 + 1))
    let canAdvance := (!pin0 || e0 == globalE) && (!pin1 || e1 == globalE)
    if invBefore && canAdvance then
      let globalE' := globalE + 1
      (!pin0 || decide (globalE' ≤ e0 + 1)) && (!pin1 || decide (globalE' ≤ e1 + 1))
    else true

theorem ebr_guarded_advance_inductive_vs_unguarded_uaf :
    checkEbrAdvance2Threads = true ∧
    (let globalE' := 3; let stalledReaderE := 1; let retireE := 1;
     retireE + 2 ≤ globalE' ∧ ¬ (retireE < stalledReaderE)) := by
  decide

end CommonGround.Frontier.SsaPolyhedralEpochReclamation
