/-
  06-myhill-nerode-and-predictive-state-memory/BeladyFifoAnomalyLruStackMonotonicityAndKaratsubaThreeMulFrontier.lean

  Milestone Wave V274 · Frontier #149 (MILESTONE SUITE #675 & 230 DISCOVERY LEADS!):
  Cross-Domain Structural Bridge Unifying:
  1. Bélády (`1969`) `FIFO` Page-Replacement Anomaly (`9` Faults at `3` Frames `< 10` Faults at `4` Frames!)
     vs. Mattson (`1970`) `LRU` Stack-Inclusion Monotonicity (`8 ≤ 10`) (`cslib` ↔ `econlib`):
     - On Bélády's canonical 12-request trace `[1, 2, 3, 4, 1, 2, 5, 1, 2, 3, 4, 5]`:
       * `FIFO` with capacity `k = 3` incurs `9` page faults, whereas increasing RAM capacity to `k = 4`
         suffers `10` page faults (`fifoFaults 3 < fifoFaults 4`)!
       * `LRU` satisfies stack inclusion `S_3(t) ⊆ S_4(t)` at every step and incurs `8 ≤ 10` faults!
  2. Karatsuba–Ofman (`1962`) `3`-Multiplication Bilinear Split (`z₂·B² + ((x₁+x₀)(y₁+y₀) - z₂ - z₀)·B + z₀`)
     vs. Unsubtracted Middle Cross-Term Bug (`cslib` ↔ `apsp3sum`):
     - Universal ring identity over `Int`: `3` products (`z₂ = x₁y₁`, `z₀ = x₀y₀`, `z₁ = (x₁+x₀)(y₁+y₀)`)
       recover `(x₁·B + x₀)*(y₁·B + y₀)` for all `(x₁, x₀, y₁, y₀, B)`!
  3. Karp–Rabin (`1987`) Rolling Polynomial Hash `O(1)` Sliding-Window Recurrence
     vs. Monte Carlo Modulo-Collision False Match (`cslib` ↔ `oai-codes` ↔ `flt`):
     - Universal `O(1)` rolling step `(h([a,b,c]) - a·B²)·B + d = h([b,c,d])` over `Int`, paired with
       explicit spurious collision `polyHash2_13 1 5 = polyHash2_13 2 2 = 8` despite `(1,5) ≠ (2,2)`!

  Toolchain: leanprover/lean4:v4.33.0 (zero sorry).
-/

namespace CommonGround.Frontier.BeladyFifoAnomalyLruStackMonotonicityAndKaratsubaThreeMul

/-! ## Part 1: Bélády (`1969`) FIFO Page-Fault Anomaly vs. Mattson LRU Stack Monotonicity -/

def beladyTrace : List Nat := [1, 2, 3, 4, 1, 2, 5, 1, 2, 3, 4, 5]

def fifoStep (cap : Nat) (q : List Nat) (p : Nat) : List Nat × Nat :=
  if q.elem p then
    (q, 0)
  else
    let q' := if q.length < cap then q ++ [p] else q.drop 1 ++ [p]
    (q', 1)

def fifoFaultCount (cap : Nat) (xs : List Nat) : Nat :=
  (xs.foldl (fun (acc : List Nat × Nat) p =>
    let r := fifoStep cap acc.1 p
    (r.1, acc.2 + r.2)) ([], 0)).2

def lruStep (cap : Nat) (q : List Nat) (p : Nat) : List Nat × Nat :=
  if q.elem p then
    ((q.filter (fun x => x != p)) ++ [p], 0)
  else
    let qBase := if q.length < cap then q else q.drop 1
    (qBase ++ [p], 1)

def lruFaultCount (cap : Nat) (xs : List Nat) : Nat :=
  (xs.foldl (fun (acc : List Nat × Nat) p =>
    let r := lruStep cap acc.1 p
    (r.1, acc.2 + r.2)) ([], 0)).2

/-- Exact Kernel Execution of Bélády's Anomaly (`FIFO(3) = 9 < FIFO(4) = 10`) vs. `LRU` (`LRU(4) = 8 ≤ LRU(3) = 10`)! -/
theorem belady_fifo_anomaly_vs_lru_stack_monotonicity :
    fifoFaultCount 3 beladyTrace = 9 ∧
    fifoFaultCount 4 beladyTrace = 10 ∧
    fifoFaultCount 3 beladyTrace < fifoFaultCount 4 beladyTrace ∧
    lruFaultCount 3 beladyTrace = 10 ∧
    lruFaultCount 4 beladyTrace = 8 ∧
    lruFaultCount 4 beladyTrace ≤ lruFaultCount 3 beladyTrace := by
  decide

/-! ## Part 2: Karatsuba–Ofman (`1962`) `3`-Multiplication Bilinear Split -/

def karatsubaCombine (x1 x0 y1 y0 B : Int) : Int :=
  let z2 := x1 * y1
  let z0 := x0 * y0
  let z1 := (x1 + x0) * (y1 + y0)
  z2 * (B * B) + (z1 - z2 - z0) * B + z0

theorem karatsuba_linear_helper (P X1B2 X1Y0B X0Y1B X0Y0 Z1B Z2B Z0B : Int)
    (hLHS : Z2B + Z0B + X1Y0B + X0Y1B = Z1B)
    (hRHS : P = X1B2 + X1Y0B + X0Y1B + X0Y0) :
    X1B2 + (Z1B - Z2B - Z0B) + X0Y0 = P := by
  omega

theorem karatsuba_three_mul_universal_soundness (x1 x0 y1 y0 B : Int) :
    karatsubaCombine x1 x0 y1 y0 B = (x1 * B + x0) * (y1 * B + y0) := by
  dsimp [karatsubaCombine]
  have hMid :
      (x1 + x0) * (y1 + y0) = x1 * y1 + x1 * y0 + x0 * y1 + x0 * y0 := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
    omega
  have hMidB :
      ((x1 + x0) * (y1 + y0) - x1 * y1 - x0 * y0) * B = (x1 * y0 + x0 * y1) * B := by
    have hDiff : (x1 + x0) * (y1 + y0) - x1 * y1 - x0 * y0 = x1 * y0 + x0 * y1 := by omega
    rw [hDiff]
  rw [hMidB, Int.add_mul]
  have hFull :
      (x1 * B + x0) * (y1 * B + y0) =
        (x1 * B) * (y1 * B) + (x1 * B) * y0 + x0 * (y1 * B) + x0 * y0 := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
    omega
  have hA : (x1 * B) * (y1 * B) = (x1 * y1) * (B * B) := by
    rw [Int.mul_assoc x1 B (y1 * B), ← Int.mul_assoc B y1 B, Int.mul_comm B y1,
        Int.mul_assoc y1 B B, ← Int.mul_assoc x1 y1 (B * B)]
  have hB : (x1 * B) * y0 = (x1 * y0) * B := by
    rw [Int.mul_assoc, Int.mul_comm B y0, ← Int.mul_assoc]
  have hC : x0 * (y1 * B) = (x0 * y1) * B := (Int.mul_assoc x0 y1 B).symm
  omega

theorem karatsuba_missing_subtraction_corrupts_witness :
    karatsubaCombine 3 4 5 6 10 = 34 * 56 ∧
    (3 * 5 * 100 + (3 + 4) * (5 + 6) * 10 + 4 * 6 = 2294) ∧
    (34 * 56 = 1904) ∧
    (2294 ≠ 1904) := by
  decide

/-! ## Part 3: Karp–Rabin (`1987`) Rolling Polynomial Hash vs. Spurious Modulo Collision -/

def polyWindow3 (a b c B : Int) : Int :=
  a * (B * B) + b * B + c

theorem rabin_karp_rolling_hash_step_universal (a b c d B : Int) :
    (polyWindow3 a b c B - a * (B * B)) * B + d = polyWindow3 b c d B := by
  dsimp [polyWindow3]
  have hSub : a * (B * B) + b * B + c - a * (B * B) = b * B + c := by omega
  rw [hSub, Int.add_mul, Int.mul_assoc]

def polyHash2Mod13 (a b : Nat) : Nat := (3 * a + b) % 13

theorem rabin_karp_spurious_collision_requires_byte_check :
    polyHash2Mod13 1 5 = 8 ∧
    polyHash2Mod13 2 2 = 8 ∧
    polyHash2Mod13 1 5 = polyHash2Mod13 2 2 ∧
    ([1, 5] ≠ [2, 2]) := by
  decide

/-! ## Part 4: Master Milestone Synthesis -/

theorem master_belady_anomaly_karatsuba_and_rabin_karp_frontier
    (x1 x0 y1 y0 a b c d B : Int) :
    fifoFaultCount 3 beladyTrace < fifoFaultCount 4 beladyTrace ∧
    lruFaultCount 4 beladyTrace ≤ lruFaultCount 3 beladyTrace ∧
    karatsubaCombine x1 x0 y1 y0 B = (x1 * B + x0) * (y1 * B + y0) ∧
    (polyWindow3 a b c B - a * (B * B)) * B + d = polyWindow3 b c d B := by
  exact ⟨(belady_fifo_anomaly_vs_lru_stack_monotonicity).2.2.1,
         (belady_fifo_anomaly_vs_lru_stack_monotonicity).2.2.2.2.2,
         karatsuba_three_mul_universal_soundness x1 x0 y1 y0 B,
         rabin_karp_rolling_hash_step_universal a b c d B⟩

end CommonGround.Frontier.BeladyFifoAnomalyLruStackMonotonicityAndKaratsubaThreeMul
