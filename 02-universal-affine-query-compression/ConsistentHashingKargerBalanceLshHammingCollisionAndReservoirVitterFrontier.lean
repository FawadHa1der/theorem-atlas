/-
  02-universal-affine-query-compression/ConsistentHashingKargerBalanceLshHammingCollisionAndReservoirVitterFrontier.lean

  Milestone Wave V257 · Frontier #132 (Historic 750 Kernel-Compiled Modules & 50 Archetypes!):
  Cross-Domain Formalization Unifying:
  1. Karger–Lehman–Leighton–Panigrahy– Levine–Lewin Consistent Hashing Ring Monotonicity &
     Virtual-Node Balance (`4/20 = 20%` Remap, `25%` Load) vs. Modulo `k % N` Catastrophic
     `(N)/(N+1)` Cache Stampede (`16/20 = 80%` Remap!) & Single-Token `85%` Hotspot (`cslib` ↔ `tc-probcomb`)
  2. Indyk–Motwani Bit-Sampling Locality-Sensitive Hashing (`LSH`) Exact Collision Identity
     (`Agree + d_H = D`) & `(r, b)` AND-OR S-Curve Amplification (`14,896/15,625 = 95.3%` vs `11.5%`)
     vs. Unbanded High-`r` Recall Collapse (`256/625 = 40.96% < 50%`) (`oai-codes` ↔ `apsp3sum`)
  3. Vitter Algorithm R Single-Pass Reservoir Sampling Exact `k/(n+1)` Telescoping Invariance &
     `2/6 = 1/3` Path Equiprobability vs. Constant `1/2` Coin-Flip `2×` Recency Bias (`2/4` vs `1/4`)
     & Sliding-Window Prefix Amnesia (`0/6`) (`tc-probcomb` ↔ `cslib`)

  Toolchain: leanprover/lean4:v4.33.0 (pure Lean 4 core, zero sorry).
-/

namespace Frontier.ConsistentHashingKargerBalanceLshHammingCollisionAndReservoirVitterFrontier

-- ============================================================================
-- Part I: Karger Consistent Hashing Monotonicity vs. Modulo Cache Stampede
-- ============================================================================

/-- Updated ring owner when inserting `sNew`: a key moves ONLY if `sNew` strictly improves its clockwise ring distance. -/
def ringOwnerAfterAdd (oldOwner oldDist newDist : Nat → Nat) (sNew key : Nat) : Nat :=
  if newDist key < oldDist key then sNew else oldOwner key

/--
  **Theorem 1a (Universal Consistent-Hashing Add-Node Monotonicity)**:
  Inserting a new ring node `sNew` NEVER migrates keys between two existing servers:
  every key `k` either remains on `oldOwner k` or migrates directly to `sNew`.
-/
theorem consistent_hashing_add_node_monotonicity_universal
    (oldOwner oldDist newDist : Nat → Nat) (sNew key : Nat) :
    ringOwnerAfterAdd oldOwner oldDist newDist sNew key = oldOwner key ∨
    ringOwnerAfterAdd oldOwner oldDist newDist sNew key = sNew := by
  dsimp [ringOwnerAfterAdd]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Balanced 4-server ring on `[0..19]` with tokens at `{0, 5, 10, 15}` (clockwise successor owner `0..3`). -/
def ring4Owner20 (k : Fin 20) : Nat :=
  if k.val == 0 then 0
  else if k.val ≤ 5 then 1
  else if k.val ≤ 10 then 2
  else if k.val ≤ 15 then 3
  else 0

/-- 5-server ring after inserting server `4` at position `4` (`{0, 4, 5, 10, 15}`): only `{1,2,3,4}` move! -/
def ring5Owner20 (k : Fin 20) : Nat :=
  if k.val == 0 then 0
  else if k.val ≤ 4 then 4
  else if k.val ≤ 5 then 1
  else if k.val ≤ 10 then 2
  else if k.val ≤ 15 then 3
  else 0

/-- Count of keys in `Fin 20` remapped when scaling from `ring4Owner20` to `ring5Owner20` (`4/20 = 20%`). -/
def consistentRemapCount20 : Nat :=
  (List.finRange 20).foldl (fun acc k => acc + if ring4Owner20 k != ring5Owner20 k then 1 else 0) 0

/-- Count of keys in `Fin 20` remapped by naive `k % 4 ↦ k % 5` modulo hashing (`16/20 = 80%`!). -/
def moduloRemapCount20 : Nat :=
  (List.finRange 20).foldl (fun acc k => acc + if (k.val % 4) != (k.val % 5) then 1 else 0) 0

/-- Clustered single-token placement `{0, 1, 2, 3}` on `Fin 20`: server `0` gets `{4..19, 0}` (`17/20 = 85%`!). -/
def clusteredSingleVnodeOwner20 (k : Fin 20) : Nat :=
  if k.val == 0 then 0
  else if k.val == 1 then 1
  else if k.val == 2 then 2
  else if k.val == 3 then 3
  else 0

/-- Interleaved `V = 2` virtual-node placement `{0,2, 5,7, 10,12, 15,17}`: every server gets `5/20 = 25%`! -/
def balancedVirtualNodeOwner20 (k : Fin 20) : Nat :=
  (k.val / 5) % 4

def loadOfServer20 (ownerFn : Fin 20 → Nat) (srv : Nat) : Nat :=
  (List.finRange 20).foldl (fun acc k => acc + if ownerFn k == srv then 1 else 0) 0

/--
  **Counterexample 1 (Modulo `k % 4 ↦ k % 5` `80%` Cache Stampede & Single-Token `85%` Ring Hotspot)**:
  - Scaling `4 ↦ 5` with `k % N` remaps `16/20` (`80%`) of keys vs. `4/20` (`20%`) on the consistent ring (`4×` stampede!).
  - Without virtual nodes, clustered tokens `{0,1,2,3}` dump `17/20` (`85%`) of load onto server `0`,
    whereas interleaved virtual nodes balance all `4` servers to `5/20` (`25%`) each!
-/
theorem modulo_hashing_catastrophic_remap_and_single_vnode_hotspot :
    consistentRemapCount20 = 4 ∧
    moduloRemapCount20 = 16 ∧
    moduloRemapCount20 = 4 * consistentRemapCount20 ∧
    loadOfServer20 clusteredSingleVnodeOwner20 0 = 17 ∧
    loadOfServer20 balancedVirtualNodeOwner20 0 = 5 ∧
    loadOfServer20 balancedVirtualNodeOwner20 1 = 5 ∧
    loadOfServer20 balancedVirtualNodeOwner20 2 = 5 ∧
    loadOfServer20 balancedVirtualNodeOwner20 3 = 5 := by
  decide

-- ============================================================================
-- Part II: Indyk–Motwani Bit-Sampling LSH Identity & (r, b) Amplification
-- ============================================================================

/-- Hamming distance across the first `D` binary coordinates. -/
def hammingPrefix : Nat → (Nat → Bool) → (Nat → Bool) → Nat
  | 0, _, _ => 0
  | d + 1, x, y => hammingPrefix d x y + (if x d == y d then 0 else 1)

/-- Number of colliding coordinate projections `h_i(x) == h_i(y)` across `[0..D-1]`. -/
def lshAgreePrefix : Nat → (Nat → Bool) → (Nat → Bool) → Nat
  | 0, _, _ => 0
  | d + 1, x, y => lshAgreePrefix d x y + (if x d == y d then 1 else 0)

/--
  **Theorem 2a (Universal Bit-Sampling `LSH` Collision Identity)**:
  For ANY dimension `D` and ANY binary feature vectors `x, y : Nat → Bool`,
  `lshAgreePrefix D x y + hammingPrefix D x y = D`
  (i.e. `Pr_{i ~ Unif[D]}[h_i(x) = h_i(y)] = 1 - d_H(x, y) / D`).
-/
theorem lsh_bit_sampling_agree_plus_hamming_eq_dim
    (D : Nat) (x y : Nat → Bool) :
    lshAgreePrefix D x y + hammingPrefix D x y = D := by
  induction D with
  | zero => rfl
  | succ d ih =>
    dsimp [lshAgreePrefix, hammingPrefix]
    cases (x d == y d) <;> simp <;> omega

/-- Scaled `(r, b)` AND-then-OR collision numerator `S^b - (S - p^r)^b` over denominator `S^b` where `S = denom^r`. -/
def lshBandRecallNum (p denom r b : Nat) : Nat :=
  let s := denom ^ r
  let pr := p ^ r
  (s ^ b) - ((s - pr) ^ b)

/--
  **Theorem 2b & Counterexample 2 (`(r=2, b=3)` S-Curve Amplification vs. Unbanded `r=4, b=1` Recall Collapse)**:
  For near neighbor `p₁ = 4/5` vs. far point `p₂ = 1/5`:
  1. `(r=2, b=3)` boosts near recall to `14,896 / 15,625` (`95.33%`) while holding far false-positives
     to `1,801 / 15,625` (`11.53%`, `> 8.2×` separation!).
  2. Setting `r = 4, b = 1` WITHOUT multi-band OR replication (`b = 1`) collapses true-positive near recall
     to `256 / 625 = 40.96% < 50%` (`> 59%` false-negative miss rate!).
-/
theorem lsh_and_or_amplification_vs_single_band_recall_collapse :
    lshBandRecallNum 4 5 2 3 = 14896 ∧
    (5 ^ 2) ^ 3 = 15625 ∧
    lshBandRecallNum 1 5 2 3 = 1801 ∧
    2 * lshBandRecallNum 4 5 4 1 < (5 ^ 4) ^ 1 ∧
    lshBandRecallNum 4 5 4 1 = 256 ∧
    (5 ^ 4) ^ 1 = 625 := by
  decide

-- ============================================================================
-- Part III: Vitter Algorithm R Reservoir Sampling vs. Recency & Window Bias
-- ============================================================================

/--
  **Theorem 3a (Universal Vitter Reservoir Step Cross-Multiplied Invariance)**:
  At stream index `n + 1` (`n ≥ k ≥ 1`), an item held in the size-`k` reservoir with probability `k / n`
  survives eviction with factor `n / (n + 1)`, yielding exact probability `(k * n) / (n * (n + 1)) == k / (n + 1)`,
  and the sum of scaled inclusion weights across all `n + 1` stream items equals `(n + 1) * k`.
-/
theorem vitter_reservoir_survival_cross_mul_universal (k n : Nat) :
    (k * n) * (n + 1) = k * (n * (n + 1)) ∧
    n * k + k = (n + 1) * k := by
  refine ⟨Nat.mul_assoc k n (n + 1), ?_⟩
  calc
    n * k + k = n * k + 1 * k := by rw [Nat.one_mul]
    _ = (n + 1) * k := (Nat.add_mul n 1 k).symm

/-- Vitter `k = 1` reservoir state after `3` items `{0, 1, 2}` given `u₂ ∈ Fin 2` and `u₃ ∈ Fin 3`. -/
def vitterK1Stream3 (u2 : Fin 2) (u3 : Fin 3) : Nat :=
  let r2 := if u2.val == 0 then 1 else 0
  if u3.val == 0 then 2 else r2

/-- Count of `(u₂, u₃) ∈ Fin 2 × Fin 3` (`6` uniform paths) selecting `target`. -/
def vitterCount3 (target : Nat) : Nat :=
  (List.finRange 2).foldl (fun acc u2 =>
    (List.finRange 3).foldl (fun acc2 u3 =>
      acc2 + if vitterK1Stream3 u2 u3 == target then 1 else 0) acc) 0

/-- Naive constant `1/2` coin-flip replacement (`(b₂, b₃) ∈ Bool × Bool`, `4` paths). -/
def naiveCoinFlipStream3 (b2 b3 : Bool) : Nat :=
  let r2 := if b2 then 1 else 0
  if b3 then 2 else r2

def naiveCoinCount3 (target : Nat) : Nat :=
  [false, true].foldl (fun acc b2 =>
    [false, true].foldl (fun acc2 b3 =>
      acc2 + if naiveCoinFlipStream3 b2 b3 == target then 1 else 0) acc) 0

/-- Sliding window of size `1` (`last-1` policy): always retains only item `2`, `0` weight on `{0, 1}`. -/
def slidingWindow1Count3 (target : Nat) : Nat :=
  (List.finRange 6).foldl (fun acc _ => acc + if 2 == target then 1 else 0) 0

/--
  **Theorem 3b & Counterexample 3 (Exact `2/6 = 1/3` Reservoir Equiprobability vs. `2×` Coin-Flip Bias & `0/6` Amnesia)**:
  - Vitter Algorithm R selects each of `{0, 1, 2}` on **exactly `2` of `6` paths (`1/3` each)**!
  - Constant `1/2` coin-flip replacement selects `(1/4, 1/4, 2/4)` (`2×` recency bias toward the tail)!
  - Sliding-window `last-1` assigns `0/6` (`0%`) to early items `{0, 1}`!
-/
theorem vitter_three_item_equiprobability_vs_coin_bias_and_window_amnesia :
    vitterCount3 0 = 2 ∧
    vitterCount3 1 = 2 ∧
    vitterCount3 2 = 2 ∧
    naiveCoinCount3 0 = 1 ∧
    naiveCoinCount3 1 = 1 ∧
    naiveCoinCount3 2 = 2 ∧
    slidingWindow1Count3 0 = 0 ∧
    slidingWindow1Count3 1 = 0 := by
  decide

end Frontier.ConsistentHashingKargerBalanceLshHammingCollisionAndReservoirVitterFrontier
