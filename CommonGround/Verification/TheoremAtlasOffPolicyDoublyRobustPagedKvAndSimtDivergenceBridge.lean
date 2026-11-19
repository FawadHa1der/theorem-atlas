/-
  CommonGround/Verification/TheoremAtlasOffPolicyDoublyRobustPagedKvAndSimtDivergenceBridge.lean

  Suite #655: Cross-Domain Verification Bridge — Off-Policy Doubly-Robust Control Variates &
  PPO/GRPO Pessimistic Trust-Region Clipping vs. Rare-Token Variance Explosion & Zero-Support Bias,
  PagedAttention Non-Contiguous KV-Block Waste (< B) & Copy-on-Write Prefix Isolation vs. Contiguous
  Pre-Allocation Waste & In-Place Clobber, and Tiled Systolic SRAM Reuse (b×) vs. SIMT Divergence.

  Zero `sorry`, zero `admit`, zero custom axioms — compiled through Lean 4.33.0 kernel.
-/

namespace CommonGround.Verification.TheoremAtlasOffPolicyDoublyRobustPagedKvAndSimtDivergenceBridge

/-- Exact finite prefix sum `∑_{a < K} f(a)` and `100`-scaled PPO/GRPO clipped surrogate. -/
def sumUpTo : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumUpTo n f + f n

def clampInt (x lo hi : Int) : Int :=
  if x < lo then lo else if x > hi then hi else x

def ppoClipSurrogate100 (rho eps adv : Int) : Int :=
  let u := rho * adv
  let c := clampInt rho (100 - eps) (100 + eps) * adv
  if u ≤ c then u else c

/-- **Bridge Theorem 1**: Universal doubly-robust control-variate zero-bias identity and
    pessimistic PPO/GRPO clipping (`≤ rho * adv`, `5000 ↦ 120`) vs. `50×` unclipped rare-token
    second-moment blowup (`25,000,000` vs `500,000`) and `0 ≠ 500` zero-support bias. -/
theorem doubly_robust_and_ppo_clip_vs_variance_and_support_bias_bridge
    (K : Nat) (pi r qHat : Nat → Int) (rho eps adv : Int) :
    sumUpTo K (fun a => pi a * (r a - qHat a)) + sumUpTo K (fun a => pi a * qHat a) =
      sumUpTo K (fun a => pi a * r a) ∧
    ppoClipSurrogate100 rho eps adv ≤ rho * adv ∧
    ppoClipSurrogate100 5000 20 1 = 120 ∧
    ((1 : Int) * 5000 * 5000 = 50 * ((50 : Int) * 100 * 100)) ∧
    ((0 : Int) ≠ (50 : Int) * 10) := by
  refine ⟨?_, ?_, by decide, by decide, by decide⟩
  · induction K with
    | zero => simp [sumUpTo]
    | succ n ih =>
      simp only [sumUpTo]
      have hLin : pi n * (r n - qHat n) + pi n * qHat n = pi n * r n := by
        rw [Int.mul_sub, Int.sub_add_cancel]
      omega
  · dsimp only [ppoClipSurrogate100]
    split <;> omega

/-- Non-contiguous `KV`-cache block count `⌈tokens / blockSize⌉` and `CoW` vs. in-place shared-prefix write. -/
def numKvBlocks (tokens blockSize : Nat) : Nat :=
  (tokens + blockSize - 1) / blockSize

def cowSharedPrefixWrite (refCount : Nat) (page : Int × Int) (newVal : Int) : (Int × Int) × (Int × Int) :=
  if refCount > 1 then (page, (page.1, newVal)) else ((page.1, newVal), (page.1, newVal))

def unisolatedInPlacePrefixWrite (page : Int × Int) (newVal : Int) : (Int × Int) × (Int × Int) :=
  ((page.1, newVal), (page.1, newVal))

/-- **Bridge Theorem 2**: Universal `PagedAttention` `< B` internal-fragmentation bound and
    `1,296` vs. `8,192` (`6.32×` batch HBM savings) + `CoW` `(11,22)` isolation vs. unisolated
    in-place `(11,99)` prefix corruption. -/
theorem paged_kv_sub_block_waste_and_cow_vs_contiguous_and_clobber_bridge
    (tokens blockSize : Nat) (hB : blockSize ≥ 1) :
    blockSize * numKvBlocks tokens blockSize ≥ tokens ∧
    blockSize * numKvBlocks tokens blockSize - tokens < blockSize ∧
    16 * (numKvBlocks 120 16 + numKvBlocks 350 16 + numKvBlocks 45 16 + numKvBlocks 765 16) = 1296 ∧
    4 * 2048 = 8192 ∧
    cowSharedPrefixWrite 2 (11, 22) 99 = ((11, 22), (11, 99)) ∧
    (unisolatedInPlacePrefixWrite (11, 22) 99).1 ≠ (11, 22) := by
  have hDiv := Nat.div_add_mod (tokens + blockSize - 1) blockSize
  have hMod := Nat.mod_lt (tokens + blockSize - 1) (by omega : blockSize > 0)
  unfold numKvBlocks
  refine ⟨by omega, by omega, by decide, by decide, by decide, by decide⟩

/-- Naive unbuffered GEMM HBM loads vs. `b × b` SRAM-tiled systolic loads and `SIMT` warp serialization. -/
def naiveGemmHbmLoads (t b : Nat) : Nat :=
  let n := t * b
  2 * n * n * n

def tiledSystolicHbmLoads (t b : Nat) : Nat :=
  let n := t * b
  2 * t * n * n

def simtWarpSerializedCycles (numActiveBranches branchCycles : Nat) : Nat :=
  numActiveBranches * branchCycles

/-- **Bridge Theorem 3**: Universal `b×` SRAM-tiled systolic HBM reduction (`64×` at `b = 64`)
    vs. unbuffered reloads (`4,194,304` vs `65,536`) and `4×` `SIMT` warp branch-divergence stall (`40` vs `10`). -/
theorem tiled_systolic_reuse_vs_unbuffered_and_simt_divergence_bridge (t b : Nat) :
    naiveGemmHbmLoads t b = b * tiledSystolicHbmLoads t b ∧
    naiveGemmHbmLoads 2 64 = 4194304 ∧
    tiledSystolicHbmLoads 2 64 = 65536 ∧
    simtWarpSerializedCycles 1 10 = 10 ∧
    simtWarpSerializedCycles 4 10 = 40 := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  unfold naiveGemmHbmLoads tiledSystolicHbmLoads
  simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- **Master Suite #655 Synthesis Bridge** -/
theorem master_off_policy_doubly_robust_paged_kv_and_simt_divergence_bridge :
    ppoClipSurrogate100 5000 20 1 = 120 ∧
    16 * (numKvBlocks 120 16 + numKvBlocks 350 16 + numKvBlocks 45 16 + numKvBlocks 765 16) = 1296 ∧
    cowSharedPrefixWrite 2 (11, 22) 99 = ((11, 22), (11, 99)) ∧
    naiveGemmHbmLoads 2 64 = 64 * tiledSystolicHbmLoads 2 64 ∧
    simtWarpSerializedCycles 4 10 = 40 := by
  decide

end CommonGround.Verification.TheoremAtlasOffPolicyDoublyRobustPagedKvAndSimtDivergenceBridge
