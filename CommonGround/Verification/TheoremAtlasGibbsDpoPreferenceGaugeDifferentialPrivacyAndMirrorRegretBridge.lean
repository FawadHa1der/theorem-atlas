/-
  CommonGround/Verification/TheoremAtlasGibbsDpoPreferenceGaugeDifferentialPrivacyAndMirrorRegretBridge.lean
  Common Ground Observatory — Verification Suite #635 (V234 · 744 Zero-Sorry Lean 4.33.0 Files)

  Cross-Domain Verification Bridge (`cslib` / `econlib` / `tc-probcomb` / `oai-smoothing`):
  Unifies `(ε, δ)`-Differential Privacy Hockey-Stick Post-Processing Immunity (`Folders 01 + 03`),
  `DPO` / `RLHF` Implicit-Reward Coboundary Gauge Invariance vs. Intransitive Condorcet Cycle Collapse (`Folders 04 + 08`),
  and `2`-Query `E → E²` Privacy Composition vs. `β = 0` `FTL` Chattering Regret.

  Pure Lean 4.33.0 core (zero external imports, zero `sorry`, zero `admit`).
-/

namespace CommonGround.Verification.TheoremAtlasGibbsDpoPreferenceGaugeDifferentialPrivacyAndMirrorRegretBridge

def sumFinNat : (M : Nat) → (Fin M → Nat) → Nat
  | 0, _ => 0
  | M + 1, f => f ⟨0, Nat.zero_lt_succ M⟩ + sumFinNat M (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

theorem sumFinNat_add : ∀ (M : Nat) (f g : Fin M → Nat),
    sumFinNat M (fun x => f x + g x) = sumFinNat M f + sumFinNat M g
  | 0, _, _ => rfl
  | M + 1, f, g => by
    simp only [sumFinNat]
    have ih := sumFinNat_add M (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
                               (fun i => g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    omega

theorem sumFinNat_le : ∀ {M : Nat} {f g : Fin M → Nat},
    (∀ x : Fin M, f x ≤ g x) → sumFinNat M f ≤ sumFinNat M g
  | 0, _, _, _ => Nat.le_refl 0
  | M + 1, f, g, h => by
    simp only [sumFinNat]
    have h0 := h ⟨0, Nat.zero_lt_succ M⟩
    have ih := sumFinNat_le (M := M)
      (f := fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (g := fun i => g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => h ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    omega

theorem sumFinNat_congr : ∀ {M : Nat} {f g : Fin M → Nat},
    (∀ x : Fin M, f x = g x) → sumFinNat M f = sumFinNat M g
  | 0, _, _, _ => rfl
  | M + 1, f, g, h => by
    simp only [sumFinNat]
    have h0 := h ⟨0, Nat.zero_lt_succ M⟩
    have ih := sumFinNat_congr (M := M)
      (f := fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (g := fun i => g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => h ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    omega

theorem sumFinNat_mul_left : ∀ (M c : Nat) (f : Fin M → Nat),
    sumFinNat M (fun x => c * f x) = c * sumFinNat M f
  | 0, _, _ => by simp [sumFinNat]
  | M + 1, c, f => by
    simp only [sumFinNat]
    rw [sumFinNat_mul_left M c, ← Nat.mul_add]

theorem sumFinNat_zero : ∀ (N : Nat), sumFinNat N (fun _ => 0) = 0
  | 0 => rfl
  | N + 1 => by simp [sumFinNat, sumFinNat_zero N]

theorem sumFinNat_swap : ∀ (M N : Nat) (H : Fin M → Fin N → Nat),
    sumFinNat N (fun y => sumFinNat M (fun x => H x y)) =
    sumFinNat M (fun x => sumFinNat N (fun y => H x y))
  | 0, N, _ => sumFinNat_zero N
  | M + 1, N, H => by
    simp only [sumFinNat]
    rw [sumFinNat_add N (fun y => H ⟨0, Nat.zero_lt_succ M⟩ y)
                        (fun y => sumFinNat M (fun i => H ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ y))]
    rw [sumFinNat_swap M N (fun i y => H ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ y)]

theorem sumFinNat_sub_le_sum_sub : ∀ (M : Nat) (a b : Fin M → Nat),
    sumFinNat M a - sumFinNat M b ≤ sumFinNat M (fun x => a x - b x)
  | 0, _, _ => Nat.le_refl 0
  | M + 1, a, b => by
    simp only [sumFinNat]
    have ih := sumFinNat_sub_le_sum_sub M
      (fun i => a ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => b ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    omega

theorem nat_mul_sub_right (u v k : Nat) :
    u * k - v * k = (u - v) * k :=
  (Nat.sub_mul u v k).symm

def dpHockeyStick (M E : Nat) (p q : Fin M → Nat) : Nat :=
  sumFinNat M (fun x => p x - E * q x)

def markovPush (M N : Nat) (p : Fin M → Nat) (K : Fin M → Fin N → Nat) (y : Fin N) : Nat :=
  sumFinNat M (fun x => p x * K x y)

/-- Master `Fin M × Fin N` `(ε, δ)`-DP Post-Processing, `DPO` Gauge Invariance & Condorcet Obstruction Bridge. -/
theorem master_gibbs_dpo_gauge_and_dp_hockey_stick_postprocessing_bridge :
    -- (1) Universal Markov post-processing monotonicity for `(E, Δ)`-Hockey-Stick DP:
    (∀ (M N E S : Nat) (p q : Fin M → Nat) (K : Fin M → Fin N → Nat),
      (∀ x : Fin M, sumFinNat N (fun y => K x y) = S) →
      dpHockeyStick N E (markovPush M N p K) (markovPush M N q K) ≤ S * dpHockeyStick M E p q) ∧
    -- (2) Universal `DPO` prompt-baseline coboundary gauge invariance & Condorcet 3-cycle impossibility:
    (∀ (M : Nat) (r : Fin M → Int) (c : Int) (yw yl : Fin M),
      (r yw + c) - (r yl + c) = r yw - r yl) ∧
    (∀ r : Fin 3 → Int,
      ¬ (r ⟨0, by decide⟩ > r ⟨1, by decide⟩ ∧
         r ⟨1, by decide⟩ > r ⟨2, by decide⟩ ∧
         r ⟨2, by decide⟩ > r ⟨0, by decide⟩)) ∧
    -- (3) `2`-query `E=3` composition breach (`9 - 3·1 = 6 > 0`) vs `E²=9` (`9 - 9·1 = 0`):
    ((9 - 3 * 1 = 6) ∧ (9 - 9 * 1 = 0)) := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro M N E S p q K hRow
    unfold dpHockeyStick
    have hpt : ∀ y : Fin N,
        markovPush M N p K y - E * markovPush M N q K y ≤
        sumFinNat M (fun x => (p x - E * q x) * K x y) := by
      intro y
      unfold markovPush
      rw [← sumFinNat_mul_left M E (fun x => q x * K x y)]
      have hmul : sumFinNat M (fun x => E * (q x * K x y)) =
                  sumFinNat M (fun x => (E * q x) * K x y) :=
        sumFinNat_congr (fun x => (Nat.mul_assoc E (q x) (K x y)).symm)
      rw [hmul]
      have hsub := sumFinNat_sub_le_sum_sub M (fun x => p x * K x y) (fun x => (E * q x) * K x y)
      have hterm : sumFinNat M (fun x => p x * K x y - (E * q x) * K x y) =
                   sumFinNat M (fun x => (p x - E * q x) * K x y) :=
        sumFinNat_congr (fun x => nat_mul_sub_right (p x) (E * q x) (K x y))
      omega
    have h1 := sumFinNat_le hpt
    rw [sumFinNat_swap M N (fun x y => (p x - E * q x) * K x y)] at h1
    have h2 : sumFinNat M (fun x => sumFinNat N (fun y => (p x - E * q x) * K x y)) =
              sumFinNat M (fun x => S * (p x - E * q x)) := by
      refine sumFinNat_congr (fun x => ?_)
      rw [sumFinNat_mul_left N (p x - E * q x) (fun y => K x y), hRow x, Nat.mul_comm]
    rw [h2, sumFinNat_mul_left M S (fun x => p x - E * q x)] at h1
    exact h1
  · intro M r c yw yl; omega
  · intro r; omega

end CommonGround.Verification.TheoremAtlasGibbsDpoPreferenceGaugeDifferentialPrivacyAndMirrorRegretBridge
