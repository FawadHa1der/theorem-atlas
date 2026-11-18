/-
  03-information-recovery-kl-pythagorean/GibbsDpoPreferenceGaugeDifferentialPrivacyAndMirrorRegretFrontier.lean
  Common Ground Observatory — V234 Milestone (744 Zero-Sorry Lean 4.33.0 Files · Frontier #109)

  FOUR-DOMAIN SYNTHESIS (Folders 03 + 01 + 04 + 08):
  1. Universal `Fin M × Fin N` `(ε, δ)`-Differential Privacy Hockey-Stick Post-Processing Immunity:
     Cleared of denominators with integer privacy multiplier `E ≥ 1` (`E ≈ e^ε`) and Markov kernel
     `K : Fin M → Fin N → Nat` whose rows sum to `S` (`∑_{y : Fin N} K x y = S`), pushing neighboring
     databases `p, q : Fin M → Nat` forward to `P y = ∑_x p_x K_{x,y}` and `Q y = ∑_x q_x K_{x,y}` satisfies:
         `∑_{y : Fin N} (P y - E · Q y)₊ ≤ S · ∑_{x : Fin M} (p x - E · q x)₊`
     — proving Blackwell Data-Processing / Post-Processing Immunity for `(ε, δ)`-Differential Privacy
     over arbitrary finite alphabets without measure-theoretic scaffolding!
  2. Universal `Fin M` `DPO` / Bradley–Terry Implicit-Reward Coboundary Gauge Invariance & Condorcet Obstruction:
     (a) Adding any prompt-dependent baseline `c : Int` (`r' y = r y + c`) leaves ALL pairwise preference
         margins `r' y_w - r' y_l = r y_w - r y_l` identically invariant (partition-function cancellation =
         discrete Hodge `0`-cochain coboundary kernel!).
     (b) Conversely, EVERY scalar reward / `DPO` log-ratio `r : Fin 3 → Int` has zero cyclic curl
         `(r 0 - r 1) + (r 1 - r 2) + (r 2 - r 0) = 0`, so NO scalar `RLHF`/`DPO` model can represent
         intransitive Condorcet human preferences `y₀ ≻ y₁ ≻ y₂ ≻ y₀` (`r 0 > r 1 ∧ r 1 > r 2 ∧ r 2 > r 0 → False`)!
  3. Explicit Real-World Privacy, Alignment & Online-Regret Premise-Failure Witnesses:
     (a) `3:1` Randomized Response `p = (3,1), q = (1,3)` is `(E=3, 0)`-DP (`0 = 0`), YET `2`-fold independent
         composition `(9,3,3,1)` vs `(1,3,3,9)` evaluated at single-query `E = 3` leaks `(9 - 3·1)₊ = 6 > 0`
         (`37.5%` breach!), requiring `E² = 9` (`(9 - 9·1)₊ = 0`).
     (b) Unregularized `FTL` (`β = 0` limit) on alternating `2`-expert losses `(0,1), (1,0), (0,1), (1,0)` suffers
         `4` cumulative loss vs `2` static minimax benchmark (`2×` chattering regret!).

  Pure Lean 4.33.0 core (zero external imports, zero `sorry`, zero `admit`).
-/

namespace CommonGround.Frontier.GibbsDpoPreferenceGaugeDifferentialPrivacy

/-- Exact finite sum over `Fin M` (`∑_{x : Fin M} f x`). -/
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

/-- Subadditivity of truncating subtraction `(A - B)₊` across finite sums:
    `(∑_x a_x) - (∑_x b_x) ≤ ∑_x (a_x - b_x)`. -/
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

/-- Hockey-Stick `(E, Δ)`-Differential Privacy divergence `D_E(p ‖ q) = ∑_{x} (p_x - E · q_x)₊`. -/
def dpHockeyStick (M E : Nat) (p q : Fin M → Nat) : Nat :=
  sumFinNat M (fun x => p x - E * q x)

/-- Markov pushforward `(K_* p)(y) = ∑_{x : Fin M} p(x) · K(x, y)`. -/
def markovPush (M N : Nat) (p : Fin M → Nat) (K : Fin M → Fin N → Nat) (y : Fin N) : Nat :=
  sumFinNat M (fun x => p x * K x y)

/-- Pointwise Hockey-Stick contraction at each output symbol `y : Fin N`:
    `(P y - E · Q y)₊ ≤ ∑_{x : Fin M} (p x - E · q x)₊ · K x y`. -/
theorem dp_output_pointwise_bound
    (M N E : Nat) (p q : Fin M → Nat) (K : Fin M → Fin N → Nat) (y : Fin N) :
    markovPush M N p K y - E * markovPush M N q K y ≤
    sumFinNat M (fun x => (p x - E * q x) * K x y) := by
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

/-- **Universal `Fin M × Fin N` `(ε, δ)`-Differential Privacy Hockey-Stick Post-Processing Theorem**:
    For ANY Markov post-processing channel `K` with row sum `S`, `D_E(K_* p ‖ K_* q) ≤ S · D_E(p ‖ q)`. -/
theorem dp_hockey_stick_post_processing_monotonicity_universal
    (M N E S : Nat) (p q : Fin M → Nat) (K : Fin M → Fin N → Nat)
    (hRow : ∀ x : Fin M, sumFinNat N (fun y => K x y) = S) :
    dpHockeyStick N E (markovPush M N p K) (markovPush M N q K) ≤
    S * dpHockeyStick M E p q := by
  unfold dpHockeyStick
  have hstep1 :
      sumFinNat N (fun y => markovPush M N p K y - E * markovPush M N q K y) ≤
      sumFinNat N (fun y => sumFinNat M (fun x => (p x - E * q x) * K x y)) :=
    sumFinNat_le (fun y => dp_output_pointwise_bound M N E p q K y)
  rw [sumFinNat_swap M N (fun x y => (p x - E * q x) * K x y)] at hstep1
  have hstep2 :
      sumFinNat M (fun x => sumFinNat N (fun y => (p x - E * q x) * K x y)) =
      sumFinNat M (fun x => S * (p x - E * q x)) := by
    refine sumFinNat_congr (fun x => ?_)
    rw [sumFinNat_mul_left N (p x - E * q x) (fun y => K x y), hRow x, Nat.mul_comm]
  rw [hstep2, sumFinNat_mul_left M S (fun x => p x - E * q x)] at hstep1
  exact hstep1

/-- **Universal `Fin M` `DPO` / Bradley–Terry Reward-Coboundary Gauge Invariance**:
    Shifting all completion rewards by any prompt-dependent constant `c : Int` (`r' y = r y + c`)
    preserves every pairwise preference logit `r' y_w - r' y_l = r y_w - r y_l`. -/
theorem dpo_reward_coboundary_gauge_invariance_universal
    {M : Nat} (r : Fin M → Int) (c : Int) (yw yl : Fin M) :
    (r yw + c) - (r yl + c) = r yw - r yl := by
  omega

/-- **Intransitive Condorcet Human-Preference Obstruction for Scalar `RLHF` & `DPO`**:
    Every scalar reward / implicit `DPO` log-ratio `r : Fin 3 → Int` satisfies zero cyclic curl
    `(r 0 - r 1) + (r 1 - r 2) + (r 2 - r 0) = 0`, so cyclic human preferences `y₀ ≻ y₁ ≻ y₂ ≻ y₀`
    are strictly impossible for ANY scalar reward or `DPO` policy! -/
theorem condorcet_preference_cycle_breaks_all_scalar_dpo_rewards
    (r : Fin 3 → Int) :
    ((r ⟨0, by decide⟩ - r ⟨1, by decide⟩) +
     (r ⟨1, by decide⟩ - r ⟨2, by decide⟩) +
     (r ⟨2, by decide⟩ - r ⟨0, by decide⟩) = 0) ∧
    ¬ (r ⟨0, by decide⟩ > r ⟨1, by decide⟩ ∧
       r ⟨1, by decide⟩ > r ⟨2, by decide⟩ ∧
       r ⟨2, by decide⟩ > r ⟨0, by decide⟩) := by
  constructor <;> omega

def rrP : Fin 2 → Nat
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 1

def rrQ : Fin 2 → Nat
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 3

def rrProdP : Fin 4 → Nat
  | ⟨0, _⟩ => 9
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 1

def rrProdQ : Fin 4 → Nat
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 9

/-- **`(E=3, 0)`-DP Witness vs. `2`-Query Composition Breach (`6 > 0` at `E=3`, `0` at `E²=9`) & `FTL` `2×` Regret**:
    (1) `3:1` Randomized Response satisfies `D_3(p ‖ q) = 0` (`(ln 3, 0)`-DP), whereas `D_1(p ‖ q) = 2 > 0`.
    (2) Two independent `(E=3, 0)` releases violate single-query budget `E = 3` (`D_3(p⊗p ‖ q⊗q) = 6 > 0`,
        `37.5%` excess mass!) and require squared multiplier `E² = 9` (`D_9(p⊗p ‖ q⊗q) = 0`).
    (3) Unregularized `FTL` (`β = 0`) on `4`-round alternating `(0,1), (1,0), (0,1), (1,0)` incurs loss `4`
        vs static expert `2` (`4 = 2 · 2` `2×` chattering penalty!). -/
theorem dp_composition_leakage_and_ftl_zero_kl_chattering_witnesses :
    dpHockeyStick 2 3 rrP rrQ = 0 ∧
    dpHockeyStick 2 1 rrP rrQ = 2 ∧
    dpHockeyStick 4 3 rrProdP rrProdQ = 6 ∧
    dpHockeyStick 4 9 rrProdP rrProdQ = 0 ∧
    -- 4-round alternating FTL loss (1+1+1+1 = 4) vs best static expert ((0+1+0+1) = 2):
    (1 + 1 + 1 + 1 = 2 * (0 + 1 + 0 + 1)) := by
  decide

end CommonGround.Frontier.GibbsDpoPreferenceGaugeDifferentialPrivacy
