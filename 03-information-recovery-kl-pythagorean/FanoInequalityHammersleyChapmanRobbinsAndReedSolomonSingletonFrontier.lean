/-
  03-information-recovery-kl-pythagorean/FanoInequalityHammersleyChapmanRobbinsAndReedSolomonSingletonFrontier.lean

  Frontier #105 (`V230`, `0` imports, `0` sorry):
  Cross-Domain Unification of Information-Theoretic Estimation, Hypothesis-Testing Converses,
  and Algebraic Maximum-Distance-Separable (`MDS`) Error-Correcting Codes:
  1. Universal `Fin M` Weighted Cauchy–Schwarz & Discrete Cramér–Rao / Hammersley–Chapman–Robbins (`HCR`)
     Variance Bound (`⟨u, s⟩_p² ≤ ⟨u, u⟩_p · ⟨s, s⟩_p` + score centering invariance) vs. Zero-Score
     Non-Identifiable Singularity (`s = 0 ⟹ ⟨u, s⟩_p = 0 ≠ 1`).
  2. Universal `Fin K` MAP / Fano Confusion Ceiling (`∑_y W(dec y, y) ≤ ∑_y U_y`) & Exhaustive `4`-Message
     `1`-Bit Bottleneck (`≤ 2 / 4` Correct Across All `256` Encoder-Decoder Pairs vs. `4 / 4` on `2` Bits).
  3. Universal `Fin N` Singleton `MDS` Bound via Prefix-Puncturing Injectivity (`d_H ≥ d ⟹ π_{N+1-d}` Injective)
     & Explicit `[4, 2, 3]₅` Polynomial Reed–Solomon Code Attaining `d = N - k + 1` Tight.
  4. Universal `Fin N` Unique Bounded-Distance Decoding (`2 t < d ⟹` Unique Ball Center) vs. Half-Distance
     Ambiguity Tie (`2 t = d` on `[2, 1, 2]₂` Parity Code at `r = (1, 0)`).
-/

namespace CommonGround.Frontier.FanoCramerRaoAndReedSolomonSingleton

/-! ## Section 1: Universal `Fin M` Weighted Cauchy–Schwarz & Discrete Cramér–Rao Bound -/

theorem sq_nonneg (z : Int) : 0 ≤ z * z := by
  by_cases h : 0 ≤ z
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -z := by omega
    have hp : 0 ≤ (-z) * (-z) := Int.mul_nonneg hn hn
    have heq : (-z) * (-z) = z * z := Int.neg_mul_neg z z
    omega

def sumFin : (M : Nat) → (Fin M → Int) → Int
  | 0, _ => 0
  | n + 1, f =>
      sumFin n (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) + f ⟨n, Nat.lt_succ_self n⟩

theorem sumFin_add (M : Nat) (f g : Fin M → Int) :
    sumFin M (fun i => f i + g i) = sumFin M f + sumFin M g := by
  induction M with
  | zero => rfl
  | succ n ih =>
      simp [sumFin, ih]
      omega

theorem sumFin_sub (M : Nat) (f g : Fin M → Int) :
    sumFin M (fun i => f i - g i) = sumFin M f - sumFin M g := by
  induction M with
  | zero => rfl
  | succ n ih =>
      simp [sumFin, ih]
      omega

theorem sumFin_scale_left (M : Nat) (c : Int) (f : Fin M → Int) :
    sumFin M (fun i => c * f i) = c * sumFin M f := by
  induction M with
  | zero => simp [sumFin]
  | succ n ih =>
      simp [sumFin, ih, Int.mul_add]

theorem sumFin_nonneg (M : Nat) :
    ∀ (f : Fin M → Int), (∀ i : Fin M, 0 ≤ f i) → 0 ≤ sumFin M f := by
  induction M with
  | zero =>
      intro f _
      simp [sumFin]
  | succ n ih =>
      intro f hf
      have h1 : 0 ≤ sumFin n (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) :=
        ih (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) (fun i => hf ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
      have h2 : 0 ≤ f ⟨n, Nat.lt_succ_self n⟩ := hf ⟨n, Nat.lt_succ_self n⟩
      simp [sumFin]
      omega

theorem sumFin_eq_zero_of_nonneg (M : Nat) :
    ∀ (f : Fin M → Int), (∀ i : Fin M, 0 ≤ f i) → sumFin M f = 0 → ∀ i : Fin M, f i = 0 := by
  induction M with
  | zero =>
      intro _ _ _ i
      exact Fin.elim0 i
  | succ n ih =>
      intro f hf hz
      have hsub : 0 ≤ sumFin n (fun j => f ⟨j.1, Nat.lt_succ_of_lt j.2⟩) :=
        sumFin_nonneg n _ (fun j => hf ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
      have hlast : 0 ≤ f ⟨n, Nat.lt_succ_self n⟩ := hf ⟨n, Nat.lt_succ_self n⟩
      simp [sumFin] at hz
      have hsub0 : sumFin n (fun j => f ⟨j.1, Nat.lt_succ_of_lt j.2⟩) = 0 := by omega
      have hlast0 : f ⟨n, Nat.lt_succ_self n⟩ = 0 := by omega
      intro i
      by_cases hi : i.1 < n
      · have hprev := ih (fun j => f ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
          (fun j => hf ⟨j.1, Nat.lt_succ_of_lt j.2⟩) hsub0 ⟨i.1, hi⟩
        have heqi : (⟨i.1, Nat.lt_succ_of_lt hi⟩ : Fin (n + 1)) = i := Fin.ext rfl
        rw [← heqi]
        exact hprev
      · have heqn : i.1 = n := by omega
        have heqi : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext heqn
        rw [heqi]
        exact hlast0

def weightedInner (M : Nat) (p u v : Fin M → Int) : Int :=
  sumFin M (fun x => p x * (u x * v x))

/-- Score centering invariance: whenever the score function `s` has zero mean under `p`
    (`∑_x p_x s_x = 0`), shifting an estimator `T` by any constant baseline `mu` leaves
    `⟨T - mu, s⟩_p = ⟨T, s⟩_p` invariant. -/
theorem score_centering_invariance (M : Nat) (p T s : Fin M → Int) (mu : Int)
    (hmean : sumFin M (fun x => p x * s x) = 0) :
    weightedInner M p (fun x => T x - mu) s = weightedInner M p T s := by
  unfold weightedInner
  have hpt : (fun x : Fin M => p x * ((T x - mu) * s x)) =
      (fun x : Fin M => p x * (T x * s x) - mu * (p x * s x)) := by
    funext x
    rw [Int.sub_mul, Int.mul_sub]
    have : p x * (mu * s x) = mu * (p x * s x) := by
      rw [← Int.mul_assoc, Int.mul_comm (p x) mu, Int.mul_assoc]
    rw [this]
  rw [hpt, sumFin_sub, sumFin_scale_left, hmean]
  omega

theorem weighted_quad_pointwise (px ux sx A B : Int) :
    px * ((A * ux - B * sx) * (A * ux - B * sx)) =
      (A * A) * (px * (ux * ux)) - (2 * A * B) * (px * (ux * sx)) + (B * B) * (px * (sx * sx)) := by
  have hexp : (A * ux - B * sx) * (A * ux - B * sx) =
      (A * A) * (ux * ux) - (A * B) * (ux * sx) - (A * B) * (ux * sx) + (B * B) * (sx * sx) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have h1 : (A * ux) * (A * ux) = (A * A) * (ux * ux) := by
      rw [Int.mul_assoc, Int.mul_left_comm ux A ux, ← Int.mul_assoc]
    have h2 : (B * sx) * (B * sx) = (B * B) * (sx * sx) := by
      rw [Int.mul_assoc, Int.mul_left_comm sx B sx, ← Int.mul_assoc]
    have h3 : (A * ux) * (B * sx) = (A * B) * (ux * sx) := by
      rw [Int.mul_assoc, Int.mul_left_comm ux B sx, ← Int.mul_assoc]
    have h4 : (B * sx) * (A * ux) = (A * B) * (ux * sx) := by
      rw [Int.mul_assoc, Int.mul_left_comm sx A ux, ← Int.mul_assoc, Int.mul_comm B A, Int.mul_comm sx ux]
    rw [h1, h2, h3, h4]
    omega
  rw [hexp, Int.mul_add, Int.mul_sub, Int.mul_sub]
  have p1 : px * ((A * A) * (ux * ux)) = (A * A) * (px * (ux * ux)) := by
    rw [← Int.mul_assoc, Int.mul_comm px (A * A), Int.mul_assoc]
  have p2 : px * ((A * B) * (ux * sx)) = (A * B) * (px * (ux * sx)) := by
    rw [← Int.mul_assoc, Int.mul_comm px (A * B), Int.mul_assoc]
  have p3 : px * ((B * B) * (sx * sx)) = (B * B) * (px * (sx * sx)) := by
    rw [← Int.mul_assoc, Int.mul_comm px (B * B), Int.mul_assoc]
  rw [p1, p2, p3]
  have p2double : (2 * A * B) * (px * (ux * sx)) =
      (A * B) * (px * (ux * sx)) + (A * B) * (px * (ux * sx)) := by
    rw [Int.mul_assoc 2 A B, Int.two_mul, Int.add_mul]
  rw [p2double]
  omega

/-- Universal `Fin M` Weighted Cauchy–Schwarz / Discrete Cramér–Rao Lower Bound:
    For any sample size `M`, non-negative weights `p ≥ 0`, centered estimator `u`, and score `s`,
    `⟨u, s⟩_p² ≤ ⟨u, u⟩_p · ⟨s, s⟩_p` (`Sensitivity² ≤ Variance · FisherInformation`). -/
theorem weighted_cauchy_schwarz_cramer_rao_universal
    (M : Nat) (p u s : Fin M → Int) (hp : ∀ x : Fin M, 0 ≤ p x) :
    weightedInner M p u s * weightedInner M p u s ≤
      weightedInner M p u u * weightedInner M p s s := by
  let A := weightedInner M p s s
  let B := weightedInner M p u s
  let C := weightedInner M p u u
  have hA_term_nn : ∀ x : Fin M, 0 ≤ p x * (s x * s x) :=
    fun x => Int.mul_nonneg (hp x) (sq_nonneg (s x))
  have hA_nn : 0 ≤ A := sumFin_nonneg M _ hA_term_nn
  by_cases hA0 : A = 0
  · have hzero := sumFin_eq_zero_of_nonneg M _ hA_term_nn hA0
    have hB_terms : ∀ x : Fin M, p x * (u x * s x) = 0 := by
      intro x
      have hx := hzero x
      cases Int.mul_eq_zero.mp hx with
      | inl hpx => simp [hpx]
      | inr hs2 =>
          cases Int.mul_eq_zero.mp hs2 with
          | inl hsx => simp [hsx]
          | inr hsx => simp [hsx]
    have hB_fn : (fun x : Fin M => p x * (u x * s x)) = (fun _ => 0) := by
      funext x
      exact hB_terms x
    have hB0 : B = 0 := by
      change sumFin M (fun x => p x * (u x * s x)) = 0
      rw [hB_fn]
      have hz : sumFin M (fun _ => (0 : Int)) = sumFin M (fun x => (0 : Int) * p x) := by
        simp
      rw [hz, sumFin_scale_left]
      simp
    change B * B ≤ C * A
    rw [hB0, hA0]
    omega
  · have hA_pos : 0 < A := by omega
    have hQ_nn : 0 ≤ sumFin M (fun x => p x * ((A * u x - B * s x) * (A * u x - B * s x))) :=
      sumFin_nonneg M _ (fun x => Int.mul_nonneg (hp x) (sq_nonneg (A * u x - B * s x)))
    have hQ_eq :
        (fun x : Fin M => p x * ((A * u x - B * s x) * (A * u x - B * s x))) =
        (fun x : Fin M =>
          (A * A) * (p x * (u x * u x)) - (2 * A * B) * (p x * (u x * s x)) + (B * B) * (p x * (s x * s x))) := by
      funext x
      exact weighted_quad_pointwise (p x) (u x) (s x) A B
    rw [hQ_eq, sumFin_add, sumFin_sub, sumFin_scale_left, sumFin_scale_left, sumFin_scale_left] at hQ_nn
    change 0 ≤ (A * A) * C - (2 * A * B) * B + (B * B) * A at hQ_nn
    have hsimp : (A * A) * C - (2 * A * B) * B + (B * B) * A = A * (A * C - B * B) := by
      have t1 : (A * A) * C = A * (A * C) := Int.mul_assoc A A C
      have t2 : (2 * A * B) * B = A * (B * B) + A * (B * B) := by
        rw [Int.mul_assoc 2 A B, Int.two_mul, Int.add_mul, Int.mul_assoc]
      have t3 : (B * B) * A = A * (B * B) := Int.mul_comm (B * B) A
      rw [t1, t2, t3, Int.mul_sub]
      omega
    rw [hsimp] at hQ_nn
    change B * B ≤ C * A
    by_cases hle : B * B ≤ C * A
    · exact hle
    · have hneg_pos : 0 < B * B - A * C := by
        rw [Int.mul_comm C A] at hle
        omega
      have hprod_pos : 0 < A * (B * B - A * C) := Int.mul_pos hA_pos hneg_pos
      have hsum0 : A * (A * C - B * B) + A * (B * B - A * C) = 0 := by
        rw [← Int.mul_add]
        have : (A * C - B * B) + (B * B - A * C) = 0 := by omega
        rw [this]
        simp
      omega

/-- Premise-Failure Counterexample (Non-Identifiable Zero-Score Model):
    When `s = 0` (`I_Fisher = 0`), NO estimator `u : Fin M → Int` can achieve unit local
    sensitivity `⟨u, s⟩_p = 1` (`0 ≠ 1`), whereas on an identifiable asymmetric Bernoulli
    channel `p = (1, 1), s = (1, -1)` (`I = 2`), `u = (1, -1)` attains equality `2² = 2 · 2`! -/
theorem zero_score_unidentifiable_vs_bernoulli_cramer_rao_attainment :
    (∀ M : Nat, ∀ p u : Fin M → Int, weightedInner M p u (fun _ => 0) = 0 ∧ weightedInner M p u (fun _ => 0) ≠ 1) ∧
    (let p2 : Fin 2 → Int := fun _ => 1
     let s2 : Fin 2 → Int := fun i => if i.1 = 0 then 1 else -1
     weightedInner 2 p2 s2 s2 = 2 ∧
     weightedInner 2 p2 s2 s2 * weightedInner 2 p2 s2 s2 =
       weightedInner 2 p2 s2 s2 * weightedInner 2 p2 s2 s2) := by
  refine ⟨?_, by decide⟩
  intro M p u
  unfold weightedInner
  have hfn : (fun x : Fin M => p x * (u x * 0)) = (fun x : Fin M => (0 : Int) * p x) := by
    funext x
    simp
  rw [hfn, sumFin_scale_left]
  simp

/-! ## Section 2: Universal `Fin K` MAP / Fano Ceiling & `4`-Message `1`-Bit Bottleneck -/

def sumFinNat : (K : Nat) → (Fin K → Nat) → Nat
  | 0, _ => 0
  | n + 1, f =>
      sumFinNat n (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩) + f ⟨n, Nat.lt_succ_self n⟩

theorem sumFinNat_le (K : Nat) :
    ∀ (f g : Fin K → Nat), (∀ y : Fin K, f y ≤ g y) → sumFinNat K f ≤ sumFinNat K g := by
  induction K with
  | zero =>
      intro f g _
      simp [sumFinNat]
  | succ n ih =>
      intro f g hfg
      have h1 := ih (fun i => f ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
                    (fun i => g ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
                    (fun i => hfg ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
      have h2 := hfg ⟨n, Nat.lt_succ_self n⟩
      simp [sumFinNat]
      omega

/-- Universal MAP / Fano Confusion Ceiling:
    For any `M` messages, `K` channel outputs, joint count matrix `W : Fin M → Fin K → Nat`,
    and columnwise MAP upper envelope `U` (`∀ x y, W x y ≤ U y`), EVERY deterministic decoder
    `dec : Fin K → Fin M` achieves at most `∑_y U_y` correct recoveries! -/
theorem map_decoder_optimality_and_fano_ceiling
    (M K : Nat) (W : Fin M → Fin K → Nat) (U : Fin K → Nat)
    (hU : ∀ (x : Fin M) (y : Fin K), W x y ≤ U y)
    (dec : Fin K → Fin M) :
    sumFinNat K (fun y => W (dec y) y) ≤ sumFinNat K U :=
  sumFinNat_le K _ _ (fun y => hU (dec y) y)

def oneBitFourMsgCorrect (enc : Fin 4 → Fin 2) (dec : Fin 2 → Fin 4) : Nat :=
  (if (dec (enc ⟨0, by decide⟩)).1 = 0 then 1 else 0) +
  (if (dec (enc ⟨1, by decide⟩)).1 = 1 then 1 else 0) +
  (if (dec (enc ⟨2, by decide⟩)).1 = 2 then 1 else 0) +
  (if (dec (enc ⟨3, by decide⟩)).1 = 3 then 1 else 0)

theorem fin2_cases (z : Fin 2) : z = ⟨0, by decide⟩ ∨ z = ⟨1, by decide⟩ := by
  rcases z with ⟨v, hv⟩
  match v with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr rfl
  | n + 2 => omega

/-- Fano `1`-Bit Bottleneck Across All `256` Encoder-Decoder Pairs:
    Compressing `4` equiprobable messages (`2` bits of entropy) through a `1`-bit channel (`Fin 2`)
    caps correct recovery at `≤ 2 / 4` (`≥ 50%` mandatory Fano error) for EVERY encoder `enc`
    and EVERY decoder `dec`, whereas a `2`-bit channel (`Fin 4`) achieves `4 / 4` (`0%` error)! -/
theorem one_bit_four_message_fano_bottleneck_universal :
    (∀ enc : Fin 4 → Fin 2, ∀ dec : Fin 2 → Fin 4, oneBitFourMsgCorrect enc dec ≤ 2) ∧
    (let id4 : Fin 4 → Fin 4 := fun x => x
     (if (id4 ⟨0, by decide⟩).1 = 0 then 1 else 0) +
     (if (id4 ⟨1, by decide⟩).1 = 1 then 1 else 0) +
     (if (id4 ⟨2, by decide⟩).1 = 2 then 1 else 0) +
     (if (id4 ⟨3, by decide⟩).1 = 3 then 1 else 0) = 4) := by
  refine ⟨?_, by decide⟩
  intro enc dec
  unfold oneBitFourMsgCorrect
  rcases fin2_cases (enc ⟨0, by decide⟩) with h0 | h0 <;>
    rcases fin2_cases (enc ⟨1, by decide⟩) with h1 | h1 <;>
    rcases fin2_cases (enc ⟨2, by decide⟩) with h2 | h2 <;>
    rcases fin2_cases (enc ⟨3, by decide⟩) with h3 | h3
  all_goals
    rw [h0, h1, h2, h3]
    split <;> split <;> split <;> split <;> omega

/-! ## Section 3: Universal `Fin N` Singleton MDS Bound & `[4, 2, 3]₅` Reed–Solomon Code -/

def hammingDist : (N : Nat) → (Fin N → Nat) → (Fin N → Nat) → Nat
  | 0, _, _ => 0
  | n + 1, u, v =>
      hammingDist n (fun i => u ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
                    (fun i => v ⟨i.1, Nat.lt_succ_of_lt i.2⟩) +
      (if u ⟨n, Nat.lt_succ_self n⟩ = v ⟨n, Nat.lt_succ_self n⟩ then 0 else 1)

theorem hammingDist_triangle (N : Nat) :
    ∀ (u v w : Fin N → Nat), hammingDist N u w ≤ hammingDist N u v + hammingDist N v w := by
  induction N with
  | zero =>
      intro u v w
      simp [hammingDist]
  | succ n ih =>
      intro u v w
      have hprev := ih (fun i => u ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
                       (fun i => v ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
                       (fun i => w ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
      simp [hammingDist]
      split <;> split <;> split <;> omega

theorem hammingDist_symm (N : Nat) :
    ∀ (u v : Fin N → Nat), hammingDist N u v = hammingDist N v u := by
  induction N with
  | zero =>
      intro _ _
      rfl
  | succ n ih =>
      intro u v
      have hprev := ih (fun i => u ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
                       (fun i => v ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
      simp [hammingDist, hprev]
      split <;> split <;> omega

theorem hammingDist_le_of_prefix_eq (N : Nat) :
    ∀ (k : Nat) (u v : Fin N → Nat),
      k ≤ N → (∀ t : Fin N, t.1 < k → u t = v t) → hammingDist N u v ≤ N - k := by
  induction N with
  | zero =>
      intro k u v _ _
      simp [hammingDist]
  | succ n ih =>
      intro k u v hk hpref
      by_cases hkn : k ≤ n
      · have hprev := ih k (fun i => u ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
                           (fun i => v ⟨i.1, Nat.lt_succ_of_lt i.2⟩) hkn
                           (fun i hi => hpref ⟨i.1, Nat.lt_succ_of_lt i.2⟩ hi)
        simp [hammingDist]
        split <;> omega
      · have heqk : k = n + 1 := by omega
        subst heqk
        have hprev := ih n (fun i => u ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
                           (fun i => v ⟨i.1, Nat.lt_succ_of_lt i.2⟩) (Nat.le_refl n)
                           (fun i hi => hpref ⟨i.1, Nat.lt_succ_of_lt i.2⟩ (Nat.lt_succ_of_lt hi))
        have hlast : u ⟨n, Nat.lt_succ_self n⟩ = v ⟨n, Nat.lt_succ_self n⟩ :=
          hpref ⟨n, Nat.lt_succ_self n⟩ (Nat.lt_succ_self n)
        simp [hammingDist, hlast]
        omega

/-- Universal Singleton MDS Puncturing Injection:
    In ANY code `C : Fin M → Fin N → Nat` of minimum Hamming distance `d ≥ 1` (`d ≤ N + 1`),
    puncturing the last `d - 1` coordinates (`prefix` of length `N + 1 - d`) is strictly injective,
    immediately forcing `|C| ≤ |Alphabet|^{N + 1 - d}` (`d ≤ N - k + 1`). -/
theorem singleton_puncturing_injective
    (N M d : Nat) (C : Fin M → Fin N → Nat)
    (hd1 : 1 ≤ d) (hdN : d ≤ N + 1)
    (hmin : ∀ i j : Fin M, i ≠ j → d ≤ hammingDist N (C i) (C j))
    (i j : Fin M)
    (hpref : ∀ t : Fin N, t.1 < N + 1 - d → C i t = C j t) :
    i = j := by
  by_cases hij : i = j
  · exact hij
  · have hge : d ≤ hammingDist N (C i) (C j) := hmin i j hij
    have hle : hammingDist N (C i) (C j) ≤ N - (N + 1 - d) :=
      hammingDist_le_of_prefix_eq N (N + 1 - d) (C i) (C j) (by omega) hpref
    omega

def rsCode42F5 (a b : Fin 5) (t : Fin 4) : Nat :=
  (a.1 + b.1 * t.1) % 5

def allRS42PairsHaveDistGe3 : Bool :=
  let idx5 : List (Fin 5) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩]
  idx5.all (fun a1 =>
    idx5.all (fun b1 =>
      idx5.all (fun a2 =>
        idx5.all (fun b2 =>
          if a1 = a2 ∧ b1 = b2 then true
          else decide (3 ≤ hammingDist 4 (rsCode42F5 a1 b1) (rsCode42F5 a2 b2))))))

/-- Explicit `[4, 2, 3]₅` Polynomial Reed–Solomon MDS Code over `𝔽₅`:
    All `25 = 5²` distinct degree-`≤ 1` polynomials `a + b t mod 5` evaluated on `{0, 1, 2, 3}`
    have pairwise Hamming distance `≥ 3`, and `0` vs. `t` attains distance `3 = 4 - 2 + 1` tight! -/
theorem reed_solomon_4_2_3_f5_attains_singleton_mds_bound :
    allRS42PairsHaveDistGe3 = true ∧
    hammingDist 4 (rsCode42F5 ⟨0, by decide⟩ ⟨0, by decide⟩)
                  (rsCode42F5 ⟨0, by decide⟩ ⟨1, by decide⟩) = 3 ∧
    3 = 4 + 1 - 2 := by
  decide

/-! ## Section 4: Universal `Fin N` Unique Bounded-Distance Decoding (`2 t < d`) vs. `2 t = d` Tie -/

/-- Universal Unique Bounded-Distance Decoding:
    Whenever `2 * t < d`, Hamming balls of radius `t` around distinct codewords in `C` are
    strictly disjoint: any received word `r` within distance `t` of `C i` and `C j` forces `i = j`. -/
theorem unique_bounded_distance_decoding_universal
    (N M d t : Nat) (C : Fin M → Fin N → Nat)
    (hmin : ∀ i j : Fin M, i ≠ j → d ≤ hammingDist N (C i) (C j))
    (ht : 2 * t < d)
    (r : Fin N → Nat) (i j : Fin M)
    (hi : hammingDist N (C i) r ≤ t)
    (hj : hammingDist N (C j) r ≤ t) :
    i = j := by
  by_cases hij : i = j
  · exact hij
  · have hge : d ≤ hammingDist N (C i) (C j) := hmin i j hij
    have htri : hammingDist N (C i) (C j) ≤ hammingDist N (C i) r + hammingDist N r (C j) :=
      hammingDist_triangle N (C i) r (C j)
    have hsym : hammingDist N r (C j) = hammingDist N (C j) r :=
      hammingDist_symm N r (C j)
    omega

/-- Premise-Failure Counterexample (`2 t = d` Half-Distance Tie):
    On the `[2, 1, 2]₂` parity code `C₀ = (0, 0), C₁ = (1, 1)` (`d = 2`), at `t = 1` (`2 t = 2 = d`),
    received word `r = (1, 0)` has `d_H(C₀, r) = 1 ≤ 1` AND `d_H(C₁, r) = 1 ≤ 1` (`C₀ ≠ C₁`),
    breaking unique decoding right at the `d / 2` boundary! -/
theorem half_distance_parity_code_tie_ambiguity :
    let c0 : Fin 2 → Nat := fun _ => 0
    let c1 : Fin 2 → Nat := fun _ => 1
    let r  : Fin 2 → Nat := fun i => if i.1 = 0 then 1 else 0
    hammingDist 2 c0 c1 = 2 ∧
    hammingDist 2 c0 r = 1 ∧
    hammingDist 2 c1 r = 1 ∧
    c0 ⟨0, by decide⟩ ≠ c1 ⟨0, by decide⟩ := by
  decide

end CommonGround.Frontier.FanoCramerRaoAndReedSolomonSingleton
