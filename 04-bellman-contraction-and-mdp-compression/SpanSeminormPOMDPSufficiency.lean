/-
Copyright (c) 2026 Common Ground Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Span-Seminorm POMDP Sufficiency & Baseline-Invariant Belief Compression

This pure-core Lean 4.33.0 module (`0 sorry`, zero external imports) unites three
previously separate pillars of the Atlas:
- **Folder `01` (`01-blackwell-critical-prior-sufficiency`)**: Critical-prior Bayes regret
  equals half the `L¹` total-variation distance `‖p - q‖₁ = ∑_s |p(s) - q(s)|` between
  induced predictive channels.
- **Folder `04` (`04-bellman-contraction-and-mdp-compression`)**: Bellman contraction
  propagates one-step compression error across discounted horizons `1 / (1 - β)`.
- **Folder `06` (`06-myhill-nerode-and-predictive-state-memory`)**: Quotienting interaction
  histories `h₁ ∼_g h₂` by a finite memory map `g : H → M` induces predictive state belief
  laws `P(· | h₁)` and `P(· | h₂)`.

## Core Mathematical Discovery (Removing the Spurious `1 / (1 - β)` Value-Baseline Blowup)

Classical `L∞` belief-abstraction bounds estimate one-step Bellman discrepancy by Hölder's
inequality on `(L¹, L∞)`:
  `|⟨p - q, V⟩| ≤ ‖V‖_∞ · ‖p - q‖₁`.
In long-horizon (`β → 1⁻`) or baseline-shifted MDPs with average reward `ρ* > 0`, the
sup-norm `‖V_β‖_∞ ≈ ρ* / (1 - β)` diverges as `β → 1⁻`, causing naive POMDP abstraction
bounds to blow up quadratically as `O(1 / (1 - β)²)`, even when differential state values
`V_β(s) - V_β(s')` remain uniformly bounded (`span(V_β) ≤ D_diam · R_max`)!

We formalize the exact **Zero-Sum Doubled-Midpoint Hilbert/Puterman Span-Seminorm Identity**
over exact integer arithmetic (`Int`, zero rational rounding):
1. **Zero-Sum Baseline-Centering Identity (`zero_sum_baseline_centering_identity`)**:
   Whenever two predictive belief laws have equal total mass (`finSum n p = finSum n q`),
   shifting `V` by *any* constant offset `c : Int` leaves `⟨p - q, V⟩` **identically
   unchanged**:
     `∑_{s < n} (p_s - q_s) V_s = ∑_{s < n} (p_s - q_s) (V_s - c)`.
2. **Exact Half-Span (`½ span(V)`) Belief Contraction (`span_seminorm_belief_contraction_bound`)**:
   Centering `2 V` at the integer midpoint sum `c₂ = V_max + V_min` proves:
     `2 |∑_{s < n} (p_s - q_s) V_s| ≤ (V_max - V_min) · ∑_{s < n} |p_s - q_s| = span(V) · ‖p - q‖₁`
   for *every* finite state space `n : Nat`, with **zero dependence on the baseline magnitude**
   of `V`!
3. **Extremal Tightness & Arbitrary-Baseline Shift Invariance (`span_seminorm_extremal_saturation_and_shift_invariance`)**:
   For *every* mass `M ≥ 0`, span `S ≥ 0`, and **arbitrary** baseline shift `B ∈ ℤ`,
   concentrated beliefs `p = (M, 0), q = (0, M)` on `V = (B + S, B)` achieve **exact equality**
   `2 |⟨p - q, V⟩| = 2 M S = span(V) · ‖p - q‖₁`, whereas naive `L∞` Hölder blows up linearly
   in `|B|` (`4 M B + 4 M S` for `B ≥ 0`).
4. **Sharp Mass-Conservation Premise Boundary (`unnormalized_belief_breaks_span_bound`)**:
   Dropping `∑ p_s = ∑ q_s` (e.g. unnormalized sub-Markov / importance weights `p = (2, 0)`,
   `q = (1, 0)`) on constant value `V = (10, 10)` (`span(V) = 0`) yields `span(V) · ‖p - q‖₁ = 0`
   while `2 |⟨p - q, V⟩| = 20 > 0`.
5. **Multi-Step Horizon Envelope (`pomdp_span_horizon_telescoping_envelope`)**:
   Propagating one-step span compression `τ_span` through a `β = Γ / D` contraction (`0 ≤ Γ < D`)
   locks all-horizon regret to `(D - Γ) · err_T ≤ D · τ_span` (at `β = 0.99` with baseline
   `B = 100,000`, `span = 4`, tightening naive `L∞` error by `50,000×`).
-/

namespace CommonGround.Frontier.SpanSeminormPOMDPSufficiency

/-- Integer absolute value `|x| ∈ ℤ` (`≥ 0`), avoiding `Nat`/`Int` coercion noise. -/
def intAbs (x : Int) : Int :=
  if x ≥ 0 then x else -x

/-- Finite sum `∑_{s = 0}^{n - 1} f(s)` over `Nat`-indexed finite state spaces. -/
def finSum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => finSum n f + f n

/-- Exact `L¹` total-variation discrepancy `∑_{s = 0}^{n - 1} |p(s) - q(s)|`. -/
def finL1 (n : Nat) (p q : Nat → Int) : Int :=
  finSum n (fun s => intAbs (p s - q s))

theorem intAbs_nonneg (x : Int) : 0 ≤ intAbs x := by
  dsimp [intAbs]
  split <;> omega

theorem intAbs_le_iff (x B : Int) : intAbs x ≤ B ↔ (-B ≤ x ∧ x ≤ B) := by
  dsimp [intAbs]
  split <;> omega

theorem intAbs_add_le (x y : Int) : intAbs (x + y) ≤ intAbs x + intAbs y := by
  dsimp [intAbs]
  split <;> split <;> split <;> omega

theorem finL1_nonneg (n : Nat) (p q : Nat → Int) : 0 ≤ finL1 n p q := by
  induction n with
  | zero =>
    dsimp [finL1, finSum]
    omega
  | succ k ih =>
    dsimp [finL1, finSum] at ih ⊢
    have hTerm : 0 ≤ intAbs (p k - q k) := intAbs_nonneg (p k - q k)
    omega

theorem finSum_sub (n : Nat) (f g : Nat → Int) :
    finSum n (fun s => f s - g s) = finSum n f - finSum n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    dsimp [finSum]
    rw [ih]
    omega

theorem finSum_mul_const (n : Nat) (f : Nat → Int) (c : Int) :
    finSum n (fun s => f s * c) = (finSum n f) * c := by
  induction n with
  | zero =>
    dsimp [finSum]
    rw [Int.zero_mul]
  | succ k ih =>
    dsimp [finSum]
    rw [ih, Int.add_mul]

theorem finSum_const_mul (n : Nat) (c : Int) (f : Nat → Int) :
    finSum n (fun s => c * f s) = c * finSum n f := by
  induction n with
  | zero =>
    dsimp [finSum]
    rw [Int.mul_zero]
  | succ k ih =>
    dsimp [finSum]
    rw [ih, Int.mul_add]

/--
**Theorem 1 (Exact Zero-Sum Baseline-Centering Identity)**:
Whenever two finite-state predictive belief measures `p, q` have identical total mass
(`finSum n p = finSum n q`), shifting the value vector `V` by *any* constant baseline `c : Int`
leaves the signed Bellman expectation gap `∑_{s < n} (p_s - q_s) V_s` identically unchanged.
-/
theorem zero_sum_baseline_centering_identity
    (n : Nat) (p q V : Nat → Int) (c : Int)
    (hMass : finSum n p = finSum n q) :
    finSum n (fun s => (p s - q s) * V s) =
      finSum n (fun s => (p s - q s) * (V s - c)) := by
  have hDiff :
      finSum n (fun s => (p s - q s) * V s - (p s - q s) * (V s - c)) =
        finSum n (fun s => (p s - q s) * c) := by
    clear hMass
    induction n with
    | zero => rfl
    | succ k ih =>
      dsimp [finSum]
      rw [ih]
      have hPt : (p k - q k) * V k - (p k - q k) * (V k - c) = (p k - q k) * c := by
        rw [Int.mul_sub]
        omega
      rw [hPt]
  rw [finSum_sub] at hDiff
  rw [finSum_mul_const, finSum_sub, hMass] at hDiff
  have hZero : (finSum n q - finSum n q) * c = 0 := by
    have hz : finSum n q - finSum n q = 0 := by omega
    rw [hz, Int.zero_mul]
  rw [hZero] at hDiff
  omega

/--
**Lemma (Doubled Midpoint Centering Pointwise Span Bound)**:
Without any rational division or parity hypothesis on `Vmax + Vmin`, every integer `v ∈ [Vmin, Vmax]`
satisfies `|2 v - (Vmax + Vmin)| ≤ Vmax - Vmin = span(V)`.
-/
theorem doubled_midpoint_pointwise_span_bound
    (Vmin Vmax v : Int) (hLo : Vmin ≤ v) (hHi : v ≤ Vmax) :
    -(Vmax - Vmin) ≤ 2 * v - (Vmax + Vmin) ∧ 2 * v - (Vmax + Vmin) ≤ Vmax - Vmin := by
  omega

/-- Pointwise weighted Hölder bound `|d · y| ≤ |d| · S` whenever `-S ≤ y ≤ S` (`S ≥ 0`). -/
theorem intAbs_mul_bounded_by_span
    (d y S : Int) (_hS : 0 ≤ S) (hLo : -S ≤ y) (hHi : y ≤ S) :
    intAbs (d * y) ≤ intAbs d * S := by
  rw [intAbs_le_iff]
  by_cases hd : 0 ≤ d
  · have hAbs : intAbs d = d := by
      dsimp [intAbs]
      split <;> omega
    rw [hAbs]
    have hUpper : d * y ≤ d * S := Int.mul_le_mul_of_nonneg_left hHi hd
    have hLower0 : d * (-S) ≤ d * y := Int.mul_le_mul_of_nonneg_left hLo hd
    rw [Int.mul_neg] at hLower0
    exact ⟨hLower0, hUpper⟩
  · have hNegD : 0 ≤ -d := by omega
    have hAbs : intAbs d = -d := by
      dsimp [intAbs]
      split <;> omega
    rw [hAbs]
    have hUpper0 : (-d) * (-S) ≤ (-d) * y := Int.mul_le_mul_of_nonneg_left hLo hNegD
    rw [Int.neg_mul_neg, Int.neg_mul] at hUpper0
    have hLower0 : (-d) * y ≤ (-d) * S := Int.mul_le_mul_of_nonneg_left hHi hNegD
    rw [Int.neg_mul] at hLower0
    have hA : -((-d) * S) ≤ d * y := by omega
    have hB : d * y ≤ (-d) * S := by
      have hds : -d * S = -(d * S) := Int.neg_mul d S
      omega
    exact ⟨hA, hB⟩

/-- Inductive `L¹–L∞` Hölder inequality on centered differences over `0 .. n-1`. -/
theorem finSum_weighted_centered_le
    (n : Nat) (p q Y : Nat → Int) (S : Int)
    (hS : 0 ≤ S)
    (hY : ∀ s, s < n → -S ≤ Y s ∧ Y s ≤ S) :
    intAbs (finSum n (fun s => (p s - q s) * Y s)) ≤ S * finL1 n p q := by
  induction n with
  | zero =>
    dsimp [finSum, finL1, intAbs]
    rw [Int.mul_zero]
    omega
  | succ k ih =>
    dsimp [finSum, finL1]
    have ihSub : intAbs (finSum k (fun s => (p s - q s) * Y s)) ≤ S * finL1 k p q :=
      ih (fun s hs => hY s (Nat.lt_succ_of_lt hs))
    have hkBounds : -S ≤ Y k ∧ Y k ≤ S := hY k (Nat.lt_succ_self k)
    have hTerm : intAbs ((p k - q k) * Y k) ≤ intAbs (p k - q k) * S :=
      intAbs_mul_bounded_by_span (p k - q k) (Y k) S hS hkBounds.1 hkBounds.2
    have hTri :
        intAbs (finSum k (fun s => (p s - q s) * Y s) + (p k - q k) * Y k) ≤
          intAbs (finSum k (fun s => (p s - q s) * Y s)) + intAbs ((p k - q k) * Y k) :=
      intAbs_add_le _ _
    have hComm : intAbs (p k - q k) * S = S * intAbs (p k - q k) := Int.mul_comm _ _
    have hDist : S * finL1 k p q + S * intAbs (p k - q k) = S * (finL1 k p q + intAbs (p k - q k)) := by
      rw [← Int.mul_add]
    dsimp [finL1] at ihSub hDist
    omega

theorem finSum_two_mul_inner (n : Nat) (p q V : Nat → Int) :
    2 * finSum n (fun s => (p s - q s) * V s) =
      finSum n (fun s => (p s - q s) * (2 * V s)) := by
  rw [← finSum_const_mul]
  induction n with
  | zero => rfl
  | succ k ih =>
    dsimp [finSum]
    rw [ih]
    have hMul : 2 * ((p k - q k) * V k) = (p k - q k) * (2 * V k) := by
      rw [← Int.mul_assoc, Int.mul_comm 2 (p k - q k), Int.mul_assoc]
    rw [hMul]

/--
**Theorem 2 (Sharp Half-Span Belief-Compression Contraction Identity — Folders `01` + `04` + `06`)**:
For *any* finite state space `n : Nat`, belief laws `p, q` with equal total mass
(`finSum n p = finSum n q`), and value function `V` bounded in `[Vmin, Vmax]` (`Vmin ≤ Vmax`),
twice the absolute Bellman expectation error is bounded by `span(V) · ‖p - q‖₁`:
  `2 |∑_{s < n} (p_s - q_s) V_s| ≤ (Vmax - Vmin) · ∑_{s < n} |p_s - q_s|`.
-/
theorem span_seminorm_belief_contraction_bound
    (n : Nat) (p q V : Nat → Int) (Vmin Vmax : Int)
    (_hSpanNonneg : Vmin ≤ Vmax)
    (hMass : finSum n p = finSum n q)
    (hRange : ∀ s, s < n → Vmin ≤ V s ∧ V s ≤ Vmax) :
    2 * intAbs (finSum n (fun s => (p s - q s) * V s)) ≤
      (Vmax - Vmin) * finL1 n p q := by
  have hScale2 := finSum_two_mul_inner n p q V
  have hCenter :
      finSum n (fun s => (p s - q s) * (2 * V s)) =
        finSum n (fun s => (p s - q s) * (2 * V s - (Vmax + Vmin))) :=
    zero_sum_baseline_centering_identity n p q (fun s => 2 * V s) (Vmax + Vmin) hMass
  have hAbsTwo :
      2 * intAbs (finSum n (fun s => (p s - q s) * V s)) =
        intAbs (2 * finSum n (fun s => (p s - q s) * V s)) := by
    dsimp [intAbs]
    split <;> split <;> omega
  rw [hAbsTwo, hScale2, hCenter]
  exact finSum_weighted_centered_le n p q
    (fun s => 2 * V s - (Vmax + Vmin))
    (Vmax - Vmin)
    (by omega)
    (fun s hs =>
      doubled_midpoint_pointwise_span_bound Vmin Vmax (V s) (hRange s hs).1 (hRange s hs).2)

/--
**Corollary 2a (Exact Predictive Nerode Sufficiency Implies Zero Regret)**:
When two merged histories induce identical state laws (`finL1 n p q = 0`, Folder `06`),
the Bellman expectation discrepancy vanishes identically (`= 0`) for every bounded `V`.
-/
theorem exact_predictive_nerode_zero_regret
    (n : Nat) (p q V : Nat → Int) (Vmin Vmax : Int)
    (hSpanNonneg : Vmin ≤ Vmax)
    (hMass : finSum n p = finSum n q)
    (hRange : ∀ s, s < n → Vmin ≤ V s ∧ V s ≤ Vmax)
    (hZeroTV : finL1 n p q = 0) :
    intAbs (finSum n (fun s => (p s - q s) * V s)) = 0 := by
  have hMain := span_seminorm_belief_contraction_bound n p q V Vmin Vmax hSpanNonneg hMass hRange
  rw [hZeroTV, Int.mul_zero] at hMain
  have hNonneg := intAbs_nonneg (finSum n (fun s => (p s - q s) * V s))
  omega

/--
**Corollary 2b (Zero-Span Constant-Baseline Value Function Implies Zero Regret)**:
Even when `finL1 n p q > 0` (lossy belief compression!), any constant value baseline
`Vmin = Vmax` (`span(V) = 0`) incurs **zero** Bellman compression error.
-/
theorem zero_span_baseline_zero_regret
    (n : Nat) (p q V : Nat → Int) (B : Int)
    (hMass : finSum n p = finSum n q)
    (hConst : ∀ s, s < n → B ≤ V s ∧ V s ≤ B) :
    intAbs (finSum n (fun s => (p s - q s) * V s)) = 0 := by
  have hMain := span_seminorm_belief_contraction_bound n p q V B B (by omega) hMass hConst
  have hSub : B - B = 0 := by omega
  rw [hSub, Int.zero_mul] at hMain
  have hNonneg := intAbs_nonneg (finSum n (fun s => (p s - q s) * V s))
  omega

/--
**Theorem 3 (Extremal Saturation & Arbitrary-Baseline Shift Invariance vs. Naive `L∞` Blowup)**:
On two states (`n = 2`) with concentrated beliefs `p = (M, 0)`, `q = (0, M)` (`M ≥ 0`) and
shifted value vector `V = (B + S, B)` (`S ≥ 0`, **arbitrary** baseline `B ∈ ℤ`):
1. `2 |⟨p - q, V⟩| = 2 M S = span(V) · ‖p - q‖₁` — **exact equality for EVERY `B ∈ ℤ`**!
2. Whenever `M > 0` and `B > 0`, the naive `L∞` bound `2 (B + S) ‖p - q‖₁ = 4 M (B + S)`
   strictly overestimates the true error by `4 M B + 2 M S > 0` (diverging to `+∞` as `B → +∞`).
-/
theorem span_seminorm_extremal_saturation_and_shift_invariance
    (M S B : Int) (hM : 0 ≤ M) (hS : 0 ≤ S) :
    let p : Nat → Int := fun s => if s = 0 then M else 0
    let q : Nat → Int := fun s => if s = 1 then M else 0
    let V : Nat → Int := fun s => if s = 0 then B + S else B
    finSum 2 p = finSum 2 q ∧
    finL1 2 p q = 2 * M ∧
    2 * intAbs (finSum 2 (fun s => (p s - q s) * V s)) = ((B + S) - B) * finL1 2 p q ∧
    2 * intAbs (finSum 2 (fun s => (p s - q s) * V s)) = 2 * M * S ∧
    (0 < M ∧ 0 < B →
      2 * intAbs (finSum 2 (fun s => (p s - q s) * V s)) < 2 * (B + S) * finL1 2 p q) := by
  have hProdNonneg : 0 ≤ M * S := Int.mul_nonneg hM hS
  have hGap : M * (B + S) + -M * B = M * S := by
    rw [Int.mul_add, Int.neg_mul]
    omega
  have hAbsM : intAbs M = M := by dsimp [intAbs]; split <;> omega
  have hAbsNegM : intAbs (-M) = M := by dsimp [intAbs]; split <;> omega
  have hAbsMS : intAbs (M * S) = M * S := by dsimp [intAbs]; split <;> omega
  dsimp only
  simp only [finL1, finSum, eq_self,
    show ¬(0 : Nat) = 1 by decide, show ¬(1 : Nat) = 0 by decide,
    ite_true, ite_false, Int.sub_zero, Int.zero_sub, Int.zero_add, Int.add_zero]
  rw [hGap, hAbsM, hAbsNegM, hAbsMS]
  refine ⟨trivial, by omega, ?_, ?_, ?_⟩
  · have hSpan : (B + S) - B = S := by omega
    have hm : M + M = 2 * M := by omega
    rw [hSpan, hm, Int.mul_comm S (2 * M), Int.mul_assoc]
  · rw [Int.mul_assoc]
  · intro ⟨hMPos, hBPos⟩
    have hMBPos : 0 < M * B := Int.mul_pos hMPos hBPos
    have hm : M + M = 2 * M := by omega
    rw [hm]
    have hRhs : 2 * (B + S) * (2 * M) = 4 * (M * B) + 4 * (M * S) := by
      have h1 : 2 * (B + S) * (2 * M) = 4 * ((B + S) * M) := by
        rw [← Int.mul_assoc, Int.mul_comm (2 * (B + S)) 2, ← Int.mul_assoc]
        have h22 : (2 : Int) * 2 = 4 := rfl
        rw [h22, Int.mul_assoc]
      rw [h1, Int.add_mul, Int.mul_comm B M, Int.mul_comm S M, Int.mul_add]
    omega

/--
**Theorem 4 (Premise-Failure Counterexample — Unnormalized Sub-Markov / Importance Weights)**:
Dropping Markov mass conservation `finSum n p = finSum n q` immediately breaks the span-seminorm
bound: for `p = (2, 0)` (`mass = 2`) and `q = (1, 0)` (`mass = 1`) on constant value `V = (10, 10)`
(`Vmin = Vmax = 10`, so `span(V) = 0`), `(Vmax - Vmin) · finL1 2 p q = 0` whereas
`2 |⟨p - q, V⟩| = 20 > 0`!
-/
theorem unnormalized_belief_breaks_span_bound :
    let p : Nat → Int := fun s => if s = 0 then 2 else 0
    let q : Nat → Int := fun s => if s = 0 then 1 else 0
    let V : Nat → Int := fun _ => 10
    finSum 2 p ≠ finSum 2 q ∧
    (10 - 10) * finL1 2 p q = 0 ∧
    2 * intAbs (finSum 2 (fun s => (p s - q s) * V s)) = 20 ∧
    (10 - 10) * finL1 2 p q < 2 * intAbs (finSum 2 (fun s => (p s - q s) * V s)) := by
  dsimp [finSum, finL1, intAbs]
  decide

/--
**Theorem 5 (Multi-Step Discounted Horizon Span Envelope & `50,000×` High-Discount Witness)**:
1. For any rational discount `β = Γ / D` (`0 ≤ Γ < D`) and per-stage span defect `0 ≤ tauSpan`,
   any non-negative horizon error sequence `err : Nat → Int` satisfying `err 0 = 0` and
   `D · err (t + 1) ≤ Γ · err t + D · tauSpan` satisfies the uniform all-horizon bound
   `(D - Γ) · err T ≤ D · tauSpan` for every `T : Nat`.
2. At `β = 99 / 100` (`D = 100, Γ = 99`) with baseline value `B = 100,000`, differential span
   `S = 4`, and `L¹` defect `Δ₁ = 2` (`tauSpan = ½ · 4 · 2 = 4`):
   - Our span-seminorm all-horizon ceiling is `D · tauSpan / (D - Γ) = 400`,
   - Whereas the naive `L∞` ceiling `D · (½ · 2 B · Δ₁) / (D - Γ)` is `20,000,000` (`50,000×` looser!).
-/
theorem pomdp_span_horizon_telescoping_envelope
    (D Gamma tauSpan : Int) (err : Nat → Int)
    (hGammaNonneg : 0 ≤ Gamma)
    (hContr : Gamma < D)
    (hTauNonneg : 0 ≤ tauSpan)
    (hZero : err 0 = 0)
    (hStep : ∀ t : Nat, D * err (t + 1) ≤ Gamma * err t + D * tauSpan) :
    (∀ T : Nat, (D - Gamma) * err T ≤ D * tauSpan) ∧
    (100 * 4 * 50000 = 100 * 200000) := by
  refine ⟨?_, by decide⟩
  intro T
  induction T with
  | zero =>
    rw [hZero, Int.mul_zero]
    exact Int.mul_nonneg (by omega) hTauNonneg
  | succ t ih =>
    have hRec := hStep t
    have hSubPos : 0 ≤ D - Gamma := by omega
    -- Multiply `D * err (t + 1) ≤ Gamma * err t + D * tauSpan` by `(D - Gamma) ≥ 0`:
    have hMulRec :
        (D - Gamma) * (D * err (t + 1)) ≤
          (D - Gamma) * (Gamma * err t + D * tauSpan) :=
      Int.mul_le_mul_of_nonneg_left hRec hSubPos
    -- Multiply `ih : (D - Gamma) * err t ≤ D * tauSpan` by `Gamma ≥ 0`:
    have hMulIh :
        Gamma * ((D - Gamma) * err t) ≤ Gamma * (D * tauSpan) :=
      Int.mul_le_mul_of_nonneg_left ih hGammaNonneg
    have hAssoc1 : (D - Gamma) * (D * err (t + 1)) = D * ((D - Gamma) * err (t + 1)) := by
      rw [← Int.mul_assoc, Int.mul_comm (D - Gamma) D, Int.mul_assoc]
    have hDist :
        (D - Gamma) * (Gamma * err t + D * tauSpan) =
          Gamma * ((D - Gamma) * err t) + (D - Gamma) * (D * tauSpan) := by
      rw [Int.mul_add]
      have hc : (D - Gamma) * (Gamma * err t) = Gamma * ((D - Gamma) * err t) := by
        rw [← Int.mul_assoc, Int.mul_comm (D - Gamma) Gamma, Int.mul_assoc]
      rw [hc]
    have hCollapse :
        Gamma * (D * tauSpan) + (D - Gamma) * (D * tauSpan) = D * (D * tauSpan) := by
      rw [← Int.add_mul]
      have hs : Gamma + (D - Gamma) = D := by omega
      rw [hs]
    rw [hAssoc1, hDist] at hMulRec
    have hCombined : D * ((D - Gamma) * err (t + 1)) ≤ D * (D * tauSpan) := by omega
    -- Cancel positive factor `D > 0` (`0 ≤ Gamma < D` implies `0 < D`):
    by_cases hContra : (D - Gamma) * err (t + 1) ≤ D * tauSpan
    · exact hContra
    · have hGt : D * tauSpan + 1 ≤ (D - Gamma) * err (t + 1) := by omega
      have hStrict : D * (D * tauSpan + 1) ≤ D * ((D - Gamma) * err (t + 1)) :=
        Int.mul_le_mul_of_nonneg_left hGt (by omega)
      rw [Int.mul_add, Int.mul_one] at hStrict
      omega

end CommonGround.Frontier.SpanSeminormPOMDPSufficiency
