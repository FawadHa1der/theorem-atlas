/-
  08-kakutani-and-galois-structural-duality / TropicalFenchelSinkhornAndParityDuality.lean
  ========================================================================================
  Pure-Core Lean 4.33.0 Frontier Formalization (Zero External Imports, Zero Sorry):
  1. Discrete Legendre–Fenchel Conjugacy (`f*`), Subgradient Contact Equality, and Exact
     Supporting-Hyperplane Biconjugate Recovery (`f** = f`) vs. Non-Convex Double-Well Duality Gap.
  2. Kantorovich / Sinkhorn `C`-Transform Order-Reversing Galois Adjunction & Exact 3-Step
     Idempotence (`R(L(R(u))) = R(u)`), Unifying Optimal Transport Potentials & `08` Galois Closure.
  3. Maslov Tropical `APSP` Triangle Stabilization vs. Negative-Cycle Divergence (`3sum-apsp` ↔
     `GaussianConditional` Schur-Complement Precision Positivity).
  4. Equivariant Bilinear Parity Decomposition (`2 B = Sym_B + Alt_B`) vs. Characteristic-2
     Symplectic/Identity Collapse (`WedgeCovectors` ↔ `InvariantForm`).
-/

namespace CommonGround.Frontier.TropicalFenchelSinkhornAndParityDuality

/-! ## Part 1: Finite Maxima/Minima Combinators on `Fin (n + 1)` -/

/-- Exact maximum of an integer function on non-empty `Fin (n + 1)`. -/
def finMax : {n : Nat} → (Fin (n + 1) → Int) → Int
  | 0, g => g ⟨0, Nat.zero_lt_succ 0⟩
  | n + 1, g =>
      let head := g ⟨0, Nat.zero_lt_succ (n + 1)⟩
      let tail := finMax (n := n) (fun i => g i.succ)
      if head ≥ tail then head else tail

theorem le_finMax : {n : Nat} → (g : Fin (n + 1) → Int) → (i : Fin (n + 1)) → g i ≤ finMax g
  | 0, g, ⟨0, _⟩ => by
      simp [finMax]
  | 0, _, ⟨k + 1, hk⟩ => by
      omega
  | n + 1, g, ⟨0, _⟩ => by
      simp only [finMax]
      split <;> omega
  | n + 1, g, ⟨k + 1, hk⟩ => by
      have hk' : k < n + 1 := Nat.lt_of_succ_lt_succ hk
      have hTail : g ⟨k + 1, hk⟩ ≤ finMax (n := n) (fun j => g j.succ) :=
        le_finMax (n := n) (fun j => g j.succ) ⟨k, hk'⟩
      simp only [finMax]
      split <;> omega

theorem finMax_le_iff :
    {n : Nat} → (g : Fin (n + 1) → Int) → (M : Int) →
    (finMax g ≤ M ↔ ∀ i : Fin (n + 1), g i ≤ M)
  | 0, g, M => by
      constructor
      · intro h ⟨k, hk⟩
        cases k with
        | zero => exact h
        | succ k' => omega
      · intro h
        exact h ⟨0, Nat.zero_lt_succ 0⟩
  | n + 1, g, M => by
      constructor
      · intro h i
        exact Int.le_trans (le_finMax g i) h
      · intro h
        have h0 : g ⟨0, Nat.zero_lt_succ (n + 1)⟩ ≤ M := h ⟨0, Nat.zero_lt_succ (n + 1)⟩
        have hTail : finMax (n := n) (fun j => g j.succ) ≤ M :=
          (finMax_le_iff (n := n) (fun j => g j.succ) M).mpr (fun j => h j.succ)
        simp only [finMax]
        split <;> omega

/-- Exact minimum of an integer function on non-empty `Fin (n + 1)`. -/
def finMin {n : Nat} (g : Fin (n + 1) → Int) : Int :=
  -finMax (fun i => -g i)

theorem finMin_le {n : Nat} (g : Fin (n + 1) → Int) (i : Fin (n + 1)) :
    finMin g ≤ g i := by
  unfold finMin
  have h := le_finMax (fun j => -g j) i
  omega

theorem le_finMin_iff {n : Nat} (g : Fin (n + 1) → Int) (m : Int) :
    m ≤ finMin g ↔ ∀ i : Fin (n + 1), m ≤ g i := by
  unfold finMin
  constructor
  · intro hm i
    have h1 : finMax (fun j => -g j) ≤ -m := by omega
    have h2 : -g i ≤ -m := (finMax_le_iff (fun j => -g j) (-m)).mp h1 i
    omega
  · intro hAll
    have h1 : finMax (fun j => -g j) ≤ -m :=
      (finMax_le_iff (fun j => -g j) (-m)).mpr (fun i => by have := hAll i; omega)
    omega

/-! ## Part 2: Discrete Legendre–Fenchel Duality, Subgradient Contact & Second-Welfare Gap -/

/-- Discrete Legendre–Fenchel conjugate `f*(y) = max_i (x_i * y - f_i)`. -/
def fenchelConj {n : Nat} (x f : Fin (n + 1) → Int) (y : Int) : Int :=
  finMax (fun i => x i * y - f i)

/-- Discrete biconjugate `f**(x_i) = max_j (x_i * y_j - f*(y_j))` over dual price grid `y`. -/
def fenchelBiconj {n m : Nat} (x f : Fin (n + 1) → Int) (y : Fin (m + 1) → Int)
    (i : Fin (n + 1)) : Int :=
  finMax (fun j => x i * y j - fenchelConj x f (y j))

/-- Universal Discrete Fenchel–Young Inequality & Exact Subgradient Contact Characterization:
    (1) `x_i * y ≤ f_i + f*(y)` holds for every state `i` and dual price `y`.
    (2) Contact equality `x_{i₀} * y = f_{i₀} + f*(y)` holds iff `y` is a global supporting
        subgradient slope of `f` at `x_{i₀}`: `∀ i, (x_i - x_{i₀}) * y ≤ f_i - f_{i₀}`. -/
theorem discrete_fenchel_young_and_subgradient_contact
    {n : Nat} (x f : Fin (n + 1) → Int) (i0 : Fin (n + 1)) (y : Int) :
    x i0 * y ≤ f i0 + fenchelConj x f y ∧
    (x i0 * y = f i0 + fenchelConj x f y ↔
      ∀ i : Fin (n + 1), (x i - x i0) * y ≤ f i - f i0) := by
  have hBase : x i0 * y - f i0 ≤ fenchelConj x f y :=
    le_finMax (fun i => x i * y - f i) i0
  refine ⟨by omega, ?_⟩
  constructor
  · intro hEq i
    have hi : x i * y - f i ≤ fenchelConj x f y :=
      le_finMax (fun k => x k * y - f k) i
    have hDiff : (x i - x i0) * y = x i * y - x i0 * y := Int.sub_mul (x i) (x i0) y
    rw [hDiff]
    omega
  · intro hSub
    have hUpper : fenchelConj x f y ≤ x i0 * y - f i0 := by
      apply (finMax_le_iff (fun i => x i * y - f i) (x i0 * y - f i0)).mpr
      intro i
      have hi := hSub i
      have hDiff : (x i - x i0) * y = x i * y - x i0 * y := Int.sub_mul (x i) (x i0) y
      rw [hDiff] at hi
      omega
    omega

/-- Discrete Biconjugate Lower Envelope (`f** ≤ f`) & Supporting-Price Exact Recovery (`f**(x_{i₀}) = f(x_{i₀})`):
    Whenever `y_{j₀}` supports `f` at `x_{i₀}` (the Second Welfare Theorem convexity hypothesis),
    the Fenchel biconjugate recovers `f(x_{i₀})` with zero duality gap! -/
theorem discrete_biconjugate_lower_envelope_and_supporting_recovery
    {n m : Nat} (x f : Fin (n + 1) → Int) (y : Fin (m + 1) → Int) :
    (∀ i : Fin (n + 1), fenchelBiconj x f y i ≤ f i) ∧
    (∀ (i0 : Fin (n + 1)) (j0 : Fin (m + 1)),
      (∀ i : Fin (n + 1), (x i - x i0) * y j0 ≤ f i - f i0) →
      fenchelBiconj x f y i0 = f i0) := by
  refine ⟨?_, ?_⟩
  · intro i
    apply (finMax_le_iff (fun j => x i * y j - fenchelConj x f (y j)) (f i)).mpr
    intro j
    have hFY := (discrete_fenchel_young_and_subgradient_contact x f i (y j)).1
    omega
  · intro i0 j0 hSupp
    have hUpper : fenchelBiconj x f y i0 ≤ f i0 := by
      apply (finMax_le_iff (fun j => x i0 * y j - fenchelConj x f (y j)) (f i0)).mpr
      intro j
      have hFY := (discrete_fenchel_young_and_subgradient_contact x f i0 (y j)).1
      omega
    have hContact : x i0 * y j0 = f i0 + fenchelConj x f (y j0) :=
      (discrete_fenchel_young_and_subgradient_contact x f i0 (y j0)).2.mpr hSupp
    have hLower : x i0 * y j0 - fenchelConj x f (y j0) ≤ fenchelBiconj x f y i0 :=
      le_finMax (fun j => x i0 * y j - fenchelConj x f (y j)) j0
    omega

/-- Premise-Failure Counterexample (Non-Convex Double-Well Potential Breaks Biconjugate / Second Welfare):
    On `x = (-1, 0, 1)` with `f = (0, 2, 0)` (an interior non-convex barrier `f(0) = 2` flanked by
    two global minima `f(-1) = f(1) = 0`), for EVERY integer price `s ∈ ℤ` (unrestricted!),
    `f*(s) ≥ |s| ≥ 0`, so `0 * s - f*(s) ≤ 0 < 2 = f(0)`. No linear supporting price can sustain
    the interior state `x = 0`, leaving an irreducible duality gap of `2`! -/
def doubleWellX : Fin 3 → Int
  | ⟨0, _⟩ => -1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1

def doubleWellF : Fin 3 → Int
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 0

theorem nonconvex_double_well_strict_biconjugate_gap (s : Int) :
    0 ≤ fenchelConj doubleWellX doubleWellF s ∧
    doubleWellX ⟨1, by decide⟩ * s - fenchelConj doubleWellX doubleWellF s ≤ 0 ∧
    doubleWellF ⟨1, by decide⟩ -
      (doubleWellX ⟨1, by decide⟩ * s - fenchelConj doubleWellX doubleWellF s) ≥ 2 := by
  have hLeft : (-1 : Int) * s - 0 ≤ fenchelConj doubleWellX doubleWellF s :=
    le_finMax (fun i => doubleWellX i * s - doubleWellF i) ⟨0, by decide⟩
  have hRight : (1 : Int) * s - 0 ≤ fenchelConj doubleWellX doubleWellF s :=
    le_finMax (fun i => doubleWellX i * s - doubleWellF i) ⟨2, by decide⟩
  have hNonneg : 0 ≤ fenchelConj doubleWellX doubleWellF s := by omega
  have hMidX : doubleWellX ⟨1, by decide⟩ = 0 := rfl
  have hMidF : doubleWellF ⟨1, by decide⟩ = 2 := rfl
  rw [hMidX, hMidF, Int.zero_mul]
  omega

/-! ## Part 3: Kantorovich / Sinkhorn `C`-Transform Galois Closure & 3-Step Idempotence -/

/-- Right `C`-transform `u^C(j) = min_i (C_{ij} - u_i)` and left `C`-transform `v^{C^T}(i) = min_j (C_{ij} - v_j)`. -/
def cTransformRight {m n : Nat} (C : Fin (m + 1) → Fin (n + 1) → Int)
    (u : Fin (m + 1) → Int) (j : Fin (n + 1)) : Int :=
  finMin (fun i => C i j - u i)

def cTransformLeft {m n : Nat} (C : Fin (m + 1) → Fin (n + 1) → Int)
    (v : Fin (n + 1) → Int) (i : Fin (m + 1)) : Int :=
  finMin (fun j => C i j - v j)

/-- Exact Galois Adjunction & 3-Step Idempotence of Optimal-Transport `C`-Transforms:
    (1) `∀ i j, u_i + v_j ≤ C_{ij}` iff `∀ j, v_j ≤ u^C(j)` iff `∀ i, u_i ≤ v^{C^T}(i)`.
    (2) Double `C`-transform inflates dual potentials: `u_i ≤ (u^C)^{C^T}(i)`.
    (3) Triple `C`-transform stabilizes identically in ONE alternating Sinkhorn/tropical sweep:
        `((u^C)^{C^T})^C(j) = u^C(j)`! -/
theorem ctransform_galois_adjunction_and_three_step_idempotence
    {m n : Nat} (C : Fin (m + 1) → Fin (n + 1) → Int)
    (u : Fin (m + 1) → Int) (v : Fin (n + 1) → Int) :
    ((∀ i j, u i + v j ≤ C i j) ↔ (∀ j, v j ≤ cTransformRight C u j)) ∧
    ((∀ i j, u i + v j ≤ C i j) ↔ (∀ i, u i ≤ cTransformLeft C v i)) ∧
    (∀ i, u i ≤ cTransformLeft C (cTransformRight C u) i) ∧
    (∀ j, cTransformRight C (cTransformLeft C (cTransformRight C u)) j = cTransformRight C u j) := by
  have hAdjR : ∀ (u' : Fin (m + 1) → Int) (v' : Fin (n + 1) → Int),
      (∀ i j, u' i + v' j ≤ C i j) ↔ (∀ j, v' j ≤ cTransformRight C u' j) := by
    intro u' v'
    constructor
    · intro hFeas j
      apply (le_finMin_iff (fun i => C i j - u' i) (v' j)).mpr
      intro i
      have hij := hFeas i j
      omega
    · intro hR i j
      have hj : v' j ≤ finMin (fun k => C k j - u' k) := hR j
      have hi : finMin (fun k => C k j - u' k) ≤ C i j - u' i :=
        finMin_le (fun k => C k j - u' k) i
      omega
  have hAdjL : ∀ (u' : Fin (m + 1) → Int) (v' : Fin (n + 1) → Int),
      (∀ i j, u' i + v' j ≤ C i j) ↔ (∀ i, u' i ≤ cTransformLeft C v' i) := by
    intro u' v'
    constructor
    · intro hFeas i
      apply (le_finMin_iff (fun j => C i j - v' j) (u' i)).mpr
      intro j
      have hij := hFeas i j
      omega
    · intro hL i j
      have hi : u' i ≤ finMin (fun k => C i k - v' k) := hL i
      have hj : finMin (fun k => C i k - v' k) ≤ C i j - v' j :=
        finMin_le (fun k => C i k - v' k) j
      omega
  have hInflL : ∀ (u' : Fin (m + 1) → Int) (i : Fin (m + 1)),
      u' i ≤ cTransformLeft C (cTransformRight C u') i := by
    intro u'
    apply (hAdjL u' (cTransformRight C u')).mp
    exact (hAdjR u' (cTransformRight C u')).mpr (fun _ => Int.le_refl _)
  have hInflR : ∀ (v' : Fin (n + 1) → Int) (j : Fin (n + 1)),
      v' j ≤ cTransformRight C (cTransformLeft C v') j := by
    intro v'
    apply (hAdjR (cTransformLeft C v') v').mp
    exact (hAdjL (cTransformLeft C v') v').mpr (fun _ => Int.le_refl _)
  refine ⟨hAdjR u v, hAdjL u v, hInflL u, ?_⟩
  intro j
  have hGe : cTransformRight C u j ≤ cTransformRight C (cTransformLeft C (cTransformRight C u)) j :=
    hInflR (cTransformRight C u) j
  have hAnti : cTransformRight C (cTransformLeft C (cTransformRight C u)) j ≤ cTransformRight C u j := by
    apply (le_finMin_iff (fun i => C i j - u i)
      (cTransformRight C (cTransformLeft C (cTransformRight C u)) j)).mpr
    intro i
    have hStep1 : cTransformRight C (cTransformLeft C (cTransformRight C u)) j ≤
        C i j - cTransformLeft C (cTransformRight C u) i :=
      finMin_le (fun k => C k j - cTransformLeft C (cTransformRight C u) k) i
    have hStep2 : u i ≤ cTransformLeft C (cTransformRight C u) i := hInflL u i
    omega
  omega

/-! ## Part 4: Tropical `APSP` Non-Negative Cycle Stability vs. Negative-Cycle Divergence -/

/-- Positive witness vs. negative-cycle divergence (`apsp3sum: APSP` ↔ `GaussianConditional`):
    (1) When cycle weight `w ≥ 0`, adding `k` cycle laps `d + k * w ≥ d` never beats the simple path `d`.
    (2) When a negative cycle `w = -1` exists, `k`-lap walk cost `d - k` drops strictly below ANY
        finite lower bound `B : Int` (`d - max(0, d - B + 1) < B`), destroying shortest-path existence! -/
theorem tropical_apsp_nonneg_stability_vs_negative_cycle_divergence
    (d w B : Int) (hw : 0 ≤ w) (k : Nat) :
    d ≤ d + (k : Int) * w ∧
    (let laps : Nat := Int.toNat (if d - B + 1 ≥ 0 then d - B + 1 else 0)
     d + (laps : Int) * (-1) < B) := by
  have hkNonneg : 0 ≤ (k : Int) * w := Int.mul_nonneg (Int.natCast_nonneg k) hw
  refine ⟨by omega, ?_⟩
  dsimp only
  split
  · next hPos =>
    have hCast : ((Int.toNat (d - B + 1) : Nat) : Int) = d - B + 1 := Int.toNat_of_nonneg hPos
    rw [hCast]
    omega
  · next hNeg =>
    simp only [Int.toNat]
    omega

/-! ## Part 5: Bilinear Parity Decomposition (`2 B = Sym_B + Alt_B`) vs. Characteristic-2 Collapse -/

/-- Over `ℤ` (scaled by `2`), EVERY `G`-invariant bilinear form decomposes canonically into a
    symmetric `G`-invariant form `S(u,v) = B(u,v) + B(v,u)` and a strictly alternating `G`-invariant
    form `A(u,v) = B(u,v) - B(v,u)` (`A(v,v) = 0`), whereas mod `2` (`𝔽₂`) `I₂` is symmetric and
    skew-symmetric yet NOT alternating (`1 ≠ 0`), while `ω₂` lies in BOTH `Sym` and `Alt`! -/
theorem bilinear_parity_decomposition_and_char2_collapse
    {V : Type} (B : V → V → Int) (g : V → V)
    (hInv : ∀ x y : V, B (g x) (g y) = B x y) (u v : V) :
    (let S := fun x y => B x y + B y x
     let A := fun x y => B x y - B y x
     S u v = S v u ∧
     A v v = 0 ∧
     2 * B u v = S u v + A u v ∧
     S (g u) (g v) = S u v ∧
     A (g u) (g v) = A u v) ∧
    (((1 * 1 + 0 * 0) % 2 = 1) ∧
     (∀ u1 u2 v1 v2 : Int,
       (u1 * v2 + u2 * v1) % 2 = (v1 * u2 + v2 * u1) % 2 ∧
       (u1 * u2 + u2 * u1) % 2 = 0)) := by
  refine ⟨?_, ?_⟩
  · dsimp only
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩
    · rw [hInv u v, hInv v u]
    · rw [hInv u v, hInv v u]
  · refine ⟨by decide, ?_⟩
    intro u1 u2 v1 v2
    have hComm1 : u1 * v2 + u2 * v1 = v1 * u2 + v2 * u1 := by
      rw [Int.mul_comm u1 v2, Int.mul_comm u2 v1, Int.add_comm]
    have hDiag : u1 * u2 + u2 * u1 = 2 * (u1 * u2) := by
      rw [Int.mul_comm u2 u1]
      omega
    rw [hComm1, hDiag]
    exact ⟨rfl, Int.mul_emod_right 2 (u1 * u2)⟩

end CommonGround.Frontier.TropicalFenchelSinkhornAndParityDuality
