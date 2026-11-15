/-
  Common Ground — Verification Suite #627 (`CommonGround/Verification`)
  Cross-Domain Bridge: Discrete Brouwer No-Retraction Wheel Obstruction,
  Lemke–Howson Complementary-Pivot Parity, Gale–Shapley Stable-Matching Lattice
  vs. Irving Roommates Odd-Cycle Collapse, Kakutani Convex-Hull Rescue,
  and Exact Integer Galois Adjunction

  Zero imports (`Init`-only pure Lean 4.33.0 kernel verification).
  Zero `sorry`, `admit`, or `sorryAx`.
-/

namespace CommonGround.Verification.TheoremAtlasSpernerParityWalrasianEquilibriumGaleShapleyLatticeAndBrouwerRetractionBridge

/-!
  ## 1. Discrete Brouwer No-Retraction Obstruction on the 6-Triangle Wheel of `Δ₂`
        vs. Contractible 2-Edge Horn Retraction
-/

def isRainbow3 (a b c : Nat) : Bool :=
  (a == 0 || b == 0 || c == 0) &&
  (a == 1 || b == 1 || c == 1) &&
  (a == 2 || b == 2 || c == 2)

/-- Count of `{0, 1, 2}` rainbow triangles across the 6 wheel triangles of `Δ₂`
    with corners `(0, 1, 2)`, boundary edge midpoints `(m01, m12, m02)`,
    and interior hub color `hub`. -/
def wheelRainbowCount (m01 m12 m02 hub : Nat) : Nat :=
  (if isRainbow3 0 m01 hub then 1 else 0) +
  (if isRainbow3 m01 1 hub then 1 else 0) +
  (if isRainbow3 1 m12 hub then 1 else 0) +
  (if isRainbow3 m12 2 hub then 1 else 0) +
  (if isRainbow3 2 m02 hub then 1 else 0) +
  (if isRainbow3 m02 0 hub then 1 else 0)

/-- Discrete Brouwer No-Retraction Theorem on the 7-Vertex Wheel Subdivision:
    for EVERY boundary-preserving choice (`m01 ∈ {0,1}`, `m12 ∈ {1,2}`, `m02 ∈ {0,2}`)
    and EVERY interior hub label `hub ∈ {0,1,2}`, at least one wheel simplex spans all 3
    boundary vertices `{0, 1, 2}` (so NO simplicial retraction `Δ₂ → ∂Δ₂` exists!). -/
theorem discrete_brouwer_no_retraction_wheel
    (b01 b12 b02 : Bool) (hub : Fin 3) :
    let m01 := if b01 then 1 else 0
    let m12 := if b12 then 2 else 1
    let m02 := if b02 then 2 else 0
    1 ≤ wheelRainbowCount m01 m12 m02 hub.val ∧
    wheelRainbowCount m01 m12 m02 hub.val % 2 = 1 := by
  revert b01 b12 b02 hub
  decide

/-- Premise-Failure Counterexample 1 (Contractible 2-Edge Horn `0 — 1 — 2`):
    Removing face `{0, 2}` from `∂Δ₂` (allowing `m02 = 1`) makes the target contractible:
    setting `m01 = 1, m12 = 1, m02 = 1, hub = 1` yields `0` rainbow triangles! -/
theorem contractible_horn_allows_simplicial_retraction :
    wheelRainbowCount 1 1 1 1 = 0 := by
  decide

/-!
  ## 2. Lemke–Howson Complementary-Pivot Parity (`deg` Handshaking → Odd True Equilibria)
        vs. Unbounded Ray Escape
-/

def sumDeg : (V : Nat) → (Fin V → Nat) → Nat
  | 0, _ => 0
  | n + 1, d =>
    sumDeg n (fun i => d ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + d ⟨n, Nat.lt_succ_self n⟩

def oddDegCount : (V : Nat) → (Fin V → Nat) → Nat
  | 0, _ => 0
  | n + 1, d =>
    oddDegCount n (fun i => d ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) +
      (d ⟨n, Nat.lt_succ_self n⟩ % 2)

/-- Universal Parity Identity: `oddDegCount V d % 2 = sumDeg V d % 2` for every degree sequence. -/
theorem oddDegCount_mod2_eq_sumDeg_mod2 : ∀ (V : Nat) (d : Fin V → Nat),
    oddDegCount V d % 2 = sumDeg V d % 2
  | 0, _ => rfl
  | n + 1, d => by
    simp only [oddDegCount, sumDeg]
    have ih := oddDegCount_mod2_eq_sumDeg_mod2 n (fun i => d ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    omega

/-- Lemke–Howson Complementary-Pivot Existence & Oddness Theorem:
    in any finite undirected pivot graph (`sumDeg V d = 2 * numEdges`) where the artificial
    `0`-strategy endpoint accounts for `1` odd-degree vertex (`oddDegCount V d = trueNashCount + 1`),
    `trueNashCount` is strictly ODD (`trueNashCount % 2 = 1`) and `1 ≤ trueNashCount`! -/
theorem lemke_howson_odd_nash_existence
    (V numEdges trueNashCount : Nat) (d : Fin V → Nat)
    (hHandshake : sumDeg V d = 2 * numEdges)
    (hSplit : oddDegCount V d = trueNashCount + 1) :
    trueNashCount % 2 = 1 ∧ 1 ≤ trueNashCount := by
  have hpar := oddDegCount_mod2_eq_sumDeg_mod2 V d
  rw [hHandshake, hSplit] at hpar
  exact ⟨by omega, by omega⟩

/-- Premise-Failure Counterexample 2 (Unbounded Ray Escape):
    If payoff non-degeneracy / boundedness fails so an infinite ray endpoint `v_inf` also has
    degree `1` (`oddDegCount = trueNashCount + 2` on `[1, 2, 1]`), `trueNashCount = 0` is possible! -/
def rayEscapeDeg (i : Fin 3) : Nat :=
  match i.val with
  | 0 => 1
  | 1 => 2
  | _ => 1

theorem lemke_howson_unbounded_ray_zero_nash_counterexample :
    sumDeg 3 rayEscapeDeg = 2 * 2 ∧
    oddDegCount 3 rayEscapeDeg = 0 + 2 := by
  decide

/-!
  ## 3. Gale–Shapley Stable-Matching Lattice (`M_P` vs. `M_R`) & Rural-Hospitals Invariance
        vs. Irving Non-Bipartite Stable-Roommates Odd-Cycle Collapse
-/

/-- Proposer rank of receiver `r` for proposer `p` (`0` = top choice, `2` = last choice)
    in the 3x3 Condorcet-Latin two-sided market. -/
def rankProposer (p r : Fin 3) : Nat := (r.val + 3 - p.val) % 3

/-- Receiver rank of proposer `p` for receiver `r` (`0` = top choice, `2` = last choice):
    `R0: P1 > P2 > P0`, `R1: P2 > P0 > P1`, `R2: P0 > P1 > P2`. -/
def rankReceiver (r p : Fin 3) : Nat := (p.val + 2 - r.val) % 3

/-- Pair `(p, r)` blocks matching `(mP, mR)` iff `p` strictly prefers `r` to `mP p`
    AND `r` strictly prefers `p` to `mR r`. -/
def blocksTwoSided (mP mR : Fin 3 → Fin 3) (p r : Fin 3) : Bool :=
  decide (rankProposer p r < rankProposer p (mP p) ∧
          rankReceiver r p < rankReceiver r (mR r))

def gsProposerOptP (p : Fin 3) : Fin 3 := p
def gsProposerOptR (r : Fin 3) : Fin 3 := r

def gsReceiverOptP (p : Fin 3) : Fin 3 := ⟨(p.val + 1) % 3, by omega⟩
def gsReceiverOptR (r : Fin 3) : Fin 3 := ⟨(r.val + 2) % 3, by omega⟩

/-- Positive Witness: Both `M_P` and `M_R` have `0` blocking pairs, are distinct (`M_P ≠ M_R`),
    match all 3 proposers and 3 receivers, and `M_P` gives strictly better rank to every proposer
    while `M_R` gives strictly better rank to every receiver! -/
theorem gale_shapley_extremal_stable_lattice_witness :
    (∀ p r : Fin 3, blocksTwoSided gsProposerOptP gsProposerOptR p r = false) ∧
    (∀ p r : Fin 3, blocksTwoSided gsReceiverOptP gsReceiverOptR p r = false) ∧
    gsProposerOptP ⟨0, by decide⟩ ≠ gsReceiverOptP ⟨0, by decide⟩ ∧
    (∀ p : Fin 3, rankProposer p (gsProposerOptP p) < rankProposer p (gsReceiverOptP p)) ∧
    (∀ r : Fin 3, rankReceiver r (gsReceiverOptR r) < rankReceiver r (gsProposerOptR r)) := by
  decide

/-- Premise-Failure Counterexample 3 (Irving 4-Agent Non-Bipartite Stable Roommates):
    Dropping two-sided bipartiteness on `{0, 1, 2, 3}` with preferences
    `0: 1 > 2 > 3`, `1: 2 > 0 > 3`, `2: 0 > 1 > 3`, `3: 0 > 1 > 2`
    destroys existence: EVERY perfect matching has a strict blocking pair! -/
def roomRank (a b : Fin 4) : Nat :=
  match a.val, b.val with
  | 0, 1 => 0 | 0, 2 => 1 | 0, 3 => 2
  | 1, 2 => 0 | 1, 0 => 1 | 1, 3 => 2
  | 2, 0 => 0 | 2, 1 => 1 | 2, 3 => 2
  | 3, 0 => 0 | 3, 1 => 1 | 3, 2 => 2
  | _, _ => 9

def roomBlocks (mate : Fin 4 → Fin 4) (a b : Fin 4) : Bool :=
  decide (a ≠ b ∧ roomRank a b < roomRank a (mate a) ∧ roomRank b a < roomRank b (mate b))

def roomMatch1 (a : Fin 4) : Fin 4 :=
  match a.val with | 0 => ⟨1, by decide⟩ | 1 => ⟨0, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨2, by decide⟩
def roomMatch2 (a : Fin 4) : Fin 4 :=
  match a.val with | 0 => ⟨2, by decide⟩ | 2 => ⟨0, by decide⟩ | 1 => ⟨3, by decide⟩ | _ => ⟨1, by decide⟩
def roomMatch3 (a : Fin 4) : Fin 4 :=
  match a.val with | 0 => ⟨3, by decide⟩ | 3 => ⟨0, by decide⟩ | 1 => ⟨2, by decide⟩ | _ => ⟨1, by decide⟩

theorem roommates_odd_cycle_every_perfect_matching_blocked :
    roomBlocks roomMatch1 ⟨1, by decide⟩ ⟨2, by decide⟩ = true ∧
    roomBlocks roomMatch2 ⟨0, by decide⟩ ⟨1, by decide⟩ = true ∧
    roomBlocks roomMatch3 ⟨2, by decide⟩ ⟨0, by decide⟩ = true := by
  decide

/-!
  ## 4. Kakutani Convex-Valued Best-Response Rescue of Matching Pennies
        vs. Disconnected `{0, 2}` Non-Convex Correspondence
-/

/-- Convexified Matching-Pennies best-response correspondence on `{0, 1, 2}²`
    (`0 ↔ P=0, 1 ↔ P=1/2, 2 ↔ P=1`): at indifference (`q = 1`), `p ∈ {0, 1, 2}` is convex. -/
def kakutaniConvexBR (p q : Fin 3) : Bool :=
  let br1 := (q.val == 0 && p.val == 0) || (q.val == 2 && p.val == 2) || (q.val == 1)
  let br2 := (p.val == 0 && q.val == 2) || (p.val == 2 && q.val == 0) || (p.val == 1)
  br1 && br2

/-- Non-convexified correspondence: at indifference (`q = 1`), agent refuses randomized `1`
    and only selects extreme pure points `{0, 2}` (`1 ∉ conv{0, 2}` dropped!). -/
def nonConvexExtremeBR (p q : Fin 3) : Bool :=
  let br1 := (q.val == 0 && p.val == 0) || (q.val == 2 && p.val == 2) ||
             (q.val == 1 && (p.val == 0 || p.val == 2))
  let br2 := (p.val == 0 && q.val == 2) || (p.val == 2 && q.val == 0) ||
             (p.val == 1 && (q.val == 0 || q.val == 2))
  br1 && br2

theorem kakutani_convex_unique_equilibrium_vs_nonconvex_empty :
    kakutaniConvexBR ⟨1, by decide⟩ ⟨1, by decide⟩ = true ∧
    (∀ p q : Fin 3, kakutaniConvexBR p q = true → p.val = 1 ∧ q.val = 1) ∧
    (∀ p q : Fin 3, nonConvexExtremeBR p q = false) := by
  decide

/-!
  ## 5. Exact Integer Galois Connection (`d * x ≤ y ↔ x ≤ y / d` for `d > 0`)
        vs. Negative-Multiplier Adjunction Breakdown
-/

/-- Universal Euclidean Floor-Division Galois Adjunction for Positive Scale `d > 0`:
    `d * x ≤ y ↔ x ≤ y / d`, together with counit `d * (y / d) ≤ y`. -/
theorem int_galois_adjunction_ediv (d x y : Int) (hd : 0 < d) :
    (d * x ≤ y ↔ x ≤ y / d) ∧ d * (y / d) ≤ y := by
  have hdiv := Int.mul_ediv_add_emod y d
  have hmod0 := Int.emod_nonneg y (by omega : d ≠ 0)
  have hmodlt := Int.emod_lt_of_pos y hd
  constructor
  · constructor
    · intro hle
      rcases Classical.em (x ≤ y / d) with h | hnot
      · exact h
      · have hgt : y / d + 1 ≤ x := by omega
        have hmul : d * (y / d + 1) ≤ d * x := Int.mul_le_mul_of_nonneg_left hgt (by omega)
        rw [Int.mul_add, Int.mul_one] at hmul
        omega
    · intro hle
      have hmul : d * x ≤ d * (y / d) := Int.mul_le_mul_of_nonneg_left hle (by omega)
      omega
  · omega

/-- Premise-Failure Counterexample 5:
    Dropping `0 < d` (`d = -2 < 0` at `x = 0, y = -1`) breaks the Galois equivalence:
    `(-2) * 0 ≤ -1` is FALSE (`0 ≤ -1`), whereas `0 ≤ (-1) / (-2)` is TRUE! -/
theorem negative_scale_breaks_galois_adjunction :
    ¬ ((-2 : Int) * 0 ≤ -1) ∧ (0 : Int) ≤ (-1 : Int) / (-2 : Int) := by
  decide

end CommonGround.Verification.TheoremAtlasSpernerParityWalrasianEquilibriumGaleShapleyLatticeAndBrouwerRetractionBridge
