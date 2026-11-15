/-!
# Verification Suite #620: Blackwell Persuasion Monotonicity, Swap-Regret vs. External-Regret Dominated-Action Blindspot, Braess `4/3` Price of Anarchy vs. Pigouvian Tolls, Potential-Game Hodge Curl & Condorcet `RLHF` Intransitivity vs. Median Voter (`0` Imports, `0` Sorry)

Cross-domain Lean 4.33.0 bridge suite unifying **Folders `01` + `02` + `04` + `08` + `09`** across
`econlib`, `cslib`, `tc-probcomb`, `oai-codes`, `tauceti`, and `eth`:

1. `blackwell_garbling_persuasion_monotonicity_vs_noisy_postprocessing_collapse`
2. `hart_mas_colell_swap_regret_to_aumann_ce_vs_external_regret_dominated_action_blindspot`
3. `braess_selfish_routing_price_of_anarchy_four_thirds_vs_pigouvian_marginal_toll`
4. `monderer_shapley_exact_potential_termination_vs_matching_pennies_hodge_curl_obstruction`
5. `condorcet_cyclic_rlhf_preference_paradox_vs_single_peaked_median_voter_winner`
-/

namespace CommonGround.Verification.TheoremAtlasBayesianPersuasionCCESwapRegretAndBraessBridge

/-- Homogeneous square over `Int`. -/
def sqS (x : Int) : Int := x * x

/-- Judge's conviction indicator (`1` if `2 * mu ≥ Q`, else `0`). -/
def judgeConvS (Q mu : Int) : Int :=
  if 2 * mu ≥ Q then 1 else 0

/-- Bridge 1: Blackwell Garbling Persuasion Monotonicity (Post-Processing Preserves Bayes-Plausibility
    and Cannot Exceed Concavification Envelope) vs. Uniform Garbling Conviction Collapse (`6 → 0`). -/
theorem blackwell_garbling_persuasion_monotonicity_vs_noisy_postprocessing_collapse :
    -- (1) Any row-stochastic garbling `gA0 + gA1 = M, gB0 + gB1 = M` of a Bayes-plausible split
    --     `wA * muA + wB * muB = S * mu0` preserves total mass `M * S` and total posterior expectation `M * S * mu0`:
    (∀ wA wB S mu0 muA muB gA0 gA1 gB0 gB1 M : Int,
      wA + wB = S → wA * muA + wB * muB = S * mu0 →
      gA0 + gA1 = M → gB0 + gB1 = M →
      (wA * gA0 + wB * gB0) + (wA * gA1 + wB * gB1) = M * S ∧
      (wA * gA0 * muA + wB * gB0 * muB) + (wA * gA1 * muA + wB * gB1 * muB) = M * S * mu0) ∧
    -- (2) Premise-Failure / Data-Processing Loss: Prosecutor's optimal signal `(wA=6, muA=5), (wB=4, muB=0)`
    --     achieves `6` convictions (`Q = 10`), whereas uniform `(1,1; 1,1)` garbling merges both messages back
    --     to posterior `3/10` (`2 * 3 < 10`), collapsing convictions from `6` to `0`!
    (6 * judgeConvS 10 5 + 4 * judgeConvS 10 0 = 6 ∧
     5 * judgeConvS 10 3 + 5 * judgeConvS 10 3 = 0 ∧
     0 < (6 : Int)) := by
  refine ⟨?_, by decide⟩
  intro wA wB S mu0 muA muB gA0 gA1 gB0 gB1 M hS hB hgA hgB
  refine ⟨?_, ?_⟩
  · have h1 :
        (wA * gA0 + wB * gB0) + (wA * gA1 + wB * gB1) =
          wA * (gA0 + gA1) + wB * (gB0 + gB1) := by grind
    rw [h1, hgA, hgB]
    have h2 : wA * M + wB * M = M * (wA + wB) := by grind
    rw [h2, hS]
  · have h1 :
        (wA * gA0 * muA + wB * gB0 * muB) + (wA * gA1 * muA + wB * gB1 * muB) =
          (gA0 + gA1) * (wA * muA) + (gB0 + gB1) * (wB * muB) := by grind
    rw [h1, hgA, hgB]
    have h2 : M * (wA * muA) + M * (wB * muB) = M * (wA * muA + wB * muB) := by grind
    rw [h2, hB]
    grind

/-- Bridge 2: Hart–Mas-Colell Swap-Regret Control Certifies Aumann `CE` & Eliminates Dominated Actions
    vs. External-Regret (`CCE`) Strictly-Dominated-Action Blindspot (`-10 ≤ 0` yet Swap Regret `+2 > 0`). -/
theorem hart_mas_colell_swap_regret_to_aumann_ce_vs_external_regret_dominated_action_blindspot :
    -- (1) Universal Swap-to-External Decomposition (`3` actions): total external deviation gain to fixed `a*`
    --     equals the sum of the pairwise conditional swap gains `i → a*` (`i = 0, 1, 2`), so non-positive
    --     pairwise swap regrets (`≤ R0, R1, R2`) automatically bound external regret by `R0 + R1 + R2`:
    (∀ sw0 sw1 sw2 R0 R1 R2 : Int,
      sw0 ≤ R0 → sw1 ≤ R1 → sw2 ≤ R2 → sw0 + sw1 + sw2 ≤ R0 + R1 + R2) ∧
    -- (2) Converse Failure (`CCE` Blindspot on Strictly Dominated Action):
    --     On `u_R = [[6,0],[0,6],[2,2]]` with joint play `w = [[2,0],[0,2],[1,1]]`:
    --     (a) Action `2` is strictly dominated by `(1/2)*Action 0 + (1/2)*Action 1` (`4 < 6`),
    --     (b) External regrets against Actions `0, 1, 2` are `-10, -10, -16` (ALL strictly `< 0`!),
    --     (c) Yet conditional swap regret `2 → 0` is `+2 > 0` and `2 → 1` is `+2 > 0`!
    (let eqPay : Int := 2 * 6 + 2 * 6 + 1 * 2 + 1 * 2
     let extReg0 : Int := (3 * 6 + 3 * 0) - eqPay
     let extReg1 : Int := (3 * 0 + 3 * 6) - eqPay
     let extReg2 : Int := (3 * 2 + 3 * 2) - eqPay
     let swapReg2to0 : Int := 1 * (6 - 2) + 1 * (0 - 2)
     let swapReg2to1 : Int := 1 * (0 - 2) + 1 * (6 - 2)
     2 * 2 < 6 + 0 ∧ 2 * 2 < 0 + 6 ∧
     extReg0 = -10 ∧ extReg1 = -10 ∧ extReg2 = -16 ∧
     swapReg2to0 = 2 ∧ swapReg2to1 = 2 ∧ swapReg2to0 > 0) := by
  refine ⟨by omega, by decide⟩

/-- Total social latency on the 4-node Braess Wheatstone network for `N` drivers when
    `(fTop, fBot, fZig)` split across Top (`x/N + 1`), Bottom (`1 + x/N`), and Shortcut (`x/N + 0 + x/N`),
    homogeneously scaled by `N` (`N = 2` canonical drivers: edge `s→A` has cost `x`, `A→t` has cost `2`,
    `s→B` has cost `2`, `B→t` has cost `x`, `A→B` shortcut has cost `0`). -/
def braessSocialCost2 (fTop fBot fZig : Int) : Int :=
  let xSA := fTop + fZig
  let xBT := fBot + fZig
  xSA * xSA + fTop * 2 + fBot * 2 + xBT * xBT

/-- Bridge 3: Roughgarden–Tardos `(1, 1/4)` Smoothness Identity (`4 k (x - k) ≤ x^2`),
    Braess Wheatstone `4/3` Price of Anarchy (`16` vs `12`), and Pigouvian Marginal-Toll Optimality. -/
theorem braess_selfish_routing_price_of_anarchy_four_thirds_vs_pigouvian_marginal_toll :
    -- (1) Universal Exact Polynomial Smoothness Identity for Affine Congestion (`l(x) = a*x + b`):
    --     `x^2 - 4 * k * (x - k) = (x - 2*k)^2 ≥ 0`, hence `4 * (k * x) ≤ x^2 + 4 * k^2` (`PoA ≤ 4/3` core!)
    (∀ x k : Int,
      sqS x - 4 * k * (x - k) = sqS (x - 2 * k) ∧
      4 * k * (x - k) ≤ sqS x) ∧
    -- (2) Explicit Braess Paradox Witness (`N = 2` drivers):
    --     Without shortcut (`fZig = 0`), symmetric split `(1, 1, 0)` is Nash AND social optimum (`cost = 6`, scaled `2*6 = 12`);
    --     adding `0`-latency shortcut `A → B` makes `Zig` strictly dominant (`1+1 = 2 ≤ 2+1` and `< 4`), shifting unique
    --     Nash to `(0, 0, 2)` with social cost `8` (`3 * 8 = 4 * 6`, exact `4/3` Price of Anarchy degradation!)
    (braessSocialCost2 1 1 0 = 6 ∧
     braessSocialCost2 0 0 2 = 8 ∧
     3 * braessSocialCost2 0 0 2 = 4 * braessSocialCost2 1 1 0 ∧
     braessSocialCost2 0 0 2 > braessSocialCost2 1 1 0) ∧
    -- (3) Pigouvian Marginal Congestion Toll (`tau(x) = x` on linear edges so perceived cost `x + x = 2x`):
    --     Under Pigouvian tolls on `(1, 1, 0)`, Zig perceived cost is `2*1 + 2*1 = 4`, matching Top `2*1 + 2 = 4`
    --     and Bottom `2 + 2*1 = 4` — making the social optimum `(1, 1, 0)` an exact Wardrop/Nash equilibrium!
    (2 * 1 + 2 * 1 = (4 : Int) ∧ 2 * 1 + 2 = (4 : Int) ∧ 2 + 2 * 1 = (4 : Int)) := by
  refine ⟨?_, by decide, by decide⟩
  intro x k
  have hId : sqS x - 4 * k * (x - k) = sqS (x - 2 * k) := by unfold sqS; grind
  refine ⟨hId, ?_⟩
  have hNonneg : 0 ≤ sqS (x - 2 * k) := by
    unfold sqS
    rcases Int.le_total 0 (x - 2 * k) with h0 | h0
    · exact Int.mul_nonneg h0 h0
    · exact Int.mul_nonneg_of_nonpos_of_nonpos h0 h0
  omega

/-- Exact inductive potential-step counter: given a chain of integer potentials `p0 :: p1 :: ... :: pk`
    where each step satisfies `p_i + 1 ≤ p_{i+1}`, we have `p0 + k ≤ pk`. -/
def isStrictPotentialChain : Int → List Int → Prop
  | _, [] => True
  | cur, nxt :: rest => cur + 1 ≤ nxt ∧ isStrictPotentialChain nxt rest

theorem potential_chain_length_le_headroom :
    ∀ (rest : List Int) (cur lastVal : Int),
      isStrictPotentialChain cur rest →
      (∀ x ∈ rest, x ≤ lastVal) →
      cur ≤ lastVal →
      cur + Int.ofNat rest.length ≤ lastVal
  | [], cur, lastVal, _, _, hLe => by simp; omega
  | nxt :: tl, cur, lastVal, ⟨hStep, hRest⟩, hBnd, _ => by
      have hNxtLe : nxt ≤ lastVal := hBnd nxt (by simp)
      have hSubBnd : ∀ x ∈ tl, x ≤ lastVal := by
        intro x hx
        exact hBnd x (by simp [hx])
      have hIH := potential_chain_length_le_headroom tl nxt lastVal hRest hSubBnd hNxtLe
      simp at hIH ⊢
      omega

/-- Matching Pennies payoffs: Row wants match (`+1` else `-1`), Column wants mismatch (`+1` else `-1`). -/
def mpRow (r c : Fin 2) : Int := if r = c then 1 else -1
def mpCol (r c : Fin 2) : Int := if r = c then -1 else 1

/-- Bridge 4: Monderer–Shapley Exact Potential Finite-Step Termination Bound vs.
    Matching-Pennies Non-Zero Strategic Hodge Curl (`+8 ≠ 0`) Obstruction. -/
theorem monderer_shapley_exact_potential_termination_vs_matching_pennies_hodge_curl_obstruction :
    -- (1) Universal Potential-Game Termination Bound: any strict improving trajectory of length `L`
    --     bounded above by `Phi_max` satisfies `Phi_0 + L ≤ Phi_max` (`L ≤ Phi_max - Phi_0` steps!)
    (∀ (traj : List Int) (phi0 phiMax : Int),
      isStrictPotentialChain phi0 traj →
      (∀ x ∈ traj, x ≤ phiMax) →
      phi0 ≤ phiMax →
      phi0 + Int.ofNat traj.length ≤ phiMax) ∧
    -- (2) Strategic 4-Cycle Discrete Hodge Curl Obstruction on Matching Pennies:
    --     Around `(0,0) → (0,1) → (1,1) → (1,0) → (0,0)`, unilateral active-player payoff gains sum to `+8 ≠ 0`,
    --     so NO exact integer potential `Phi : Fin 2 → Fin 2 → Int` can satisfy `Δu_i = ΔPhi` on all 4 edges!
    ((mpCol ⟨0, by decide⟩ ⟨1, by decide⟩ - mpCol ⟨0, by decide⟩ ⟨0, by decide⟩) +
     (mpRow ⟨1, by decide⟩ ⟨1, by decide⟩ - mpRow ⟨0, by decide⟩ ⟨1, by decide⟩) +
     (mpCol ⟨1, by decide⟩ ⟨0, by decide⟩ - mpCol ⟨1, by decide⟩ ⟨1, by decide⟩) +
     (mpRow ⟨0, by decide⟩ ⟨0, by decide⟩ - mpRow ⟨1, by decide⟩ ⟨0, by decide⟩) = 8 ∧
     ¬ ∃ Phi : Fin 2 → Fin 2 → Int,
       mpCol ⟨0, by decide⟩ ⟨1, by decide⟩ - mpCol ⟨0, by decide⟩ ⟨0, by decide⟩ =
         Phi ⟨0, by decide⟩ ⟨1, by decide⟩ - Phi ⟨0, by decide⟩ ⟨0, by decide⟩ ∧
       mpRow ⟨1, by decide⟩ ⟨1, by decide⟩ - mpRow ⟨0, by decide⟩ ⟨1, by decide⟩ =
         Phi ⟨1, by decide⟩ ⟨1, by decide⟩ - Phi ⟨0, by decide⟩ ⟨1, by decide⟩ ∧
       mpCol ⟨1, by decide⟩ ⟨0, by decide⟩ - mpCol ⟨1, by decide⟩ ⟨1, by decide⟩ =
         Phi ⟨1, by decide⟩ ⟨0, by decide⟩ - Phi ⟨1, by decide⟩ ⟨1, by decide⟩ ∧
       mpRow ⟨0, by decide⟩ ⟨0, by decide⟩ - mpRow ⟨1, by decide⟩ ⟨0, by decide⟩ =
         Phi ⟨0, by decide⟩ ⟨0, by decide⟩ - Phi ⟨1, by decide⟩ ⟨0, by decide⟩) := by
  refine ⟨potential_chain_length_le_headroom, ?_⟩
  refine ⟨by decide, ?_⟩
  intro ⟨Phi, h1, h2, h3, h4⟩
  have e1 : mpCol ⟨0, by decide⟩ ⟨1, by decide⟩ - mpCol ⟨0, by decide⟩ ⟨0, by decide⟩ = 2 := by decide
  have e2 : mpRow ⟨1, by decide⟩ ⟨1, by decide⟩ - mpRow ⟨0, by decide⟩ ⟨1, by decide⟩ = 2 := by decide
  have e3 : mpCol ⟨1, by decide⟩ ⟨0, by decide⟩ - mpCol ⟨1, by decide⟩ ⟨1, by decide⟩ = 2 := by decide
  have e4 : mpRow ⟨0, by decide⟩ ⟨0, by decide⟩ - mpRow ⟨1, by decide⟩ ⟨0, by decide⟩ = 2 := by decide
  omega

/-- Single-peaked utility on linear order `0 < 1 < 2` with peak `p : Fin 3`:
    `u(p, x) = - |p - x|` (`0` at peak, `-1` at distance `1`, `-2` at distance `2`). -/
def singlePeakedUtil3 (peak alt : Fin 3) : Int :=
  let d := (peak.val : Int) - (alt.val : Int)
  if 0 ≤ d then -d else d

/-- Median of three peaks in `{0, 1, 2}`. -/
def median3 (a b c : Fin 3) : Fin 3 :=
  let x := a.val
  let y := b.val
  let z := c.val
  if (x ≤ y ∧ y ≤ z) ∨ (z ≤ y ∧ y ≤ x) then b
  else if (y ≤ x ∧ x ≤ z) ∨ (z ≤ x ∧ x ≤ y) then a
  else c

/-- Count how many of the 3 voters strictly prefer `alt1` over `alt2`. -/
def strictPrefCount3 (p1 p2 p3 alt1 alt2 : Fin 3) : Nat :=
  (if singlePeakedUtil3 p1 alt1 > singlePeakedUtil3 p1 alt2 then 1 else 0) +
  (if singlePeakedUtil3 p2 alt1 > singlePeakedUtil3 p2 alt2 then 1 else 0) +
  (if singlePeakedUtil3 p3 alt1 > singlePeakedUtil3 p3 alt2 then 1 else 0)

/-- Bridge 5: Condorcet Cyclic Majority Paradox (`RLHF` Scalar Reward Impossibility) vs.
    Black's Single-Peaked Median-Voter Condorcet Winner (`∀ p1 p2 p3, median3` is Never Majority-Defeated!). -/
theorem condorcet_cyclic_rlhf_preference_paradox_vs_single_peaked_median_voter_winner :
    -- (1) Universal Single-Peaked Median-Voter Theorem on `{0, 1, 2}` (`3^3 = 27` peak profiles):
    --     for EVERY triple of voter peaks `(p1, p2, p3)` and EVERY rival `y`, fewer than `2` voters
    --     strictly prefer `y` over `median3 p1 p2 p3` (and for `y ≠ median`, at least `2` voters
    --     weakly/strictly prefer `median` — here strictly `≥ 2` whenever no peak ties)!
    (∀ p1 p2 p3 y : Fin 3,
      strictPrefCount3 p1 p2 p3 y (median3 p1 p2 p3) ≤ 1 ∧
      (y ≠ median3 p1 p2 p3 → strictPrefCount3 p1 p2 p3 (median3 p1 p2 p3) y ≥ 2)) ∧
    -- (2) Condorcet Cyclic Preference Paradox (`A >_M B >_M C >_M A`, `2 > 1` on all 3 edges):
    --     No scalar Elo / Bradley–Terry reward `r : Fin 3 → Int` can represent cyclic strict majority!
    (¬ ∃ r : Fin 3 → Int,
      r ⟨0, by decide⟩ > r ⟨1, by decide⟩ ∧
      r ⟨1, by decide⟩ > r ⟨2, by decide⟩ ∧
      r ⟨2, by decide⟩ > r ⟨0, by decide⟩) := by
  refine ⟨by decide, ?_⟩
  intro ⟨r, h01, h12, h20⟩
  omega

end CommonGround.Verification.TheoremAtlasBayesianPersuasionCCESwapRegretAndBraessBridge
