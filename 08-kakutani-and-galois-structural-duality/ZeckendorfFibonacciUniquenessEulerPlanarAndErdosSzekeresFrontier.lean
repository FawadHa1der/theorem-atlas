/-!
# Historic `850`-File Milestone Frontier (`Frontier #162`): Zeckendorf Non-Adjacent Fibonacci Uniqueness, Euler Planar `K₅`/`K₃,₃` Impossibility & Erdős–Szekeres Universal Pigeonhole Bound

Pure Lean 4.33.0 zero-sorry frontier module (zero external imports) formalizing three universal
cross-domain theorems with constructive proofs AND explicit premise-failure counterexamples:

1. **Zeckendorf (`1972`) Non-Adjacent Fibonacci Uniqueness & Tail-Sum Ceiling**
   (`tc-numtheory` ↔ `oai-codes` ↔ `cslib`):
   - `zeckendorf_sparse_sum_lt_next_fib`: For EVERY non-adjacent strictly-decreasing Fibonacci
     index list `k :: rest` (`i ≥ j + 2`), `zeckSum (k :: rest) < fib (k + 1)` universally!
   - `zeckendorf_uniqueness_universal`: Any two valid Zeckendorf representations with equal sum
     are **identically equal** (`L₁ = L₂`) across ALL `Nat`!
   - `zeckendorf_adjacent_index_collision_counterexample`: Dropping the non-adjacency gap (`i ≥ j + 2`)
     causes immediate representation collision (`zeckSum [1, 0] = 2 + 1 = 3 = zeckSum [2]`),
     breaking self-synchronizing `11`-delimited Fibonacci universal codes!

2. **Euler (`1752`) Planar Polyhedral Edge Bounds (`E ≤ 3V - 6`, Bipartite `E ≤ 2V - 4`) & `K₅`/`K₃,₃` Non-Planarity vs. Torus (`g = 1`) Escape**
   (`tc-topology` ↔ `cslib` ↔ `apsp3sum`):
   - `euler_planar_edge_bound_universal`: `V - E + F = 2 ∧ 3*F ≤ 2*E → E + 6 ≤ 3*V`.
   - `euler_bipartite_planar_edge_bound_universal`: `V - E + F = 2 ∧ 4*F ≤ 2*E → E + 4 ≤ 2*V`.
   - `k5_and_k33_nonplanar_universal`: NO `F : Nat` admits a planar embedding of `K₅` (`V=5, E=10`)
     or triangle-free `K₃,₃` (`V=6, E=9`).
   - `torus_genus1_k5_k33_embedding_escape`: Dropping genus `g = 0` (`χ = 2`) for a Torus
     (`g = 1`, `χ = 0`) allows BOTH `K₅` (`V=5, E=10, F=5`) and `K₃,₃` (`V=6, E=9, F=3`) to embed!

3. **Erdős–Szekeres (`1935`) Universal Pigeonhole Monotone-Subsequence Principle vs. Tight `r·s` Grid**
   (`tc-probcomb` ↔ `cslib` ↔ `econlib`):
   - `erdos_szekeres_pair_injection`: On ANY pairwise-distinct sequence `a : Fin N → Int`, the
     longest-increasing / longest-decreasing pair map `i ↦ (inc i, dec i)` is strictly injective!
   - `erdos_szekeres_universal_pigeonhole`: For ALL `r, s, N : Nat` with `r * s < N`, every
     valid `(inc, dec)` DP labeling MUST witness some index `i` with `inc i > r ∨ dec i > s`!
   - `erdos_szekeres_tight_rs_and_duplicate_counterexamples`: At `N = 3 * 3 = 9`, the explicit
     sequence `[3, 2, 1, 6, 5, 4, 9, 8, 7]` has `maxStrictInc = 3` and `maxStrictDec = 3`
     (strictly tight!), and dropping distinctness on `[5, 5, 5, 5, 5]` (`N = 5 > 2*2`) collapses
     both strict lengths to `1`!
-/

namespace ZeckendorfEulerErdosSzekeresFrontier

/-! ## Section 1: Zeckendorf (`1972`) Non-Adjacent Fibonacci Uniqueness vs. Adjacent Collision -/

/-- Fibonacci numbers starting at `fib 0 = 1, fib 1 = 2, fib 2 = 3, fib 3 = 5, fib 4 = 8, ...` -/
def fib : Nat → Nat
  | 0 => 1
  | 1 => 2
  | n + 2 => fib (n + 1) + fib n

theorem fib_pos (n : Nat) : 0 < fib n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | k + 2 =>
      simp only [fib]
      have h1 := ih (k + 1) (by omega)
      have h2 := ih k (by omega)
      omega

theorem fib_mono : ∀ {a b : Nat}, a ≤ b → fib a ≤ fib b := by
  intro a b hab
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ b ih =>
    by_cases heq : a = b + 1
    · subst heq; exact Nat.le_refl _
    · have hle : a ≤ b := by omega
      have h1 := ih hle
      have hstep : fib b ≤ fib (b + 1) := by
        cases b with
        | zero => decide
        | succ m =>
          simp only [fib]
          omega
      omega

def zeckSum : List Nat → Nat
  | [] => 0
  | k :: rest => fib k + zeckSum rest

/-- Valid Zeckendorf index list: strictly decreasing with non-adjacency gap `i ≥ j + 2`. -/
inductive ZeckValid : List Nat → Prop where
  | nil : ZeckValid []
  | single (k : Nat) : ZeckValid [k]
  | cons {k j : Nat} {rest : List Nat} (hgap : j + 2 ≤ k) (hrest : ZeckValid (j :: rest)) :
      ZeckValid (k :: j :: rest)

/-- Universal Zeckendorf Tail-Sum Ceiling: ANY valid non-adjacent Fibonacci sum starting at
    index `k` is STRICTLY less than the next Fibonacci number `fib (k + 1)`! -/
theorem zeckendorf_sparse_sum_lt_next_fib_aux :
    ∀ {L : List Nat}, ZeckValid L → match L with
      | [] => True
      | k :: rest => zeckSum (k :: rest) < fib (k + 1) := by
  intro L hval
  induction hval with
  | nil => trivial
  | single m =>
    simp only [zeckSum, Nat.add_zero]
    cases m with
    | zero => decide
    | succ m' =>
      simp only [fib]
      have hp := fib_pos m'
      omega
  | @cons k j rest hgap hrest ih =>
    simp only [zeckSum]
    have hmono : fib (j + 1) ≤ fib (k - 1) := fib_mono (by omega)
    have hsplit : fib (k + 1) = fib k + fib (k - 1) := by
      cases k with
      | zero => omega
      | succ k' =>
        simp only [fib, Nat.add_sub_cancel]
    have hrest_lt : fib j + zeckSum rest < fib (j + 1) := by
      simpa [zeckSum] using ih
    omega

theorem zeckendorf_sparse_sum_lt_next_fib {k : Nat} {rest : List Nat}
    (hval : ZeckValid (k :: rest)) : zeckSum (k :: rest) < fib (k + 1) :=
  zeckendorf_sparse_sum_lt_next_fib_aux hval

/-- Universal Zeckendorf Uniqueness: for ALL valid non-adjacent index lists `L₁, L₂ : List Nat`,
    `zeckSum L₁ = zeckSum L₂` forces `L₁ = L₂` identically! -/
theorem zeckendorf_uniqueness_universal :
    ∀ {L1 L2 : List Nat}, ZeckValid L1 → ZeckValid L2 → zeckSum L1 = zeckSum L2 → L1 = L2 := by
  intro L1
  induction L1 with
  | nil =>
    intro L2 _ _ hsum
    cases L2 with
    | nil => rfl
    | cons k rest =>
      simp only [zeckSum] at hsum
      have hp := fib_pos k
      omega
  | cons k1 r1 ih =>
    intro L2 hv1 hv2 hsum
    cases L2 with
    | nil =>
      simp only [zeckSum] at hsum
      have hp := fib_pos k1
      omega
    | cons k2 r2 =>
      have hk_eq : k1 = k2 := by
        by_cases hlt : k1 < k2
        · have h1 := zeckendorf_sparse_sum_lt_next_fib hv1
          have h2 : fib (k1 + 1) ≤ fib k2 := fib_mono (by omega)
          have hge : fib k2 ≤ zeckSum (k2 :: r2) := by simp [zeckSum]
          omega
        · by_cases hgt : k2 < k1
          · have h2 := zeckendorf_sparse_sum_lt_next_fib hv2
            have h1 : fib (k2 + 1) ≤ fib k1 := fib_mono (by omega)
            have hge : fib k1 ≤ zeckSum (k1 :: r1) := by simp [zeckSum]
            omega
          · omega
      subst hk_eq
      have hrest_sum : zeckSum r1 = zeckSum r2 := by
        simp only [zeckSum] at hsum
        omega
      have hv1' : ZeckValid r1 := by
        cases hv1 with
        | single => exact ZeckValid.nil
        | cons _ hr => exact hr
      have hv2' : ZeckValid r2 := by
        cases hv2 with
        | single => exact ZeckValid.nil
        | cons _ hr => exact hr
      rw [ih hv1' hv2' hrest_sum]

/-- Explicit Premise-Failure Counterexample (Dropping Non-Adjacency Gap `i ≥ j + 2`):
    Valid Zeckendorf `[5, 2, 0]` (`13 + 3 + 1 = 17`) is unique, whereas allowing adjacent indices
    `[1, 0]` collides with `[2]` (`2 + 1 = 3`) and `[4, 3]` collides with `[5]` (`8 + 5 = 13`)! -/
theorem zeckendorf_adjacent_index_collision_counterexample :
    ZeckValid [5, 2, 0] ∧
    zeckSum [5, 2, 0] = 17 ∧
    zeckSum [1, 0] = zeckSum [2] ∧
    ([1, 0] : List Nat) ≠ [2] ∧
    zeckSum [4, 3] = zeckSum [5] ∧
    ([4, 3] : List Nat) ≠ [5] := by
  refine ⟨ZeckValid.cons (by omega) (ZeckValid.cons (by omega) (ZeckValid.single 0)), by decide⟩

/-! ## Section 2: Euler (`1752`) Planar Edge Bounds (`K₅`, `K₃,₃`) vs. Torus (`g = 1`) Embedding Escape -/

/-- Universal Euler Planar Edge Bound: for ANY connected planar embedding (`V - E + F = 2`,
    integer form `(V : Int) - E + F = 2`) where every face has boundary length `≥ 3` (`3F ≤ 2E`),
    edges satisfy `E + 6 ≤ 3 * V` (`E ≤ 3V - 6`)! -/
theorem euler_planar_edge_bound_universal (V E F : Nat)
    (heuler : (V : Int) - (E : Int) + (F : Int) = 2) (hface : 3 * F ≤ 2 * E) :
    E + 6 ≤ 3 * V := by
  omega

/-- Universal Bipartite / Triangle-Free Planar Edge Bound: when every face has length `≥ 4`
    (`4F ≤ 2E`), edges satisfy `E + 4 ≤ 2 * V` (`E ≤ 2V - 4`)! -/
theorem euler_bipartite_planar_edge_bound_universal (V E F : Nat)
    (heuler : (V : Int) - (E : Int) + (F : Int) = 2) (hface : 4 * F ≤ 2 * E) :
    E + 4 ≤ 2 * V := by
  omega

/-- Universal Kuratowski Non-Planarity Corollaries:
    - `K₅` (`V = 5, E = 10`) has NO planar face count `F : Nat` with `V - E + F = 2 ∧ 3F ≤ 2E`.
    - `K₃,₃` (`V = 6, E = 9`) has NO triangle-free planar face count `F : Nat` with `V - E + F = 2 ∧ 4F ≤ 2E`. -/
theorem k5_and_k33_nonplanar_universal :
    (¬ ∃ F : Nat, (5 : Int) - 10 + (F : Int) = 2 ∧ 3 * F ≤ 2 * 10) ∧
    (¬ ∃ F : Nat, (6 : Int) - 9 + (F : Int) = 2 ∧ 4 * F ≤ 2 * 9) := by
  constructor
  · intro ⟨F, he, hf⟩; have := euler_planar_edge_bound_universal 5 10 F he hf; omega
  · intro ⟨F, he, hf⟩; have := euler_bipartite_planar_edge_bound_universal 6 9 F he hf; omega

/-- Universal Orientable Genus-`g` Edge Bound (`χ = 2 - 2g`): `E + 6 ≤ 3V + 6g` (and bipartite
    `E + 4 ≤ 2V + 4g`), explaining why lifting from the sphere (`g = 0`) to a Torus (`g = 1`,
    `χ = 0`) admits exact embeddings of BOTH `K₅` (`V=5, E=10, F=5`) and `K₃,₃` (`V=6, E=9, F=3`)! -/
theorem torus_genus1_k5_k33_embedding_escape :
    (∀ V E F g : Nat, (V : Int) - (E : Int) + (F : Int) = 2 - 2 * (g : Int) → 3 * F ≤ 2 * E →
      E + 6 ≤ 3 * V + 6 * g) ∧
    (((5 : Int) - 10 + 5 = 2 - 2 * 1 ∧ 3 * 5 ≤ 2 * 10) ∧
     ((6 : Int) - 9 + 3 = 2 - 2 * 1 ∧ 4 * 3 ≤ 2 * 9)) := by
  refine ⟨?_, by decide⟩
  intro V E F g he hf
  omega

/-! ## Section 3: Erdős–Szekeres (`1935`) Universal Pigeonhole Monotone Subsequence vs. Tight `r·s` Grid -/

/-- Pure-core Finite Pigeonhole Principle: there is NO injective map from `Fin N` into `Fin M`
    when `M < N` (proved by structural induction on `M` via value-deletion swap). -/
theorem fin_pigeonhole_no_inj :
    ∀ (M N : Nat), M < N → ∀ (f : Fin N → Fin M), ¬ (∀ i j : Fin N, f i = f j → i = j) := by
  intro M
  induction M with
  | zero =>
    intro N hlt f _
    exact Fin.elim0 (f ⟨0, hlt⟩)
  | succ M ih =>
    intro N hlt f hinj
    let lastIdx : Fin N := ⟨N - 1, by omega⟩
    let lastVal : Fin (M + 1) := f lastIdx
    have hneq_last : ∀ (i : Fin (N - 1)), (f ⟨i.val, by omega⟩).val ≠ lastVal.val := by
      intro i hv
      have h1 : (⟨i.val, by omega⟩ : Fin N) = lastIdx := hinj ⟨i.val, by omega⟩ lastIdx (Fin.ext hv)
      have h2 : i.val = N - 1 := congrArg (fun x : Fin N => x.val) h1
      omega
    let g : Fin (N - 1) → Fin M := fun i =>
      let v := f ⟨i.val, by omega⟩
      if hltv : v.val < lastVal.val then
        ⟨v.val, by omega⟩
      else
        ⟨v.val - 1, by
          have hne := hneq_last i
          omega⟩
    have hg_inj : ∀ i j : Fin (N - 1), g i = g j → i = j := by
      intro i j hEq
      have hval : (g i).val = (g j).val := congrArg (fun x : Fin M => x.val) hEq
      have hne_i := hneq_last i
      have hne_j := hneq_last j
      have hfeq : f ⟨i.val, by omega⟩ = f ⟨j.val, by omega⟩ := by
        apply Fin.ext
        dsimp only [g] at hval
        by_cases hi_lt : (f ⟨i.val, by omega⟩).val < lastVal.val <;>
        by_cases hj_lt : (f ⟨j.val, by omega⟩).val < lastVal.val <;>
        simp [hi_lt, hj_lt] at hval <;> omega
      have hij : (⟨i.val, by omega⟩ : Fin N) = ⟨j.val, by omega⟩ := hinj _ _ hfeq
      have hval_ij : i.val = j.val := congrArg (fun x : Fin N => x.val) hij
      exact Fin.ext hval_ij
    exact ih (N - 1) (by omega) g hg_inj

/-- Universal Erdős–Szekeres Pair Injection: on ANY pairwise-distinct sequence `a : Fin N → Int`,
    any DP labeling `(inc, dec)` satisfying the monotone extension inequalities maps every index
    `i : Fin N` to a STRICTLY DISTINCT pair `(inc i, dec i)`! -/
theorem erdos_szekeres_pair_injection {N : Nat} (a : Fin N → Int) (inc dec : Fin N → Nat)
    (hdist : ∀ i j : Fin N, i.val < j.val → a i ≠ a j)
    (hinc : ∀ i j : Fin N, i.val < j.val → a i < a j → inc i < inc j)
    (hdec : ∀ i j : Fin N, i.val < j.val → a j < a i → dec i < dec j) :
    ∀ i j : Fin N, inc i = inc j → dec i = dec j → i = j := by
  intro i j hi hd
  by_cases hlt : i.val < j.val
  · exfalso
    have hne := hdist i j hlt
    by_cases hord : a i < a j
    · have := hinc i j hlt hord; omega
    · have := hdec i j hlt (by omega); omega
  · by_cases hgt : j.val < i.val
    · exfalso
      have hne := hdist j i hgt
      by_cases hord : a j < a i
      · have := hinc j i hgt hord; omega
      · have := hdec j i hgt (by omega); omega
    · exact Fin.ext (by omega)

/-- Universal Erdős–Szekeres (`1935`) Theorem: for ALL `r, s, N : Nat` with `r * s < N`,
    on ANY pairwise-distinct sequence `a : Fin N → Int` with valid positive DP labels `inc, dec ≥ 1`,
    there MUST exist an index `i : Fin N` witnessing either `r < inc i` (an increasing subsequence
    of length `≥ r + 1`) or `s < dec i` (a decreasing subsequence of length `≥ s + 1`)! -/
theorem erdos_szekeres_universal_pigeonhole {r s N : Nat} (hN : r * s < N)
    (a : Fin N → Int) (inc dec : Fin N → Nat)
    (hpos_inc : ∀ i, 1 ≤ inc i) (hpos_dec : ∀ i, 1 ≤ dec i)
    (hdist : ∀ i j : Fin N, i.val < j.val → a i ≠ a j)
    (hinc : ∀ i j : Fin N, i.val < j.val → a i < a j → inc i < inc j)
    (hdec : ∀ i j : Fin N, i.val < j.val → a j < a i → dec i < dec j) :
    ∃ i : Fin N, r < inc i ∨ s < dec i := by
  by_cases hex : ∃ i : Fin N, r < inc i ∨ s < dec i
  · exact hex
  · exfalso
    have hbound : ∀ i : Fin N, inc i ≤ r ∧ dec i ≤ s := by
      intro i
      by_cases h1 : r < inc i
      · exact False.elim (hex ⟨i, Or.inl h1⟩)
      · by_cases h2 : s < dec i
        · exact False.elim (hex ⟨i, Or.inr h2⟩)
        · exact ⟨by omega, by omega⟩
    have hs_pos : 0 < s := by
      have h0 : Fin N := ⟨0, by omega⟩
      have := hpos_dec h0
      have := (hbound h0).2
      omega
    let f : Fin N → Fin (r * s) := fun i =>
      ⟨(inc i - 1) * s + (dec i - 1), by
        have hb := hbound i
        have hp1 := hpos_inc i
        have hp2 := hpos_dec i
        have hmul : (inc i - 1) * s + s ≤ r * s := by
          have : (inc i - 1 + 1) * s ≤ r * s := Nat.mul_le_mul_right s (by omega)
          rw [Nat.add_mul, Nat.one_mul] at this
          exact this
        omega⟩
    have hf_inj : ∀ i j : Fin N, f i = f j → i = j := by
      intro i j hEq
      have hval : (inc i - 1) * s + (dec i - 1) = (inc j - 1) * s + (dec j - 1) :=
        congrArg Fin.val hEq
      have hbi := hbound i
      have hbj := hbound j
      have hpi := hpos_inc i
      have hpj := hpos_inc j
      have hpdi := hpos_dec i
      have hpdj := hpos_dec j
      have hdiv : ((inc i - 1) * s + (dec i - 1)) / s = ((inc j - 1) * s + (dec j - 1)) / s :=
        congrArg (· / s) hval
      have hmod : ((inc i - 1) * s + (dec i - 1)) % s = ((inc j - 1) * s + (dec j - 1)) % s :=
        congrArg (· % s) hval
      have hdi : ((inc i - 1) * s + (dec i - 1)) / s = inc i - 1 := by
        rw [Nat.mul_comm, Nat.mul_add_div hs_pos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
      have hdj : ((inc j - 1) * s + (dec j - 1)) / s = inc j - 1 := by
        rw [Nat.mul_comm, Nat.mul_add_div hs_pos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
      have hmi : ((inc i - 1) * s + (dec i - 1)) % s = dec i - 1 := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      have hmj : ((inc j - 1) * s + (dec j - 1)) % s = dec j - 1 := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      rw [hdi, hdj] at hdiv
      rw [hmi, hmj] at hmod
      exact erdos_szekeres_pair_injection a inc dec hdist hinc hdec i j (by omega) (by omega)
    exact fin_pigeonhole_no_inj (r * s) N hN f hf_inj

/-- Longest strictly increasing / decreasing subsequence length helper for finite lists. -/
def lisEndsAt (xs : List Int) : List (Int × Nat) :=
  xs.foldl (fun acc x =>
    let best := acc.foldl (fun m p => if p.1 < x && m < p.2 then p.2 else m) 0
    acc ++ [(x, best + 1)]) []

def ldsEndsAt (xs : List Int) : List (Int × Nat) :=
  xs.foldl (fun acc x =>
    let best := acc.foldl (fun m p => if x < p.1 && m < p.2 then p.2 else m) 0
    acc ++ [(x, best + 1)]) []

def maxLen (ps : List (Int × Nat)) : Nat :=
  ps.foldl (fun m p => if m < p.2 then p.2 else m) 0

/-- Explicit Premise-Failure Counterexamples:
    1. Tight `N = r * s = 9` Grid (`[3, 2, 1, 6, 5, 4, 9, 8, 7]`): dropping strict excess `N > 9`
       yields `LIS = 3 ≤ 3` AND `LDS = 3 ≤ 3` (no monotone subsequence of length `4` exists!).
    2. Dropping distinctness (`[5, 5, 5, 5, 5]`, `N = 5 > 2*2`): strict `LIS = 1` AND strict `LDS = 1`! -/
theorem erdos_szekeres_tight_rs_and_duplicate_counterexamples :
    let tight9 : List Int := [3, 2, 1, 6, 5, 4, 9, 8, 7]
    let const5 : List Int := [5, 5, 5, 5, 5]
    tight9.length = 9 ∧
    maxLen (lisEndsAt tight9) = 3 ∧
    maxLen (ldsEndsAt tight9) = 3 ∧
    const5.length = 5 ∧
    maxLen (lisEndsAt const5) = 1 ∧
    maxLen (ldsEndsAt const5) = 1 := by
  decide

end ZeckendorfEulerErdosSzekeresFrontier
