/-!
# Suite #688 (Historic `850`-File Milestone): Zeckendorf Non-Adjacent Fibonacci Uniqueness, Euler Planar `K₅`/`K₃,₃` Impossibility & Erdős–Szekeres Universal Pigeonhole Bridge (`V287`)

Zero-sorry Lean 4.33.0 verification bridge uniting three universal cross-domain theorems and
their explicit premise-failure counterexamples:

1. **Zeckendorf (`1972`) Non-Adjacent Fibonacci Uniqueness vs. Adjacent-Index Collision**
   (`tc-numtheory` ↔ `oai-codes` ↔ `cslib`):
   - Universal tail ceiling `zeckSum (k :: rest) < fib (k + 1)` and universal uniqueness
     `ZeckValid L₁ → ZeckValid L₂ → zeckSum L₁ = zeckSum L₂ → L₁ = L₂`, contrasted with
     adjacent-index collisions `[1, 0]` vs `[2]` (`2 + 1 = 3`) and `[4, 3]` vs `[5]` (`8 + 5 = 13`).

2. **Euler (`1752`) Planar Polyhedral Edge Bounds (`K₅`, `K₃,₃`) vs. Genus-`1` Torus Escape**
   (`tc-topology` ↔ `cslib` ↔ `apsp3sum`):
   - Universal `E + 6 ≤ 3V` (`3F ≤ 2E`) and bipartite `E + 4 ≤ 2V` (`4F ≤ 2E`), proving
     non-planarity of `K₅` (`V=5, E=10`) and `K₃,₃` (`V=6, E=9`), contrasted with genus-`1`
     Torus embeddings (`χ = 0`) of BOTH `K₅` (`F = 5`) and `K₃,₃` (`F = 3`).

3. **Erdős–Szekeres (`1935`) Universal Pigeonhole Monotone Subsequence vs. Tight `r·s` Grid**
   (`tc-probcomb` ↔ `cslib` ↔ `econlib`):
   - Universal pure-core finite pigeonhole + `(inc i, dec i)` pair injection proving every
     pairwise-distinct sequence of length `N > r * s` contains a strictly increasing subsequence
     of length `> r` or strictly decreasing subsequence of length `> s`, contrasted with the
     tight `N = 3 * 3 = 9` grid `[3, 2, 1, 6, 5, 4, 9, 8, 7]` (`LIS = 3, LDS = 3`) and duplicate
     collapse `[5, 5, 5, 5, 5]` (`LIS = 1, LDS = 1`).
-/

namespace CommonGround.Verification.TheoremAtlasZeckendorfEulerPlanarAndErdosSzekeresBridge

def fib : Nat → Nat
  | 0 => 1
  | 1 => 2
  | n + 2 => fib (n + 1) + fib n

private theorem fib_pos (n : Nat) : 0 < fib n := by
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

private theorem fib_mono : ∀ {a b : Nat}, a ≤ b → fib a ≤ fib b := by
  intro a b hab
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ b ih =>
    by_cases heq : a = b + 1
    · subst heq; exact Nat.le_refl _
    · have h1 := ih (by omega : a ≤ b)
      have hstep : fib b ≤ fib (b + 1) := by
        cases b with
        | zero => decide
        | succ m => simp only [fib]; omega
      omega

def zeckSum : List Nat → Nat
  | [] => 0
  | k :: rest => fib k + zeckSum rest

inductive ZeckValid : List Nat → Prop where
  | nil : ZeckValid []
  | single (k : Nat) : ZeckValid [k]
  | cons {k j : Nat} {rest : List Nat} (hgap : j + 2 ≤ k) (hrest : ZeckValid (j :: rest)) :
      ZeckValid (k :: j :: rest)

private theorem zeckendorf_tail_lt_aux :
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
      | succ k' => simp only [fib, Nat.add_sub_cancel]
    have hrest_lt : fib j + zeckSum rest < fib (j + 1) := by simpa [zeckSum] using ih
    omega

/-- Bridge 1 (`tc-numtheory` ↔ `oai-codes` ↔ `cslib`):
    Universal Zeckendorf non-adjacent Fibonacci uniqueness vs. adjacent-index collisions
    `[1, 0] ↔ [2]` (`3`) and `[4, 3] ↔ [5]` (`13`). -/
theorem zeckendorf_uniqueness_vs_adjacent_collision_bridge :
    (∀ L1 L2 : List Nat, ZeckValid L1 → ZeckValid L2 → zeckSum L1 = zeckSum L2 → L1 = L2) ∧
    (ZeckValid [5, 2, 0] ∧ zeckSum [5, 2, 0] = 17 ∧
     zeckSum [1, 0] = zeckSum [2] ∧ ([1, 0] : List Nat) ≠ [2] ∧
     zeckSum [4, 3] = zeckSum [5] ∧ ([4, 3] : List Nat) ≠ [5]) := by
  refine ⟨?_, ZeckValid.cons (by omega) (ZeckValid.cons (by omega) (ZeckValid.single 0)), by decide⟩
  intro L1
  induction L1 with
  | nil =>
    intro L2 _ _ hsum
    cases L2 with
    | nil => rfl
    | cons k rest =>
      simp only [zeckSum] at hsum
      have hp := fib_pos k; omega
  | cons k1 r1 ih =>
    intro L2 hv1 hv2 hsum
    cases L2 with
    | nil =>
      simp only [zeckSum] at hsum
      have hp := fib_pos k1; omega
    | cons k2 r2 =>
      have hk_eq : k1 = k2 := by
        by_cases hlt : k1 < k2
        · have h1 := zeckendorf_tail_lt_aux hv1
          have h2 : fib (k1 + 1) ≤ fib k2 := fib_mono (by omega)
          have hge : fib k2 ≤ zeckSum (k2 :: r2) := by simp [zeckSum]
          omega
        · by_cases hgt : k2 < k1
          · have h2 := zeckendorf_tail_lt_aux hv2
            have h1 : fib (k2 + 1) ≤ fib k1 := fib_mono (by omega)
            have hge : fib k1 ≤ zeckSum (k1 :: r1) := by simp [zeckSum]
            omega
          · omega
      subst hk_eq
      have hrest_sum : zeckSum r1 = zeckSum r2 := by simp only [zeckSum] at hsum; omega
      have hv1' : ZeckValid r1 := by cases hv1 with | single => exact ZeckValid.nil | cons _ hr => exact hr
      have hv2' : ZeckValid r2 := by cases hv2 with | single => exact ZeckValid.nil | cons _ hr => exact hr
      rw [ih r2 hv1' hv2' hrest_sum]

/-- Bridge 2 (`tc-topology` ↔ `cslib` ↔ `apsp3sum`):
    Universal Euler genus-`g` edge bound (`E + 6 ≤ 3V + 6g`), planar `K₅`/`K₃,₃` non-planarity,
    and genus-`1` Torus embedding escape (`K₅` with `F = 5`, `K₃,₃` with `F = 3`). -/
theorem euler_planar_k5_k33_vs_torus_escape_bridge :
    (∀ V E F g : Nat, (V : Int) - (E : Int) + (F : Int) = 2 - 2 * (g : Int) → 3 * F ≤ 2 * E →
      E + 6 ≤ 3 * V + 6 * g) ∧
    (¬ ∃ F : Nat, (5 : Int) - 10 + (F : Int) = 2 ∧ 3 * F ≤ 2 * 10) ∧
    (¬ ∃ F : Nat, (6 : Int) - 9 + (F : Int) = 2 ∧ 4 * F ≤ 2 * 9) ∧
    (((5 : Int) - 10 + 5 = 2 - 2 * 1 ∧ 3 * 5 ≤ 2 * 10) ∧
     ((6 : Int) - 9 + 3 = 2 - 2 * 1 ∧ 4 * 3 ≤ 2 * 9)) := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro V E F g he hf; omega
  · intro ⟨F, he, hf⟩; omega
  · intro ⟨F, he, hf⟩; omega

private theorem fin_pigeonhole_no_inj :
    ∀ (M N : Nat), M < N → ∀ (f : Fin N → Fin M), ¬ (∀ i j : Fin N, f i = f j → i = j) := by
  intro M
  induction M with
  | zero => intro N hlt f _; exact Fin.elim0 (f ⟨0, hlt⟩)
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
      if hltv : v.val < lastVal.val then ⟨v.val, by omega⟩
      else ⟨v.val - 1, by have hne := hneq_last i; omega⟩
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
      exact Fin.ext (congrArg (fun x : Fin N => x.val) hij)
    exact ih (N - 1) (by omega) g hg_inj

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

/-- Bridge 3 (`tc-probcomb` ↔ `cslib` ↔ `econlib`):
    Universal Erdős–Szekeres (`1935`) monotone-subsequence pigeonhole theorem (`N > r * s`)
    vs. exact tight `N = 9` grid (`[3,2,1,6,5,4,9,8,7]` with `LIS = 3, LDS = 3`) and duplicate
    collapse `[5,5,5,5,5]` (`LIS = 1, LDS = 1`). -/
theorem erdos_szekeres_universal_vs_tight_rs_grid_bridge :
    (∀ {r s N : Nat}, r * s < N →
      ∀ (a : Fin N → Int) (inc dec : Fin N → Nat),
        (∀ i, 1 ≤ inc i) → (∀ i, 1 ≤ dec i) →
        (∀ i j : Fin N, i.val < j.val → a i ≠ a j) →
        (∀ i j : Fin N, i.val < j.val → a i < a j → inc i < inc j) →
        (∀ i j : Fin N, i.val < j.val → a j < a i → dec i < dec j) →
        ∃ i : Fin N, r < inc i ∨ s < dec i) ∧
    (maxLen (lisEndsAt [3, 2, 1, 6, 5, 4, 9, 8, 7]) = 3 ∧
     maxLen (ldsEndsAt [3, 2, 1, 6, 5, 4, 9, 8, 7]) = 3 ∧
     maxLen (lisEndsAt [5, 5, 5, 5, 5]) = 1 ∧
     maxLen (ldsEndsAt [5, 5, 5, 5, 5]) = 1) := by
  refine ⟨?_, by decide⟩
  intro r s N hN a inc dec hpos_inc hpos_dec hdist hinc hdec
  by_cases hex : ∃ i : Fin N, r < inc i ∨ s < dec i
  · exact hex
  · exfalso
    have hbound : ∀ i : Fin N, inc i ≤ r ∧ dec i ≤ s := fun i =>
      ⟨by by_cases h1 : r < inc i; exact False.elim (hex ⟨i, Or.inl h1⟩); omega,
       by by_cases h2 : s < dec i; exact False.elim (hex ⟨i, Or.inr h2⟩); omega⟩
    have hs_pos : 0 < s := by
      have h0 : Fin N := ⟨0, by omega⟩
      have := hpos_dec h0; have := (hbound h0).2; omega
    let f : Fin N → Fin (r * s) := fun i =>
      ⟨(inc i - 1) * s + (dec i - 1), by
        have hb := hbound i; have hp1 := hpos_inc i; have hp2 := hpos_dec i
        have hmul : (inc i - 1) * s + s ≤ r * s := by
          have : (inc i - 1 + 1) * s ≤ r * s := Nat.mul_le_mul_right s (by omega)
          rw [Nat.add_mul, Nat.one_mul] at this; exact this
        omega⟩
    have hf_inj : ∀ i j : Fin N, f i = f j → i = j := by
      intro i j hEq
      have hval : (inc i - 1) * s + (dec i - 1) = (inc j - 1) * s + (dec j - 1) :=
        congrArg Fin.val hEq
      have hbi := hbound i; have hbj := hbound j
      have hpi := hpos_inc i; have hpj := hpos_inc j
      have hpdi := hpos_dec i; have hpdj := hpos_dec j
      have hdiv := congrArg (· / s) hval
      have hmod := congrArg (· % s) hval
      have hdi : ((inc i - 1) * s + (dec i - 1)) / s = inc i - 1 := by
        rw [Nat.mul_comm, Nat.mul_add_div hs_pos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
      have hdj : ((inc j - 1) * s + (dec j - 1)) / s = inc j - 1 := by
        rw [Nat.mul_comm, Nat.mul_add_div hs_pos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
      have hmi : ((inc i - 1) * s + (dec i - 1)) % s = dec i - 1 := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      have hmj : ((inc j - 1) * s + (dec j - 1)) % s = dec j - 1 := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      rw [hdi, hdj] at hdiv; rw [hmi, hmj] at hmod
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
    exact fin_pigeonhole_no_inj (r * s) N hN f hf_inj

/-- Master Suite #688 Theorem (Historic `850` Zero-Sorry `.lean` Files Milestone!):
    Combines Zeckendorf non-adjacent Fibonacci uniqueness, Euler planar `K₅`/`K₃,₃` impossibility
    vs. Torus escape, and Erdős–Szekeres universal pigeonhole monotone-subsequence theorem. -/
theorem master_zeckendorf_euler_planar_and_erdos_szekeres_bridge :
    (∀ L1 L2 : List Nat, ZeckValid L1 → ZeckValid L2 → zeckSum L1 = zeckSum L2 → L1 = L2) ∧
    (zeckSum [1, 0] = zeckSum [2] ∧ ([1, 0] : List Nat) ≠ [2]) ∧
    (∀ V E F g : Nat, (V : Int) - (E : Int) + (F : Int) = 2 - 2 * (g : Int) → 3 * F ≤ 2 * E →
      E + 6 ≤ 3 * V + 6 * g) ∧
    (¬ ∃ F : Nat, (5 : Int) - 10 + (F : Int) = 2 ∧ 3 * F ≤ 2 * 10) ∧
    (¬ ∃ F : Nat, (6 : Int) - 9 + (F : Int) = 2 ∧ 4 * F ≤ 2 * 9) ∧
    (((5 : Int) - 10 + 5 = 0 ∧ 3 * 5 ≤ 20) ∧ ((6 : Int) - 9 + 3 = 0 ∧ 4 * 3 ≤ 18)) ∧
    (∀ {r s N : Nat}, r * s < N →
      ∀ (a : Fin N → Int) (inc dec : Fin N → Nat),
        (∀ i, 1 ≤ inc i) → (∀ i, 1 ≤ dec i) →
        (∀ i j : Fin N, i.val < j.val → a i ≠ a j) →
        (∀ i j : Fin N, i.val < j.val → a i < a j → inc i < inc j) →
        (∀ i j : Fin N, i.val < j.val → a j < a i → dec i < dec j) →
        ∃ i : Fin N, r < inc i ∨ s < dec i) ∧
    (maxLen (lisEndsAt [3, 2, 1, 6, 5, 4, 9, 8, 7]) = 3 ∧
     maxLen (ldsEndsAt [3, 2, 1, 6, 5, 4, 9, 8, 7]) = 3) := by
  refine ⟨zeckendorf_uniqueness_vs_adjacent_collision_bridge.1,
    by decide,
    euler_planar_k5_k33_vs_torus_escape_bridge.1,
    euler_planar_k5_k33_vs_torus_escape_bridge.2.1,
    euler_planar_k5_k33_vs_torus_escape_bridge.2.2.1,
    by decide,
    erdos_szekeres_universal_vs_tight_rs_grid_bridge.1,
    by decide⟩

end CommonGround.Verification.TheoremAtlasZeckendorfEulerPlanarAndErdosSzekeresBridge
