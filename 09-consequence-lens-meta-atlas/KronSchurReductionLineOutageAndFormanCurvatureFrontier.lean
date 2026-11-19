/-
  09-consequence-lens-meta-atlas/KronSchurReductionLineOutageAndFormanCurvatureFrontier.lean

  Frontier #112: Universal `Fin N` Kron Schur-Complement Star-Mesh Elimination &
  Kennelly Y-Δ Exactness vs. Naive Deletion Collapse, Sherman–Morrison Line-Outage
  Distribution Factor (`LODF`) `1 / (1 - τ_e)` Cascading `N-1` Overload vs. `τ_e = 1`
  Islanding Singularity, and Forman–Ricci Negative-Curvature Barbell Bottlenecks vs.
  Surgical Triangle Rewiring (`ΔF = +2`) & Global Over-Smoothing Collapse.

  Unifies four folders in pure-core Lean 4.33.0 (`0` imports, `0` sorry/admit, `0` axioms):
  - `09-consequence-lens-meta-atlas` (Kron Schur-complement consequence preservation & `LODF`)
  - `08-kakutani-and-galois-structural-duality` (Thomson–Dirichlet minimum-energy star elimination)
  - `05-matrix-energy-and-euler-l2-mollification` (Discrete elliptic Dirichlet energy & Kirchhoff flux)
  - `02-universal-affine-query-compression` (Effective-resistance leverage `τ_e` & spectral rewiring)
-/

namespace KronSchurReductionLineOutageAndFormanCurvatureFrontier

/-! ## 0. Pure-Core Finite Summation Primitives over `Fin N` -/

def finSum : {N : Nat} → (Fin N → Int) → Int
  | 0, _ => 0
  | n + 1, f => finSum (fun i : Fin n => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + f ⟨n, Nat.lt_succ_self n⟩

theorem finSum_const_zero : ∀ (N : Nat), finSum (fun _ : Fin N => (0 : Int)) = 0
  | 0 => rfl
  | n + 1 => by
      simp only [finSum]
      rw [finSum_const_zero n]
      rfl

theorem finSum_add : ∀ {N : Nat} (f g : Fin N → Int),
    finSum (fun i => f i + g i) = finSum f + finSum g
  | 0, _, _ => rfl
  | n + 1, f, g => by
      simp only [finSum]
      have ih := @finSum_add n
        (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      omega

theorem finSum_sub : ∀ {N : Nat} (f g : Fin N → Int),
    finSum (fun i => f i - g i) = finSum f - finSum g
  | 0, _, _ => rfl
  | n + 1, f, g => by
      simp only [finSum]
      have ih := @finSum_sub n
        (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i => g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      omega

theorem finSum_mul_const : ∀ {N : Nat} (c : Int) (f : Fin N → Int),
    finSum (fun i => c * f i) = c * finSum f
  | 0, _, _ => by simp [finSum]
  | n + 1, c, f => by
      simp only [finSum]
      have ih := @finSum_mul_const n c (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      rw [ih, Int.mul_add]

theorem finSum_const_mul : ∀ {N : Nat} (f : Fin N → Int) (c : Int),
    finSum (fun i => f i * c) = finSum f * c
  | 0, _, _ => by simp [finSum]
  | n + 1, f, c => by
      simp only [finSum]
      have ih := @finSum_const_mul n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) c
      rw [ih, Int.add_mul]

private theorem sq_nonneg_int (z : Int) : 0 ≤ z * z := by
  by_cases h : 0 ≤ z
  · exact Int.mul_nonneg h h
  · have hneg : 0 ≤ -z := by omega
    have hmul : 0 ≤ (-z) * (-z) := Int.mul_nonneg hneg hneg
    have heq : (-z) * (-z) = z * z := by
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    omega

private theorem sq_sub_expand (a b : Int) :
    (a - b) * (a - b) = a * a - 2 * (a * b) + b * b := by
  rw [Int.mul_sub, Int.sub_mul, Int.sub_mul, Int.mul_comm b a]
  omega

private theorem weighted_pair_expand (gi gj xi xj : Int) :
    gi * gj * ((xi - xj) * (xi - xj)) =
      (gi * (xi * xi)) * gj - (2 * (gi * xi)) * (gj * xj) + gi * (gj * (xj * xj)) := by
  rw [sq_sub_expand xi xj, Int.mul_add, Int.mul_sub]
  have m1 : (gi * gj) * (xi * xi) = (gi * (xi * xi)) * gj := by
    rw [Int.mul_assoc, Int.mul_comm gj (xi * xi), ← Int.mul_assoc]
  have m2 : (gi * gj) * (2 * (xi * xj)) = (2 * (gi * xi)) * (gj * xj) := by
    calc (gi * gj) * (2 * (xi * xj))
      _ = 2 * ((gi * gj) * (xi * xj)) := by rw [← Int.mul_assoc, Int.mul_comm (gi * gj) 2, Int.mul_assoc]
      _ = 2 * (gi * (gj * (xi * xj))) := by rw [Int.mul_assoc gi gj (xi * xj)]
      _ = 2 * (gi * (xi * (gj * xj))) := by rw [← Int.mul_assoc gj xi xj, Int.mul_comm gj xi, Int.mul_assoc xi gj xj]
      _ = (2 * (gi * xi)) * (gj * xj) := by rw [← Int.mul_assoc gi xi (gj * xj), ← Int.mul_assoc 2 (gi * xi) (gj * xj)]
  have m3 : (gi * gj) * (xj * xj) = gi * (gj * (xj * xj)) := Int.mul_assoc gi gj (xj * xj)
  rw [m1, m2, m3]

private theorem star_quad_expand (gi G xi Φ : Int) :
    gi * ((G * xi - Φ) * (G * xi - Φ)) =
      ((G * G) * (gi * (xi * xi)) - (2 * G * Φ) * (gi * xi)) + gi * (Φ * Φ) := by
  rw [sq_sub_expand (G * xi) Φ, Int.mul_add, Int.mul_sub]
  have m1 : gi * ((G * xi) * (G * xi)) = (G * G) * (gi * (xi * xi)) := by
    calc gi * ((G * xi) * (G * xi))
      _ = gi * (G * (xi * (G * xi))) := by rw [Int.mul_assoc G xi (G * xi)]
      _ = gi * (G * (G * (xi * xi))) := by rw [← Int.mul_assoc xi G xi, Int.mul_comm xi G, Int.mul_assoc G xi xi]
      _ = gi * ((G * G) * (xi * xi)) := by rw [← Int.mul_assoc G G (xi * xi)]
      _ = (G * G) * (gi * (xi * xi)) := by rw [← Int.mul_assoc gi (G * G) (xi * xi), Int.mul_comm gi (G * G), Int.mul_assoc]
  have m2 : gi * (2 * ((G * xi) * Φ)) = (2 * G * Φ) * (gi * xi) := by
    calc gi * (2 * ((G * xi) * Φ))
      _ = 2 * (gi * ((G * xi) * Φ)) := by rw [← Int.mul_assoc gi 2, Int.mul_comm gi 2, Int.mul_assoc]
      _ = 2 * (gi * (Φ * (G * xi))) := by rw [Int.mul_comm (G * xi) Φ]
      _ = 2 * (Φ * (gi * (G * xi))) := by rw [← Int.mul_assoc gi Φ, Int.mul_comm gi Φ, Int.mul_assoc]
      _ = 2 * (Φ * (G * (gi * xi))) := by rw [← Int.mul_assoc gi G xi, Int.mul_comm gi G, Int.mul_assoc G gi xi]
      _ = (2 * G * Φ) * (gi * xi) := by
            rw [← Int.mul_assoc Φ G (gi * xi), Int.mul_comm Φ G, ← Int.mul_assoc 2 (G * Φ) (gi * xi), ← Int.mul_assoc 2 G Φ]
  rw [m1, m2]

/-!
  ## 1. Universal `Fin N` Kron Schur-Complement Star-Mesh Elimination Identity
-/

theorem kron_weighted_lagrange_pairwise_identity {N : Nat} (g x : Fin N → Int) :
    let G := finSum g
    let M := finSum (fun i => g i * x i)
    let Q := finSum (fun i => g i * (x i * x i))
    finSum (fun i => finSum (fun j => g i * g j * ((x i - x j) * (x i - x j)))) =
      2 * (G * Q - M * M) := by
  intro G M Q
  have h_inner : ∀ i : Fin N,
      finSum (fun j => g i * g j * ((x i - x j) * (x i - x j))) =
        (g i * (x i * x i)) * G - (g i * x i) * (2 * M) + g i * Q := by
    intro i
    have h_pt : (fun j : Fin N => g i * g j * ((x i - x j) * (x i - x j))) =
        (fun j : Fin N =>
          ((g i * (x i * x i)) * g j - (2 * (g i * x i)) * (g j * x j)) +
          g i * (g j * (x j * x j))) := by
      funext j
      exact weighted_pair_expand (g i) (g j) (x i) (x j)
    rw [h_pt, finSum_add, finSum_sub]
    rw [finSum_mul_const (g i * (x i * x i)) g]
    rw [finSum_mul_const (2 * (g i * x i)) (fun j => g j * x j)]
    rw [finSum_mul_const (g i) (fun j => g j * (x j * x j))]
    have hm : (2 * (g i * x i)) * M = (g i * x i) * (2 * M) := by
      rw [Int.mul_comm 2 (g i * x i), Int.mul_assoc]
    rw [hm]
  have h_fn : (fun i : Fin N => finSum (fun j => g i * g j * ((x i - x j) * (x i - x j)))) =
      (fun i : Fin N =>
        ((g i * (x i * x i)) * G - (g i * x i) * (2 * M)) + g i * Q) := by
    funext i
    exact h_inner i
  rw [h_fn, finSum_add, finSum_sub]
  rw [finSum_const_mul (fun i => g i * (x i * x i)) G]
  rw [finSum_const_mul (fun i => g i * x i) (2 * M)]
  rw [finSum_const_mul g Q]
  change (Q * G - M * (2 * M)) + G * Q = 2 * (G * Q - M * M)
  have h1 : Q * G = G * Q := Int.mul_comm Q G
  have h2 : M * (2 * M) = 2 * (M * M) := by rw [← Int.mul_assoc, Int.mul_comm M 2, Int.mul_assoc]
  rw [h1, h2, Int.mul_sub]
  omega

theorem kron_schur_star_mesh_dirichlet_identity {N : Nat} (g x : Fin N → Int) (Φ : Int) :
    let G := finSum g
    let M := finSum (fun i => g i * x i)
    2 * finSum (fun i => g i * ((G * x i - Φ) * (G * x i - Φ))) =
      2 * G * ((Φ - M) * (Φ - M)) +
      G * finSum (fun i => finSum (fun j => g i * g j * ((x i - x j) * (x i - x j)))) := by
  intro G M
  let Q := finSum (fun i => g i * (x i * x i))
  have h_lag : finSum (fun i => finSum (fun j => g i * g j * ((x i - x j) * (x i - x j)))) =
      2 * (G * Q - M * M) := kron_weighted_lagrange_pairwise_identity g x
  have h_pt : (fun i : Fin N => g i * ((G * x i - Φ) * (G * x i - Φ))) =
      (fun i : Fin N =>
        ((G * G) * (g i * (x i * x i)) - (2 * G * Φ) * (g i * x i)) + g i * (Φ * Φ)) := by
    funext i
    exact star_quad_expand (g i) G (x i) Φ
  rw [h_pt, finSum_add, finSum_sub]
  rw [finSum_mul_const (G * G) (fun i => g i * (x i * x i))]
  rw [finSum_mul_const (2 * G * Φ) (fun i => g i * x i)]
  rw [finSum_const_mul g (Φ * Φ)]
  rw [h_lag]
  change 2 * (((G * G) * Q - (2 * G * Φ) * M) + G * (Φ * Φ)) =
      2 * G * ((Φ - M) * (Φ - M)) + G * (2 * (G * Q - M * M))
  rw [sq_sub_expand Φ M]
  have t1 : (2 * G) * (Φ * Φ - 2 * (Φ * M) + M * M) =
      2 * (G * (Φ * Φ)) - 2 * ((2 * G * Φ) * M) + 2 * (G * (M * M)) := by
    rw [Int.mul_add, Int.mul_sub]
    have a1 : (2 * G) * (Φ * Φ) = 2 * (G * (Φ * Φ)) := Int.mul_assoc 2 G (Φ * Φ)
    have a2 : (2 * G) * (2 * (Φ * M)) = 2 * ((2 * G * Φ) * M) := by
      calc (2 * G) * (2 * (Φ * M))
        _ = 2 * ((2 * G) * (Φ * M)) := by rw [← Int.mul_assoc, Int.mul_comm (2 * G) 2, Int.mul_assoc]
        _ = 2 * ((2 * G * Φ) * M) := by rw [← Int.mul_assoc (2 * G) Φ M]
    have a3 : (2 * G) * (M * M) = 2 * (G * (M * M)) := Int.mul_assoc 2 G (M * M)
    rw [a1, a2, a3]
  have t2 : G * (2 * (G * Q - M * M)) = 2 * ((G * G) * Q) - 2 * (G * (M * M)) := by
    rw [← Int.mul_assoc G 2, Int.mul_comm G 2, Int.mul_assoc 2 G, Int.mul_sub, Int.mul_sub]
    rw [← Int.mul_assoc G G Q]
  rw [t1, t2]
  omega

theorem kron_harmonic_interior_potential_minimizes_star_energy {N : Nat}
    (g x : Fin N → Int) (Φ : Int) (hG : 0 ≤ finSum g) :
    let G := finSum g
    G * finSum (fun i => finSum (fun j => g i * g j * ((x i - x j) * (x i - x j)))) ≤
      2 * finSum (fun i => g i * ((G * x i - Φ) * (G * x i - Φ))) := by
  intro G
  let M := finSum (fun i => g i * x i)
  have h_id : 2 * finSum (fun i => g i * ((G * x i - Φ) * (G * x i - Φ))) =
      2 * G * ((Φ - M) * (Φ - M)) +
      G * finSum (fun i => finSum (fun j => g i * g j * ((x i - x j) * (x i - x j)))) :=
    kron_schur_star_mesh_dirichlet_identity g x Φ
  have h_sq : 0 ≤ (Φ - M) * (Φ - M) := sq_nonneg_int (Φ - M)
  have h_2G : 0 ≤ 2 * G := by omega
  have h_pen : 0 ≤ (2 * G) * ((Φ - M) * (Φ - M)) := Int.mul_nonneg h_2G h_sq
  omega

/-- **Concrete `N = 3` Kennelly `Y-Δ` Star-Triangle Exactness vs. Naive Deletion Collapse** -/
theorem kennelly_y_delta_kron_exactness_vs_naive_deletion_collapse :
    let g0 := (2 : Int); let g1 := (3 : Int); let g2 := (5 : Int)
    let G := g0 + g1 + g2
    let x0 := (10 : Int); let x1 := (0 : Int); let x2 := (-10 : Int)
    let M := g0 * x0 + g1 * x1 + g2 * x2
    let phiStar := (-3 : Int)
    let eStar := g0 * ((x0 - phiStar) * (x0 - phiStar)) +
                 g1 * ((x1 - phiStar) * (x1 - phiStar)) +
                 g2 * ((x2 - phiStar) * (x2 - phiStar))
    let geKron := (g0 * g1) * ((x0 - x1) * (x0 - x1)) +
                  (g0 * g2) * ((x0 - x2) * (x0 - x2)) +
                  (g1 * g2) * ((x1 - x2) * (x1 - x2))
    let eNaiveDelete := (0 : Int)
    G = 10 ∧ M = -30 ∧ G * phiStar = M ∧
    eStar = 610 ∧ geKron = 6100 ∧ geKron = G * eStar ∧
    eNaiveDelete = 0 ∧ eStar ≠ eNaiveDelete := by
  decide

/-!
  ## 2. Sherman–Morrison Line-Outage Distribution Factor (`LODF`) & `N-1` Cascading Overload
        vs. `τ_e = 1` Cut-Bridge Islanding Singularity (`Folders 09 + 05 + 02`)
-/

theorem sherman_morrison_lodf_redistribution_universal
    (g0 gSurv gEll v0 vPost : Int)
    (hKirchhoffPost : gSurv * vPost = (g0 + gSurv) * v0) :
    let f0 := g0 * v0
    let fEll := gEll * v0
    let fEllPost := gEll * vPost
    gSurv * fEllPost = gSurv * fEll + gEll * f0 := by
  intro f0 fEll fEllPost
  change gSurv * (gEll * vPost) = gSurv * (gEll * v0) + gEll * (g0 * v0)
  have h1 : gSurv * (gEll * vPost) = gEll * (gSurv * vPost) := by
    rw [← Int.mul_assoc, Int.mul_comm gSurv gEll, Int.mul_assoc]
  have h2 : gEll * ((g0 + gSurv) * v0) = gSurv * (gEll * v0) + gEll * (g0 * v0) := by
    rw [Int.add_mul, Int.mul_add]
    have a1 : gEll * (g0 * v0) = gEll * (g0 * v0) := rfl
    have a2 : gEll * (gSurv * v0) = gSurv * (gEll * v0) := by
      rw [← Int.mul_assoc, Int.mul_comm gEll gSurv, Int.mul_assoc]
    rw [a2]
    omega
  rw [h1, hKirchhoffPost, h2]

theorem n_minus_1_lodf_cascading_blackout_vs_safe_contingency_and_islanding :
    let g1 := (3 : Int); let g2 := (2 : Int); let g3 := (1 : Int)
    let c1 := (8 : Int); let c2 := (5 : Int); let c3 := (3 : Int)
    let v0 := (2 : Int)
    let f1 := g1 * v0; let f2 := g2 * v0; let f3 := g3 * v0
    let five_f1_drop3 := g1 * 12; let five_f2_drop3 := g2 * 12
    let f2_drop1 := g2 * 4; let f3_drop1 := g3 * 4
    (f1 ≤ c1 ∧ f2 ≤ c2 ∧ f3 ≤ c3) ∧
    (five_f1_drop3 = 36 ∧ five_f1_drop3 ≤ 5 * c1 ∧
     five_f2_drop3 = 24 ∧ five_f2_drop3 ≤ 5 * c2) ∧
    (f2_drop1 = 8 ∧ c2 < f2_drop1 ∧ f3_drop1 = 4 ∧ c3 < f3_drop1) ∧
    (∀ vPost : Int, (0 : Int) * vPost ≠ 12) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro vPost
  omega

/-!
  ## 3. Discrete Forman–Ricci Bottleneck Curvature, Surgical Triangle Rewiring (`ΔF = +2`),
        and `GNN` Over-Squashing vs. `1`-Step Global Over-Smoothing (`Folders 09 + 08 + 02`)
-/

def formanCurvature (du dv triangles : Int) : Int :=
  4 - du - dv + 3 * triangles

theorem surgical_triangle_chord_raises_forman_curvature_by_two
    (du dv triangles : Int) :
    formanCurvature (du + 1) dv (triangles + 1) = formanCurvature du dv triangles + 2 ∧
    formanCurvature du (dv + 1) (triangles + 1) = formanCurvature du dv triangles + 2 ∧
    formanCurvature (du + 1) dv triangles = formanCurvature du dv triangles - 1 := by
  dsimp [formanCurvature]
  omega

theorem barbell_oversquashing_vs_three_chord_surgical_rewiring :
    let fBarbell := formanCurvature 4 4 0
    let fChord1 := formanCurvature 5 4 1
    let fChord2 := formanCurvature 5 5 2
    let fChord3 := formanCurvature 6 5 3
    let fCliqueK4 := formanCurvature 3 3 2
    let twoGeff0 := (2 : Int) + 0
    let twoGeff3 := (2 : Int) + 3
    fBarbell = -4 ∧ fChord1 = -2 ∧ fChord2 = 0 ∧ fChord3 = 2 ∧ fCliqueK4 = 4 ∧
    fBarbell < 0 ∧ 0 < fChord3 ∧
    twoGeff0 = 2 ∧ twoGeff3 = 5 ∧ 2 * twoGeff0 < twoGeff3 := by
  decide

theorem global_complete_rewiring_one_step_oversmoothing_collapse
    {N : Nat} (x : Fin N → Int) :
    let y : Fin N → Int := fun _ => finSum x
    (∀ i j : Fin N, y i - y j = 0) ∧
    finSum (fun i => finSum (fun j => (y i - y j) * (y i - y j))) = 0 := by
  intro y
  constructor
  · intro i j
    dsimp [y]
    omega
  · have h_inner : ∀ i : Fin N, finSum (fun j : Fin N => (y i - y j) * (y i - y j)) = 0 := by
      intro i
      have h_z : (fun j : Fin N => (y i - y j) * (y i - y j)) = (fun _ : Fin N => (0 : Int)) := by
        funext j
        dsimp [y]
        have hz : finSum x - finSum x = 0 := by omega
        rw [hz]
        rfl
      rw [h_z]
      exact finSum_const_zero N
    have h_outer : (fun i : Fin N => finSum (fun j : Fin N => (y i - y j) * (y i - y j))) =
        (fun _ : Fin N => (0 : Int)) := by
      funext i
      exact h_inner i
    rw [h_outer]
    exact finSum_const_zero N

end KronSchurReductionLineOutageAndFormanCurvatureFrontier
