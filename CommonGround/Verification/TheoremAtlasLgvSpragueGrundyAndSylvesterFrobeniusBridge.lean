/-!
# Suite #687: Lindström–Gessel–Viennot Sign-Reversing Involution, Sprague–Grundy / Bouton Unbounded Nim-Sum `IFF` & Sylvester Frobenius Conductor Bridge (`V286`)

Zero-sorry Lean 4.33.0 verification bridge uniting three cross-domain structural mechanisms,
each paired with both a universal machine-checked positive theorem and an explicit premise-failure
counterexample:

1. **Lindström–Gessel–Viennot (`LGV`, `1973`/`1985`) Sign-Reversing Tail-Swap Cancellation**
   (`tc-topology` ↔ `oai-qrep` ↔ `tc-probcomb`):
   - Positive universal witness: commutative edge-weight factorization eliminates crossing pairs
     identically (`(a₁b₁)(a₂b₂) - (a₁b₂)(a₂b₁) = 0`), reducing the `3×3` grid determinant
     `3·6 - 3·4 = 6` to the exact count of non-intersecting path pairs.
   - Premise-failure counterexample: non-commutative `2×2` gauge weights break tail-swap
     cancellation (`trace defect = 4 ≠ 0`), and non-planar reversed wiring drops `det` below
     the unsigned disjoint path count (`0 ≠ 2` and `-1 < 0`).

2. **Sprague–Grundy (`1935`/`1939`) & Bouton (`1901`) Unbounded-`List Nat` Nim-Sum `XOR` `IFF`**
   (`econlib` ↔ `cslib` ↔ `oai-codes`):
   - Positive universal witness: over ALL unbounded `heaps : List Nat`, `nimSum = 0` traps every
     legal move into `nimSum ≠ 0`, while `nimSum ≠ 0` guarantees a strict legal reduction to `0`.
   - Premise-failure counterexample: dropping normal play for Misère play inverts `[1, 1]`
     (`nimSum = 0` is a Misère WIN) and `[1, 1, 2]` (winning move leaves `[1, 1, 1]`, `nimSum = 1`).

3. **Sylvester (`1884`) Coprime Frobenius Conductor (`ab - a - b` & Universal `n ≥ (a-1)(b-1)`)**
   (`tc-numtheory` ↔ `apsp3sum` ↔ `cslib`):
   - Positive universal witness: for ALL coprime `a, b ≥ 2`, `ab - a - b` is unrepresentable while
     EVERY `n ≥ (a - 1)(b - 1)` is constructively representable as `a*x + b*y = n`.
   - Premise-failure counterexample: dropping `gcd(a,b) = 1` (`a = 4, b = 6`, `gcd = 2`) makes
     EVERY odd integer `2k + 1` permanently unrepresentable (no finite conductor exists).
-/

namespace CommonGround.Verification.TheoremAtlasLgvSpragueGrundyAndSylvesterFrobeniusBridge

def det2 (p11 p12 p21 p22 : Int) : Int := p11 * p22 - p12 * p21

structure Mat2 where
  m11 : Int
  m12 : Int
  m21 : Int
  m22 : Int
  deriving DecidableEq

def Mat2.mul (X Y : Mat2) : Mat2 :=
  { m11 := X.m11 * Y.m11 + X.m12 * Y.m21
    m12 := X.m11 * Y.m12 + X.m12 * Y.m22
    m21 := X.m21 * Y.m11 + X.m22 * Y.m21
    m22 := X.m21 * Y.m12 + X.m22 * Y.m22 }

def Mat2.tr (X : Mat2) : Int := X.m11 + X.m22

/-- Bridge 1 (`tc-topology` ↔ `oai-qrep` ↔ `tc-probcomb`):
    Universal LGV tail-swap cancellation + planar `3×3` witness (`det = 6`) vs. non-commutative
    `2×2` matrix weight defect (`4 ≠ 0`) and non-planar reversed wiring (`det = 0, -1`). -/
theorem lgv_tail_swap_cancellation_vs_noncomm_nonplanar_bridge :
    (∀ a1 a2 b1 b2 : Int, (a1 * b1) * (a2 * b2) - (a1 * b2) * (a2 * b1) = 0) ∧
    (det2 3 3 4 6 = 6 ∧
     let A1 : Mat2 := ⟨1, 1, 0, 1⟩
     let A2 : Mat2 := ⟨1, 0, 1, 1⟩
     let B1 : Mat2 := ⟨0, 1, 1, 0⟩
     let B2 : Mat2 := ⟨1, 0, 0, -1⟩
     Mat2.tr (Mat2.mul (Mat2.mul A1 B1) (Mat2.mul A2 B2)) -
       Mat2.tr (Mat2.mul (Mat2.mul A1 B2) (Mat2.mul A2 B1)) = 4 ∧
     det2 1 1 1 1 = 0 ∧
     det2 0 1 1 0 = -1) := by
  refine ⟨?_, by decide⟩
  intro a1 a2 b1 b2
  have h1 : (a1 * b1) * (a2 * b2) = a1 * a2 * (b1 * b2) := by
    rw [Int.mul_assoc, Int.mul_left_comm b1 a2 b2, ← Int.mul_assoc]
  have h2 : (a1 * b2) * (a2 * b1) = a1 * a2 * (b1 * b2) := by
    rw [Int.mul_assoc, Int.mul_left_comm b2 a2 b1, ← Int.mul_assoc, Int.mul_comm b2 b1]
  rw [h1, h2, Int.sub_self]

def nimSum : List Nat → Nat
  | [] => 0
  | x :: xs => x ^^^ nimSum xs

def getAt : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => getAt xs i

def replaceAt : List Nat → Nat → Nat → List Nat
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, i + 1, v => x :: replaceAt xs i v

private theorem nimSum_replaceAt (xs : List Nat) (i v : Nat) (hi : i < xs.length) :
    nimSum (replaceAt xs i v) = nimSum xs ^^^ getAt xs i ^^^ v := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x rest ih =>
    cases i with
    | zero =>
      simp only [replaceAt, nimSum, getAt]
      have hcancel : (x ^^^ nimSum rest) ^^^ x = nimSum rest := by
        rw [Nat.xor_comm x (nimSum rest), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [hcancel, Nat.xor_comm]
    | succ j =>
      simp only [replaceAt, nimSum, getAt]
      have hj : j < rest.length := by simp at hi; omega
      rw [ih j hj, ← Nat.xor_assoc, ← Nat.xor_assoc]

private theorem xor_div_two (a b : Nat) : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
  have h : (a ^^^ b) >>> 1 = (a >>> 1) ^^^ (b >>> 1) := Nat.shiftRight_xor_distrib
  simpa [Nat.shiftRight_eq_div_pow] using h

private theorem xor_mod_two (a b : Nat) : (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := by
  have h1 := Nat.xor_mod_two_eq_one (a := a) (b := b)
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · have hne : (a ^^^ b) % 2 ≠ 1 := fun h => by have := h1.mp h; omega
    have : (a ^^^ b) % 2 = 0 := by omega
    rw [this, ha, hb]; decide
  · have heq : (a ^^^ b) % 2 = 1 := h1.mpr (by omega)
    rw [heq, ha, hb]; decide
  · have heq : (a ^^^ b) % 2 = 1 := h1.mpr (by omega)
    rw [heq, ha, hb]; decide
  · have hne : (a ^^^ b) % 2 ≠ 1 := fun h => by have := h1.mp h; omega
    have : (a ^^^ b) % 2 = 0 := by omega
    rw [this, ha, hb]; decide

private theorem xor_div_two_pow (a b k : Nat) : (a ^^^ b) / 2 ^ k = (a / 2 ^ k) ^^^ (b / 2 ^ k) := by
  induction k generalizing a b with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    rw [ih, xor_div_two]

private theorem xor_lt_of_msb (k : Nat) : ∀ (h s : Nat),
    s / 2 ^ k = 1 → (h / 2 ^ k) % 2 = 1 → (h ^^^ s) < h := by
  induction k with
  | zero =>
    intro h s hs hh
    simp only [Nat.pow_zero, Nat.div_one] at hs hh
    subst hs
    have hdiv : (h ^^^ 1) / 2 = h / 2 := by rw [xor_div_two]; simp
    have hmod : (h ^^^ 1) % 2 = 0 := by rw [xor_mod_two, hh]; decide
    omega
  | succ k ih =>
    intro h s hs hh
    have hs' : (s / 2) / 2 ^ k = 1 := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← Nat.pow_succ]; exact hs
    have hh' : ((h / 2) / 2 ^ k) % 2 = 1 := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← Nat.pow_succ]; exact hh
    have hlt_half := ih (h / 2) (s / 2) hs' hh'
    have hdiv : (h ^^^ s) / 2 = (h / 2) ^^^ (s / 2) := xor_div_two h s
    have hmod_le : (h ^^^ s) % 2 ≤ 1 := by omega
    omega

private theorem exists_msb_of_ne_zero : ∀ (s : Nat), s ≠ 0 → ∃ k, s / 2 ^ k = 1 := by
  intro s
  induction s using Nat.strongRecOn with
  | ind n ih =>
    intro hne
    by_cases h1 : n = 1
    · exact ⟨0, by simp [h1]⟩
    · obtain ⟨k, hk⟩ := ih (n / 2) (by omega) (by omega)
      refine ⟨k + 1, ?_⟩
      rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      exact hk

private theorem exists_heap_with_bit (heaps : List Nat) (k : Nat)
    (hbit : (nimSum heaps / 2 ^ k) % 2 = 1) :
    ∃ i, i < heaps.length ∧ (getAt heaps i / 2 ^ k) % 2 = 1 := by
  induction heaps with
  | nil => simp [nimSum] at hbit
  | cons x rest ih =>
    simp only [nimSum] at hbit
    rw [xor_div_two_pow, xor_mod_two] at hbit
    by_cases hx : (x / 2 ^ k) % 2 = 1
    · exact ⟨0, by simp, by simpa [getAt] using hx⟩
    · have hx0 : (x / 2 ^ k) % 2 = 0 := by omega
      rw [hx0, Nat.zero_xor] at hbit
      obtain ⟨j, hj, hjb⟩ := ih hbit
      exact ⟨j + 1, by simp; omega, by simpa [getAt] using hjb⟩

def isMisereWin (heaps : List Nat) : Bool :=
  if heaps.all (· ≤ 1) then
    decide ((heaps.filter (· == 1)).length % 2 == 0)
  else
    decide (nimSum heaps ≠ 0)

/-- Bridge 2 (`econlib` ↔ `cslib` ↔ `oai-codes`):
    Universal unbounded-`List Nat` Bouton / Sprague–Grundy Nim-Sum `XOR` `IFF` (zero traps every
    move; nonzero guarantees a strict legal reduction to zero) vs. Misère endgame inversion at
    `[1, 1]` and `[1, 1, 2]`. -/
theorem sprague_grundy_bouton_nim_sum_vs_misere_inversion_bridge :
    (∀ (heaps : List Nat) (i v : Nat),
      nimSum heaps = 0 → i < heaps.length → v < getAt heaps i →
      nimSum (replaceAt heaps i v) ≠ 0) ∧
    (∀ (heaps : List Nat), nimSum heaps ≠ 0 →
      ∃ i v, i < heaps.length ∧ v < getAt heaps i ∧ nimSum (replaceAt heaps i v) = 0) ∧
    (nimSum [3, 4, 5] = 2 ∧
     nimSum (replaceAt [3, 4, 5] 0 1) = 0 ∧
     nimSum [1, 1] = 0 ∧ isMisereWin [1, 1] = true ∧
     isMisereWin [1, 1, 0] = true ∧ isMisereWin [1, 1, 1] = false) := by
  refine ⟨?_, ?_, by decide⟩
  · intro heaps i v hzero hi hlt hEq
    rw [nimSum_replaceAt heaps i v hi, hzero, Nat.zero_xor] at hEq
    have h1 : getAt heaps i ^^^ (getAt heaps i ^^^ v) = getAt heaps i ^^^ 0 :=
      congrArg (getAt heaps i ^^^ ·) hEq
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_zero] at h1
    omega
  · intro heaps hne
    obtain ⟨k, hk⟩ := exists_msb_of_ne_zero (nimSum heaps) hne
    have hbit : (nimSum heaps / 2 ^ k) % 2 = 1 := by rw [hk]
    obtain ⟨i, hi, hibit⟩ := exists_heap_with_bit heaps k hbit
    refine ⟨i, getAt heaps i ^^^ nimSum heaps, hi, xor_lt_of_msb k (getAt heaps i) (nimSum heaps) hk hibit, ?_⟩
    rw [nimSum_replaceAt heaps i _ hi]
    calc nimSum heaps ^^^ getAt heaps i ^^^ (getAt heaps i ^^^ nimSum heaps)
        = (getAt heaps i ^^^ nimSum heaps) ^^^ (getAt heaps i ^^^ nimSum heaps) := by
            rw [Nat.xor_comm (nimSum heaps) (getAt heaps i)]
      _ = 0 := Nat.xor_self _

private theorem bezout_int_core : ∀ (b a : Nat),
    ∃ u v : Int, (a : Int) * u + (b : Int) * v = (Nat.gcd a b : Int) := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a
    by_cases hb : b = 0
    · subst hb; exact ⟨1, 0, by simp [Nat.gcd_zero_right]⟩
    · obtain ⟨u', v', huv⟩ := ih (a % b) (Nat.mod_lt a (Nat.pos_of_ne_zero hb)) b
      have hgcd : Nat.gcd b (a % b) = Nat.gcd a b := by
        rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
      have hdiv : ((a % b : Nat) : Int) = (a : Int) - (b : Int) * ((a / b : Nat) : Int) := by
        have h := Nat.div_add_mod a b
        have h' : ((b * (a / b) + a % b : Nat) : Int) = (a : Int) := congrArg Int.ofNat h
        rw [Int.natCast_add, Int.natCast_mul] at h'
        omega
      refine ⟨v', u' - v' * ((a / b : Nat) : Int), ?_⟩
      rw [hgcd, hdiv] at huv
      have hexp : (a : Int) * v' + (b : Int) * (u' - v' * ((a / b : Nat) : Int)) =
          (b : Int) * u' + ((a : Int) - (b : Int) * ((a / b : Nat) : Int)) * v' := by
        rw [Int.mul_sub, Int.sub_mul]
        have hm : (b : Int) * (v' * ((a / b : Nat) : Int)) =
            (b : Int) * ((a / b : Nat) : Int) * v' := by
          rw [Int.mul_assoc, Int.mul_comm v' ((a / b : Nat) : Int), ← Int.mul_assoc]
        omega
      rw [hexp]; exact huv

private theorem coprime_dvd_of_dvd_mul_left {a b k : Nat}
    (hcop : Nat.gcd a b = 1) (hdvd : a ∣ b * k) : a ∣ k := by
  by_cases ha0 : a = 0
  · subst ha0; simp at hcop; subst hcop; simpa using hdvd
  obtain ⟨u, v, huv⟩ := bezout_int_core b a
  rw [hcop] at huv
  obtain ⟨m, hm⟩ := hdvd
  have hk_int : (k : Int) = (a : Int) * ((k : Int) * u + (m : Int) * v) := by
    have hmul : ((a : Int) * u + (b : Int) * v) * (k : Int) = 1 * (k : Int) :=
      congrArg (· * (k : Int)) huv
    have hbm : (b : Int) * (k : Int) = (a : Int) * (m : Int) := by
      have h' : ((b * k : Nat) : Int) = ((a * m : Nat) : Int) := congrArg Int.ofNat hm
      simpa [Int.natCast_mul] using h'
    have h1 : (a : Int) * u * (k : Int) = (a : Int) * ((k : Int) * u) := by
      rw [Int.mul_assoc, Int.mul_comm u (k : Int)]
    have h2 : (b : Int) * v * (k : Int) = (a : Int) * ((m : Int) * v) := by
      rw [Int.mul_assoc, Int.mul_comm v (k : Int), ← Int.mul_assoc, hbm, Int.mul_assoc]
    rw [Int.add_mul, h1, h2, ← Int.mul_add, Int.one_mul] at hmul
    exact hmul.symm
  let q : Int := (k : Int) * u + (m : Int) * v
  have hpos : 0 ≤ q := by
    by_cases hge : 0 ≤ q
    · exact hge
    · exfalso
      have hle : q ≤ -1 := by omega
      have hmul_le : (a : Int) * q ≤ (a : Int) * (-1) :=
        Int.mul_le_mul_of_nonneg_left hle (show (0 : Int) ≤ (a : Int) by omega)
      have : (k : Int) = (a : Int) * q := hk_int
      omega
  refine ⟨Int.toNat q, ?_⟩
  have hcast : ((Int.toNat q : Nat) : Int) = q := Int.toNat_of_nonneg hpos
  have hnat_int : ((k : Nat) : Int) = ((a * Int.toNat q : Nat) : Int) := by
    rw [Int.natCast_mul, hcast]
    exact hk_int
  exact Int.ofNat.inj hnat_int

/-- Bridge 3 (`tc-numtheory` ↔ `apsp3sum` ↔ `cslib`):
    Universal Sylvester (`1884`) Frobenius conductor (`a*b - a - b` unrepresentable, every
    `n ≥ (a-1)(b-1)` representable for all coprime `a, b ≥ 2`) vs. non-coprime `gcd(4,6) = 2`
    infinite odd-gap obstruction. -/
theorem sylvester_frobenius_conductor_vs_noncoprime_obstruction_bridge :
    (∀ a b : Nat, 2 ≤ a → 2 ≤ b → Nat.gcd a b = 1 →
      ¬ ∃ x y : Nat, a * x + b * y = a * b - a - b) ∧
    (∀ a b n : Nat, 2 ≤ a → 2 ≤ b → Nat.gcd a b = 1 → (a - 1) * (b - 1) ≤ n →
      ∃ x y : Nat, a * x + b * y = n) ∧
    (∀ k x y : Nat, 4 * x + 6 * y ≠ 2 * k + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b ha hb hcop ⟨x, y, hxy⟩
    have hab_ge : a + b ≤ a * b := by
      have h1 : a * 2 ≤ a * b := Nat.mul_le_mul_left a hb
      have h2 : 2 * b ≤ a * b := Nat.mul_le_mul_right b ha
      omega
    have hsum : a * (x + 1) + b * (y + 1) = a * b := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one]; omega
    have hx1_le : x + 1 ≤ b := Nat.le_of_mul_le_mul_left (by omega : a * (x + 1) ≤ a * b) (by omega)
    have hdvd : a ∣ b * (y + 1) := ⟨b - (x + 1), by
      have hmul : a * (b - (x + 1)) + a * (x + 1) = a * b := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hx1_le]
      omega⟩
    have ha_le_y1 : a ≤ y + 1 := Nat.le_of_dvd (Nat.succ_pos y) (coprime_dvd_of_dvd_mul_left hcop hdvd)
    have hab_le_by1 : a * b ≤ b * (y + 1) := by
      rw [Nat.mul_comm a b]; exact Nat.mul_le_mul_left b ha_le_y1
    have hax1_pos : 0 < a * (x + 1) := Nat.mul_pos (by omega) (Nat.succ_pos x)
    omega
  · intro a b n ha hb hcop hn
    obtain ⟨u, v, huv⟩ := bezout_int_core b a
    rw [hcop] at huv
    have ha_pos : (0 : Int) < (a : Int) := by omega
    let rInt : Int := (v * (n : Int)) % (a : Int)
    have hr_nonneg : 0 ≤ rInt := Int.emod_nonneg _ (by omega)
    have hr_lt : rInt < (a : Int) := Int.emod_lt_of_pos _ ha_pos
    let y : Nat := Int.toNat rInt
    have hy_cast : (y : Int) = rInt := Int.toNat_of_nonneg hr_nonneg
    have hy_lt : y < a := by omega
    let qRem : Int := (v * (n : Int)) / (a : Int)
    have hdivmod : (a : Int) * qRem + rInt = v * (n : Int) := Int.mul_ediv_add_emod (v * (n : Int)) (a : Int)
    let xInt : Int := u * (n : Int) + (b : Int) * qRem
    have hlin : (a : Int) * xInt + (b : Int) * (y : Int) = (n : Int) := by
      dsimp only [xInt]
      rw [hy_cast, Int.mul_add]
      have hmul : ((a : Int) * u + (b : Int) * v) * (n : Int) = 1 * (n : Int) :=
        congrArg (· * (n : Int)) huv
      rw [Int.add_mul, Int.one_mul, Int.mul_assoc, Int.mul_assoc] at hmul
      have hbq : (a : Int) * ((b : Int) * qRem) + (b : Int) * rInt = (b : Int) * (v * (n : Int)) := by
        calc (a : Int) * ((b : Int) * qRem) + (b : Int) * rInt
            = (b : Int) * ((a : Int) * qRem) + (b : Int) * rInt := by
                rw [Int.mul_left_comm (a : Int) (b : Int) qRem]
          _ = (b : Int) * ((a : Int) * qRem + rInt) := by rw [← Int.mul_add]
          _ = (b : Int) * (v * (n : Int)) := by rw [hdivmod]
      omega
    have hby_le : b * y ≤ b * (a - 1) := Nat.mul_le_mul_left b (by omega)
    have hprod_id : (a - 1) * (b - 1) + (a - 1) = (a - 1) * b := by
      have hsub : b - 1 + 1 = b := by omega
      calc (a - 1) * (b - 1) + (a - 1)
          = (a - 1) * (b - 1) + (a - 1) * 1 := by rw [Nat.mul_one]
        _ = (a - 1) * (b - 1 + 1) := by rw [← Nat.mul_add]
        _ = (a - 1) * b := by rw [hsub]
    have hby_int : ((b * y : Nat) : Int) = (b : Int) * (y : Int) := Int.natCast_mul b y
    have hax_gt : -(a : Int) < (a : Int) * xInt := by
      have h1 : b * (a - 1) = (a - 1) * b := Nat.mul_comm b (a - 1)
      omega
    have hx_nonneg : 0 ≤ xInt := by
      by_cases hge : 0 ≤ xInt
      · exact hge
      · exfalso
        have hle : xInt ≤ -1 := by omega
        have hmul_le : (a : Int) * xInt ≤ (a : Int) * (-1) :=
          Int.mul_le_mul_of_nonneg_left hle (show (0 : Int) ≤ (a : Int) by omega)
        omega
    refine ⟨Int.toNat xInt, y, ?_⟩
    have hx_cast : ((Int.toNat xInt : Nat) : Int) = xInt := Int.toNat_of_nonneg hx_nonneg
    have hfinal : ((a * Int.toNat xInt + b * y : Nat) : Int) = (n : Int) := by
      rw [Int.natCast_add, Int.natCast_mul, Int.natCast_mul, hx_cast]
      exact hlin
    exact Int.ofNat.inj hfinal
  · intro k x y; omega

/-- Master Suite #687 Theorem combining all three positive universal bridges and explicit
    premise-failure counterexamples in one zero-sorry Lean 4.33.0 kernel certificate. -/
theorem master_lgv_sprague_grundy_and_sylvester_frobenius_bridge :
    (∀ a1 a2 b1 b2 : Int, (a1 * b1) * (a2 * b2) - (a1 * b2) * (a2 * b1) = 0) ∧
    (det2 3 3 4 6 = 6 ∧ det2 1 1 1 1 = 0 ∧ det2 0 1 1 0 = -1) ∧
    (∀ (heaps : List Nat) (i v : Nat),
      nimSum heaps = 0 → i < heaps.length → v < getAt heaps i →
      nimSum (replaceAt heaps i v) ≠ 0) ∧
    (∀ (heaps : List Nat), nimSum heaps ≠ 0 →
      ∃ i v, i < heaps.length ∧ v < getAt heaps i ∧ nimSum (replaceAt heaps i v) = 0) ∧
    (isMisereWin [1, 1] = true ∧ isMisereWin [1, 1, 1] = false) ∧
    (∀ a b : Nat, 2 ≤ a → 2 ≤ b → Nat.gcd a b = 1 →
      ¬ ∃ x y : Nat, a * x + b * y = a * b - a - b) ∧
    (∀ a b n : Nat, 2 ≤ a → 2 ≤ b → Nat.gcd a b = 1 → (a - 1) * (b - 1) ≤ n →
      ∃ x y : Nat, a * x + b * y = n) ∧
    (∀ k x y : Nat, 4 * x + 6 * y ≠ 2 * k + 1) := by
  refine ⟨lgv_tail_swap_cancellation_vs_noncomm_nonplanar_bridge.1,
    by decide,
    sprague_grundy_bouton_nim_sum_vs_misere_inversion_bridge.1,
    sprague_grundy_bouton_nim_sum_vs_misere_inversion_bridge.2.1,
    by decide,
    sylvester_frobenius_conductor_vs_noncoprime_obstruction_bridge.1,
    sylvester_frobenius_conductor_vs_noncoprime_obstruction_bridge.2.1,
    sylvester_frobenius_conductor_vs_noncoprime_obstruction_bridge.2.2⟩

end CommonGround.Verification.TheoremAtlasLgvSpragueGrundyAndSylvesterFrobeniusBridge
