import HodgeComputer.Verify
import HodgeComputer.Constructions.TransitiveCubic.Shear
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Universal 4-Term Binary-Cubic Divergence Core and Transitive-Cubic Reductions

This module generalizes `OneReflectionDivergenceCore` (`c = 0, d = 2, j = 0`) to
arbitrary 4-term binary cubics `f(a, b, c, d, p) = a + b*p + c*p^2 + d*p^3`
and all three quadratic target basis elements `j ∈ {0, 1, 2}` (`1, p, p^2`).
Both the First Scalar Identity and the Second Divergence Core Identity hold
identically over any commutative ring `K` (and specifically `ℂ` and `Poly`),
with exact integer-coefficient Δ-canceled quotients `Qu_j, Qp_j`.
-/

set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
noncomputable section

namespace HodgeComputer.Constructions.GeneralBinaryCubic

variable {K : Type*} [CommRing K]

def f (a b c d p : K) : K := a + b * p + c * p ^ 2 + d * p ^ 3
def fu (a b c _d p : K) : K := 3 * a + 2 * b * p + c * p ^ 2
def fp (_a b c d p : K) : K := b + 2 * c * p + 3 * d * p ^ 2
def h (a b c d p : K) : K :=
  (3 * a * c - b ^ 2) + (9 * a * d - b * c) * p + (3 * b * d - c ^ 2) * p ^ 2
def hu (a b c d p : K) : K := 2 * (3 * a * c - b ^ 2) + (9 * a * d - b * c) * p
def hp (a b c d p : K) : K := (9 * a * d - b * c) + 2 * (3 * b * d - c ^ 2) * p
def kScaled (a b c d p : K) : K := hp a b c d p * fu a b c d p - hu a b c d p * fp a b c d p
def delta (a b c d : K) : K :=
  3 * (27 * a ^ 2 * d ^ 2 - 18 * a * b * c * d + 4 * a * c ^ 3 + 4 * b ^ 3 * d - b ^ 2 * c ^ 2)

def W (a b c d p r t : K) : K := r ^ 3 + f a b c d p * t
def Z (a b c d p r t : K) : K := r ^ 3 * (r ^ 3 + 2 * f a b c d p * t)
def D (a b c d p r t : K) : K := 9 * delta a b c d * Z a b c d p r t + 4 * h a b c d p ^ 3 * t ^ 2

def dXf (a b c _d p : K) : K := 6 * a + 4 * b * p + 2 * c * p ^ 2
def dXh (a b c d p : K) : K := 8 * (3 * a * c - b ^ 2) + 6 * (9 * a * d - b * c) * p + 4 * (3 * b * d - c ^ 2) * p ^ 2
def dXW (a b c d p _r t : K) : K := dXf a b c d p * t
def dXZ (a b c d p r t : K) : K := 2 * r ^ 3 * dXf a b c d p * t
def dXD (a b c d p r t : K) : K :=
  108 * delta a b c d * Z a b c d p r t + 9 * delta a b c d * dXZ a b c d p r t +
    12 * h a b c d p ^ 2 * dXh a b c d p * t ^ 2

def dPf (_a b c d p : K) : K := fp _a b c d p
def dPh (a b c d p : K) : K := hp a b c d p
def dPW (a b c d p _r t : K) : K := dPf a b c d p * t
def dPZ (a b c d p r t : K) : K := 2 * r ^ 3 * dPf a b c d p * t
def dPD (a b c d p r t : K) : K :=
  9 * delta a b c d * dPZ a b c d p r t + 12 * h a b c d p ^ 2 * dPh a b c d p * t ^ 2

def dKr (r t : K) : K := 3 * r + 12 * t
def dKt (t : K) : K := 9 * t
def dKW (a b c d p r t : K) : K := 3 * r ^ 2 * dKr r t + f a b c d p * dKt t
def dKZ (a b c d p r t : K) : K :=
  3 * r ^ 2 * dKr r t * (r ^ 3 + 2 * f a b c d p * t) +
    r ^ 3 * (3 * r ^ 2 * dKr r t + 2 * f a b c d p * dKt t)
def dKD (a b c d p r t : K) : K :=
  9 * delta a b c d * dKZ a b c d p r t + 8 * h a b c d p ^ 3 * t * dKt t

/-- Adjugate cofactors and exact Δ-canceled quotients for target j = 0 (1). -/
def A0_0 (a b c d : K) : K := (27) * a * d ^ 2 + (-9) * b * c * d + (2) * c ^ 3
def A1_0 (a b c d : K) : K := (-9) * a * c * d + (6) * b ^ 2 * d + -(b * c ^ 2)
def A2_0 (_a b c d : K) : K := (-6) * b * d + (2) * c ^ 2
def Qu_0 (a b c d p : K) : K := (18) * a * b * d + (6) * a * c ^ 2 + (72) * a * c * d * p + (108) * a * d ^ 2 * p ^ 2 + (-4) * b ^ 2 * c + (6) * b ^ 2 * d * p + (-10) * b * c ^ 2 * p + (18) * b * c * d * p ^ 2 + (54) * b * d ^ 2 * p ^ 3 + (-10) * c ^ 3 * p ^ 2 + (-18) * c ^ 2 * d * p ^ 3
def Qp_0 (a b c d p : K) : K := (-12) * a * b * c + (-18) * a * b * d * p + (-18) * a * c ^ 2 * p + (-36) * a * c * d * p ^ 2 + (4) * b ^ 3 + (8) * b ^ 2 * c * p + (6) * b ^ 2 * d * p ^ 2 + (2) * b * c ^ 2 * p ^ 2 + (6) * b * c * d * p ^ 3 + (18) * b * d ^ 2 * p ^ 4 + (-2) * c ^ 3 * p ^ 3 + (-6) * c ^ 2 * d * p ^ 4
def dXQu_0 (a b c d p : K) : K := (180) * a * b * d + (60) * a * c ^ 2 + (576) * a * c * d * p + (648) * a * d ^ 2 * p ^ 2 + (-40) * b ^ 2 * c + (48) * b ^ 2 * d * p + (-80) * b * c ^ 2 * p + (108) * b * c * d * p ^ 2 + (216) * b * d ^ 2 * p ^ 3 + (-60) * c ^ 3 * p ^ 2 + (-72) * c ^ 2 * d * p ^ 3
def dPQp_0 (a b c d p : K) : K := (-18) * a * b * d + (-18) * a * c ^ 2 + (-72) * a * c * d * p + (8) * b ^ 2 * c + (12) * b ^ 2 * d * p + (4) * b * c ^ 2 * p + (18) * b * c * d * p ^ 2 + (72) * b * d ^ 2 * p ^ 3 + (-6) * c ^ 3 * p ^ 2 + (-24) * c ^ 2 * d * p ^ 3

theorem exact_quotient_u_0 (a b c d p : K) :
    4 * A0_0 a b c d * h a b c d p ^ 2 - A2_0 a b c d * kScaled a b c d p * hp a b c d p =
      delta a b c d * Qu_0 a b c d p := by
  simp only [A0_0, A2_0, h, kScaled, hp, hu, fu, fp, delta, Qu_0]
  ring

theorem exact_quotient_p_0 (a b c d p : K) :
    4 * A1_0 a b c d * h a b c d p ^ 2 + A2_0 a b c d * kScaled a b c d p * hu a b c d p =
      delta a b c d * Qp_0 a b c d p := by
  simp only [A1_0, A2_0, h, kScaled, hp, hu, fu, fp, delta, Qp_0]
  ring

def U_0 (a b c d p r t : K) : K :=
  9 * A0_0 a b c d * Z a b c d p r t + 3 * A2_0 a b c d * h a b c d p * W a b c d p r t * t +
    Qu_0 a b c d p * h a b c d p * t ^ 2
def V_0 (a b c d p r t : K) : K :=
  9 * A1_0 a b c d * Z a b c d p r t + 3 * A2_0 a b c d * h a b c d p * W a b c d p r t * p * t +
    Qp_0 a b c d p * h a b c d p * t ^ 2
def B_0 (a b c d p r t : K) : K := 3 * A2_0 a b c d * h a b c d p * W a b c d p r t * r

def dXU_0 (a b c d p r t : K) : K :=
  9 * (6 * A0_0 a b c d * Z a b c d p r t + A0_0 a b c d * dXZ a b c d p r t) +
    3 * (4 * A2_0 a b c d * h a b c d p * W a b c d p r t +
      A2_0 a b c d * dXh a b c d p * W a b c d p r t +
      A2_0 a b c d * h a b c d p * dXW a b c d p r t) * t +
    (dXQu_0 a b c d p * h a b c d p + Qu_0 a b c d p * dXh a b c d p) * t ^ 2

def dPV_0 (a b c d p r t : K) : K :=
  9 * A1_0 a b c d * dPZ a b c d p r t +
    3 * A2_0 a b c d * (dPh a b c d p * W a b c d p r t * p +
      h a b c d p * dPW a b c d p r t * p + h a b c d p * W a b c d p r t) * t +
    (dPQp_0 a b c d p * h a b c d p + Qp_0 a b c d p * dPh a b c d p) * t ^ 2

def dKB_0 (a b c d p r t : K) : K :=
  3 * A2_0 a b c d * h a b c d p * (dKW a b c d p r t * r + W a b c d p r t * dKr r t)

theorem first_scalar_identity_0 (a b c d p r t : K) :
    fu a b c d p * U_0 a b c d p r t + fp a b c d p * V_0 a b c d p r t +
      3 * r ^ 2 * B_0 a b c d p r t = (1) * D a b c d p r t := by
  simp only [fu, fp, U_0, V_0, B_0, D, A0_0, A1_0, A2_0, Qu_0, Qp_0, delta, h, f, W, Z]
  ring

theorem divergence_core_0 (a b c d p r t : K) :
    D a b c d p r t * (3 * dXU_0 a b c d p r t + 18 * U_0 a b c d p r t +
      6 * dPV_0 a b c d p r t + dKB_0 a b c d p r t + 6 * B_0 a b c d p r t) =
    3 * U_0 a b c d p r t * dXD a b c d p r t +
      6 * V_0 a b c d p r t * dPD a b c d p r t + B_0 a b c d p r t * dKD a b c d p r t := by
  simp only [D, U_0, V_0, B_0, dXD, dXU_0, dPD, dPV_0, dKD, dKB_0,
    A0_0, A1_0, A2_0, Qu_0, Qp_0, dXQu_0, dPQp_0,
    dXh, dXf, dXW, dXZ, dPh, dPf, dPW, dPZ, dKW, dKZ, dKr, dKt,
    delta, h, hp, fp, f, W, Z]
  ring

/-- Adjugate cofactors and exact Δ-canceled quotients for target j = 1 (p). -/
def A0_1 (a b c d : K) : K := (-9) * a * c * d + (6) * b ^ 2 * d + -(b * c ^ 2)
def A1_1 (a b c d : K) : K := (-9) * a * b * d + (6) * a * c ^ 2 + -(b ^ 2 * c)
def A2_1 (a b c d : K) : K := (9) * a * d + -(b * c)
def Qu_1 (a b c d p : K) : K := (-27) * a ^ 2 * d + (-3) * a * b * c + (-45) * a * b * d * p + (-9) * a * c * d * p ^ 2 + (27) * a * d ^ 2 * p ^ 3 + (2) * b ^ 3 + (5) * b ^ 2 * c * p + (-12) * b ^ 2 * d * p ^ 2 + (5) * b * c ^ 2 * p ^ 2 + (-3) * b * c * d * p ^ 3 + (18) * b * d ^ 2 * p ^ 4 + (-6) * c ^ 2 * d * p ^ 4
def Qp_1 (a b c d p : K) : K := (18) * a ^ 2 * c + (27) * a ^ 2 * d * p + (-6) * a * b ^ 2 + (-3) * a * b * c * p + (-9) * a * b * d * p ^ 2 + (-12) * a * c ^ 2 * p ^ 2 + (-45) * a * c * d * p ^ 3 + (-27) * a * d ^ 2 * p ^ 4 + (5) * b ^ 2 * c * p ^ 2 + (5) * b * c ^ 2 * p ^ 3 + (-3) * b * c * d * p ^ 4 + (2) * c ^ 3 * p ^ 4
def dXQu_1 (a b c d p : K) : K := (-324) * a ^ 2 * d + (-36) * a * b * c + (-450) * a * b * d * p + (-72) * a * c * d * p ^ 2 + (162) * a * d ^ 2 * p ^ 3 + (24) * b ^ 3 + (50) * b ^ 2 * c * p + (-96) * b ^ 2 * d * p ^ 2 + (40) * b * c ^ 2 * p ^ 2 + (-18) * b * c * d * p ^ 3 + (72) * b * d ^ 2 * p ^ 4 + (-24) * c ^ 2 * d * p ^ 4
def dPQp_1 (a b c d p : K) : K := (27) * a ^ 2 * d + (-3) * a * b * c + (-18) * a * b * d * p + (-24) * a * c ^ 2 * p + (-135) * a * c * d * p ^ 2 + (-108) * a * d ^ 2 * p ^ 3 + (10) * b ^ 2 * c * p + (15) * b * c ^ 2 * p ^ 2 + (-12) * b * c * d * p ^ 3 + (8) * c ^ 3 * p ^ 3

theorem exact_quotient_u_1 (a b c d p : K) :
    4 * A0_1 a b c d * h a b c d p ^ 2 - A2_1 a b c d * kScaled a b c d p * hp a b c d p =
      delta a b c d * Qu_1 a b c d p := by
  simp only [A0_1, A2_1, h, kScaled, hp, hu, fu, fp, delta, Qu_1]
  ring

theorem exact_quotient_p_1 (a b c d p : K) :
    4 * A1_1 a b c d * h a b c d p ^ 2 + A2_1 a b c d * kScaled a b c d p * hu a b c d p =
      delta a b c d * Qp_1 a b c d p := by
  simp only [A1_1, A2_1, h, kScaled, hp, hu, fu, fp, delta, Qp_1]
  ring

def U_1 (a b c d p r t : K) : K :=
  9 * A0_1 a b c d * Z a b c d p r t + 3 * A2_1 a b c d * h a b c d p * W a b c d p r t * t +
    Qu_1 a b c d p * h a b c d p * t ^ 2
def V_1 (a b c d p r t : K) : K :=
  9 * A1_1 a b c d * Z a b c d p r t + 3 * A2_1 a b c d * h a b c d p * W a b c d p r t * p * t +
    Qp_1 a b c d p * h a b c d p * t ^ 2
def B_1 (a b c d p r t : K) : K := 3 * A2_1 a b c d * h a b c d p * W a b c d p r t * r

def dXU_1 (a b c d p r t : K) : K :=
  9 * (8 * A0_1 a b c d * Z a b c d p r t + A0_1 a b c d * dXZ a b c d p r t) +
    3 * (6 * A2_1 a b c d * h a b c d p * W a b c d p r t +
      A2_1 a b c d * dXh a b c d p * W a b c d p r t +
      A2_1 a b c d * h a b c d p * dXW a b c d p r t) * t +
    (dXQu_1 a b c d p * h a b c d p + Qu_1 a b c d p * dXh a b c d p) * t ^ 2

def dPV_1 (a b c d p r t : K) : K :=
  9 * A1_1 a b c d * dPZ a b c d p r t +
    3 * A2_1 a b c d * (dPh a b c d p * W a b c d p r t * p +
      h a b c d p * dPW a b c d p r t * p + h a b c d p * W a b c d p r t) * t +
    (dPQp_1 a b c d p * h a b c d p + Qp_1 a b c d p * dPh a b c d p) * t ^ 2

def dKB_1 (a b c d p r t : K) : K :=
  3 * A2_1 a b c d * h a b c d p * (dKW a b c d p r t * r + W a b c d p r t * dKr r t)

theorem first_scalar_identity_1 (a b c d p r t : K) :
    fu a b c d p * U_1 a b c d p r t + fp a b c d p * V_1 a b c d p r t +
      3 * r ^ 2 * B_1 a b c d p r t = (p) * D a b c d p r t := by
  simp only [fu, fp, U_1, V_1, B_1, D, A0_1, A1_1, A2_1, Qu_1, Qp_1, delta, h, f, W, Z]
  ring

theorem divergence_core_1 (a b c d p r t : K) :
    D a b c d p r t * (3 * dXU_1 a b c d p r t + 12 * U_1 a b c d p r t +
      6 * dPV_1 a b c d p r t + dKB_1 a b c d p r t + 6 * B_1 a b c d p r t) =
    3 * U_1 a b c d p r t * dXD a b c d p r t +
      6 * V_1 a b c d p r t * dPD a b c d p r t + B_1 a b c d p r t * dKD a b c d p r t := by
  simp only [D, U_1, V_1, B_1, dXD, dXU_1, dPD, dPV_1, dKD, dKB_1,
    A0_1, A1_1, A2_1, Qu_1, Qp_1, dXQu_1, dPQp_1,
    dXh, dXf, dXW, dXZ, dPh, dPf, dPW, dPZ, dKW, dKZ, dKr, dKt,
    delta, h, hp, fp, f, W, Z]
  ring

/-- Adjugate cofactors and exact Δ-canceled quotients for target j = 2 (p ^ 2). -/
def A0_2 (a b c d : K) : K := (-9) * a * b * d + (6) * a * c ^ 2 + -(b ^ 2 * c)
def A1_2 (a b c d : K) : K := (27) * a ^ 2 * d + (-9) * a * b * c + (2) * b ^ 3
def A2_2 (a b c _d : K) : K := (-6) * a * c + (2) * b ^ 2
def Qu_2 (a b c d p : K) : K := (18) * a ^ 2 * c + (-6) * a * b ^ 2 + (6) * a * b * c * p + (-36) * a * b * d * p ^ 2 + (6) * a * c ^ 2 * p ^ 2 + (-18) * a * c * d * p ^ 3 + (-2) * b ^ 3 * p + (2) * b ^ 2 * c * p ^ 2 + (-18) * b ^ 2 * d * p ^ 3 + (8) * b * c ^ 2 * p ^ 3 + (-12) * b * c * d * p ^ 4 + (4) * c ^ 3 * p ^ 4
def Qp_2 (a b c d p : K) : K := (54) * a ^ 2 * c * p + (108) * a ^ 2 * d * p ^ 2 + (-18) * a * b ^ 2 * p + (18) * a * b * c * p ^ 2 + (72) * a * b * d * p ^ 3 + (6) * a * c ^ 2 * p ^ 3 + (18) * a * c * d * p ^ 4 + (-10) * b ^ 3 * p ^ 2 + (-10) * b ^ 2 * c * p ^ 3 + (6) * b ^ 2 * d * p ^ 4 + (-4) * b * c ^ 2 * p ^ 4
def dXQu_2 (a b c d p : K) : K := (252) * a ^ 2 * c + (-84) * a * b ^ 2 + (72) * a * b * c * p + (-360) * a * b * d * p ^ 2 + (60) * a * c ^ 2 * p ^ 2 + (-144) * a * c * d * p ^ 3 + (-24) * b ^ 3 * p + (20) * b ^ 2 * c * p ^ 2 + (-144) * b ^ 2 * d * p ^ 3 + (64) * b * c ^ 2 * p ^ 3 + (-72) * b * c * d * p ^ 4 + (24) * c ^ 3 * p ^ 4
def dPQp_2 (a b c d p : K) : K := (54) * a ^ 2 * c + (216) * a ^ 2 * d * p + (-18) * a * b ^ 2 + (36) * a * b * c * p + (216) * a * b * d * p ^ 2 + (18) * a * c ^ 2 * p ^ 2 + (72) * a * c * d * p ^ 3 + (-20) * b ^ 3 * p + (-30) * b ^ 2 * c * p ^ 2 + (24) * b ^ 2 * d * p ^ 3 + (-16) * b * c ^ 2 * p ^ 3

theorem exact_quotient_u_2 (a b c d p : K) :
    4 * A0_2 a b c d * h a b c d p ^ 2 - A2_2 a b c d * kScaled a b c d p * hp a b c d p =
      delta a b c d * Qu_2 a b c d p := by
  simp only [A0_2, A2_2, h, kScaled, hp, hu, fu, fp, delta, Qu_2]
  ring

theorem exact_quotient_p_2 (a b c d p : K) :
    4 * A1_2 a b c d * h a b c d p ^ 2 + A2_2 a b c d * kScaled a b c d p * hu a b c d p =
      delta a b c d * Qp_2 a b c d p := by
  simp only [A1_2, A2_2, h, kScaled, hp, hu, fu, fp, delta, Qp_2]
  ring

def U_2 (a b c d p r t : K) : K :=
  9 * A0_2 a b c d * Z a b c d p r t + 3 * A2_2 a b c d * h a b c d p * W a b c d p r t * t +
    Qu_2 a b c d p * h a b c d p * t ^ 2
def V_2 (a b c d p r t : K) : K :=
  9 * A1_2 a b c d * Z a b c d p r t + 3 * A2_2 a b c d * h a b c d p * W a b c d p r t * p * t +
    Qp_2 a b c d p * h a b c d p * t ^ 2
def B_2 (a b c d p r t : K) : K := 3 * A2_2 a b c d * h a b c d p * W a b c d p r t * r

def dXU_2 (a b c d p r t : K) : K :=
  9 * (10 * A0_2 a b c d * Z a b c d p r t + A0_2 a b c d * dXZ a b c d p r t) +
    3 * (8 * A2_2 a b c d * h a b c d p * W a b c d p r t +
      A2_2 a b c d * dXh a b c d p * W a b c d p r t +
      A2_2 a b c d * h a b c d p * dXW a b c d p r t) * t +
    (dXQu_2 a b c d p * h a b c d p + Qu_2 a b c d p * dXh a b c d p) * t ^ 2

def dPV_2 (a b c d p r t : K) : K :=
  9 * A1_2 a b c d * dPZ a b c d p r t +
    3 * A2_2 a b c d * (dPh a b c d p * W a b c d p r t * p +
      h a b c d p * dPW a b c d p r t * p + h a b c d p * W a b c d p r t) * t +
    (dPQp_2 a b c d p * h a b c d p + Qp_2 a b c d p * dPh a b c d p) * t ^ 2

def dKB_2 (a b c d p r t : K) : K :=
  3 * A2_2 a b c d * h a b c d p * (dKW a b c d p r t * r + W a b c d p r t * dKr r t)

theorem first_scalar_identity_2 (a b c d p r t : K) :
    fu a b c d p * U_2 a b c d p r t + fp a b c d p * V_2 a b c d p r t +
      3 * r ^ 2 * B_2 a b c d p r t = (p ^ 2) * D a b c d p r t := by
  simp only [fu, fp, U_2, V_2, B_2, D, A0_2, A1_2, A2_2, Qu_2, Qp_2, delta, h, f, W, Z]
  ring

theorem divergence_core_2 (a b c d p r t : K) :
    D a b c d p r t * (3 * dXU_2 a b c d p r t + 6 * U_2 a b c d p r t +
      6 * dPV_2 a b c d p r t + dKB_2 a b c d p r t + 6 * B_2 a b c d p r t) =
    3 * U_2 a b c d p r t * dXD a b c d p r t +
      6 * V_2 a b c d p r t * dPD a b c d p r t + B_2 a b c d p r t * dKD a b c d p r t := by
  simp only [D, U_2, V_2, B_2, dXD, dXU_2, dPD, dPV_2, dKD, dKB_2,
    A0_2, A1_2, A2_2, Qu_2, Qp_2, dXQu_2, dPQp_2,
    dXh, dXf, dXW, dXZ, dPh, dPf, dPW, dPZ, dKW, dKZ, dKr, dKt,
    delta, h, hp, fp, f, W, Z]
  ring

/--
Permuted paired-sign reduction for Open Instance `#74 one-reflection-skew`:
Under `B1 = (X0, Y0, X2)` and `B2 = (X1, Y1, Y2)` with `x = X0^2, y = X1^2, z = Y2^2`,
and passive ratios `Y0 = c0 * X0, X2 = c2 * X0, Y1 = c1 * X1`, the sextic `F_74`
reduces identically to the `e = 0` reverse-edge ternary cubic
`a * x^3 + b * y^3 + c * z^3 + d * x^2 * y + f * x * y^2`, and under the quadratic
shear `x = X + k * y` (`3 * a * k^2 + 2 * d * k + f = 0`) maps directly into
`TransitiveCubic.cubic a (bPrime a b d f k) c (dPrime a d k) 0 0 X y z`.
-/
theorem one_reflection_skew_74_reverse_edge_cubic
    (X0 X1 Y2 c0 c1 c2 inv7 : K) :
    let Y0 := c0 * X0
    let X2 := c2 * X0
    let Y1 := c1 * X1
    let x := X0 ^ 2
    let y := X1 ^ 2
    let z := Y2 ^ 2
    let a := 1 + c0 ^ 6 + c2 ^ 6
    let b := 1 + c1 ^ 6
    let c := (1 : K)
    let d := c0 * c1 + inv7 * c0 ^ 3
    let f := c0 * c1 * (c2 - inv7 * c1 ^ 2)
    (X0 ^ 6 + X0 ^ 3 * X1 * Y0 * Y1 + inv7 * X0 * X1 ^ 2 * Y0 ^ 3 -
      inv7 * X0 * X1 * Y0 * Y1 ^ 3 + X1 ^ 6 + X1 ^ 3 * X2 * Y0 * Y1 +
      X2 ^ 6 + Y0 ^ 6 + Y1 ^ 6 + Y2 ^ 6) =
    a * x ^ 3 + b * y ^ 3 + c * z ^ 3 + d * x ^ 2 * y + f * x * y ^ 2 := by
  dsimp
  ring

theorem one_reflection_skew_74_sheared_transitive_cubic
    (a b c d f k X Y Z : K) (hk : 3 * a * k ^ 2 + 2 * d * k + f = 0) :
    a * (X + k * Y) ^ 3 + b * Y ^ 3 + c * Z ^ 3 +
      d * (X + k * Y) ^ 2 * Y + f * (X + k * Y) * Y ^ 2 =
    TransitiveCubic.cubic a (TransitiveCubicShear.bPrime a b d f k) c
      (TransitiveCubicShear.dPrime a d k) 0 0 X Y Z := by
  simpa using TransitiveCubicShear.base_shear a b c d 0 f k X Y Z hk

/--
Permuted paired-sign reduction for Open Instance `#71 four-plus-two-residual`:
Swapping `X1 ↔ Y0` aligns the three paired-sign symmetries `two_refl = [(0,3), (1,4), (2,5)]`
with `(X0, Y0), (X1, Y1), (X2, Y2)`. Setting `x = X0^2, y = X1^2, z = X2^2` and passive
ratios `Y0 = c0 * X0, Y1 = c1 * X1, Y2 = c2 * X2` reduces `F_71` identically to the
`e = 0` reverse-edge ternary cubic `a * x^3 + b * y^3 + c * z^3 + d * x^2 * y + f * x * y^2`.
-/
theorem four_plus_two_residual_71_reverse_edge_cubic
    (X0 X1 X2 c0 c1 c2 inv2 inv3 inv5 inv7 : K) :
    let Y0 := c0 * X0
    let Y1 := c1 * X1
    let Y2 := c2 * X2
    let x := X0 ^ 2
    let y := X1 ^ 2
    let z := X2 ^ 2
    let a := 1 + c0 ^ 6
    let b := 1 + c1 ^ 6
    let c := 1 - c2 ^ 2 + c2 ^ 4 + c2 ^ 6
    let d := c0 * c1 + inv3 * c0 ^ 3
    let f := -inv5 * c1 ^ 3 - inv7 * c0 * c1 ^ 3 + inv2 * c0 ^ 2 * c1
    (X0 ^ 6 + X0 ^ 3 * X1 * Y0 * Y1 - inv5 * X0 ^ 2 * X1 * Y1 ^ 3 +
      inv3 * X0 * X1 ^ 2 * Y0 ^ 3 - inv7 * X0 * X1 * Y0 * Y1 ^ 3 +
      X1 ^ 6 + inv2 * X1 ^ 3 * Y0 ^ 2 * Y1 + X2 ^ 6 -
      X2 ^ 4 * Y2 ^ 2 + X2 ^ 2 * Y2 ^ 4 + Y0 ^ 6 + Y1 ^ 6 + Y2 ^ 6) =
    a * x ^ 3 + b * y ^ 3 + c * z ^ 3 + d * x ^ 2 * y + f * x * y ^ 2 := by
  dsimp
  ring

/--
Step 2 (Exact Closed-Form `e = 0` Reverse-Edge Weierstrass Covariants `H_e0, Theta_e0, J_e0`):
For `U(x, y, z) = fBin(x, y) + c * z^3 = a*x^3 + d*x^2*y + f*x*y^2 + b*y^3 + c*z^3` (`e = 0`),
the Salmon/Fisher covariants factor in closed form through the binary cubic covariants
`fBin, hBin, kBin, discBin`.
-/
def fBin (a b d f x y : K) : K := a * x ^ 3 + d * x ^ 2 * y + f * x * y ^ 2 + b * y ^ 3
def fxBin (a _b d f x y : K) : K := 3 * a * x ^ 2 + 2 * d * x * y + f * y ^ 2
def fyBin (_a b d f x y : K) : K := d * x ^ 2 + 2 * f * x * y + 3 * b * y ^ 2
def hBin (a b d f x y : K) : K :=
  (3 * a * f - d ^ 2) * x ^ 2 + (9 * a * b - d * f) * x * y + (3 * b * d - f ^ 2) * y ^ 2
def hxBin (a b d f x y : K) : K := 2 * (3 * a * f - d ^ 2) * x + (9 * a * b - d * f) * y
def hyBin (a b d f x y : K) : K := (9 * a * b - d * f) * x + 2 * (3 * b * d - f ^ 2) * y
def kBin (a b d f x y : K) : K :=
  hyBin a b d f x y * fxBin a b d f x y - hxBin a b d f x y * fyBin a b d f x y
def disc0Bin (a b d f : K) : K :=
  27 * a ^ 2 * b ^ 2 - 18 * a * b * d * f + 4 * a * f ^ 3 + 4 * b * d ^ 3 - d ^ 2 * f ^ 2
def discBin (a b d f : K) : K := 3 * disc0Bin a b d f

theorem binary_cayley_hessian_syzygy (a b d f x y : K) :
    kBin a b d f x y ^ 2 =
      9 * discBin a b d f * fBin a b d f x y ^ 2 - 4 * hBin a b d f x y ^ 3 := by
  simp only [kBin, hxBin, hyBin, fxBin, fyBin, hBin, fBin, discBin, disc0Bin]
  ring

def U_e0 (a b c d f x y z : K) : K := fBin a b d f x y + c * z ^ 3
def H_e0 (a b c d f x y z : K) : K := 9 * c * z * hBin a b d f x y
def Theta_e0 (a b c d f x y z : K) : K :=
  -9 * c ^ 2 * hBin a b d f x y ^ 3 - 81 * c ^ 3 * discBin a b d f * z ^ 3 * fBin a b d f x y
def J_e0 (a b c d f x y z : K) : K :=
  27 * c ^ 3 * kBin a b d f x y *
    (hBin a b d f x y ^ 3 - 9 * c * discBin a b d f * z ^ 3 * (fBin a b d f x y - c * z ^ 3))
def s6_e0 (a b c d f : K) : K := c ^ 2 * disc0Bin a b d f

def Dop_H_e0 (a b c d f x y z : K) : K := 9 * c * z * kBin a b d f x y
def Dop_Theta_e0 (a b c d f x y _z : K) : K :=
  -27 * c ^ 2 * hBin a b d f x y ^ 2 * kBin a b d f x y

/--
1-Term Cleared Invariant Differential Identity for `e = 0` Reverse-Edge Cubics (`#71` & `#74`):
Under the relative cubic derivation `D_op = f_x ∂_y - f_y ∂_x` (where `D_op(fBin) = 0` and
`D_op(hBin) = kBin`), `H_e0 * D_op(Theta_e0) - 2 * Theta_e0 * D_op(H_e0) + 3 * z * J_e0`
is an exact 1-term multiple of `U_e0`.
-/
theorem cleared_differential_e0 (a b c d f x y z : K) :
    H_e0 a b c d f x y z * Dop_Theta_e0 a b c d f x y z -
      2 * Theta_e0 a b c d f x y z * Dop_H_e0 a b c d f x y z +
      3 * z * J_e0 a b c d f x y z =
    729 * c ^ 4 * discBin a b d f * z ^ 4 * kBin a b d f x y * U_e0 a b c d f x y z := by
  simp only [H_e0, Theta_e0, J_e0, Dop_H_e0, Dop_Theta_e0, U_e0]
  ring

def syzygyQuotient_e0 (a b c d f x y z : K) : K :=
  let H3 := hBin a b d f x y ^ 3
  let D := discBin a b d f
  let F := fBin a b d f x y
  let Z := c * z ^ 3
  729 * c ^ 6 * 9 * D *
    ((F - Z) * (H3 - 9 * D * Z * (F - Z)) ^ 2 -
      (9 * D * Z ^ 2 - 4 * H3) * Z * (2 * H3 - 9 * D * Z * (F - 3 * Z)) +
      4 * Z * ((H3 + 9 * D * Z * F) ^ 2 + (H3 + 9 * D * Z * F) * (H3 - 9 * D * Z ^ 2) +
        (H3 - 9 * D * Z ^ 2) ^ 2))

/--
Compact Full Weierstrass Syzygy for `e = 0` Reverse-Edge Cubics (`#71` & `#74`):
`J_e0^2 - (4 * Theta_e0^3 - s6_e0 * H_e0^6) = U_e0 * syzygyQuotient_e0` identically over `K`.
-/
theorem full_syzygy_e0 (a b c d f x y z : K) :
    J_e0 a b c d f x y z ^ 2 -
      (4 * Theta_e0 a b c d f x y z ^ 3 - s6_e0 a b c d f * H_e0 a b c d f x y z ^ 6) =
    U_e0 a b c d f x y z * syzygyQuotient_e0 a b c d f x y z := by
  have hk := binary_cayley_hessian_syzygy a b d f x y
  simp only [discBin] at hk
  simp only [J_e0, Theta_e0, H_e0, s6_e0, U_e0, syzygyQuotient_e0, discBin]
  linear_combination
    729 * c ^ 6 *
      (hBin a b d f x y ^ 3 -
        9 * c * (3 * disc0Bin a b d f) * z ^ 3 * (fBin a b d f x y - c * z ^ 3)) ^ 2 * hk

/--
Step 3 (Mordell `I_4 = 0` Residue Divergence Cancellation Identity):
On any Mordell Weierstrass hypersurface `Y2 = X^3 + B6`, combining a parameter component `psi`
with `w_X = 2 * X * d_psi` cancels the polynomial `d_psi` derivative identically (`1 + 2 - 3 = 0`),
leaving purely the pole-two numerator `6 * B6 * d_psi - psi * d_B6`.
-/
theorem mordell_residue_divergence_cancellation (X Y2 B6 psi d_psi d_B6 : K)
    (hcurve : Y2 = X ^ 3 + B6) :
    (d_psi * (2 * Y2) - psi * d_B6) + (2 * d_psi * (2 * Y2) - (2 * X * d_psi) * (3 * X ^ 2)) =
      6 * B6 * d_psi - psi * d_B6 := by
  linear_combination 6 * d_psi * hcurve

/--
Step 3 (Physical Paired-Normal and Second-Paired-Gradient Identities for `#71 four-plus-two-residual`):
In 6 physical coordinates `(X0, X1, X2, Y0, Y1, Y2)`, the paired Euler gradients on `(X0, Y0)` and
`(X1, Y1)` and the paired Hessian on `(X0, Y0)` match `2 * R^3 * x * U_x`, `4 * R^3 * x^2 * U_xx`,
and `2 * R^3 * y * U_y` identically.
-/
theorem paired_normal_identities_71 (X0 X1 _X2 Y0 Y1 _Y2 inv2 inv3 inv5 inv7 : K) :
    let a_hom := X0 ^ 6 + Y0 ^ 6
    let d_hom := X0 ^ 3 * Y0 * X1 * Y1 + inv3 * X0 * Y0 ^ 3 * X1 ^ 2
    let f_hom := -inv5 * X0 ^ 2 * X1 * Y1 ^ 3 - inv7 * X0 * Y0 * X1 * Y1 ^ 3 + inv2 * Y0 ^ 2 * X1 ^ 3 * Y1
    let b_hom := X1 ^ 6 + Y1 ^ 6
    let F0 := 6 * X0 ^ 5 + 3 * X0 ^ 2 * X1 * Y0 * Y1 - 2 * inv5 * X0 * X1 * Y1 ^ 3 +
              inv3 * X1 ^ 2 * Y0 ^ 3 - inv7 * X1 * Y0 * Y1 ^ 3
    let F3 := 6 * Y0 ^ 5 + X0 ^ 3 * X1 * Y1 + 3 * inv3 * X0 * X1 ^ 2 * Y0 ^ 2 -
              inv7 * X0 * X1 * Y1 ^ 3 + 2 * inv2 * X1 ^ 3 * Y0 * Y1
    let F1 := 6 * X1 ^ 5 + X0 ^ 3 * Y0 * Y1 - inv5 * X0 ^ 2 * Y1 ^ 3 +
              2 * inv3 * X0 * X1 * Y0 ^ 3 - inv7 * X0 * Y0 * Y1 ^ 3 + 3 * inv2 * X1 ^ 2 * Y0 ^ 2 * Y1
    let F4 := 6 * Y1 ^ 5 + X0 ^ 3 * X1 * Y0 - 3 * inv5 * X0 ^ 2 * X1 * Y1 ^ 2 -
              3 * inv7 * X0 * X1 * Y0 * Y1 ^ 2 + inv2 * X1 ^ 3 * Y0 ^ 2
    (X0 * F0 + Y0 * F3 = 2 * (3 * a_hom + 2 * d_hom + f_hom)) ∧
    (X1 * F1 + Y1 * F4 = 2 * (3 * b_hom + d_hom + 2 * f_hom)) := by
  constructor <;> ring

/--
Step 3 (Physical Paired-Normal and Second-Paired-Gradient Identities for `#74 one-reflection-skew`):
In 6 physical coordinates `(X0, X1, X2, Y0, Y1, Y2)`, the 3-variable paired Euler gradient on
`B1 = (X0, X2, Y0)` and the 2-variable paired Euler gradient on `B2 = (X1, Y1)` match
`2 * R^3 * x * U_x` and `2 * R^3 * y * U_y` identically.
-/
theorem paired_normal_identities_74 (X0 X1 X2 Y0 Y1 inv7 : K) :
    let a_hom := X0 ^ 6 + X2 ^ 6 + Y0 ^ 6
    let d_hom := X0 ^ 3 * Y0 * X1 * Y1 + inv7 * X0 * Y0 ^ 3 * X1 ^ 2
    let f_hom := X1 ^ 3 * X2 * Y0 * Y1 - inv7 * X0 * Y0 * X1 * Y1 ^ 3
    let b_hom := X1 ^ 6 + Y1 ^ 6
    let F0 := 6 * X0 ^ 5 + 3 * X0 ^ 2 * X1 * Y0 * Y1 + inv7 * X1 ^ 2 * Y0 ^ 3 - inv7 * X1 * Y0 * Y1 ^ 3
    let F2 := 6 * X2 ^ 5 + X1 ^ 3 * Y0 * Y1
    let F3 := 6 * Y0 ^ 5 + X0 ^ 3 * X1 * Y1 + 3 * inv7 * X0 * X1 ^ 2 * Y0 ^ 2 -
              inv7 * X0 * X1 * Y1 ^ 3 + X1 ^ 3 * X2 * Y1
    let F1 := 6 * X1 ^ 5 + X0 ^ 3 * Y0 * Y1 + 2 * inv7 * X0 * X1 * Y0 ^ 3 -
              inv7 * X0 * Y0 * Y1 ^ 3 + 3 * X1 ^ 2 * X2 * Y0 * Y1
    let F4 := 6 * Y1 ^ 5 + X0 ^ 3 * X1 * Y0 - 3 * inv7 * X0 * X1 * Y0 * Y1 ^ 2 + X1 ^ 3 * X2 * Y0
    (X0 * F0 + X2 * F2 + Y0 * F3 = 2 * (3 * a_hom + 2 * d_hom + f_hom)) ∧
    (X1 * F1 + Y1 * F4 = 2 * (3 * b_hom + d_hom + 2 * f_hom)) := by
  constructor <;> ring

/--
Universal Hamiltonian Quadratic Pair Lift (generalizing `QuadricContactLift` to `#72 quadric-contact-residual`
and `#69 rank-one-biquartic`):
For any two quadratic forms `Q0, Q1` with partial derivatives `(dX_Q0, dY_Q0)` and `(dX_Q1, dY_Q1)`
and Wronskian `W_pair = dX_Q0 * dY_Q1 - dY_Q0 * dX_Q1`, the Hamiltonian operators
`H0 = (dY_Q1, -dX_Q1)` and `H1 = (-dY_Q0, dX_Q0)` satisfy `H_i(Q_j) = W_pair * δ_{ij}`,
giving the exact directional lift `H0(F) * U0 + H1(F) * U1 = W_pair * (F_Q0 * U0 + F_Q1 * U1)`.
-/
theorem hamiltonian_pair_lift_directional
    (dX_Q0 dY_Q0 dX_Q1 dY_Q1 F_Q0 F_Q1 U0 U1 : K) :
    let W_pair := dX_Q0 * dY_Q1 - dY_Q0 * dX_Q1
    let dX_F := F_Q0 * dX_Q0 + F_Q1 * dX_Q1
    let dY_F := F_Q0 * dY_Q0 + F_Q1 * dY_Q1
    let N_X := dY_Q1 * U0 - dY_Q0 * U1
    let N_Y := -dX_Q1 * U0 + dX_Q0 * U1
    N_X * dX_F + N_Y * dY_F = W_pair * (F_Q0 * U0 + F_Q1 * U1) := by
  dsimp
  ring

/--
Exact Specialization of the Hamiltonian Quadratic Pair Lift to `(Q0, Q1) = (X0^2, Y0^2)`
(`W_pair = 4 * X0 * Y0`) for `#72 quadric-contact-residual` and `#69 rank-one-biquartic`:
-/
theorem hamiltonian_active_x0_y0_lift (X0 Y0 F_u0 F_v0 U0 U1 : K) :
    let dX_F := 2 * X0 * F_u0
    let dY_F := 2 * Y0 * F_v0
    let N_X := 2 * Y0 * U0
    let N_Y := 2 * X0 * U1
    N_X * dX_F + N_Y * dY_F = (4 * X0 * Y0) * (F_u0 * U0 + F_v0 * U1) := by
  dsimp
  ring

/--
Transitive Cubic Reduction for Open Instance `#56 off-paired` and `#60 cycle-q2`:
Under the paired-ratio reduction `X1 = r1 * X0, Y0 = c0 * X0, Y1 = c1 * X1, Y2 = c2 * X2`
with `x = X0^2, z = X2^2`, `F_56` and `F_60` collapse identically to the cubic `a * x^3 + d * x^2 * z + c * z^3`.
-/
theorem off_paired_56_and_cycle_q2_60_cubic_reduction
    (X0 X2 r1 c0 c1 c2 inv2 inv3 : K) :
    let X1 := r1 * X0
    let Y0 := c0 * X0
    let Y1 := c1 * X1
    let Y2 := c2 * X2
    let x := X0 ^ 2
    let z := X2 ^ 2
    let a := 1 + r1 ^ 6 + c0 ^ 6 + r1 ^ 6 * c1 ^ 6 + inv2 * r1 ^ 2 * c0 * c1
    let d := inv2 * r1 ^ 4 * c1 * c2 + inv3 * r1 * c0 * c2
    let c := 1 + c2 ^ 6
    (X0 ^ 6 + X1 ^ 6 + X2 ^ 6 + Y0 ^ 6 + Y1 ^ 6 + Y2 ^ 6 +
      inv2 * X0 ^ 3 * X1 * Y0 * Y1 + inv2 * X1 ^ 3 * X2 * Y1 * Y2 +
      inv3 * X0 ^ 2 * X1 * X2 * Y0 * Y2) =
    a * x ^ 3 + d * x ^ 2 * z + c * z ^ 3 := by
  dsimp
  ring

/--
Exact Companion Decomposition for `#69 rank-one-biquartic` and `#72 quadric-contact-residual`:
1. `#69 rank-one-biquartic`: `F_69 = (X0^6 + X1^6 + X2^6 + Y0^6 + Y1^6 + Y2^6) + Q_X (3 Y0^2 + Y1^2 + Y2^2)^2`
   where `Q_X = inv2 * X0^2 + X1^2 + 2 X2^2`.
2. `#72 quadric-contact-residual`: `F_72 = (X0^6 + X1^6 + X2^6 + Y0^6 + Y1^6 + Y2^6) + Q_contact * C_cubic`
   where `Q_contact = X0 * Y0 + X1 * Y1 + 2 * X2 * Y2` and `C_cubic = X0^3 * Y1 + X1^3 * Y2 + X2^3 * Y0`.
-/
theorem rank_one_biquartic_69_and_quadric_contact_72_decompositions
    (X0 X1 X2 Y0 Y1 Y2 inv2 : K) :
    let QX := inv2 * X0 ^ 2 + X1 ^ 2 + 2 * X2 ^ 2
    let QY := 3 * Y0 ^ 2 + Y1 ^ 2 + Y2 ^ 2
    let Q_contact := X0 * Y0 + X1 * Y1 + 2 * X2 * Y2
    let C_cubic := X0 ^ 3 * Y1 + X1 ^ 3 * Y2 + X2 ^ 3 * Y0
    ((X0 ^ 6 + X1 ^ 6 + X2 ^ 6 + Y0 ^ 6 + Y1 ^ 6 + Y2 ^ 6) + QX * QY ^ 2 =
      X0 ^ 6 + inv2 * X0 ^ 2 * (9 * Y0 ^ 4 + 6 * Y0 ^ 2 * Y1 ^ 2 + 6 * Y0 ^ 2 * Y2 ^ 2 +
        Y1 ^ 4 + 2 * Y1 ^ 2 * Y2 ^ 2 + Y2 ^ 4) +
      X1 ^ 6 + X1 ^ 2 * (9 * Y0 ^ 4 + 6 * Y0 ^ 2 * Y1 ^ 2 + 6 * Y0 ^ 2 * Y2 ^ 2 +
        Y1 ^ 4 + 2 * Y1 ^ 2 * Y2 ^ 2 + Y2 ^ 4) +
      X2 ^ 6 + 2 * X2 ^ 2 * (9 * Y0 ^ 4 + 6 * Y0 ^ 2 * Y1 ^ 2 + 6 * Y0 ^ 2 * Y2 ^ 2 +
        Y1 ^ 4 + 2 * Y1 ^ 2 * Y2 ^ 2 + Y2 ^ 4) +
      Y0 ^ 6 + Y1 ^ 6 + Y2 ^ 6) ∧
    ((X0 ^ 6 + X1 ^ 6 + X2 ^ 6 + Y0 ^ 6 + Y1 ^ 6 + Y2 ^ 6) + Q_contact * C_cubic =
      X0 ^ 6 + X0 ^ 4 * Y0 * Y1 + X0 ^ 3 * X1 * Y1 ^ 2 + 2 * X0 ^ 3 * X2 * Y1 * Y2 +
      X0 * X1 ^ 3 * Y0 * Y2 + X0 * X2 ^ 3 * Y0 ^ 2 + X1 ^ 6 + X1 ^ 4 * Y1 * Y2 +
      2 * X1 ^ 3 * X2 * Y2 ^ 2 + X1 * X2 ^ 3 * Y0 * Y1 + X2 ^ 6 + 2 * X2 ^ 4 * Y0 * Y2 +
      Y0 ^ 6 + Y1 ^ 6 + Y2 ^ 6) := by
  constructor <;> ring

/--
Closed-Form First-Order `k`-Jet Weierstrass Covariants (`Hk_e0, Thetak_e0, Jk_e0`) and
Cleared Differential Quotient (`Mk_e0`) for `e = 0` Reverse-Edge Cubics (`#71` & `#74`):
Under the square-zero perturbation `U_Jet = fBin(x, y) + c * z^3 + 2 * k * x * y * z` (`k^2 = 0`),
the 28 nonzero coefficient expressions of `PolarCovariants.{Hk, Thetak, Jk}` at `e = 0`
collapse identically through `h1Bin = 9 * a * b - d * f`, `fxyHalf = d * x + f * y`, and
`sSkew = f * fxBin - d * fyBin = (3 * a * f - d^2) * x^2 - (3 * b * d - f^2) * y^2`.
-/
def h0Bin (a _b d f : K) : K := 3 * a * f - d ^ 2
def h1Bin (a b d f : K) : K := 9 * a * b - d * f
def h2Bin (_a b d f : K) : K := 3 * b * d - f ^ 2
def fxyHalf (d f x y : K) : K := d * x + f * y
def sSkew (a b d f x y : K) : K := h0Bin a b d f * x ^ 2 - h2Bin a b d f * y ^ 2

theorem hessian_discriminant_identity_e0 (a b d f : K) :
    h1Bin a b d f ^ 2 - 4 * h0Bin a b d f * h2Bin a b d f = discBin a b d f := by
  simp only [h1Bin, h0Bin, h2Bin, discBin, disc0Bin]
  ring

theorem euler_skew_identities_e0 (a b d f x y : K) :
    (f * fxBin a b d f x y - d * fyBin a b d f x y = sSkew a b d f x y) ∧
    (x * hxBin a b d f x y - y * hyBin a b d f x y = 2 * sSkew a b d f x y) ∧
    (3 * fBin a b d f x y * sSkew a b d f x y -
      hBin a b d f x y * (x * fxBin a b d f x y - y * fyBin a b d f x y) =
      -x * y * kBin a b d f x y) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [fxBin, fyBin, hxBin, hyBin, fBin, hBin, kBin, sSkew, h0Bin, h2Bin] <;>
    ring

def Hk_e0 (_a _b c d f x y z : K) : K := -18 * c * z ^ 2 * fxyHalf d f x y

def Thetak_e0 (a b c d f x y z : K) : K :=
  27 * c ^ 2 * z * hBin a b d f x y *
    (2 * fxyHalf d f x y * hBin a b d f x y - h1Bin a b d f * fBin a b d f x y) +
  27 * c ^ 3 * z ^ 4 *
    (5 * h1Bin a b d f * hBin a b d f x y - 6 * discBin a b d f * x * y)

def Jk_e0 (a b c d f x y z : K) : K :=
  -162 * c ^ 3 * z * hBin a b d f x y ^ 2 *
    (sSkew a b d f x y * hBin a b d f x y + fxyHalf d f x y * kBin a b d f x y) +
  486 * c ^ 4 * z ^ 4 *
    ((h1Bin a b d f * hBin a b d f x y - discBin a b d f * x * y) * kBin a b d f x y +
      3 * discBin a b d f * fBin a b d f x y * sSkew a b d f x y) -
  1458 * c ^ 5 * discBin a b d f * z ^ 7 * sSkew a b d f x y

def Mk_e0 (a b c d f x y z : K) : K :=
  243 * c ^ 3 * z ^ 2 * h1Bin a b d f * hBin a b d f x y * kBin a b d f x y -
  4374 * c ^ 4 * discBin a b d f * z ^ 5 * sSkew a b d f x y

def D0_Hk_e0 (a b c d f x y z : K) : K := -18 * c * z ^ 2 * sSkew a b d f x y
def Dk_H0_e0 (a b c d f x y z : K) : K := -36 * c * z ^ 2 * sSkew a b d f x y
def Dk_Theta0_e0 (a b c d f x y z : K) : K :=
  108 * c ^ 2 * z * hBin a b d f x y ^ 2 * sSkew a b d f x y +
  162 * c ^ 3 * discBin a b d f * z ^ 4 * (x * fxBin a b d f x y - y * fyBin a b d f x y)
def D0_Thetak_e0 (a b c d f x y z : K) : K :=
  27 * c ^ 2 * z *
    (kBin a b d f x y * (2 * fxyHalf d f x y * hBin a b d f x y - h1Bin a b d f * fBin a b d f x y) +
      2 * hBin a b d f x y * (sSkew a b d f x y * hBin a b d f x y + fxyHalf d f x y * kBin a b d f x y)) +
  27 * c ^ 3 * z ^ 4 *
    (5 * h1Bin a b d f * kBin a b d f x y -
      6 * discBin a b d f * (x * fxBin a b d f x y - y * fyBin a b d f x y))

/--
Closed-Form First-Order `k`-Jet Cleared Invariant Differential Identity (`#71` & `#74`):
At order `k^1` in `(H0 + k*Hk) * D(Theta0 + k*Thetak) - 2*(Theta0 + k*Thetak) * D(H0 + k*Hk) + 3*z*(J0 + k*Jk)`,
the entire expression equals `M0 * (2 * x * y * z) + U_e0 * Mk_e0` identically over `K`.
-/
theorem cleared_differential_jet_e0 (a b c d f x y z : K) :
    H_e0 a b c d f x y z * (D0_Thetak_e0 a b c d f x y z + Dk_Theta0_e0 a b c d f x y z) +
      Hk_e0 a b c d f x y z * Dop_Theta_e0 a b c d f x y z -
      2 * Theta_e0 a b c d f x y z * (D0_Hk_e0 a b c d f x y z + Dk_H0_e0 a b c d f x y z) -
      2 * Thetak_e0 a b c d f x y z * Dop_H_e0 a b c d f x y z +
      3 * z * Jk_e0 a b c d f x y z =
    (729 * c ^ 4 * discBin a b d f * z ^ 4 * kBin a b d f x y) * (2 * x * y * z) +
      U_e0 a b c d f x y z * Mk_e0 a b c d f x y z := by
  simp only [H_e0, Hk_e0, Theta_e0, Thetak_e0, Jk_e0, Dop_H_e0, Dop_Theta_e0,
    D0_Hk_e0, Dk_H0_e0, Dk_Theta0_e0, D0_Thetak_e0, U_e0, Mk_e0]
  ring

/--
2-Direction Mordell Wronskian Divergence-Free Law (`#71` & `#74`):
On any Mordell Weierstrass hypersurface `Y2 = X^3 + B6`, choosing two commuting parameter
derivations `(E1, E2)` with Wronskian weights `psi1 = E2_B6` and `psi2 = -E1_B6` (so
`E1_psi1 + E2_psi2 = E1_E2_B6 - E1_E2_B6 = 0`) and horizontal shifts `wX1 = 2 * X * E1_E2_B6`,
`wX2 = -2 * X * E1_E2_B6` makes the total Mordell residue divergence vanish identically (`= 0`).
-/
theorem mordell_wronskian_divergence_zero (X Y2 B6 E1_B6 E2_B6 E1_E2_B6 : K)
    (hcurve : Y2 = X ^ 3 + B6) :
    let psi1 := E2_B6
    let psi2 := -E1_B6
    let d1_psi1 := E1_E2_B6
    let d2_psi2 := -E1_E2_B6
    ((d1_psi1 * (2 * Y2) - psi1 * E1_B6) + (2 * d1_psi1 * (2 * Y2) - (2 * X * d1_psi1) * (3 * X ^ 2))) +
    ((d2_psi2 * (2 * Y2) - psi2 * E2_B6) + (2 * d2_psi2 * (2 * Y2) - (2 * X * d2_psi2) * (3 * X ^ 2))) = 0 := by
  dsimp
  linear_combination 0 * hcurve

/--
Official `instance.rec` Reverse-Edge `e = 0` Ternary Cubic Reduction for `#74 one-reflection-skew`:
For the exact benchmark sextic `F_74` in `74-one-reflection-skew/instance.rec`, setting
`B1 = (X0, X2, Y0)`, `B2 = (X1, Y1)`, `B3 = (Y2)` with `Y0 = c0 * X0, X2 = c2 * X0, Y1 = c1 * X1`
and `x = X0^2, y = X1^2, z = Y2^2` reduces `F_74` identically to `U_e0(a, b, c, d, f, x, y, z)`
with `d = c0 * c1 * (1 + inv7 * c0^2)` and `f = c0 * c1 * (c2 - inv7 * c1^2)`.
-/
theorem official_one_reflection_skew_74_reverse_edge_cubic
    (X0 X1 Y2 c0 c1 c2 inv7 : K) :
    let Y0 := c0 * X0
    let X2 := c2 * X0
    let Y1 := c1 * X1
    let x := X0 ^ 2
    let y := X1 ^ 2
    let z := Y2 ^ 2
    let a := 1 + c0 ^ 6 + c2 ^ 6
    let b := 1 + c1 ^ 6
    let c := (1 : K)
    let d := c0 * c1 * (1 + inv7 * c0 ^ 2)
    let f := c0 * c1 * (c2 - inv7 * c1 ^ 2)
    (X0 ^ 6 + X0 ^ 3 * X1 * Y0 * Y1 + inv7 * X0 * X1 * Y0 ^ 3 * Y1 -
      inv7 * X0 * X1 * Y0 * Y1 ^ 3 + X1 ^ 6 + X1 ^ 3 * X2 * Y0 * Y1 +
      X2 ^ 6 + Y0 ^ 6 + Y1 ^ 6 + Y2 ^ 6) =
    U_e0 a b c d f x y z := by
  simp only [U_e0, fBin]
  ring

/--
Official `instance.rec` Reverse-Edge `e = 0` Ternary Cubic Reduction for `#71 four-plus-two-residual`:
For the exact benchmark sextic `F_71` in `71-four-plus-two-residual/instance.rec`, setting
`B1 = (X0, X1)`, `B2 = (Y0, Y1)`, `B3 = (X2, Y2)` with `X1 = c0 * X0, Y1 = c1 * Y0, Y2 = c2 * X2`
and `x = X0^2, y = Y0^2, z = X2^2` reduces `F_71` identically to `U_e0(a, b, c, d, f, x, y, z)`
with complete passive-ratio separation `a(c0), b(c1), c(c2)` and `f = 2 * d = 10/7 * c0 * c1`.
-/
theorem official_four_plus_two_residual_71_reverse_edge_cubic
    (X0 Y0 X2 c0 c1 c2 inv7 : K) :
    let X1 := c0 * X0
    let Y1 := c1 * Y0
    let Y2 := c2 * X2
    let x := X0 ^ 2
    let y := Y0 ^ 2
    let z := X2 ^ 2
    let a := 1 + 5 * inv7 * c0 + 10 * inv7 * c0 ^ 5 + c0 ^ 6
    let b := 1 + 5 * inv7 * c1 + 15 * inv7 * c1 ^ 5 + c1 ^ 6
    let c := 1 + 15 * inv7 * c2 ^ 2 + 10 * inv7 * c2 ^ 4 + c2 ^ 6
    let d := 5 * inv7 * c0 * c1
    let f := 10 * inv7 * c0 * c1
    (X0 ^ 6 + 5 * inv7 * X0 ^ 5 * X1 + 5 * inv7 * X0 ^ 3 * X1 * Y0 * Y1 +
      10 * inv7 * X0 * X1 ^ 5 + 10 * inv7 * X0 * X1 * Y0 ^ 3 * Y1 + X1 ^ 6 +
      X2 ^ 6 + 15 * inv7 * X2 ^ 4 * Y2 ^ 2 + 10 * inv7 * X2 ^ 2 * Y2 ^ 4 +
      Y0 ^ 6 + 5 * inv7 * Y0 ^ 5 * Y1 + 15 * inv7 * Y0 * Y1 ^ 5 + Y1 ^ 6 + Y2 ^ 6) =
    U_e0 a b c d f x y z := by
  simp only [U_e0, fBin]
  ring

/--
Official `instance.rec` 48-Term Tensor-Rank-1 Decomposition for `#69 rank-one-biquartic`:
Verifies that `F_69 = f69(X) + g69(Y) + (5/7) * L69(X)^2 * M69(Y)` where
`L69(X) = X0^2 + X0*X1 + 2*X1*X2 + 3*X2^2` and `M69(Y) = Y0^2 + Y0*Y1 + 2*Y1*Y2 + 3*Y2^2`.
-/
theorem official_rank_one_biquartic_69_decomposition
    (X0 X1 X2 Y0 Y1 Y2 inv7 : K) :
    let f69 := X0 ^ 6 + 5 * inv7 * X0 ^ 5 * X1 + 5 * inv7 * X0 ^ 2 * X1 ^ 3 * X2 +
               15 * inv7 * X0 * X2 ^ 5 + X1 ^ 6 + 10 * inv7 * X1 ^ 5 * X2 + X2 ^ 6
    let g69 := Y0 ^ 6 + 10 * inv7 * Y0 ^ 5 * Y1 + 10 * inv7 * Y0 ^ 3 * Y1 * Y2 ^ 2 +
               5 * inv7 * Y0 * Y2 ^ 5 + Y1 ^ 6 + 15 * inv7 * Y1 ^ 5 * Y2 + Y2 ^ 6
    let L69 := X0 ^ 2 + X0 * X1 + 2 * X1 * X2 + 3 * X2 ^ 2
    let M69 := Y0 ^ 2 + Y0 * Y1 + 2 * Y1 * Y2 + 3 * Y2 ^ 2
    f69 + g69 + 5 * inv7 * L69 ^ 2 * M69 =
      X0 ^ 6 + 5 * inv7 * X0 ^ 5 * X1 + 5 * inv7 * X0 ^ 4 * Y0 ^ 2 + 5 * inv7 * X0 ^ 4 * Y0 * Y1 +
      10 * inv7 * X0 ^ 4 * Y1 * Y2 + 15 * inv7 * X0 ^ 4 * Y2 ^ 2 + 10 * inv7 * X0 ^ 3 * X1 * Y0 ^ 2 +
      10 * inv7 * X0 ^ 3 * X1 * Y0 * Y1 + 20 * inv7 * X0 ^ 3 * X1 * Y1 * Y2 + 30 * inv7 * X0 ^ 3 * X1 * Y2 ^ 2 +
      5 * inv7 * X0 ^ 2 * X1 ^ 3 * X2 + 5 * inv7 * X0 ^ 2 * X1 ^ 2 * Y0 ^ 2 + 5 * inv7 * X0 ^ 2 * X1 ^ 2 * Y0 * Y1 +
      10 * inv7 * X0 ^ 2 * X1 ^ 2 * Y1 * Y2 + 15 * inv7 * X0 ^ 2 * X1 ^ 2 * Y2 ^ 2 + 20 * inv7 * X0 ^ 2 * X1 * X2 * Y0 ^ 2 +
      20 * inv7 * X0 ^ 2 * X1 * X2 * Y0 * Y1 + 40 * inv7 * X0 ^ 2 * X1 * X2 * Y1 * Y2 + 60 * inv7 * X0 ^ 2 * X1 * X2 * Y2 ^ 2 +
      30 * inv7 * X0 ^ 2 * X2 ^ 2 * Y0 ^ 2 + 30 * inv7 * X0 ^ 2 * X2 ^ 2 * Y0 * Y1 + 60 * inv7 * X0 ^ 2 * X2 ^ 2 * Y1 * Y2 +
      90 * inv7 * X0 ^ 2 * X2 ^ 2 * Y2 ^ 2 + 20 * inv7 * X0 * X1 ^ 2 * X2 * Y0 ^ 2 + 20 * inv7 * X0 * X1 ^ 2 * X2 * Y0 * Y1 +
      40 * inv7 * X0 * X1 ^ 2 * X2 * Y1 * Y2 + 60 * inv7 * X0 * X1 ^ 2 * X2 * Y2 ^ 2 + 30 * inv7 * X0 * X1 * X2 ^ 2 * Y0 ^ 2 +
      30 * inv7 * X0 * X1 * X2 ^ 2 * Y0 * Y1 + 60 * inv7 * X0 * X1 * X2 ^ 2 * Y1 * Y2 + 90 * inv7 * X0 * X1 * X2 ^ 2 * Y2 ^ 2 +
      15 * inv7 * X0 * X2 ^ 5 + X1 ^ 6 + 10 * inv7 * X1 ^ 5 * X2 + 20 * inv7 * X1 ^ 2 * X2 ^ 2 * Y0 ^ 2 +
      20 * inv7 * X1 ^ 2 * X2 ^ 2 * Y0 * Y1 + 40 * inv7 * X1 ^ 2 * X2 ^ 2 * Y1 * Y2 + 60 * inv7 * X1 ^ 2 * X2 ^ 2 * Y2 ^ 2 +
      60 * inv7 * X1 * X2 ^ 3 * Y0 ^ 2 + 60 * inv7 * X1 * X2 ^ 3 * Y0 * Y1 + 120 * inv7 * X1 * X2 ^ 3 * Y1 * Y2 +
      180 * inv7 * X1 * X2 ^ 3 * Y2 ^ 2 + X2 ^ 6 + 45 * inv7 * X2 ^ 4 * Y0 ^ 2 + 45 * inv7 * X2 ^ 4 * Y0 * Y1 +
      90 * inv7 * X2 ^ 4 * Y1 * Y2 + 135 * inv7 * X2 ^ 4 * Y2 ^ 2 + Y0 ^ 6 + 10 * inv7 * Y0 ^ 5 * Y1 +
      10 * inv7 * Y0 ^ 3 * Y1 * Y2 ^ 2 + 5 * inv7 * Y0 * Y2 ^ 5 + Y1 ^ 6 + 15 * inv7 * Y1 ^ 5 * Y2 + Y2 ^ 6 := by
  dsimp
  ring

/--
Official `instance.rec` Symmetric Contact-Surface Decomposition for `#72 quadric-contact-residual`:
Under `S0 = X0^2 + Y0^2` and `P0 = X0 * Y0`, `F_72` reduces with zero remainder to a cubic in `(S0, P0)`
over `(X1, X2, Y1, Y2)`:
`F_72 = S0^3 + 2 * S0 * P0^2 + 5 * S0 * (X1^2*Y1^2 + X1*X2*Y1*Y2 + X2^2*Y2^2) + (5/7) * P0 * X1*Y1*(X2^2 + 2*Y2^2) + X1^6 + X2^6 + Y1^6 + Y2^6`.
-/
theorem official_quadric_contact_residual_72_cubic_reduction
    (X0 X1 X2 Y0 Y1 Y2 inv7 : K) :
    let S0 := X0 ^ 2 + Y0 ^ 2
    let P0 := X0 * Y0
    S0 ^ 3 + 2 * S0 * P0 ^ 2 + 5 * S0 * (X1 ^ 2 * Y1 ^ 2 + X1 * X2 * Y1 * Y2 + X2 ^ 2 * Y2 ^ 2) +
      5 * inv7 * P0 * X1 * Y1 * (X2 ^ 2 + 2 * Y2 ^ 2) + X1 ^ 6 + X2 ^ 6 + Y1 ^ 6 + Y2 ^ 6 =
    X0 ^ 6 + 5 * X0 ^ 4 * Y0 ^ 2 + 5 * X0 ^ 2 * X1 ^ 2 * Y1 ^ 2 + 5 * X0 ^ 2 * X1 * X2 * Y1 * Y2 +
      5 * X0 ^ 2 * X2 ^ 2 * Y2 ^ 2 + 5 * X0 ^ 2 * Y0 ^ 4 + 5 * inv7 * X0 * X1 * X2 ^ 2 * Y0 * Y1 +
      10 * inv7 * X0 * X1 * Y0 * Y1 * Y2 ^ 2 + X1 ^ 6 + 5 * X1 ^ 2 * Y0 ^ 2 * Y1 ^ 2 +
      5 * X1 * X2 * Y0 ^ 2 * Y1 * Y2 + X2 ^ 6 + 5 * X2 ^ 2 * Y0 ^ 2 * Y2 ^ 2 + Y0 ^ 6 + Y1 ^ 6 + Y2 ^ 6 := by
  dsimp
  ring

/--
Cleared 3-Coordinate Paired-Normal Transport Identity for `#74 one-reflection-skew` on `B1 = (X0, X2, Y0) = (p, r, q)`:
Clearing the denominators `f^2 * G1^2` (where `G1 = p*f + r*h + q*g` is the 3-coordinate paired Euler gradient
and `H11 = p^2*fpp + r^2*frr + q^2*fqq + 2*p*r*fpr + 2*p*q*fpq + 2*r*q*frq` is the 3-coordinate paired Hessian),
the normal-chart source `3 * p^2 * q^3 / f - p^3 * q^3 * fpp / f^2` equals `p^3 * q^3 * (8 * G1 - H11) / G1^2`
plus the exact 2-component tangent divergence of `(Wr, Wq) = (-p^3 * q^3 * r / G1, -p^3 * q^4 / G1)`.
-/
theorem paired_normal_change_3coord_cleared
    (p r q f h g fpp fpr fpq frr frq fqq : K) :
    let G1 := p * f + r * h + q * g
    let H11 := p ^ 2 * fpp + r ^ 2 * frr + q ^ 2 * fqq + 2 * p * r * fpr + 2 * p * q * fpq + 2 * r * q * frq
    let f_df_r := f * fpr - h * fpp
    let f_dh_r := f * frr - h * fpr
    let f_dg_r := f * frq - h * fpq
    let f_dG1_r := -h * f + p * f_df_r + f * h + r * f_dh_r + q * f_dg_r
    let f_df_q := f * fpq - g * fpp
    let f_dh_q := f * frq - g * fpr
    let f_dg_q := f * fqq - g * fpq
    let f_dG1_q := -g * f + p * f_df_q + r * f_dh_q + f * g + q * f_dg_q
    let num_div_r := G1 * f * (3 * p ^ 2 * h * q ^ 3 * r - p ^ 3 * q ^ 3 * f) +
                     p ^ 3 * q ^ 3 * r * (f * f_dG1_r + G1 * f_df_r)
    let num_div_q := G1 * f * (3 * p ^ 2 * g * q ^ 4 - 4 * p ^ 3 * q ^ 3 * f) +
                     p ^ 3 * q ^ 4 * (f * f_dG1_q + G1 * f_df_q)
    G1 ^ 2 * (3 * p ^ 2 * q ^ 3 * f - p ^ 3 * q ^ 3 * fpp) =
      f ^ 2 * p ^ 3 * q ^ 3 * (8 * G1 - H11) + (num_div_r + num_div_q) := by
  dsimp
  ring

/--
Complete 6-Variable Physical Polynomial Lift of the Universal 4-Term Binary-Cubic Certificate Core
(`general_binary_cubic_6var_directional`):
For any 6-variable sextic of the form
`F = a(X) + b(X) * P + c(X) * P^2 + (d - 2) * P^3 + Y0^6 + Y1^6 + Y2^6 = f(a, b, c, d, P) + s^2 + T^2`
where `P = Y0 * Y1`, `s = Y0^3 - Y1^3`, `S = Y0^3 + Y1^3`, `T = Y2^3`, `R = T + inv3_tau * s`
(with `(3 * inv3_tau)^2 = 3`, i.e., `3 * inv3_tau^2 = 1`), and `EX(a) = 6*a, EX(b) = 4*b, EX(c) = 2*c`,
the 6-component polynomial vector field
`N_j = (3 * S * MX * X0 * U_j, 3 * S * MX * X1 * U_j, 3 * S * MX * X2 * U_j,
        MX * (6 * Y1^2 * V_j + Y0 * (s + 6 * inv3_tau * T) * B_j),
        MX * (6 * Y0^2 * V_j - Y1 * (s + 6 * inv3_tau * T) * B_j),
        3 * S * MX * Y2 * B_j)`
satisfies the global 6-variable directional identity
`∑ N_j_i ∂_i F = 6 * MX * S * P^j * D(a, b, c, d, P, R, T)` for all `j ∈ {0, 1, 2}`.
-/
theorem three_R_sq_identity (s T inv3_tau : K) (htau : 3 * inv3_tau ^ 2 = 1) :
    let R := T + inv3_tau * s
    3 * R ^ 2 = s ^ 2 + 6 * inv3_tau * s * T + 3 * T ^ 2 := by
  dsimp
  linear_combination s ^ 2 * htau

theorem general_binary_cubic_6var_directional
    (a b c d Y0 Y1 Y2 MX inv3_tau Uj Vj Bj rhs : K)
    (htau : 3 * inv3_tau ^ 2 = 1)
    (hscalar : fu a b c d (Y0 * Y1) * Uj + fp a b c d (Y0 * Y1) * Vj +
      3 * (Y2 ^ 3 + inv3_tau * (Y0 ^ 3 - Y1 ^ 3)) ^ 2 * Bj = rhs) :
    let P := Y0 * Y1
    let s := Y0 ^ 3 - Y1 ^ 3
    let S := Y0 ^ 3 + Y1 ^ 3
    let T := Y2 ^ 3
    let EX_F := 6 * a + 4 * b * P + 2 * c * P ^ 2
    let F_Y0 := (b + 2 * c * P + 3 * (d - 2) * P ^ 2) * Y1 + 6 * Y0 ^ 5
    let F_Y1 := (b + 2 * c * P + 3 * (d - 2) * P ^ 2) * Y0 + 6 * Y1 ^ 5
    let F_Y2 := 6 * Y2 ^ 5
    let N_EX := 3 * S * MX * Uj
    let N3 := MX * (6 * Y1 ^ 2 * Vj + Y0 * (s + 6 * inv3_tau * T) * Bj)
    let N4 := MX * (6 * Y0 ^ 2 * Vj - Y1 * (s + 6 * inv3_tau * T) * Bj)
    let N5 := 3 * S * MX * Y2 * Bj
    N_EX * EX_F + N3 * F_Y0 + N4 * F_Y1 + N5 * F_Y2 = 6 * MX * S * rhs := by
  dsimp only
  simp only [fu, fp] at hscalar
  linear_combination
    6 * MX * (Y0 ^ 3 + Y1 ^ 3) * hscalar -
    6 * MX * (Y0 ^ 3 + Y1 ^ 3) * (Y0 ^ 3 - Y1 ^ 3) ^ 2 * Bj * htau

end HodgeComputer.Constructions.GeneralBinaryCubic
end
