import HodgeComputer.Verify
import HodgeComputer.Constructions.TransitiveCubic.Shear
import Mathlib.Tactic.Ring

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

end HodgeComputer.Constructions.GeneralBinaryCubic
end
