import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Closed-Form `e = 0` Reverse-Edge Cubic Covariants and First-Order `k`-Jets

For any reverse-edge ternary cubic `U(x, y, z) = a*x^3 + d*x^2*y + f*x*y^2 + b*y^3 + c*z^3` (`e = 0`),
all Salmon/Fisher Weierstrass covariants (`H_e0, Theta_e0, J_e0, s6_e0`) and their first-order
`k`-jets under `U + 2*k*x*y*z` (`Hk_e0, Thetak_e0, Jk_e0, Mk_e0`) factor in closed form through
the binary cubic covariants `fBin, hBin, kBin, discBin`.
-/
noncomputable section
set_option maxHeartbeats 4000000
namespace ReverseEdgeCovariants

variable {K : Type*} [CommRing K]

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

def M0_e0 (a b c d f x y z : K) : K :=
  729 * c ^ 4 * discBin a b d f * z ^ 4 * kBin a b d f x y

theorem cleared_differential_jet_e0 (a b c d f x y z : K) :
    H_e0 a b c d f x y z * (D0_Thetak_e0 a b c d f x y z + Dk_Theta0_e0 a b c d f x y z) +
      Hk_e0 a b c d f x y z * Dop_Theta_e0 a b c d f x y z -
      2 * Theta_e0 a b c d f x y z * (D0_Hk_e0 a b c d f x y z + Dk_H0_e0 a b c d f x y z) -
      2 * Thetak_e0 a b c d f x y z * Dop_H_e0 a b c d f x y z +
      3 * z * Jk_e0 a b c d f x y z =
    M0_e0 a b c d f x y z * (2 * x * y * z) +
      U_e0 a b c d f x y z * Mk_e0 a b c d f x y z := by
  simp only [H_e0, Theta_e0, Hk_e0, Thetak_e0, Jk_e0, Mk_e0, M0_e0, U_e0,
    Dop_H_e0, Dop_Theta_e0, D0_Hk_e0, Dk_H0_e0, Dk_Theta0_e0, D0_Thetak_e0,
    fxyHalf, sSkew, h0Bin, h1Bin, h2Bin, discBin, disc0Bin,
    fBin, fxBin, fyBin, hBin, hxBin, hyBin, kBin]
  ring

end ReverseEdgeCovariants
end
