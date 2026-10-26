import Proposal.PhysicalNormalTransport

/-!
# First-Order `k`-Jet Covariant Calculus in the Physical Function Field for `#74 one-reflection-skew`

Instantiates the closed-form `e = 0` reverse-edge Weierstrass covariants (`H_e0, Theta_e0, J_e0`)
in `FunctionField` of `#74 one-reflection-skew`, proving that the Weierstrass point `(xi, eta)`
lies on the Mordell (`I_4 = 0`) curve `eta^2 = xi^3 + bWeierstrass` (`bWeierstrass = -s6_e0 / 4`).
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace OneReflectionSkewCubicJets
open OneReflectionSkewPhysical OneReflectionSkewCoordinates OneReflectionSkewNormalTransport
open ReverseEdgeCovariants

def H_phys : FunctionField := H_e0 coeffA coeffB coeffC coeffD coeffF x y 1
def Theta_phys : FunctionField := Theta_e0 coeffA coeffB coeffC coeffD coeffF x y 1
def J_phys : FunctionField := J_e0 coeffA coeffB coeffC coeffD coeffF x y 1
def s6_phys : FunctionField := s6_e0 coeffA coeffB coeffC coeffD coeffF

def xi : FunctionField := Theta_phys / H_phys^2
def eta : FunctionField := -J_phys / (2 * H_phys^3)
def bWeierstrass : FunctionField := -s6_phys / 4

theorem mordell_syzygy_in_field :
    J_phys^2 - (4 * Theta_phys^3 - s6_phys * H_phys^6) = 0 := by
  unfold J_phys Theta_phys H_phys s6_phys
  rw [full_syzygy_e0, cubic_equation, zero_mul]

theorem mordell_weierstrass_curve (hH : H_phys ≠ 0) :
    eta^2 = xi^3 + bWeierstrass := by
  have hs := mordell_syzygy_in_field
  have h2 : (2 : FunctionField) ≠ 0 := by
    intro h
    have hc : (residueMap.comp MvPolynomial.C) (2 : ℂ) = 0 := by
      rw [RingHom.comp_apply, map_ofNat, map_ofNat, h]
    exact (by norm_num : (2 : ℂ) ≠ 0) ((map_eq_zero (residueMap.comp MvPolynomial.C)).mp hc)
  have h4 : (4 : FunctionField) ≠ 0 := by
    rw [show (4 : FunctionField) = 2 * 2 by ring]
    exact mul_ne_zero h2 h2
  unfold eta xi bWeierstrass
  field_simp [hH, h2, h4]
  linear_combination 4 * hs

end OneReflectionSkewCubicJets
end
