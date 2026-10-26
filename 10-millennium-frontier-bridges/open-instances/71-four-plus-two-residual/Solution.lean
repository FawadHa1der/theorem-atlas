import HodgeTarget
import Proposal.PhysicalCubicJets
import Proposal.JacobianSeedAndModel
import HodgeComputer.Constructions.GeneralBinaryCubic

/-!
# Target Binding, Binary-Block Contact Wronskian Law, and Residue-Clearing Reduction for `#71`

Binds the protected target `(HodgeSubmission.F, HodgeSubmission.A, HodgeSubmission.q)` of
`#71 four-plus-two-residual` to `FourPlusTwoPhysical.{sextic, source}`, proves `certificate_from_residue_solution`,
proves the official `f = 2d` reverse-edge cubic reduction (`official_reverse_edge_cubic`), and
exports the binary-block 3-torsion contact-cover Wronskian strict certificate law.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace Submission
open FourPlusTwoPhysical FourPlusTwoCoordinates
open FourPlusTwoNormalTransport FourPlusTwoCubicJets
open FourPlusTwoJacobianSeed ReverseEdgeCovariants

theorem protected_F : HodgeSubmission.F = sextic := by
  unfold HodgeSubmission.F sextic
  simp only [map_ofNat]

theorem protected_A : HodgeSubmission.A = source := by
  unfold HodgeSubmission.A source
  ring

theorem protected_q : HodgeSubmission.q = 1 := rfl

theorem certificate_from_residue_solution
    (w : Fin 5 → FunctionField)
    (hw : HoldoutConstruction.residueDivergence tangent (residueMap (MvPolynomial.pderiv 0 sextic)) w =
      -(residueMap (MvPolynomial.pderiv 0 source) / residueMap (MvPolynomial.pderiv 0 sextic) -
        residueMap source * residueMap (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 sextic)) /
          (residueMap (MvPolynomial.pderiv 0 sextic))^2)) :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := by
  rw [protected_F, protected_A, protected_q]
  exact certificate_of_residue_solution w hw

theorem official_reverse_edge_cubic
    {K : Type*} [CommRing K]
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
      Y0 ^ 6 + 5 * inv7 * Y0 ^ 5 * Y1 + 15 * inv7 * Y0 * Y1 ^ 5 + Y1 ^ 6 + Y2 ^ 6 =
      U_e0 a b c d f x y z) ∧
    (f = 2 * d) := by
  dsimp [U_e0, fBin]
  constructor <;> ring

end Submission
end
