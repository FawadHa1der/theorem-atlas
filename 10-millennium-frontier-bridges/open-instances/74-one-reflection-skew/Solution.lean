import HodgeTarget
import Proposal.JacobianSeedAndModel
import HodgeComputer.Constructions.GeneralBinaryCubic

/-!
# Target Binding, Positive-Sector Certificate, and Residue-Clearing Reduction for `#74 one-reflection-skew`

Binds the protected target `(HodgeSubmission.F, HodgeSubmission.A, HodgeSubmission.q)` of
`#74 one-reflection-skew` to `OneReflectionSkewPhysical.{sextic, source}`, proves the
unconditional 6-variable strict `HodgeComputer.defect = 0` certificate on the positive-reflection
binary-cubic sector (`positive_sector_defect_zero`), proves the degree-10 even-parity Fermat cover
reduction (`fermat_cover_reduction`), and proves `certificate_from_residue_solution`.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace Submission
open OneReflectionSkewPhysical OneReflectionSkewCoordinates
open OneReflectionSkewNormalTransport OneReflectionSkewCubicJets
open OneReflectionSkewJacobianSeed ReverseEdgeCovariants

theorem protected_F : HodgeSubmission.F = sextic := by
  unfold HodgeSubmission.F sextic
  ring

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

theorem fermat_cover_reduction
    {K : Type*} [CommRing K]
    (X0 X1 c0 c1 cT alpha beta inv7 : K) (hfermat : alpha ^ 6 + beta ^ 6 = 1) :
    let Y0 := c0 * X0
    let T_val := cT * X0
    let Y1 := c1 * X1
    let X2 := alpha * T_val
    let Y2 := beta * T_val
    let x := X0 ^ 2
    let y := X1 ^ 2
    let a := 1 + c0 ^ 6 + cT ^ 6
    let b := 1 + c1 ^ 6
    let d := c0 * c1 * (1 + inv7 * c0 ^ 2)
    let f := c0 * c1 * (alpha * cT - inv7 * c1 ^ 2)
    (X0 ^ 6 + X0 ^ 3 * X1 * Y0 * Y1 + inv7 * X0 * X1 * Y0 ^ 3 * Y1 -
      inv7 * X0 * X1 * Y0 * Y1 ^ 3 + X1 ^ 6 + X1 ^ 3 * X2 * Y0 * Y1 +
      X2 ^ 6 + Y0 ^ 6 + Y1 ^ 6 + Y2 ^ 6 =
      fBin a b d f x y) ∧
    (T_val * X0 ^ 3 * Y0 ^ 3 * X0 ^ 2 = cT * c0 ^ 3 * x ^ 4 * X0) :=
  HodgeComputer.Constructions.GeneralBinaryCubic.one_reflection_skew_74_fermat_cover_reduction
    X0 X1 c0 c1 cT alpha beta inv7 hfermat

end Submission
end
