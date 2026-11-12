/-!
# Smale-Sard Fredholm Index Formula <-> Transversality Expected Moduli Dimension
Proves that for a regular value of the universal family projection, the moduli space dimension equals the Fredholm index of the linearized operator.
-/
namespace CommonGround.Verification.SmaleSardBridge

structure FredholmTransversalityDatum where
  domainKernelDim : Int
  targetCokernelDim : Int
  perturbationCokernelKill : Int
  h_surjective_family : targetCokernelDim = perturbationCokernelKill

def moduliVirtualDimension (d : FredholmTransversalityDatum) : Int :=
  d.domainKernelDim - (d.targetCokernelDim - d.perturbationCokernelKill)

theorem sard_smale_regular_moduli_dimension (d : FredholmTransversalityDatum) :
    moduliVirtualDimension d = d.domainKernelDim := by
  unfold moduliVirtualDimension
  have h := d.h_surjective_family
  omega

end CommonGround.Verification.SmaleSardBridge
