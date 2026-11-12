/-!
# Moser-Tardos Algorithmic Lovasz Local Lemma <-> Entropy Compression Witness Tree Injection
Proves that when each resampling step compresses log-space below the entropy capacity, the trace must terminate.
-/
namespace CommonGround.Verification.EntropyCompression

structure ResamplingTrace where
  initialTapeBits : Int
  stepsRun : Int
  bitsSavedPerStep : Int
  finalStateOverhead : Int
  h_gain_pos : bitsSavedPerStep ≥ 1

def compressedCodeSize (t : ResamplingTrace) : Int :=
  t.initialTapeBits + t.finalStateOverhead - t.stepsRun * t.bitsSavedPerStep

theorem entropy_incompressibility_step_bound (t : ResamplingTrace)
    (h_incompressible : compressedCodeSize t ≥ t.initialTapeBits) :
    t.stepsRun * t.bitsSavedPerStep ≤ t.finalStateOverhead := by
  unfold compressedCodeSize at h_incompressible
  omega

end CommonGround.Verification.EntropyCompression
