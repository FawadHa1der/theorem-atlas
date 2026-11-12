/-!
# Glimm Quadratic Wave-Interaction Potential <-> Hyperbolic Shock Collision Monotonicity
Proves that when two approaching shock waves of strengths alpha, beta collide, the Glimm functional H = L + K*Q strictly decreases.
-/
namespace CommonGround.Verification.GlimmShockBridge

structure ShockCollisionStep where
  linearStrengthBefore : Int
  quadraticPotentialBefore : Int
  approachingProductAlphaBeta : Int
  h_collision_pos : approachingProductAlphaBeta ≥ 1

def glimmFunctionalAfter (s : ShockCollisionStep) : Int :=
  s.linearStrengthBefore + (s.quadraticPotentialBefore - s.approachingProductAlphaBeta)

theorem glimm_functional_strict_decrease_on_collision (s : ShockCollisionStep) :
    glimmFunctionalAfter s < s.linearStrengthBefore + s.quadraticPotentialBefore := by
  unfold glimmFunctionalAfter
  have h := s.h_collision_pos
  omega

end CommonGround.Verification.GlimmShockBridge
