import Econlib.Optimization.DynamicProgramming.Core.Bellman

open Econlib.Optimization.DynamicProgramming
open Econlib.Optimization.DynamicProgramming.UnboundedDetMDP

namespace CommonGround.BellmanResidual

/-- A uniform exact Bellman residual bounds the error of a bounded candidate.
This is a local application of the contraction estimate to native Econlib
definitions. It supplies no approximate-oracle or policy guarantee. -/
theorem abs_sub_valueFunction_le_of_residual_le
    {S A : Type*} [Nonempty S] (M : DetMDP S A)
    (v : S → ℝ) (hv : Blackwell.UniformBounded v)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hres : ∀ s, |v s - M.bellmanOperator v s| ≤ ε) :
    ∀ s, |v s - M.valueFunction s| ≤ ε / (1 - M.β) := by
  let f := Blackwell.toBddFun v hv
  have hdist : dist f (bellmanOperatorBddFun M f) ≤ ε :=
    (BoundedContinuousFunction.dist_le hε).2 (fun s => by
      simpa only [f, Real.dist_eq, bellmanOperatorBddFun_apply,
        Blackwell.toBddFun_apply, Blackwell.toBddFun_coe] using hres s)
  have hbound : dist f (M.contractingWith_bellmanOperatorBddFun.fixedPoint
      (bellmanOperatorBddFun M)) ≤ ε / (1 - M.β) :=
    (M.contractingWith_bellmanOperatorBddFun.dist_fixedPoint_le f).trans
      ((div_le_div_iff_of_pos_right (sub_pos.mpr M.β_lt_one)).2 hdist)
  exact fun s => by
    simpa only [f, Real.dist_eq, Blackwell.toBddFun_apply,
      DetMDP.valueFunction, Blackwell.bddFixedPoint] using
      (BoundedContinuousFunction.dist_coe_le_dist (f := f)
        (g := M.contractingWith_bellmanOperatorBddFun.fixedPoint
          (bellmanOperatorBddFun M)) s).trans hbound

end CommonGround.BellmanResidual
