import Cycle12.PotentialPayment12
import Cycle12.FiniteCutoffBounds

namespace Cycle12.Global12.FinitePayment06
open Real
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem fee_bound : (FiniteChains.Chain004.costBound:ℝ)≤C*phi0 := by
  norm_num [FiniteChains.Chain004.costBound,C,phi0]

theorem graph_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (horder : (Fintype.card V:ℝ)≤(2:ℝ)^((((1777893408069323493784387493/14947799968992617042944000):ℚ):ℝ)))
    : ∃ P : Cycle13.CyclePacking G,
      P.weight≤C*orderPotential (Fintype.card V)*Fintype.card V := by
  have hn : (Fintype.card V:ℝ)≤(2:ℝ)^((((118941/1000):ℚ):ℝ)) :=
    horder.trans (rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  have hp := FiniteAverageBounds.cutoff004 G (simple_graph_degree_cap G hn)
  exact potential_weight_from_floor G fee_bound hp

end
end Cycle12.Global12.FinitePayment06
