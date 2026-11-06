import Cycle12.PotentialPayment12
import Cycle12.FiniteCutoffBounds
import Cycle12.FinitePotentialAnchors.Anchor12.Total

namespace Cycle12.Global12.FinitePayment12
open Real
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem decayPoint : (2:ℝ)^((((0/1):ℚ):ℝ)) ≤ (((1/1):ℚ):ℝ) := by
  exact (Cycle13.certified_power_two (y:=(0/1)) (0)
    (q:=(0/1)) (L:=(1/1)) (U:=(1/1))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2

theorem fee_bound : (FiniteChains.Chain054.costBound:ℝ)≤C*globalPhi (((55698660434967067471327493/467118749031019282592000):ℚ):ℝ) := by
  have ha : b*wA≤(((55698660434967067471327493/467118749031019282592000):ℚ):ℝ) := by norm_num [b,wA]
  have hx : (((55698660434967067471327493/467118749031019282592000):ℚ):ℝ)≤(((55698660434967067471327493/467118749031019282592000):ℚ):ℝ) := by norm_num
  have hU : globalLoss (((55698660434967067471327493/467118749031019282592000):ℚ):ℝ)≤(((2979547974693611958347/40000000000000000000000):ℚ):ℝ) := by
    exact FiniteAnchor12.loss_bound
  have hv : (2:ℝ)^(-(lossRate/b)*((((55698660434967067471327493/467118749031019282592000):ℚ):ℝ)-(((55698660434967067471327493/467118749031019282592000):ℚ):ℝ)))≤(((1/1):ℚ):ℝ) := by
    have he : -(lossRate/b)*((((55698660434967067471327493/467118749031019282592000):ℚ):ℝ)-(((55698660434967067471327493/467118749031019282592000):ℚ):ℝ))=(((0/1):ℚ):ℝ) := by
      norm_num [lossRate,eps,theta2,b]
    rw [he]
    exact decayPoint
  have hp := globalPhi_from_anchor ha hx hU hv
  have hh : (FiniteChains.Chain054.costBound:ℝ)≤C*(1-(((1/1):ℚ):ℝ)*(((2979547974693611958347/40000000000000000000000):ℚ):ℝ)) := by
    norm_num [FiniteChains.Chain054.costBound,C]
  exact hh.trans (mul_le_mul_of_nonneg_left hp (by norm_num [C]))

theorem graph_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (horder : (Fintype.card V:ℝ)≤(2:ℝ)^((((27921325795703254143697493/233559374515509641296000):ℚ):ℝ)))
    (hlower : (((55698660434967067471327493/467118749031019282592000):ℚ):ℝ)≤logb 2 (Fintype.card V))
    : ∃ P : Cycle13.CyclePacking G,
      P.weight≤C*orderPotential (Fintype.card V)*Fintype.card V := by
  have hn : (Fintype.card V:ℝ)≤(2:ℝ)^((((29887/250):ℚ):ℝ)) :=
    horder.trans (rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  have hp := FiniteAverageBounds.cutoff054 G (simple_graph_degree_cap G hn)
  exact potential_weight_from_fee G fee_bound hlower hp

end
end Cycle12.Global12.FinitePayment12
