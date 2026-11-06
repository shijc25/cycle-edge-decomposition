import Cycle12.PotentialPayment12
import Cycle12.FiniteCutoffBounds
import Cycle12.FinitePotentialAnchors.Anchor10.Total

namespace Cycle12.Global12.FinitePayment10
open Real
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem decayPoint : (2:ℝ)^((((0/1):ℚ):ℝ)) ≤ (((1/1):ℚ):ℝ) := by
  exact (Cycle13.certified_power_two (y:=(0/1)) (0)
    (q:=(0/1)) (L:=(1/1)) (U:=(1/1))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2

theorem fee_bound : (FiniteChains.Chain049.costBound:ℝ)≤C*globalPhi (((222362668270549947437107493/1868474996124077130368000):ℚ):ℝ) := by
  have ha : b*wA≤(((222362668270549947437107493/1868474996124077130368000):ℚ):ℝ) := by norm_num [b,wA]
  have hx : (((222362668270549947437107493/1868474996124077130368000):ℚ):ℝ)≤(((222362668270549947437107493/1868474996124077130368000):ℚ):ℝ) := by norm_num
  have hU : globalLoss (((222362668270549947437107493/1868474996124077130368000):ℚ):ℝ)≤(((18827206801975587825543/250000000000000000000000):ℚ):ℝ) := by
    exact FiniteAnchor10.loss_bound
  have hv : (2:ℝ)^(-(lossRate/b)*((((222362668270549947437107493/1868474996124077130368000):ℚ):ℝ)-(((222362668270549947437107493/1868474996124077130368000):ℚ):ℝ)))≤(((1/1):ℚ):ℝ) := by
    have he : -(lossRate/b)*((((222362668270549947437107493/1868474996124077130368000):ℚ):ℝ)-(((222362668270549947437107493/1868474996124077130368000):ℚ):ℝ))=(((0/1):ℚ):ℝ) := by
      norm_num [lossRate,eps,theta2,b]
    rw [he]
    exact decayPoint
  have hp := globalPhi_from_anchor ha hx hU hv
  have hh : (FiniteChains.Chain049.costBound:ℝ)≤C*(1-(((1/1):ℚ):ℝ)*(((18827206801975587825543/250000000000000000000000):ℚ):ℝ)) := by
    norm_num [FiniteChains.Chain049.costBound,C]
  exact hh.trans (mul_le_mul_of_nonneg_left hp (by norm_num [C]))

theorem graph_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (horder : (Fintype.card V:ℝ)≤(2:ℝ)^((((6544313512558511419211029/54955146944825797952000):ℚ):ℝ)))
    (hlower : (((222362668270549947437107493/1868474996124077130368000):ℚ):ℝ)≤logb 2 (Fintype.card V))
    : ∃ P : Cycle13.CyclePacking G,
      P.weight≤C*orderPotential (Fintype.card V)*Fintype.card V := by
  have hn : (Fintype.card V:ℝ)≤(2:ℝ)^((((23817/200):ℚ):ℝ)) :=
    horder.trans (rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  have hp := FiniteAverageBounds.cutoff049 G (simple_graph_degree_cap G hn)
  exact potential_weight_from_fee G fee_bound hlower hp

end
end Cycle12.Global12.FinitePayment10
