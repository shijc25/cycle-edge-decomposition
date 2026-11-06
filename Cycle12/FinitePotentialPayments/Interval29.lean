import Cycle12.PotentialPayment12
import Cycle12.FiniteCutoffBounds
import Cycle12.FinitePotentialAnchors.Anchor14.Total

namespace Cycle12.Global12.FinitePayment29
open Real
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem decayPoint : (2:ℝ)^((((-13801114895260823060573927104741698886078509/28443361739867446928000000000000000000000000):ℚ):ℝ)) ≤ (((178597784037852381945761/250000000000000000000000):ℚ):ℝ) := by
  exact (Cycle13.certified_power_two (y:=(14642246844606623867426072895258301113921491/28443361739867446928000000000000000000000000)) (-1)
    (q:=(-13801114895260823060573927104741698886078509/28443361739867446928000000000000000000000000)) (L:=(22324723004731547743219/31250000000000000000000)) (U:=(178597784037852381945761/250000000000000000000000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2

theorem fee_bound : (FiniteChains.Chain060.costBound:ℝ)≤C*globalPhi (((2024065727832869965111861/14597460907219352581000):ℚ):ℝ) := by
  have ha : b*wA≤(((14032658476071347479882493/116779687257754820648000):ℚ):ℝ) := by norm_num [b,wA]
  have hx : (((14032658476071347479882493/116779687257754820648000):ℚ):ℝ)≤(((2024065727832869965111861/14597460907219352581000):ℚ):ℝ) := by norm_num
  have hU : globalLoss (((14032658476071347479882493/116779687257754820648000):ℚ):ℝ)≤(((71305432040481402198983/1000000000000000000000000):ℚ):ℝ) := by
    exact FiniteAnchor14.loss_bound
  have hv : (2:ℝ)^(-(lossRate/b)*((((2024065727832869965111861/14597460907219352581000):ℚ):ℝ)-(((14032658476071347479882493/116779687257754820648000):ℚ):ℝ)))≤(((178597784037852381945761/250000000000000000000000):ℚ):ℝ) := by
    have he : -(lossRate/b)*((((2024065727832869965111861/14597460907219352581000):ℚ):ℝ)-(((14032658476071347479882493/116779687257754820648000):ℚ):ℝ))=(((-13801114895260823060573927104741698886078509/28443361739867446928000000000000000000000000):ℚ):ℝ) := by
      norm_num [lossRate,eps,theta2,b]
    rw [he]
    exact decayPoint
  have hp := globalPhi_from_anchor ha hx hU hv
  have hh : (FiniteChains.Chain060.costBound:ℝ)≤C*(1-(((178597784037852381945761/250000000000000000000000):ℚ):ℝ)*(((71305432040481402198983/1000000000000000000000000):ℚ):ℝ)) := by
    norm_num [FiniteChains.Chain060.costBound,C]
  exact hh.trans (mul_le_mul_of_nonneg_left hp (by norm_num [C]))

theorem graph_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (horder : (Fintype.card V:ℝ)≤(2:ℝ)^((((16336516979102400536962381/116779687257754820648000):ℚ):ℝ)))
    (hlower : (((2024065727832869965111861/14597460907219352581000):ℚ):ℝ)≤logb 2 (Fintype.card V))
    : ∃ P : Cycle13.CyclePacking G,
      P.weight≤C*orderPotential (Fintype.card V)*Fintype.card V := by
  have hn : (Fintype.card V:ℝ)≤(2:ℝ)^((((34973/250):ℚ):ℝ)) :=
    horder.trans (rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  have hp := FiniteAverageBounds.cutoff060 G (simple_graph_degree_cap G hn)
  exact potential_weight_from_fee G fee_bound hlower hp

end
end Cycle12.Global12.FinitePayment29
