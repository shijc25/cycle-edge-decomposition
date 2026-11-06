import Cycle12.PotentialPayment12
import Cycle12.FiniteCutoffBounds
import Cycle12.FinitePotentialAnchors.Anchor10.Total

namespace Cycle12.Global12.FinitePayment11
open Real
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem decayPoint : (2:ℝ)^((((-4600371631753607686857975701580566295359503/2275468939189395754240000000000000000000000000):ℚ):ℝ)) ≤ (((998599628699165280902377/1000000000000000000000000):ℚ):ℝ) := by
  exact (Cycle13.certified_power_two (y:=(2270868567557642146553142024298419433704640497/2275468939189395754240000000000000000000000000)) (-1)
    (q:=(-4600371631753607686857975701580566295359503/2275468939189395754240000000000000000000000000)) (L:=(199719925739833055624517/200000000000000000000000)) (U:=(998599628699165280902377/1000000000000000000000000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2

theorem fee_bound : (FiniteChains.Chain006.costBound:ℝ)≤C*globalPhi (((6544313512558511419211029/54955146944825797952000):ℚ):ℝ) := by
  have ha : b*wA≤(((222362668270549947437107493/1868474996124077130368000):ℚ):ℝ) := by norm_num [b,wA]
  have hx : (((222362668270549947437107493/1868474996124077130368000):ℚ):ℝ)≤(((6544313512558511419211029/54955146944825797952000):ℚ):ℝ) := by norm_num
  have hU : globalLoss (((222362668270549947437107493/1868474996124077130368000):ℚ):ℝ)≤(((18827206801975587825543/250000000000000000000000):ℚ):ℝ) := by
    exact FiniteAnchor10.loss_bound
  have hv : (2:ℝ)^(-(lossRate/b)*((((6544313512558511419211029/54955146944825797952000):ℚ):ℝ)-(((222362668270549947437107493/1868474996124077130368000):ℚ):ℝ)))≤(((998599628699165280902377/1000000000000000000000000):ℚ):ℝ) := by
    have he : -(lossRate/b)*((((6544313512558511419211029/54955146944825797952000):ℚ):ℝ)-(((222362668270549947437107493/1868474996124077130368000):ℚ):ℝ))=(((-4600371631753607686857975701580566295359503/2275468939189395754240000000000000000000000000):ℚ):ℝ) := by
      norm_num [lossRate,eps,theta2,b]
    rw [he]
    exact decayPoint
  have hp := globalPhi_from_anchor ha hx hU hv
  have hh : (FiniteChains.Chain006.costBound:ℝ)≤C*(1-(((998599628699165280902377/1000000000000000000000000):ℚ):ℝ)*(((18827206801975587825543/250000000000000000000000):ℚ):ℝ)) := by
    norm_num [FiniteChains.Chain006.costBound,C]
  exact hh.trans (mul_le_mul_of_nonneg_left hp (by norm_num [C]))

theorem graph_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (horder : (Fintype.card V:ℝ)≤(2:ℝ)^((((55698660434967067471327493/467118749031019282592000):ℚ):ℝ)))
    (hlower : (((6544313512558511419211029/54955146944825797952000):ℚ):ℝ)≤logb 2 (Fintype.card V))
    : ∃ P : Cycle13.CyclePacking G,
      P.weight≤C*orderPotential (Fintype.card V)*Fintype.card V := by
  have hn : (Fintype.card V:ℝ)≤(2:ℝ)^((((119239/1000):ℚ):ℝ)) :=
    horder.trans (rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  have hp := FiniteAverageBounds.cutoff006 G (simple_graph_degree_cap G hn)
  exact potential_weight_from_fee G fee_bound hlower hp

end
end Cycle12.Global12.FinitePayment11
