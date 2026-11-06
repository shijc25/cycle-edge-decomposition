import Cycle12.PotentialPayment12
import Cycle12.FiniteCutoffBounds
import Cycle12.FinitePotentialAnchors.Anchor14.Total

namespace Cycle12.Global12.FinitePayment37
open Real
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem decayPoint : (2:ℝ)^((((-105808547530332976797733441136353024793268569/142216808699337234640000000000000000000000000):ℚ):ℝ)) ≤ (((597083799811865199001477/1000000000000000000000000):ℚ):ℝ) := by
  exact (Cycle13.certified_power_two (y:=(36408261169004257842266558863646975206731431/142216808699337234640000000000000000000000000)) (-1)
    (q:=(-105808547530332976797733441136353024793268569/142216808699337234640000000000000000000000000)) (L:=(149270949952966299750369/250000000000000000000000)) (U:=(597083799811865199001477/1000000000000000000000000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2

theorem fee_bound : (FiniteChains.Chain062.costBound:ℝ)≤C*globalPhi (((1084028442136155390589677/7298730453609676290500):ℚ):ℝ) := by
  have ha : b*wA≤(((14032658476071347479882493/116779687257754820648000):ℚ):ℝ) := by norm_num [b,wA]
  have hx : (((14032658476071347479882493/116779687257754820648000):ℚ):ℝ)≤(((1084028442136155390589677/7298730453609676290500):ℚ):ℝ) := by norm_num
  have hU : globalLoss (((14032658476071347479882493/116779687257754820648000):ℚ):ℝ)≤(((71305432040481402198983/1000000000000000000000000):ℚ):ℝ) := by
    exact FiniteAnchor14.loss_bound
  have hv : (2:ℝ)^(-(lossRate/b)*((((1084028442136155390589677/7298730453609676290500):ℚ):ℝ)-(((14032658476071347479882493/116779687257754820648000):ℚ):ℝ)))≤(((597083799811865199001477/1000000000000000000000000):ℚ):ℝ) := by
    have he : -(lossRate/b)*((((1084028442136155390589677/7298730453609676290500):ℚ):ℝ)-(((14032658476071347479882493/116779687257754820648000):ℚ):ℝ))=(((-105808547530332976797733441136353024793268569/142216808699337234640000000000000000000000000):ℚ):ℝ) := by
      norm_num [lossRate,eps,theta2,b]
    rw [he]
    exact decayPoint
  have hp := globalPhi_from_anchor ha hx hU hv
  have hh : (FiniteChains.Chain062.costBound:ℝ)≤C*(1-(((597083799811865199001477/1000000000000000000000000):ℚ):ℝ)*(((71305432040481402198983/1000000000000000000000000):ℚ):ℝ)) := by
    norm_num [FiniteChains.Chain062.costBound,C]
  exact hh.trans (mul_le_mul_of_nonneg_left hp (by norm_num [C]))

theorem graph_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (horder : (Fintype.card V:ℝ)≤(2:ℝ)^((((699537849224717082620093/4671187490310192825920):ℚ):ℝ)))
    (hlower : (((1084028442136155390589677/7298730453609676290500):ℚ):ℝ)≤logb 2 (Fintype.card V))
    : ∃ P : Cycle13.CyclePacking G,
      P.weight≤C*orderPotential (Fintype.card V)*Fintype.card V := by
  have hn : (Fintype.card V:ℝ)≤(2:ℝ)^((((37439/250):ℚ):ℝ)) :=
    horder.trans (rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  have hp := FiniteAverageBounds.cutoff062 G (simple_graph_degree_cap G hn)
  exact potential_weight_from_fee G fee_bound hlower hp

end
end Cycle12.Global12.FinitePayment37
