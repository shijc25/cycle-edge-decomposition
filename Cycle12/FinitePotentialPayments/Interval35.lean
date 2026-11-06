import Cycle12.PotentialPayment12
import Cycle12.FiniteCutoffBounds
import Cycle12.FinitePotentialAnchors.Anchor14.Total

namespace Cycle12.Global12.FinitePayment35
open Real
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem decayPoint : (2:ℝ)^((((-96607804266825761424017489733191892202549563/142216808699337234640000000000000000000000000):ℚ):ℝ)) ≤ (((1248936839363502462301/2000000000000000000000):ℚ):ℝ) := by
  exact (Cycle13.certified_power_two (y:=(45609004432511473215982510266808107797450437/142216808699337234640000000000000000000000000)) (-1)
    (q:=(-96607804266825761424017489733191892202549563/142216808699337234640000000000000000000000000)) (L:=(624468419681751231150499/1000000000000000000000000)) (U:=(1248936839363502462301/2000000000000000000000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2

theorem fee_bound : (FiniteChains.Chain028.costBound:ℝ)≤C*globalPhi (((8528236380649802308649923/58389843628877410324000):ℚ):ℝ) := by
  have ha : b*wA≤(((14032658476071347479882493/116779687257754820648000):ℚ):ℝ) := by norm_num [b,wA]
  have hx : (((14032658476071347479882493/116779687257754820648000):ℚ):ℝ)≤(((8528236380649802308649923/58389843628877410324000):ℚ):ℝ) := by norm_num
  have hU : globalLoss (((14032658476071347479882493/116779687257754820648000):ℚ):ℝ)≤(((71305432040481402198983/1000000000000000000000000):ℚ):ℝ) := by
    exact FiniteAnchor14.loss_bound
  have hv : (2:ℝ)^(-(lossRate/b)*((((8528236380649802308649923/58389843628877410324000):ℚ):ℝ)-(((14032658476071347479882493/116779687257754820648000):ℚ):ℝ)))≤(((1248936839363502462301/2000000000000000000000):ℚ):ℝ) := by
    have he : -(lossRate/b)*((((8528236380649802308649923/58389843628877410324000):ℚ):ℝ)-(((14032658476071347479882493/116779687257754820648000):ℚ):ℝ))=(((-96607804266825761424017489733191892202549563/142216808699337234640000000000000000000000000):ℚ):ℝ) := by
      norm_num [lossRate,eps,theta2,b]
    rw [he]
    exact decayPoint
  have hp := globalPhi_from_anchor ha hx hU hv
  have hh : (FiniteChains.Chain028.costBound:ℝ)≤C*(1-(((1248936839363502462301/2000000000000000000000):ℚ):ℝ)*(((71305432040481402198983/1000000000000000000000000):ℚ):ℝ)) := by
    norm_num [FiniteChains.Chain028.costBound,C]
  exact hh.trans (mul_le_mul_of_nonneg_left hp (by norm_num [C]))

theorem graph_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (horder : (Fintype.card V:ℝ)≤(2:ℝ)^((((17200463917739045433367339/116779687257754820648000):ℚ):ℝ)))
    (hlower : (((8528236380649802308649923/58389843628877410324000):ℚ):ℝ)≤logb 2 (Fintype.card V))
    : ∃ P : Cycle13.CyclePacking G,
      P.weight≤C*orderPotential (Fintype.card V)*Fintype.card V := by
  have hn : (Fintype.card V:ℝ)≤(2:ℝ)^((((14729/100):ℚ):ℝ)) :=
    horder.trans (rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  have hp := FiniteAverageBounds.cutoff028 G (simple_graph_degree_cap G hn)
  exact potential_weight_from_fee G fee_bound hlower hp

end
end Cycle12.Global12.FinitePayment35
