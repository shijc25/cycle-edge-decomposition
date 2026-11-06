import Cycle12.PotentialPayment12
import Cycle12.FiniteCutoffBounds

namespace Cycle12.Global12.FinitePayment09
open Real
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem decayPoint : (2:ℝ)^((((-4600371631753607686857975701580566295359503/4550937878378791508480000000000000000000000000):ℚ):ℝ)) ≤ (((999299569047823256841779/1000000000000000000000000):ℚ):ℝ) := by
  exact (Cycle13.certified_power_two (y:=(4546337506747037900793142024298419433704640497/4550937878378791508480000000000000000000000000)) (-1)
    (q:=(-4600371631753607686857975701580566295359503/4550937878378791508480000000000000000000000000)) (L:=(62456223065488953375851/62500000000000000000000)) (U:=(999299569047823256841779/1000000000000000000000000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2

theorem fee_bound : (FiniteChains.Chain031.costBound:ℝ)≤C*globalPhi (((444581345384660454058147493/3736949992248154260736000):ℚ):ℝ) := by
  have ha : b*wA≤(((13888667319631906663815/116779687257754820648):ℚ):ℝ) := by norm_num [b,wA]
  have hx : (((13888667319631906663815/116779687257754820648):ℚ):ℝ)≤(((444581345384660454058147493/3736949992248154260736000):ℚ):ℝ) := by norm_num
  have hU : globalLoss (((13888667319631906663815/116779687257754820648):ℚ):ℝ)≤(((75584414501537703333549/1000000000000000000000000):ℚ):ℝ) := by
    have he : b*wA=(((13888667319631906663815/116779687257754820648):ℚ):ℝ) := by norm_num [b,wA]
    rw [←he]
    exact globalLoss_anchor_bound
  have hv : (2:ℝ)^(-(lossRate/b)*((((444581345384660454058147493/3736949992248154260736000):ℚ):ℝ)-(((13888667319631906663815/116779687257754820648):ℚ):ℝ)))≤(((999299569047823256841779/1000000000000000000000000):ℚ):ℝ) := by
    have he : -(lossRate/b)*((((444581345384660454058147493/3736949992248154260736000):ℚ):ℝ)-(((13888667319631906663815/116779687257754820648):ℚ):ℝ))=(((-4600371631753607686857975701580566295359503/4550937878378791508480000000000000000000000000):ℚ):ℝ) := by
      norm_num [lossRate,eps,theta2,b]
    rw [he]
    exact decayPoint
  have hp := globalPhi_from_anchor ha hx hU hv
  have hh : (FiniteChains.Chain031.costBound:ℝ)≤C*(1-(((999299569047823256841779/1000000000000000000000000):ℚ):ℝ)*(((75584414501537703333549/1000000000000000000000000):ℚ):ℝ)) := by
    norm_num [FiniteChains.Chain031.costBound,C]
  exact hh.trans (mul_le_mul_of_nonneg_left hp (by norm_num [C]))

theorem graph_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (horder : (Fintype.card V:ℝ)≤(2:ℝ)^((((222362668270549947437107493/1868474996124077130368000):ℚ):ℝ)))
    (hlower : (((444581345384660454058147493/3736949992248154260736000):ℚ):ℝ)≤logb 2 (Fintype.card V))
    : ∃ P : Cycle13.CyclePacking G,
      P.weight≤C*orderPotential (Fintype.card V)*Fintype.card V := by
  have hn : (Fintype.card V:ℝ)≤(2:ℝ)^((((14876/125):ℚ):ℝ)) :=
    horder.trans (rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  have hp := FiniteAverageBounds.cutoff031 G (simple_graph_degree_cap G hn)
  exact potential_weight_from_fee G fee_bound hlower hp

end
end Cycle12.Global12.FinitePayment09
