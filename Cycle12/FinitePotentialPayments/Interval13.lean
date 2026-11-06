import Cycle12.PotentialPayment12
import Cycle12.FiniteCutoffBounds
import Cycle12.FinitePotentialAnchors.Anchor12.Total

namespace Cycle12.Global12.FinitePayment13
open Real
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem decayPoint : (2:ℝ)^((((-4600371631753607686857975701580566295359503/568867234797348938560000000000000000000000000):ℚ):ℝ)) ≤ (((994410270054452697810583/1000000000000000000000000):ℚ):ℝ) := by
  exact (Cycle13.certified_power_two (y:=(564266863165595330873142024298419433704640497/568867234797348938560000000000000000000000000)) (-1)
    (q:=(-4600371631753607686857975701580566295359503/568867234797348938560000000000000000000000000)) (L:=(994410270054452695305051/1000000000000000000000000)) (U:=(994410270054452697810583/1000000000000000000000000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2

theorem fee_bound : (FiniteChains.Chain055.costBound:ℝ)≤C*globalPhi (((27921325795703254143697493/233559374515509641296000):ℚ):ℝ) := by
  have ha : b*wA≤(((55698660434967067471327493/467118749031019282592000):ℚ):ℝ) := by norm_num [b,wA]
  have hx : (((55698660434967067471327493/467118749031019282592000):ℚ):ℝ)≤(((27921325795703254143697493/233559374515509641296000):ℚ):ℝ) := by norm_num
  have hU : globalLoss (((55698660434967067471327493/467118749031019282592000):ℚ):ℝ)≤(((2979547974693611958347/40000000000000000000000):ℚ):ℝ) := by
    exact FiniteAnchor12.loss_bound
  have hv : (2:ℝ)^(-(lossRate/b)*((((27921325795703254143697493/233559374515509641296000):ℚ):ℝ)-(((55698660434967067471327493/467118749031019282592000):ℚ):ℝ)))≤(((994410270054452697810583/1000000000000000000000000):ℚ):ℝ) := by
    have he : -(lossRate/b)*((((27921325795703254143697493/233559374515509641296000):ℚ):ℝ)-(((55698660434967067471327493/467118749031019282592000):ℚ):ℝ))=(((-4600371631753607686857975701580566295359503/568867234797348938560000000000000000000000000):ℚ):ℝ) := by
      norm_num [lossRate,eps,theta2,b]
    rw [he]
    exact decayPoint
  have hp := globalPhi_from_anchor ha hx hU hv
  have hh : (FiniteChains.Chain055.costBound:ℝ)≤C*(1-(((994410270054452697810583/1000000000000000000000000):ℚ):ℝ)*(((2979547974693611958347/40000000000000000000000):ℚ):ℝ)) := by
    norm_num [FiniteChains.Chain055.costBound,C]
  exact hh.trans (mul_le_mul_of_nonneg_left hp (by norm_num [C]))

theorem graph_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (horder : (Fintype.card V:ℝ)≤(2:ℝ)^((((14032658476071347479882493/116779687257754820648000):ℚ):ℝ)))
    (hlower : (((27921325795703254143697493/233559374515509641296000):ℚ):ℝ)≤logb 2 (Fintype.card V))
    : ∃ P : Cycle13.CyclePacking G,
      P.weight≤C*orderPotential (Fintype.card V)*Fintype.card V := by
  have hn : (Fintype.card V:ℝ)≤(2:ℝ)^((((30041/250):ℚ):ℝ)) :=
    horder.trans (rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  have hp := FiniteAverageBounds.cutoff055 G (simple_graph_degree_cap G hn)
  exact potential_weight_from_fee G fee_bound hlower hp

end
end Cycle12.Global12.FinitePayment13
