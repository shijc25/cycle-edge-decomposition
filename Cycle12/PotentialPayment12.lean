import Cycle12.GlobalPotential12
import Cycle12.SupportedEdges
import Cycle12.Foundations.PackingExtension

namespace Cycle12.Global12
open Real
noncomputable section

theorem globalLoss_from_anchor {a x U : ℝ} (ha : b*wA≤a) (hx : a≤x)
    (hU : globalLoss a≤U) : globalLoss x≤(2:ℝ)^(-(lossRate/b)*(x-a))*U :=
  (globalLoss_decay ha hx).trans (mul_le_mul_of_nonneg_left hU (rpow_nonneg (by norm_num) _))

theorem globalPhi_from_anchor {a x U v : ℝ} (ha : b*wA≤a) (hx : a≤x)
    (hU : globalLoss a≤U) (hv : (2:ℝ)^(-(lossRate/b)*(x-a))≤v) :
    1-v*U≤globalPhi x := by
  rw [globalPhi_large (ha.trans hx)]
  have hh := (globalLoss_from_anchor ha hx hU).trans
    (mul_le_mul_of_nonneg_right hv ((globalLoss_nonneg ha).trans hU))
  linarith only [hh]

theorem simple_graph_degree_cap {V : Type} [Fintype V] (G : SimpleGraph V)
    {D : ℝ} (hD : (Fintype.card V:ℝ)≤D) :
    2*(G.edgeSet.ncard:ℝ)≤D*Fintype.card V := by
  classical
  have hh := Cycle13.MixedSample.twice_graph_edges_le_order_sq G
  simp only [Set.fintypeCard_eq_ncard] at hh
  have hm := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg (Fintype.card V))
  nlinarith only [hh,hm]

theorem potential_weight_from_fee {V : Type} [Fintype V] (G : SimpleGraph V) {f x : ℝ}
    (hfee : f≤C*globalPhi x) (hx : x≤logb 2 (Fintype.card V))
    (hpack : ∃ P : Cycle13.CyclePacking G,P.weight≤f*Fintype.card V) :
    ∃ P : Cycle13.CyclePacking G,P.weight≤C*orderPotential (Fintype.card V)*Fintype.card V := by
  obtain ⟨P,hP⟩ := hpack
  have hm := mul_le_mul_of_nonneg_left (globalPhi_monotone hx) (show 0≤C by norm_num [C])
  exact ⟨P,hP.trans (mul_le_mul_of_nonneg_right (hfee.trans hm) (Nat.cast_nonneg _))⟩

theorem potential_weight_from_floor {V : Type} [Fintype V] (G : SimpleGraph V) {f : ℝ}
    (hfee : f≤C*phi0) (hpack : ∃ P : Cycle13.CyclePacking G,P.weight≤f*Fintype.card V) :
    ∃ P : Cycle13.CyclePacking G,P.weight≤C*orderPotential (Fintype.card V)*Fintype.card V := by
  obtain ⟨P,hP⟩ := hpack
  have hm := mul_le_mul_of_nonneg_left (orderPotential_lower (Fintype.card V))
    (show 0≤C by norm_num [C])
  exact ⟨P,hP.trans (mul_le_mul_of_nonneg_right (hfee.trans hm) (Nat.cast_nonneg _))⟩

end
end Cycle12.Global12
