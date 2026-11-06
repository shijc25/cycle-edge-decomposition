import Cycle12.DirectBankParameters
import Cycle12.DirectEdgeSplit
import Cycle12.DirectCycleClosure
import Cycle12.Foundations.SampleGraphBounds

namespace Cycle12
open Real Finset SimpleGraph Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Every retained-cut and capacity condition is realized by an actual edge split
and actual simultaneous paths in the sampled graph. -/
theorem direct_cycles_from_sample (c : DirectBankParameters) (hc : c.Valid)
    (G : SimpleGraph V) (U : Finset V) {x s P incidentUpper edgeLower : ℝ}
    (hx : 0 < x) (hxl : c.sample.xl ≤ x) (hxh : x ≤ c.sample.xh)
    (hs : c.sample.s0 ≤ s) (hPl : c.sample.Plo ≤ P) (hPu : P ≤ c.sample.Pu)
    (hn : (Fintype.card V:ℝ)=4*(43/10)^3*s^2/(coverScaleW x)^3)
    (horder : (U.card:ℝ)=coverRoutingOrder x s P)
    (hhalf : P*coverScaleW x < 1/2)
    (hU : GoodVertexSample G U (c.dm*coverScaleZ x s P) (c.beta*coverScaleZ x s P) c.L
      U.card U.card edgeLower incidentUpper) :
    ∃ C : CyclePacking G, 2*C.count ≤ Fintype.card V-U.card ∧
      C.singles ≤ incidentEdgeCount G U+(Fintype.card V-U.card) := by
  classical
  have hs0 : 0 < c.sample.s0 := by linarith only [hc.sampling.density_lower]
  have hsp := hs0.trans_le hs
  have hP0 := hc.sampling.ratio_positive.trans_le hPl
  have hxm := hxh.trans hc.sampling.xmax
  have hw := cover_w_pos hx
  have hp := mul_pos hP0 hw
  have hz := cover_scale_interval_lower hc.sampling.xl_nonneg hxl hx hxh hc.sampling.xmax
    hs0 hs hc.sampling.ratio_positive.le hPl
  have hzlo : c.zLower ≤ coverScaleZ x s P := hc.z_lower.trans hz.2.1
  have hzpos : 0 < coverScaleZ x s P := by
    unfold coverScaleZ
    positivity [cover_h_pos hx.le,cover_den_pos hx.le hxm]
  have hβ : 1 ≤ c.beta*coverScaleZ x s P := hc.mincut.trans
    (mul_le_mul_of_nonneg_left hzlo hc.beta_pos.le)
  have horderlo : c.sample.Nlo ≤ (U.card:ℝ) := by
    rw [horder]
    apply hc.sampling.sample_lower.trans
    unfold coverRoutingOrder
    have hwle := cover_w_mono hx.le hxh
    have hPhi := hc.sampling.ratio_positive.le
    gcongr
  have hN2 : 2 ≤ U.card := by exact_mod_cast hc.sample_two.trans horderlo
  have hNR : (0:ℝ) < U.card := by exact_mod_cast (show 0 < U.card by omega)
  have hpn : (P*coverScaleW x)*(Fintype.card V:ℝ)=(U.card:ℝ) := by
    rw [horder]
    exact cover_routing_sample_identity hx hn
  have hnpos : (0:ℝ) < Fintype.card V := by rw [hn]; positivity
  have hhalfN : 2*U.card ≤ Fintype.card V := by
    have hh := mul_le_mul_of_nonneg_right hhalf.le hnpos.le
    have hh' : 2*(U.card:ℝ) ≤ Fintype.card V := by nlinarith only [hh,hpn]
    exact_mod_cast hh'
  let k := directOutsideCapacity (Fintype.card V) U.card
  obtain ⟨hk0,hkcap,hkbound⟩ := direct_outside_capacity_bounds (show 0 < U.card by omega) hhalfN
  have hk : (k:ℝ) ≤ 1/(P*coverScaleW x) := by
    have he : (Fintype.card V:ℝ)/(U.card:ℝ)=1/(P*coverScaleW x) := by
      apply (div_eq_div_iff hNR.ne' hp.ne').mpr
      nlinarith only [hpn]
    exact hkbound.trans_eq he
  have hW := hc.weight_lower.trans hz.2.2.2
  have hWrel := (cover_scale_relations (P:=P) hx hxm hsp hn).2.1
  have hfw : 1 ≤ c.fan*c.beta*((P*coverScaleW x)*coverScaleZ x s P) := by
    have hh := hc.source_capacity.trans
      (mul_le_mul_of_nonneg_left hW (mul_nonneg hc.fan_pos.le hc.beta_pos.le))
    simpa only [← hWrel,mul_comm (coverScaleW x) P] using hh
  have hkbeta : (k:ℝ) ≤ c.fan*(c.beta*coverScaleZ x s P) := by
    apply hk.trans
    apply (div_le_iff₀ hp).mpr
    nlinarith only [hfw]
  have hr := hc.r_lower.trans hz.1
  have hratio : 4096 ≤ (U.card:ℝ)/((c.router*c.beta)*coverScaleZ x s P) := by
    rw [horder,cover_direct_ratio (mul_pos hc.router_pos hc.beta_pos) hx hxm hsp hP0]
    exact hc.ratio.trans (div_le_div_of_nonneg_right hr (mul_nonneg hc.router_pos.le hc.beta_pos.le))
  have hcub := hc.routing_capacity.trans (cover_direct_cubic_lower
    (mul_nonneg hc.router_pos.le hc.beta_pos.le) hc.sampling.xl_nonneg hxl hxm
    hs0.le hs hc.sampling.ratio_positive.le hPl)
  have hcube := cover_direct_cubic_capacity (c:=(k:ℝ)) (Nat.cast_nonneg _)
    (mul_pos hc.router_pos hc.beta_pos) hx hxm hsp hP0 hk hcub
  rw [← horder] at hcube
  have hcut := cover_bank_cut_tail (N:=U.card) (by omega) hc.sampling.xl_nonneg hxl hx hxh
    hc.sampling.xmax hs0 hs hc.sampling.ratio_positive hPl hPu horder hc.z_lower
    hc.dm_pos.le hc.log_upper hc.log_lower hc.gap
  let H := G.induce (U:Set V)
  let q : unitInterval := ⟨c.mean,hc.mean_pos.le,hc.mean_lt_one.le⟩
  obtain ⟨ω,hF,hJ⟩ := exists_direct_edge_split H q hc.epsilon_nonneg
    (mul_pos hc.dm_pos hzpos) (by simpa only [Fintype.card_coe,Set.fintypeCard_eq_ncard,Set.ncard_coe_finset] using hN2)
    (hU.induced_mincut G U hβ) hc.fan_le hc.router_le
    (by simpa only [Fintype.card_coe,Set.fintypeCard_eq_ncard,Set.ncard_coe_finset] using hcut.1)
    (by simpa only [Fintype.card_coe,Set.fintypeCard_eq_ncard,Set.ncard_coe_finset] using hcut.2.trans hc.cut_tail) hc.failure
  have hJexp : CutExpands (splitBank H ω false) ((c.router*c.beta)*coverScaleZ x s P) := by
    intro S hS
    have hh := (mul_le_mul_of_nonneg_left (sample_induced_expansion G U hU.cuts S hS)
      hc.router_pos.le).trans (hJ S)
    simpa only [boundaryCount_eq_legacy_cutSize,mul_assoc] using hh
  have hdis : Disjoint (splitBank H ω true).edgeSet (splitBank H ω false).edgeSet := by
    rw [splitBank_edges,splitBank_edges]
    apply Set.disjoint_left.mpr
    intro e he he'
    exact Bool.noConfusion (he.2.symm.trans he'.2)
  exact direct_cycles_from_two_banks G U hU (splitBank H ω true) (splitBank H ω false)
    (fun _ _ h => h.1) (fun _ _ h => h.1) hdis hF hJexp
    (mul_pos (mul_pos hc.router_pos hc.beta_pos) hzpos) hc.fan_pos.le
    (by linarith only [hc.fan_le,hc.epsilon_nonneg,hc.mean_lt_one]) hc.anchoring
    k hk0 hkcap hkbeta hratio hcube

end
end Cycle12
