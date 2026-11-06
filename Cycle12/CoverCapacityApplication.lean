import Cycle12.CoverCapacityParameters

namespace Cycle12
open Real Finset SimpleGraph Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- A checked routing rectangle and its actual good sample produce actual
edge-disjoint cycles, paying every floor and integer-capacity loss. -/
theorem cover_cycles_from_sample (c : CoverCapacityParameters) (hc : c.Valid)
    (G : SimpleGraph V) (U : Finset V) {x s P incidentUpper : ℝ}
    (hx : 0 < x) (hxl : c.bank.sample.xl ≤ x) (hxh : x ≤ c.bank.sample.xh)
    (hs : c.bank.sample.s0 ≤ s) (hPl : c.bank.sample.Plo ≤ P) (hPu : P ≤ c.bank.sample.Pu)
    (hbounded : ∀ sh, c.bank.maximumScale=some sh → s ≤ sh)
    (hn : (Fintype.card V:ℝ)=coverRoutingAmbient x s)
    (horder : (U.card:ℝ)=coverRoutingOrder x s P)
    (hU : GoodVertexSample G U (c.bank.dm*coverScaleZ x s P) (c.bank.beta*coverScaleZ x s P) c.bank.L
      U.card U.card ((97/100)*(2*s*(coverRoutingQ x s P)^2)) incidentUpper)
    (hlocal : c.localCuts=true → LocalSampleCutExpansion G U (c.routeBeta*coverScaleZ x s P) (1/125)) :
    ∃ C : CyclePacking G, (C.count:ℝ) ≤ ((Fintype.card V:ℝ)-U.card)/2 ∧
      (C.singles:ℝ) ≤ incidentUpper+(Fintype.card V:ℝ)-U.card := by
  have hb := hc.bank_valid
  have hbox := hb.sampling
  have hs0 : 0 < c.bank.sample.s0 := by linarith only [hbox.density_lower]
  have hsp := hs0.trans_le hs
  have hP := hbox.ratio_positive.trans_le hPl
  have hxm := hxh.trans hbox.xmax
  have hQ := cover_routing_q_pos hx hsp hP
  have hn0 : (0:ℝ) < Fintype.card V := by rw [hn]; exact cover_routing_ambient_pos hx hsp
  have hz : 0 < coverScaleZ x s P := by
    unfold coverScaleZ
    positivity [cover_w_pos hx,cover_h_pos hx.le,cover_den_pos hx.le hxm]
  have hpUpper : P*coverScaleW x ≤ c.pUpper :=
    (mul_le_mul hPu (cover_w_mono hx.le hxh) (cover_w_nonneg x)
      (hP.le.trans hPu)).trans hc.p_upper
  have hpLower : c.bank.sample.pl ≤ P*coverScaleW x := hbox.probability_lower.trans
    (mul_le_mul hPl (cover_w_mono hbox.xl_nonneg hxl) (cover_w_nonneg _) hP.le)
  have hsample : (U.card:ℝ)=(P*coverScaleW x)*(Fintype.card V:ℝ) := by
    rw [horder,hn]
    exact (cover_routing_sample_identity hx rfl).symm
  have hsize := cover_routing_size_lower hb.coeff_positive.le hbox.xl_nonneg hx hxl hxh
    hs0 hs hbox.ratio_positive hPl hpUpper
  have hT : 24 ≤ c.bank.coeff*coverRoutingQ x s P := hc.size_lower.trans hsize
  obtain ⟨B⟩ := cover_bank_from_sample c.bank hb G U hx hxl hxh hs hPl hPu hbounded horder hT hU
  have ht := cover_bank_model_size_bounds c.bank hT
  have hK := cover_routing_k_nonneg hb.coeff_positive hb.fan_positive.le hc.route_positive.le
    hc.branch_nonneg hx.le hxm
  have hfactor := cover_routing_factor_lower hb.coeff_positive hb.fan_positive.le hc.route_positive.le
    hc.branch_nonneg hbox.xl_nonneg hx hxl hxh hbox.xmax hs0 hs hbox.ratio_positive hPl hpUpper
  have hKT : 1 ≤ coverRoutingK c.bank.coeff c.bank.fan c.routeBeta c.bank.branch x*
      (c.bank.coeff*coverRoutingQ x s P) := hc.factor_lower.trans hfactor
  have hbudget := (cover_routing_k_budget (d:=c.bank.branch) (s:=s) (P:=P)
    hb.coeff_positive hb.fan_positive.le hc.route_positive.le hx hxm).le
  have hpairbox := cover_routing_pair_box_lower hb.coeff_positive.le hbox.xl_nonneg hx hxl hxh
    hs0 hs hbox.ratio_positive hPl hpUpper
  have hfanbox := cover_routing_fan_box_lower hb.coeff_positive hb.fan_positive.le hc.route_positive.le
    hc.branch_nonneg hbox.xl_nonneg hx hxl hxh hbox.xmax hs0 hs hbox.ratio_positive hPl hpUpper
  have hpair := cover_routing_complement_payment hn0 hsample hpLower hc.pair_capacity (by rwa [hn])
  have hfan := cover_routing_complement_payment hn0 hsample hpLower hc.fan_capacity (by rwa [hn])
  have hd : 0 ≤ c.bank.branch*coverRoutingQ x s P := mul_nonneg hc.branch_nonneg hQ.le
  have hfBeta : 0 < c.bank.fan*(c.bank.beta*coverScaleZ x s P) :=
    mul_pos hb.fan_positive (mul_pos hb.beta_positive hz)
  cases he : c.localCuts with
  | false =>
    have heq := hc.global_beta he
    rw [heq] at hK hKT hbudget hfan
    exact cycles_of_global_capacity_bounds G U hU B ht.1 ht.2.1
      (by linarith only [hT]) ht.2.2.1 ht.2.2.2 hb.fan_positive.le hc.fan_upper hc.anchoring
      hfBeta hd hK hKT hbudget hpair hfan
  | true =>
    have hW := cover_scale_interval_lower hbox.xl_nonneg hxl hx hxh hbox.xmax hs0 hs
      hbox.ratio_positive.le hPl
    have hlargebox := cover_routing_large_box_lower hb.coeff_positive.le hb.fan_positive.le
      hb.beta_positive.le (by norm_num : (0:ℝ) ≤ 1/125) hx hxm hs0 hs hP hpUpper
      (hc.weight_lower.trans hW.2.2.2)
    have hlarge : (Fintype.card V:ℝ)-U.card ≤
        (c.bank.fan*(c.bank.beta*coverScaleZ x s P))*((1/125)*(U.card:ℝ))-
        c.bank.coeff*coverRoutingQ x s P := by
      have hh := cover_routing_complement_payment hn0 hsample hpLower (hc.large_capacity he)
        (by rwa [hn] : c.largeBound ≤
          ((c.bank.fan*(c.bank.beta*coverScaleZ x s P))*((1/125)*((P*coverScaleW x)*(Fintype.card V:ℝ)))-
          c.bank.coeff*coverRoutingQ x s P)/(Fintype.card V:ℝ))
      simpa only [← hsample] using hh
    exact cycles_of_local_capacity_bounds G U hU (hlocal he) B ht.1 ht.2.1
      (by linarith only [hT]) ht.2.2.1 ht.2.2.2 hb.fan_positive.le hc.fan_upper hc.anchoring
      hfBeta (mul_pos hb.fan_positive (mul_pos hc.route_positive hz))
      (by norm_num) (Nat.cast_nonneg _) hd hK hKT hbudget hpair hfan hlarge

end
end Cycle12
