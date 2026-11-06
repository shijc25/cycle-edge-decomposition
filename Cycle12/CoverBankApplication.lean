import Cycle12.CoverBankParameters

namespace Cycle12
open Real Finset SimpleGraph Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def coverBankLowerDegree {G : SimpleGraph V} {U : Finset V} {t : ℕ} {f d d' : ℝ}
    (B : SampleRoutingBank G U t f d) (h : d' ≤ d) : SampleRoutingBank G U t f d' where
  model := B.model
  cuts := B.cuts
  degrees i := h.trans (B.degrees i)

/-- A checked rectangle constructs an actual immersion and the unused-edge
routing bank. No cut-event probability premise is left to the caller. -/
theorem cover_bank_from_sample (c : CoverBankParameters) (hc : c.Valid)
    (G : SimpleGraph V) (U : Finset V) {x s P incidentUpper : ℝ}
    (hx : 0 < x) (hxl : c.sample.xl ≤ x) (hxh : x ≤ c.sample.xh)
    (hs : c.sample.s0 ≤ s) (hPl : c.sample.Plo ≤ P) (hPu : P ≤ c.sample.Pu)
    (hbounded : ∀ sh, c.maximumScale=some sh → s ≤ sh)
    (horder : (U.card:ℝ)=coverRoutingOrder x s P)
    (hT : 24 ≤ c.coeff*coverRoutingQ x s P)
    (hU : GoodVertexSample G U (c.dm*coverScaleZ x s P) (c.beta*coverScaleZ x s P) c.L
      U.card U.card ((97/100)*(2*s*(coverRoutingQ x s P)^2)) incidentUpper) :
    Nonempty (SampleRoutingBank G U (c.modelSize (c.coeff*coverRoutingQ x s P))
      c.fan (c.branch*coverRoutingQ x s P)) := by
  have hs0 : 0 < c.sample.s0 := by linarith only [hc.sampling.density_lower]
  have hsp := hs0.trans_le hs
  have hP0 := hc.sampling.ratio_positive.trans_le hPl
  have hxm := hxh.trans hc.sampling.xmax
  have hQ := cover_routing_q_pos hx hsp hP0
  have hz := cover_scale_interval_lower hc.sampling.xl_nonneg hxl hx hxh hc.sampling.xmax
    hs0 hs hc.sampling.ratio_positive.le hPl
  have hzlo : c.zLower ≤ coverScaleZ x s P := hc.z_lower.trans hz.2.1
  have hzpos : 0 < coverScaleZ x s P := by
    unfold coverScaleZ
    positivity [cover_w_pos hx,cover_h_pos hx.le,cover_den_pos hx.le hxm]
  have hβ : 1 ≤ c.beta*coverScaleZ x s P := hc.sample_mincut.trans
    (mul_le_mul_of_nonneg_left hzlo hc.beta_positive.le)
  have horderlo : c.sample.Nlo ≤ (U.card:ℝ) := by
    rw [horder]
    apply hc.sampling.sample_lower.trans
    unfold coverRoutingOrder
    have hw := cover_w_pos hx
    have hwle := cover_w_mono hx.le hxh
    have hPhi := hc.sampling.ratio_positive.le
    gcongr
  have hn2 : 2 ≤ U.card := by exact_mod_cast hc.sample_two.trans horderlo
  have hm0 : 0 < c.mean := hc.fan_positive.trans_le (hc.fan_le_degree.trans hc.degree_lt_mean.le)
  have hm1 : c.mean < 1 := by linarith only [hc.mean_lt_one]
  have hg0 := hc.fan_positive.le.trans hc.fan_le_degree
  have hg1 := hc.degree_lt_mean.trans hm1
  let q : unitInterval := ⟨c.mean,hm0.le,hm1.le⟩
  have hcut := cover_bank_cut_tail (N:=U.card) (by omega) hc.sampling.xl_nonneg hxl hx hxh
    hc.sampling.xmax hs0 hs hc.sampling.ratio_positive hPl hPu horder hc.z_lower
    hc.degree_positive.le hc.cut_log hc.cut_log_lower hc.cut_gap
  have hfail := hcut.2.trans hc.cut_tail
  have hcore := (cover_bank_core_tail hx hxh hs0 hs hc.sampling.ratio_positive.le hPl hU.edges).trans hc.core_tail
  have hbranch := (cover_bank_branch_tail hx hxh hs0 hs hc.sampling.ratio_positive hPl hPu horder
    hc.q_lower (cover_bank_dc_pos c hc).le hg1 hc.branch_scale).trans hc.branch_tail
  have hgain : c.gain-c.gain^2*c.ac/(4*s) ≤ 1 := by
    rcases hc.dense_gain with he | ⟨sh,hsh,hg⟩
    · rw [he]
      have hp : 0 ≤ c.ac/(4*s) := by positivity [cover_bank_ac_pos c hc]
      norm_num only [one_pow,one_mul]
      linarith only [hp]
    · exact (cover_bank_dense_gain_mono (cover_bank_ac_pos c hc).le hsp (hbounded sh hsh)).trans hg
  have hdense := cover_bank_dense (cover_bank_ac_pos c hc) hx hsp hP0 hgain
  have hDN := cover_bank_degree_le_order hx hs0 hs hP0 hc.dense_size
  have hE : coverBankEdges c.ac x s P ≤
      (1-c.mean-1/1000)*(sampledEdgeCount G (U:Set V):ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hU.edges
      (show 0 ≤ 1-c.mean-1/1000 by linarith only [hc.mean_lt_one])
    convert hh using 1 <;> unfold coverBankEdges CoverBankParameters.ac <;> ring
  have hdegree := cover_bank_branch_lower (dc:=c.dc) (a:=c.coeff) (cost:=c.cost)
    (g:=c.degreeFraction) hc.degree_positive.le hc.sampling.xl_nonneg hx hxl hxm hsp hP0
  have hnupper : (U.card:ℝ) ≤ coverRoutingOrder x s P := horder.le
  cases hmode : c.strong with
  | false =>
    have hTD := mul_le_mul_of_nonneg_right (hc.weak_degree hmode) hQ.le
    obtain ⟨B⟩ := exists_weak_sample_bank (T:=c.coeff*coverRoutingQ x s P)
      (D:=c.dc*coverRoutingQ x s P) (N:=coverRoutingOrder x s P) (E:=coverBankEdges c.ac x s P) G U q hU hβ (mul_pos hc.degree_positive hzpos) hn2
      (by linarith only [hT]) (by nlinarith only [hTD]) hDN hnupper hE hdense hg0 hc.degree_lt_mean
      (by norm_num : (0:ℝ) ≤ 1/1000) (hc.fan_le_degree.trans hc.degree_lt_mean.le)
      hcut.1 hfail hcore (Or.inr hbranch) hc.probability_sum
    have hh : c.branch*coverRoutingQ x s P ≤
        max ((c.dc*coverRoutingQ x s P)/(1-c.degreeFraction)) (c.dm*coverScaleZ x s P)-
          (11/10)*(c.coeff*coverRoutingQ x s P) := by
      simpa only [CoverBankParameters.branch,CoverBankParameters.cost,hmode,Bool.false_eq_true,ite_false] using hdegree
    exact ⟨by simpa only [CoverBankParameters.modelSize,hmode,Bool.false_eq_true,ite_false] using coverBankLowerDegree B hh⟩
  | true =>
    have hTD := mul_le_mul_of_nonneg_right (hc.strong_degree hmode) hQ.le
    obtain ⟨sh,hsh,hstop⟩ := hc.strong_stopping hmode
    have hstopping := cover_bank_strong_stopping hc.coeff_positive hx hsp hP0 (hbounded sh hsh) hstop
    obtain ⟨B⟩ := exists_strong_sample_bank (T:=c.coeff*coverRoutingQ x s P)
      (D:=c.dc*coverRoutingQ x s P) (N:=coverRoutingOrder x s P) (E:=coverBankEdges c.ac x s P) G U q hU hβ (mul_pos hc.degree_positive hzpos) hn2
      (by linarith only [hT]) hTD hDN hnupper hE hdense hstopping hg0 hc.degree_lt_mean
      (by norm_num : (0:ℝ) ≤ 1/1000) (hc.fan_le_degree.trans hc.degree_lt_mean.le)
      hcut.1 hfail hcore (Or.inr hbranch) hc.probability_sum
    have hh : c.branch*coverRoutingQ x s P ≤
        max ((c.dc*coverRoutingQ x s P)/(1-c.degreeFraction)) (c.dm*coverScaleZ x s P)-
          c.coeff*coverRoutingQ x s P := by
      simpa only [CoverBankParameters.branch,CoverBankParameters.cost,hmode,ite_true,one_mul] using hdegree
    exact ⟨by simpa only [CoverBankParameters.modelSize,hmode,ite_true] using coverBankLowerDegree B hh⟩

end
end Cycle12
