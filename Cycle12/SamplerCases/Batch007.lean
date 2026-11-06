import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch007
import Cycle12.CertifiedGlobalFailures.Batch007
import Cycle12.CutFailureCertificates.Budget014
import Cycle12.CutFailureCertificates.Budget015
import Cycle12.DegreeCertificates.Batch007
import Cycle12.GeometryCertificates.Batch014
import Cycle12.GeometryCertificates.Batch015
import Cycle12.MomentCertificates.Batch007
import Cycle12.WitnessCertificates.Batch014
import Cycle12.WitnessCertificates.Batch015

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch007
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate140 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate140,DegreeCertificates.Batch007.certificate140,(WitnessCertificates.Batch014.certificate280).beta,(WitnessCertificates.Batch014.certificate281).L,none,(CutFailureCertificates.Budget014.certificate280).bound,(CutFailureCertificates.Budget014.certificate281).bound,0⟩
theorem numericValid140 : certificate140.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound140 : certificate140.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch014.certificate280 H MomentCertificates.Batch007.valid140.1 GeometryCertificates.Batch014.valid280 GeometryCertificates.Batch014.sound280 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch014.certificate281 H MomentCertificates.Batch007.valid140.1 GeometryCertificates.Batch014.valid281 GeometryCertificates.Batch014.sound281 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound140 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound140 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate140 GeometryCertificates.Batch014.certificate280 numericValid140
    MomentCertificates.Batch007.valid140 DegreeCertificates.Batch007.valid140 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate140,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate141 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate141,DegreeCertificates.Batch007.certificate141,(WitnessCertificates.Batch014.certificate282).beta,(WitnessCertificates.Batch014.certificate283).L,none,(CutFailureCertificates.Budget014.certificate282).bound,(CutFailureCertificates.Budget014.certificate283).bound,0⟩
theorem numericValid141 : certificate141.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound141 : certificate141.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch014.certificate282 H MomentCertificates.Batch007.valid141.1 GeometryCertificates.Batch014.valid282 GeometryCertificates.Batch014.sound282 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch014.certificate283 H MomentCertificates.Batch007.valid141.1 GeometryCertificates.Batch014.valid283 GeometryCertificates.Batch014.sound283 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound141 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound141 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate141 GeometryCertificates.Batch014.certificate282 numericValid141
    MomentCertificates.Batch007.valid141 DegreeCertificates.Batch007.valid141 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate141,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate142 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate142,DegreeCertificates.Batch007.certificate142,(WitnessCertificates.Batch014.certificate284).beta,(WitnessCertificates.Batch014.certificate285).L,none,(CutFailureCertificates.Budget014.certificate284).bound,(CutFailureCertificates.Budget014.certificate285).bound,0⟩
theorem numericValid142 : certificate142.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound142 : certificate142.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch014.certificate284 H MomentCertificates.Batch007.valid142.1 GeometryCertificates.Batch014.valid284 GeometryCertificates.Batch014.sound284 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch014.certificate285 H MomentCertificates.Batch007.valid142.1 GeometryCertificates.Batch014.valid285 GeometryCertificates.Batch014.sound285 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound142 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound142 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate142 GeometryCertificates.Batch014.certificate284 numericValid142
    MomentCertificates.Batch007.valid142 DegreeCertificates.Batch007.valid142 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate142,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate143 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate143,DegreeCertificates.Batch007.certificate143,(WitnessCertificates.Batch014.certificate286).beta,(WitnessCertificates.Batch014.certificate287).L,none,(CutFailureCertificates.Budget014.certificate286).bound,(CutFailureCertificates.Budget014.certificate287).bound,0⟩
theorem numericValid143 : certificate143.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound143 : certificate143.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch014.certificate286 H MomentCertificates.Batch007.valid143.1 GeometryCertificates.Batch014.valid286 GeometryCertificates.Batch014.sound286 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch014.certificate287 H MomentCertificates.Batch007.valid143.1 GeometryCertificates.Batch014.valid287 GeometryCertificates.Batch014.sound287 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound143 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound143 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate143 GeometryCertificates.Batch014.certificate286 numericValid143
    MomentCertificates.Batch007.valid143 DegreeCertificates.Batch007.valid143 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate143,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate144 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate144,DegreeCertificates.Batch007.certificate144,(WitnessCertificates.Batch014.certificate288).beta,(WitnessCertificates.Batch014.certificate289).L,none,(CutFailureCertificates.Budget014.certificate288).bound,(CutFailureCertificates.Budget014.certificate289).bound,0⟩
theorem numericValid144 : certificate144.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound144 : certificate144.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch014.certificate288 H MomentCertificates.Batch007.valid144.1 GeometryCertificates.Batch014.valid288 GeometryCertificates.Batch014.sound288 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch014.certificate289 H MomentCertificates.Batch007.valid144.1 GeometryCertificates.Batch014.valid289 GeometryCertificates.Batch014.sound289 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound144 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound144 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate144 GeometryCertificates.Batch014.certificate288 numericValid144
    MomentCertificates.Batch007.valid144 DegreeCertificates.Batch007.valid144 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate144,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate145 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate145,DegreeCertificates.Batch007.certificate145,(WitnessCertificates.Batch014.certificate290).beta,(WitnessCertificates.Batch014.certificate291).L,none,(CutFailureCertificates.Budget014.certificate290).bound,(CutFailureCertificates.Budget014.certificate291).bound,0⟩
theorem numericValid145 : certificate145.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound145 : certificate145.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch014.certificate290 H MomentCertificates.Batch007.valid145.1 GeometryCertificates.Batch014.valid290 GeometryCertificates.Batch014.sound290 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch014.certificate291 H MomentCertificates.Batch007.valid145.1 GeometryCertificates.Batch014.valid291 GeometryCertificates.Batch014.sound291 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound145 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound145 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate145 GeometryCertificates.Batch014.certificate290 numericValid145
    MomentCertificates.Batch007.valid145 DegreeCertificates.Batch007.valid145 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate145,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate146 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate146,DegreeCertificates.Batch007.certificate146,(WitnessCertificates.Batch014.certificate292).beta,(WitnessCertificates.Batch014.certificate293).L,none,(CutFailureCertificates.Budget014.certificate292).bound,(CutFailureCertificates.Budget014.certificate293).bound,0⟩
theorem numericValid146 : certificate146.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound146 : certificate146.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch014.certificate292 H MomentCertificates.Batch007.valid146.1 GeometryCertificates.Batch014.valid292 GeometryCertificates.Batch014.sound292 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch014.certificate293 H MomentCertificates.Batch007.valid146.1 GeometryCertificates.Batch014.valid293 GeometryCertificates.Batch014.sound293 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound146 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound146 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate146 GeometryCertificates.Batch014.certificate292 numericValid146
    MomentCertificates.Batch007.valid146 DegreeCertificates.Batch007.valid146 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate146,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate147 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate147,DegreeCertificates.Batch007.certificate147,(WitnessCertificates.Batch014.certificate294).beta,(WitnessCertificates.Batch014.certificate295).L,none,(CutFailureCertificates.Budget014.certificate294).bound,(CutFailureCertificates.Budget014.certificate295).bound,0⟩
theorem numericValid147 : certificate147.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound147 : certificate147.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch014.certificate294 H MomentCertificates.Batch007.valid147.1 GeometryCertificates.Batch014.valid294 GeometryCertificates.Batch014.sound294 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch014.certificate295 H MomentCertificates.Batch007.valid147.1 GeometryCertificates.Batch014.valid295 GeometryCertificates.Batch014.sound295 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound147 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound147 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate147 GeometryCertificates.Batch014.certificate294 numericValid147
    MomentCertificates.Batch007.valid147 DegreeCertificates.Batch007.valid147 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate147,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate148 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate148,DegreeCertificates.Batch007.certificate148,(WitnessCertificates.Batch014.certificate296).beta,(WitnessCertificates.Batch014.certificate297).L,none,(CutFailureCertificates.Budget014.certificate296).bound,(CutFailureCertificates.Budget014.certificate297).bound,0⟩
theorem numericValid148 : certificate148.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound148 : certificate148.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch014.certificate296 H MomentCertificates.Batch007.valid148.1 GeometryCertificates.Batch014.valid296 GeometryCertificates.Batch014.sound296 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch014.certificate297 H MomentCertificates.Batch007.valid148.1 GeometryCertificates.Batch014.valid297 GeometryCertificates.Batch014.sound297 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound148 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound148 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate148 GeometryCertificates.Batch014.certificate296 numericValid148
    MomentCertificates.Batch007.valid148 DegreeCertificates.Batch007.valid148 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate148,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate149 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate149,DegreeCertificates.Batch007.certificate149,(WitnessCertificates.Batch014.certificate298).beta,(WitnessCertificates.Batch014.certificate299).L,none,(CutFailureCertificates.Budget014.certificate298).bound,(CutFailureCertificates.Budget014.certificate299).bound,0⟩
theorem numericValid149 : certificate149.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound149 : certificate149.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch014.certificate298 H MomentCertificates.Batch007.valid149.1 GeometryCertificates.Batch014.valid298 GeometryCertificates.Batch014.sound298 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch014.certificate299 H MomentCertificates.Batch007.valid149.1 GeometryCertificates.Batch014.valid299 GeometryCertificates.Batch014.sound299 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound149 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound149 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate149 GeometryCertificates.Batch014.certificate298 numericValid149
    MomentCertificates.Batch007.valid149 DegreeCertificates.Batch007.valid149 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate149,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate150 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate150,DegreeCertificates.Batch007.certificate150,(WitnessCertificates.Batch015.certificate300).beta,(WitnessCertificates.Batch015.certificate301).L,none,(CutFailureCertificates.Budget015.certificate300).bound,(CutFailureCertificates.Budget015.certificate301).bound,0⟩
theorem numericValid150 : certificate150.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound150 : certificate150.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch015.certificate300 H MomentCertificates.Batch007.valid150.1 GeometryCertificates.Batch015.valid300 GeometryCertificates.Batch015.sound300 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch015.certificate301 H MomentCertificates.Batch007.valid150.1 GeometryCertificates.Batch015.valid301 GeometryCertificates.Batch015.sound301 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound150 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound150 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate150 GeometryCertificates.Batch015.certificate300 numericValid150
    MomentCertificates.Batch007.valid150 DegreeCertificates.Batch007.valid150 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate150,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate151 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate151,DegreeCertificates.Batch007.certificate151,(WitnessCertificates.Batch015.certificate302).beta,(WitnessCertificates.Batch015.certificate303).L,none,(CutFailureCertificates.Budget015.certificate302).bound,(CutFailureCertificates.Budget015.certificate303).bound,0⟩
theorem numericValid151 : certificate151.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound151 : certificate151.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch015.certificate302 H MomentCertificates.Batch007.valid151.1 GeometryCertificates.Batch015.valid302 GeometryCertificates.Batch015.sound302 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch015.certificate303 H MomentCertificates.Batch007.valid151.1 GeometryCertificates.Batch015.valid303 GeometryCertificates.Batch015.sound303 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound151 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound151 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate151 GeometryCertificates.Batch015.certificate302 numericValid151
    MomentCertificates.Batch007.valid151 DegreeCertificates.Batch007.valid151 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate151,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate152 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate152,DegreeCertificates.Batch007.certificate152,(WitnessCertificates.Batch015.certificate304).beta,(WitnessCertificates.Batch015.certificate305).L,none,(CutFailureCertificates.Budget015.certificate304).bound,(CutFailureCertificates.Budget015.certificate305).bound,0⟩
theorem numericValid152 : certificate152.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound152 : certificate152.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch015.certificate304 H MomentCertificates.Batch007.valid152.1 GeometryCertificates.Batch015.valid304 GeometryCertificates.Batch015.sound304 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch015.certificate305 H MomentCertificates.Batch007.valid152.1 GeometryCertificates.Batch015.valid305 GeometryCertificates.Batch015.sound305 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound152 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound152 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate152 GeometryCertificates.Batch015.certificate304 numericValid152
    MomentCertificates.Batch007.valid152 DegreeCertificates.Batch007.valid152 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate152,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate153 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate153,DegreeCertificates.Batch007.certificate153,(WitnessCertificates.Batch015.certificate306).beta,(WitnessCertificates.Batch015.certificate307).L,none,(CutFailureCertificates.Budget015.certificate306).bound,(CutFailureCertificates.Budget015.certificate307).bound,0⟩
theorem numericValid153 : certificate153.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound153 : certificate153.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch015.certificate306 H MomentCertificates.Batch007.valid153.1 GeometryCertificates.Batch015.valid306 GeometryCertificates.Batch015.sound306 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch015.certificate307 H MomentCertificates.Batch007.valid153.1 GeometryCertificates.Batch015.valid307 GeometryCertificates.Batch015.sound307 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound153 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound153 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate153 GeometryCertificates.Batch015.certificate306 numericValid153
    MomentCertificates.Batch007.valid153 DegreeCertificates.Batch007.valid153 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate153,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate154 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate154,DegreeCertificates.Batch007.certificate154,(WitnessCertificates.Batch015.certificate308).beta,(WitnessCertificates.Batch015.certificate309).L,none,(CutFailureCertificates.Budget015.certificate308).bound,(CutFailureCertificates.Budget015.certificate309).bound,0⟩
theorem numericValid154 : certificate154.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound154 : certificate154.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch015.certificate308 H MomentCertificates.Batch007.valid154.1 GeometryCertificates.Batch015.valid308 GeometryCertificates.Batch015.sound308 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch015.certificate309 H MomentCertificates.Batch007.valid154.1 GeometryCertificates.Batch015.valid309 GeometryCertificates.Batch015.sound309 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound154 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound154 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate154 GeometryCertificates.Batch015.certificate308 numericValid154
    MomentCertificates.Batch007.valid154 DegreeCertificates.Batch007.valid154 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate154,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate155 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate155,DegreeCertificates.Batch007.certificate155,(WitnessCertificates.Batch015.certificate310).beta,(WitnessCertificates.Batch015.certificate311).L,none,(CutFailureCertificates.Budget015.certificate310).bound,(CutFailureCertificates.Budget015.certificate311).bound,0⟩
theorem numericValid155 : certificate155.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound155 : certificate155.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch015.certificate310 H MomentCertificates.Batch007.valid155.1 GeometryCertificates.Batch015.valid310 GeometryCertificates.Batch015.sound310 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch015.certificate311 H MomentCertificates.Batch007.valid155.1 GeometryCertificates.Batch015.valid311 GeometryCertificates.Batch015.sound311 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound155 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound155 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate155 GeometryCertificates.Batch015.certificate310 numericValid155
    MomentCertificates.Batch007.valid155 DegreeCertificates.Batch007.valid155 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate155,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate156 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate156,DegreeCertificates.Batch007.certificate156,(WitnessCertificates.Batch015.certificate312).beta,(WitnessCertificates.Batch015.certificate313).L,none,(CutFailureCertificates.Budget015.certificate312).bound,(CutFailureCertificates.Budget015.certificate313).bound,0⟩
theorem numericValid156 : certificate156.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound156 : certificate156.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch015.certificate312 H MomentCertificates.Batch007.valid156.1 GeometryCertificates.Batch015.valid312 GeometryCertificates.Batch015.sound312 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch015.certificate313 H MomentCertificates.Batch007.valid156.1 GeometryCertificates.Batch015.valid313 GeometryCertificates.Batch015.sound313 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound156 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound156 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate156 GeometryCertificates.Batch015.certificate312 numericValid156
    MomentCertificates.Batch007.valid156 DegreeCertificates.Batch007.valid156 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate156,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate157 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate157,DegreeCertificates.Batch007.certificate157,(WitnessCertificates.Batch015.certificate314).beta,(WitnessCertificates.Batch015.certificate315).L,none,(CutFailureCertificates.Budget015.certificate314).bound,(CutFailureCertificates.Budget015.certificate315).bound,0⟩
theorem numericValid157 : certificate157.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound157 : certificate157.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch015.certificate314 H MomentCertificates.Batch007.valid157.1 GeometryCertificates.Batch015.valid314 GeometryCertificates.Batch015.sound314 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch015.certificate315 H MomentCertificates.Batch007.valid157.1 GeometryCertificates.Batch015.valid315 GeometryCertificates.Batch015.sound315 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound157 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound157 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate157 GeometryCertificates.Batch015.certificate314 numericValid157
    MomentCertificates.Batch007.valid157 DegreeCertificates.Batch007.valid157 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate157,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate158 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate158,DegreeCertificates.Batch007.certificate158,(WitnessCertificates.Batch015.certificate316).beta,(WitnessCertificates.Batch015.certificate317).L,none,(CutFailureCertificates.Budget015.certificate316).bound,(CutFailureCertificates.Budget015.certificate317).bound,0⟩
theorem numericValid158 : certificate158.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound158 : certificate158.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch015.certificate316 H MomentCertificates.Batch007.valid158.1 GeometryCertificates.Batch015.valid316 GeometryCertificates.Batch015.sound316 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch015.certificate317 H MomentCertificates.Batch007.valid158.1 GeometryCertificates.Batch015.valid317 GeometryCertificates.Batch015.sound317 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound158 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound158 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate158 GeometryCertificates.Batch015.certificate316 numericValid158
    MomentCertificates.Batch007.valid158 DegreeCertificates.Batch007.valid158 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate158,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate159 : RatSamplerCase := ⟨MomentCertificates.Batch007.certificate159,DegreeCertificates.Batch007.certificate159,(WitnessCertificates.Batch015.certificate318).beta,(WitnessCertificates.Batch015.certificate319).L,none,(CutFailureCertificates.Budget015.certificate318).bound,(CutFailureCertificates.Budget015.certificate319).bound,0⟩
theorem numericValid159 : certificate159.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound159 : certificate159.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch015.certificate318 H MomentCertificates.Batch007.valid159.1 GeometryCertificates.Batch015.valid318 GeometryCertificates.Batch015.sound318 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch015.certificate319 H MomentCertificates.Batch007.valid159.1 GeometryCertificates.Batch015.valid319 GeometryCertificates.Batch015.sound319 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch007.probabilityBound159 H st hI
  have hanchor := CertifiedAnchorFailures.Batch007.probabilityBound159 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate159 GeometryCertificates.Batch015.certificate318 numericValid159
    MomentCertificates.Batch007.valid159 DegreeCertificates.Batch007.valid159 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate159,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate140,certificate141,certificate142,certificate143,certificate144,certificate145,certificate146,certificate147,certificate148,certificate149,certificate150,certificate151,certificate152,certificate153,certificate154,certificate155,certificate156,certificate157,certificate158,certificate159]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound140,List.forall_mem_cons.mpr ⟨sound141,List.forall_mem_cons.mpr ⟨sound142,List.forall_mem_cons.mpr ⟨sound143,List.forall_mem_cons.mpr ⟨sound144,List.forall_mem_cons.mpr ⟨sound145,List.forall_mem_cons.mpr ⟨sound146,List.forall_mem_cons.mpr ⟨sound147,List.forall_mem_cons.mpr ⟨sound148,List.forall_mem_cons.mpr ⟨sound149,List.forall_mem_cons.mpr ⟨sound150,List.forall_mem_cons.mpr ⟨sound151,List.forall_mem_cons.mpr ⟨sound152,List.forall_mem_cons.mpr ⟨sound153,List.forall_mem_cons.mpr ⟨sound154,List.forall_mem_cons.mpr ⟨sound155,List.forall_mem_cons.mpr ⟨sound156,List.forall_mem_cons.mpr ⟨sound157,List.forall_mem_cons.mpr ⟨sound158,List.forall_mem_cons.mpr ⟨sound159,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch007
