import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch004
import Cycle12.CertifiedGlobalFailures.Batch004
import Cycle12.CutFailureCertificates.Budget008
import Cycle12.CutFailureCertificates.Budget009
import Cycle12.DegreeCertificates.Batch004
import Cycle12.GeometryCertificates.Batch008
import Cycle12.GeometryCertificates.Batch009
import Cycle12.MomentCertificates.Batch004
import Cycle12.WitnessCertificates.Batch008
import Cycle12.WitnessCertificates.Batch009

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch004
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate80 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate80,DegreeCertificates.Batch004.certificate80,(WitnessCertificates.Batch008.certificate160).beta,(WitnessCertificates.Batch008.certificate161).L,none,(CutFailureCertificates.Budget008.certificate160).bound,(CutFailureCertificates.Budget008.certificate161).bound,0⟩
theorem numericValid80 : certificate80.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound80 : certificate80.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch008.certificate160 H MomentCertificates.Batch004.valid80.1 GeometryCertificates.Batch008.valid160 GeometryCertificates.Batch008.sound160 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch008.certificate161 H MomentCertificates.Batch004.valid80.1 GeometryCertificates.Batch008.valid161 GeometryCertificates.Batch008.sound161 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound80 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound80 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate80 GeometryCertificates.Batch008.certificate160 numericValid80
    MomentCertificates.Batch004.valid80 DegreeCertificates.Batch004.valid80 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate80,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate81 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate81,DegreeCertificates.Batch004.certificate81,(WitnessCertificates.Batch008.certificate162).beta,(WitnessCertificates.Batch008.certificate163).L,none,(CutFailureCertificates.Budget008.certificate162).bound,(CutFailureCertificates.Budget008.certificate163).bound,0⟩
theorem numericValid81 : certificate81.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound81 : certificate81.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch008.certificate162 H MomentCertificates.Batch004.valid81.1 GeometryCertificates.Batch008.valid162 GeometryCertificates.Batch008.sound162 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch008.certificate163 H MomentCertificates.Batch004.valid81.1 GeometryCertificates.Batch008.valid163 GeometryCertificates.Batch008.sound163 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound81 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound81 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate81 GeometryCertificates.Batch008.certificate162 numericValid81
    MomentCertificates.Batch004.valid81 DegreeCertificates.Batch004.valid81 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate81,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate82 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate82,DegreeCertificates.Batch004.certificate82,(WitnessCertificates.Batch008.certificate164).beta,(WitnessCertificates.Batch008.certificate165).L,none,(CutFailureCertificates.Budget008.certificate164).bound,(CutFailureCertificates.Budget008.certificate165).bound,0⟩
theorem numericValid82 : certificate82.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound82 : certificate82.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch008.certificate164 H MomentCertificates.Batch004.valid82.1 GeometryCertificates.Batch008.valid164 GeometryCertificates.Batch008.sound164 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch008.certificate165 H MomentCertificates.Batch004.valid82.1 GeometryCertificates.Batch008.valid165 GeometryCertificates.Batch008.sound165 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound82 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound82 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate82 GeometryCertificates.Batch008.certificate164 numericValid82
    MomentCertificates.Batch004.valid82 DegreeCertificates.Batch004.valid82 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate82,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate83 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate83,DegreeCertificates.Batch004.certificate83,(WitnessCertificates.Batch008.certificate166).beta,(WitnessCertificates.Batch008.certificate167).L,none,(CutFailureCertificates.Budget008.certificate166).bound,(CutFailureCertificates.Budget008.certificate167).bound,0⟩
theorem numericValid83 : certificate83.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound83 : certificate83.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch008.certificate166 H MomentCertificates.Batch004.valid83.1 GeometryCertificates.Batch008.valid166 GeometryCertificates.Batch008.sound166 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch008.certificate167 H MomentCertificates.Batch004.valid83.1 GeometryCertificates.Batch008.valid167 GeometryCertificates.Batch008.sound167 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound83 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound83 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate83 GeometryCertificates.Batch008.certificate166 numericValid83
    MomentCertificates.Batch004.valid83 DegreeCertificates.Batch004.valid83 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate83,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate84 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate84,DegreeCertificates.Batch004.certificate84,(WitnessCertificates.Batch008.certificate168).beta,(WitnessCertificates.Batch008.certificate169).L,none,(CutFailureCertificates.Budget008.certificate168).bound,(CutFailureCertificates.Budget008.certificate169).bound,0⟩
theorem numericValid84 : certificate84.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound84 : certificate84.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch008.certificate168 H MomentCertificates.Batch004.valid84.1 GeometryCertificates.Batch008.valid168 GeometryCertificates.Batch008.sound168 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch008.certificate169 H MomentCertificates.Batch004.valid84.1 GeometryCertificates.Batch008.valid169 GeometryCertificates.Batch008.sound169 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound84 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound84 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate84 GeometryCertificates.Batch008.certificate168 numericValid84
    MomentCertificates.Batch004.valid84 DegreeCertificates.Batch004.valid84 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate84,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate85 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate85,DegreeCertificates.Batch004.certificate85,(WitnessCertificates.Batch008.certificate170).beta,(WitnessCertificates.Batch008.certificate171).L,none,(CutFailureCertificates.Budget008.certificate170).bound,(CutFailureCertificates.Budget008.certificate171).bound,0⟩
theorem numericValid85 : certificate85.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound85 : certificate85.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch008.certificate170 H MomentCertificates.Batch004.valid85.1 GeometryCertificates.Batch008.valid170 GeometryCertificates.Batch008.sound170 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch008.certificate171 H MomentCertificates.Batch004.valid85.1 GeometryCertificates.Batch008.valid171 GeometryCertificates.Batch008.sound171 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound85 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound85 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate85 GeometryCertificates.Batch008.certificate170 numericValid85
    MomentCertificates.Batch004.valid85 DegreeCertificates.Batch004.valid85 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate85,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate86 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate86,DegreeCertificates.Batch004.certificate86,(WitnessCertificates.Batch008.certificate172).beta,(WitnessCertificates.Batch008.certificate173).L,none,(CutFailureCertificates.Budget008.certificate172).bound,(CutFailureCertificates.Budget008.certificate173).bound,0⟩
theorem numericValid86 : certificate86.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound86 : certificate86.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch008.certificate172 H MomentCertificates.Batch004.valid86.1 GeometryCertificates.Batch008.valid172 GeometryCertificates.Batch008.sound172 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch008.certificate173 H MomentCertificates.Batch004.valid86.1 GeometryCertificates.Batch008.valid173 GeometryCertificates.Batch008.sound173 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound86 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound86 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate86 GeometryCertificates.Batch008.certificate172 numericValid86
    MomentCertificates.Batch004.valid86 DegreeCertificates.Batch004.valid86 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate86,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate87 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate87,DegreeCertificates.Batch004.certificate87,(WitnessCertificates.Batch008.certificate174).beta,(WitnessCertificates.Batch008.certificate175).L,none,(CutFailureCertificates.Budget008.certificate174).bound,(CutFailureCertificates.Budget008.certificate175).bound,0⟩
theorem numericValid87 : certificate87.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound87 : certificate87.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch008.certificate174 H MomentCertificates.Batch004.valid87.1 GeometryCertificates.Batch008.valid174 GeometryCertificates.Batch008.sound174 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch008.certificate175 H MomentCertificates.Batch004.valid87.1 GeometryCertificates.Batch008.valid175 GeometryCertificates.Batch008.sound175 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound87 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound87 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate87 GeometryCertificates.Batch008.certificate174 numericValid87
    MomentCertificates.Batch004.valid87 DegreeCertificates.Batch004.valid87 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate87,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate88 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate88,DegreeCertificates.Batch004.certificate88,(WitnessCertificates.Batch008.certificate176).beta,(WitnessCertificates.Batch008.certificate177).L,none,(CutFailureCertificates.Budget008.certificate176).bound,(CutFailureCertificates.Budget008.certificate177).bound,0⟩
theorem numericValid88 : certificate88.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound88 : certificate88.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch008.certificate176 H MomentCertificates.Batch004.valid88.1 GeometryCertificates.Batch008.valid176 GeometryCertificates.Batch008.sound176 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch008.certificate177 H MomentCertificates.Batch004.valid88.1 GeometryCertificates.Batch008.valid177 GeometryCertificates.Batch008.sound177 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound88 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound88 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate88 GeometryCertificates.Batch008.certificate176 numericValid88
    MomentCertificates.Batch004.valid88 DegreeCertificates.Batch004.valid88 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate88,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate89 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate89,DegreeCertificates.Batch004.certificate89,(WitnessCertificates.Batch008.certificate178).beta,(WitnessCertificates.Batch008.certificate179).L,none,(CutFailureCertificates.Budget008.certificate178).bound,(CutFailureCertificates.Budget008.certificate179).bound,0⟩
theorem numericValid89 : certificate89.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound89 : certificate89.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch008.certificate178 H MomentCertificates.Batch004.valid89.1 GeometryCertificates.Batch008.valid178 GeometryCertificates.Batch008.sound178 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch008.certificate179 H MomentCertificates.Batch004.valid89.1 GeometryCertificates.Batch008.valid179 GeometryCertificates.Batch008.sound179 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound89 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound89 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate89 GeometryCertificates.Batch008.certificate178 numericValid89
    MomentCertificates.Batch004.valid89 DegreeCertificates.Batch004.valid89 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate89,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate90 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate90,DegreeCertificates.Batch004.certificate90,(WitnessCertificates.Batch009.certificate180).beta,(WitnessCertificates.Batch009.certificate181).L,none,(CutFailureCertificates.Budget009.certificate180).bound,(CutFailureCertificates.Budget009.certificate181).bound,0⟩
theorem numericValid90 : certificate90.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound90 : certificate90.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch009.certificate180 H MomentCertificates.Batch004.valid90.1 GeometryCertificates.Batch009.valid180 GeometryCertificates.Batch009.sound180 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch009.certificate181 H MomentCertificates.Batch004.valid90.1 GeometryCertificates.Batch009.valid181 GeometryCertificates.Batch009.sound181 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound90 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound90 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate90 GeometryCertificates.Batch009.certificate180 numericValid90
    MomentCertificates.Batch004.valid90 DegreeCertificates.Batch004.valid90 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate90,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate91 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate91,DegreeCertificates.Batch004.certificate91,(WitnessCertificates.Batch009.certificate182).beta,(WitnessCertificates.Batch009.certificate183).L,none,(CutFailureCertificates.Budget009.certificate182).bound,(CutFailureCertificates.Budget009.certificate183).bound,0⟩
theorem numericValid91 : certificate91.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound91 : certificate91.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch009.certificate182 H MomentCertificates.Batch004.valid91.1 GeometryCertificates.Batch009.valid182 GeometryCertificates.Batch009.sound182 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch009.certificate183 H MomentCertificates.Batch004.valid91.1 GeometryCertificates.Batch009.valid183 GeometryCertificates.Batch009.sound183 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound91 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound91 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate91 GeometryCertificates.Batch009.certificate182 numericValid91
    MomentCertificates.Batch004.valid91 DegreeCertificates.Batch004.valid91 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate91,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate92 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate92,DegreeCertificates.Batch004.certificate92,(WitnessCertificates.Batch009.certificate184).beta,(WitnessCertificates.Batch009.certificate185).L,none,(CutFailureCertificates.Budget009.certificate184).bound,(CutFailureCertificates.Budget009.certificate185).bound,0⟩
theorem numericValid92 : certificate92.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound92 : certificate92.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch009.certificate184 H MomentCertificates.Batch004.valid92.1 GeometryCertificates.Batch009.valid184 GeometryCertificates.Batch009.sound184 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch009.certificate185 H MomentCertificates.Batch004.valid92.1 GeometryCertificates.Batch009.valid185 GeometryCertificates.Batch009.sound185 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound92 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound92 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate92 GeometryCertificates.Batch009.certificate184 numericValid92
    MomentCertificates.Batch004.valid92 DegreeCertificates.Batch004.valid92 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate92,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate93 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate93,DegreeCertificates.Batch004.certificate93,(WitnessCertificates.Batch009.certificate186).beta,(WitnessCertificates.Batch009.certificate187).L,none,(CutFailureCertificates.Budget009.certificate186).bound,(CutFailureCertificates.Budget009.certificate187).bound,0⟩
theorem numericValid93 : certificate93.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound93 : certificate93.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch009.certificate186 H MomentCertificates.Batch004.valid93.1 GeometryCertificates.Batch009.valid186 GeometryCertificates.Batch009.sound186 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch009.certificate187 H MomentCertificates.Batch004.valid93.1 GeometryCertificates.Batch009.valid187 GeometryCertificates.Batch009.sound187 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound93 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound93 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate93 GeometryCertificates.Batch009.certificate186 numericValid93
    MomentCertificates.Batch004.valid93 DegreeCertificates.Batch004.valid93 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate93,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate94 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate94,DegreeCertificates.Batch004.certificate94,(WitnessCertificates.Batch009.certificate188).beta,(WitnessCertificates.Batch009.certificate189).L,none,(CutFailureCertificates.Budget009.certificate188).bound,(CutFailureCertificates.Budget009.certificate189).bound,0⟩
theorem numericValid94 : certificate94.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound94 : certificate94.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch009.certificate188 H MomentCertificates.Batch004.valid94.1 GeometryCertificates.Batch009.valid188 GeometryCertificates.Batch009.sound188 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch009.certificate189 H MomentCertificates.Batch004.valid94.1 GeometryCertificates.Batch009.valid189 GeometryCertificates.Batch009.sound189 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound94 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound94 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate94 GeometryCertificates.Batch009.certificate188 numericValid94
    MomentCertificates.Batch004.valid94 DegreeCertificates.Batch004.valid94 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate94,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate95 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate95,DegreeCertificates.Batch004.certificate95,(WitnessCertificates.Batch009.certificate190).beta,(WitnessCertificates.Batch009.certificate191).L,none,(CutFailureCertificates.Budget009.certificate190).bound,(CutFailureCertificates.Budget009.certificate191).bound,0⟩
theorem numericValid95 : certificate95.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound95 : certificate95.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch009.certificate190 H MomentCertificates.Batch004.valid95.1 GeometryCertificates.Batch009.valid190 GeometryCertificates.Batch009.sound190 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch009.certificate191 H MomentCertificates.Batch004.valid95.1 GeometryCertificates.Batch009.valid191 GeometryCertificates.Batch009.sound191 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound95 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound95 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate95 GeometryCertificates.Batch009.certificate190 numericValid95
    MomentCertificates.Batch004.valid95 DegreeCertificates.Batch004.valid95 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate95,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate96 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate96,DegreeCertificates.Batch004.certificate96,(WitnessCertificates.Batch009.certificate192).beta,(WitnessCertificates.Batch009.certificate193).L,none,(CutFailureCertificates.Budget009.certificate192).bound,(CutFailureCertificates.Budget009.certificate193).bound,0⟩
theorem numericValid96 : certificate96.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound96 : certificate96.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch009.certificate192 H MomentCertificates.Batch004.valid96.1 GeometryCertificates.Batch009.valid192 GeometryCertificates.Batch009.sound192 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch009.certificate193 H MomentCertificates.Batch004.valid96.1 GeometryCertificates.Batch009.valid193 GeometryCertificates.Batch009.sound193 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound96 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound96 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate96 GeometryCertificates.Batch009.certificate192 numericValid96
    MomentCertificates.Batch004.valid96 DegreeCertificates.Batch004.valid96 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate96,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate97 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate97,DegreeCertificates.Batch004.certificate97,(WitnessCertificates.Batch009.certificate194).beta,(WitnessCertificates.Batch009.certificate195).L,none,(CutFailureCertificates.Budget009.certificate194).bound,(CutFailureCertificates.Budget009.certificate195).bound,0⟩
theorem numericValid97 : certificate97.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound97 : certificate97.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch009.certificate194 H MomentCertificates.Batch004.valid97.1 GeometryCertificates.Batch009.valid194 GeometryCertificates.Batch009.sound194 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch009.certificate195 H MomentCertificates.Batch004.valid97.1 GeometryCertificates.Batch009.valid195 GeometryCertificates.Batch009.sound195 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound97 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound97 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate97 GeometryCertificates.Batch009.certificate194 numericValid97
    MomentCertificates.Batch004.valid97 DegreeCertificates.Batch004.valid97 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate97,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate98 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate98,DegreeCertificates.Batch004.certificate98,(WitnessCertificates.Batch009.certificate196).beta,(WitnessCertificates.Batch009.certificate197).L,none,(CutFailureCertificates.Budget009.certificate196).bound,(CutFailureCertificates.Budget009.certificate197).bound,0⟩
theorem numericValid98 : certificate98.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound98 : certificate98.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch009.certificate196 H MomentCertificates.Batch004.valid98.1 GeometryCertificates.Batch009.valid196 GeometryCertificates.Batch009.sound196 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch009.certificate197 H MomentCertificates.Batch004.valid98.1 GeometryCertificates.Batch009.valid197 GeometryCertificates.Batch009.sound197 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound98 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound98 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate98 GeometryCertificates.Batch009.certificate196 numericValid98
    MomentCertificates.Batch004.valid98 DegreeCertificates.Batch004.valid98 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate98,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate99 : RatSamplerCase := ⟨MomentCertificates.Batch004.certificate99,DegreeCertificates.Batch004.certificate99,(WitnessCertificates.Batch009.certificate198).beta,(WitnessCertificates.Batch009.certificate199).L,none,(CutFailureCertificates.Budget009.certificate198).bound,(CutFailureCertificates.Budget009.certificate199).bound,0⟩
theorem numericValid99 : certificate99.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound99 : certificate99.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch009.certificate198 H MomentCertificates.Batch004.valid99.1 GeometryCertificates.Batch009.valid198 GeometryCertificates.Batch009.sound198 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch009.certificate199 H MomentCertificates.Batch004.valid99.1 GeometryCertificates.Batch009.valid199 GeometryCertificates.Batch009.sound199 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch004.probabilityBound99 H st hI
  have hanchor := CertifiedAnchorFailures.Batch004.probabilityBound99 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate99 GeometryCertificates.Batch009.certificate198 numericValid99
    MomentCertificates.Batch004.valid99 DegreeCertificates.Batch004.valid99 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate99,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate80,certificate81,certificate82,certificate83,certificate84,certificate85,certificate86,certificate87,certificate88,certificate89,certificate90,certificate91,certificate92,certificate93,certificate94,certificate95,certificate96,certificate97,certificate98,certificate99]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound80,List.forall_mem_cons.mpr ⟨sound81,List.forall_mem_cons.mpr ⟨sound82,List.forall_mem_cons.mpr ⟨sound83,List.forall_mem_cons.mpr ⟨sound84,List.forall_mem_cons.mpr ⟨sound85,List.forall_mem_cons.mpr ⟨sound86,List.forall_mem_cons.mpr ⟨sound87,List.forall_mem_cons.mpr ⟨sound88,List.forall_mem_cons.mpr ⟨sound89,List.forall_mem_cons.mpr ⟨sound90,List.forall_mem_cons.mpr ⟨sound91,List.forall_mem_cons.mpr ⟨sound92,List.forall_mem_cons.mpr ⟨sound93,List.forall_mem_cons.mpr ⟨sound94,List.forall_mem_cons.mpr ⟨sound95,List.forall_mem_cons.mpr ⟨sound96,List.forall_mem_cons.mpr ⟨sound97,List.forall_mem_cons.mpr ⟨sound98,List.forall_mem_cons.mpr ⟨sound99,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch004
