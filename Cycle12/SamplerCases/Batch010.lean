import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch010
import Cycle12.CertifiedGlobalFailures.Batch010
import Cycle12.CutFailureCertificates.Budget020
import Cycle12.CutFailureCertificates.Budget021
import Cycle12.DegreeCertificates.Batch010
import Cycle12.GeometryCertificates.Batch020
import Cycle12.GeometryCertificates.Batch021
import Cycle12.MomentCertificates.Batch010
import Cycle12.WitnessCertificates.Batch020
import Cycle12.WitnessCertificates.Batch021

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch010
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate200 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate200,DegreeCertificates.Batch010.certificate200,(WitnessCertificates.Batch020.certificate400).beta,(WitnessCertificates.Batch020.certificate401).L,none,(CutFailureCertificates.Budget020.certificate400).bound,(CutFailureCertificates.Budget020.certificate401).bound,0⟩
theorem numericValid200 : certificate200.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound200 : certificate200.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch020.certificate400 H MomentCertificates.Batch010.valid200.1 GeometryCertificates.Batch020.valid400 GeometryCertificates.Batch020.sound400 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch020.certificate401 H MomentCertificates.Batch010.valid200.1 GeometryCertificates.Batch020.valid401 GeometryCertificates.Batch020.sound401 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound200 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound200 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate200 GeometryCertificates.Batch020.certificate400 numericValid200
    MomentCertificates.Batch010.valid200 DegreeCertificates.Batch010.valid200 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate200,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate201 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate201,DegreeCertificates.Batch010.certificate201,(WitnessCertificates.Batch020.certificate402).beta,(WitnessCertificates.Batch020.certificate403).L,none,(CutFailureCertificates.Budget020.certificate402).bound,(CutFailureCertificates.Budget020.certificate403).bound,0⟩
theorem numericValid201 : certificate201.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound201 : certificate201.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch020.certificate402 H MomentCertificates.Batch010.valid201.1 GeometryCertificates.Batch020.valid402 GeometryCertificates.Batch020.sound402 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch020.certificate403 H MomentCertificates.Batch010.valid201.1 GeometryCertificates.Batch020.valid403 GeometryCertificates.Batch020.sound403 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound201 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound201 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate201 GeometryCertificates.Batch020.certificate402 numericValid201
    MomentCertificates.Batch010.valid201 DegreeCertificates.Batch010.valid201 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate201,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate202 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate202,DegreeCertificates.Batch010.certificate202,(WitnessCertificates.Batch020.certificate404).beta,(WitnessCertificates.Batch020.certificate405).L,none,(CutFailureCertificates.Budget020.certificate404).bound,(CutFailureCertificates.Budget020.certificate405).bound,0⟩
theorem numericValid202 : certificate202.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound202 : certificate202.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch020.certificate404 H MomentCertificates.Batch010.valid202.1 GeometryCertificates.Batch020.valid404 GeometryCertificates.Batch020.sound404 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch020.certificate405 H MomentCertificates.Batch010.valid202.1 GeometryCertificates.Batch020.valid405 GeometryCertificates.Batch020.sound405 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound202 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound202 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate202 GeometryCertificates.Batch020.certificate404 numericValid202
    MomentCertificates.Batch010.valid202 DegreeCertificates.Batch010.valid202 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate202,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate203 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate203,DegreeCertificates.Batch010.certificate203,(WitnessCertificates.Batch020.certificate406).beta,(WitnessCertificates.Batch020.certificate407).L,none,(CutFailureCertificates.Budget020.certificate406).bound,(CutFailureCertificates.Budget020.certificate407).bound,0⟩
theorem numericValid203 : certificate203.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound203 : certificate203.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch020.certificate406 H MomentCertificates.Batch010.valid203.1 GeometryCertificates.Batch020.valid406 GeometryCertificates.Batch020.sound406 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch020.certificate407 H MomentCertificates.Batch010.valid203.1 GeometryCertificates.Batch020.valid407 GeometryCertificates.Batch020.sound407 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound203 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound203 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate203 GeometryCertificates.Batch020.certificate406 numericValid203
    MomentCertificates.Batch010.valid203 DegreeCertificates.Batch010.valid203 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate203,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate204 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate204,DegreeCertificates.Batch010.certificate204,(WitnessCertificates.Batch020.certificate408).beta,(WitnessCertificates.Batch020.certificate409).L,none,(CutFailureCertificates.Budget020.certificate408).bound,(CutFailureCertificates.Budget020.certificate409).bound,0⟩
theorem numericValid204 : certificate204.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound204 : certificate204.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch020.certificate408 H MomentCertificates.Batch010.valid204.1 GeometryCertificates.Batch020.valid408 GeometryCertificates.Batch020.sound408 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch020.certificate409 H MomentCertificates.Batch010.valid204.1 GeometryCertificates.Batch020.valid409 GeometryCertificates.Batch020.sound409 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound204 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound204 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate204 GeometryCertificates.Batch020.certificate408 numericValid204
    MomentCertificates.Batch010.valid204 DegreeCertificates.Batch010.valid204 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate204,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate205 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate205,DegreeCertificates.Batch010.certificate205,(WitnessCertificates.Batch020.certificate410).beta,(WitnessCertificates.Batch020.certificate411).L,none,(CutFailureCertificates.Budget020.certificate410).bound,(CutFailureCertificates.Budget020.certificate411).bound,0⟩
theorem numericValid205 : certificate205.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound205 : certificate205.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch020.certificate410 H MomentCertificates.Batch010.valid205.1 GeometryCertificates.Batch020.valid410 GeometryCertificates.Batch020.sound410 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch020.certificate411 H MomentCertificates.Batch010.valid205.1 GeometryCertificates.Batch020.valid411 GeometryCertificates.Batch020.sound411 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound205 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound205 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate205 GeometryCertificates.Batch020.certificate410 numericValid205
    MomentCertificates.Batch010.valid205 DegreeCertificates.Batch010.valid205 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate205,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate206 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate206,DegreeCertificates.Batch010.certificate206,(WitnessCertificates.Batch020.certificate412).beta,(WitnessCertificates.Batch020.certificate413).L,none,(CutFailureCertificates.Budget020.certificate412).bound,(CutFailureCertificates.Budget020.certificate413).bound,0⟩
theorem numericValid206 : certificate206.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound206 : certificate206.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch020.certificate412 H MomentCertificates.Batch010.valid206.1 GeometryCertificates.Batch020.valid412 GeometryCertificates.Batch020.sound412 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch020.certificate413 H MomentCertificates.Batch010.valid206.1 GeometryCertificates.Batch020.valid413 GeometryCertificates.Batch020.sound413 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound206 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound206 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate206 GeometryCertificates.Batch020.certificate412 numericValid206
    MomentCertificates.Batch010.valid206 DegreeCertificates.Batch010.valid206 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate206,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate207 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate207,DegreeCertificates.Batch010.certificate207,(WitnessCertificates.Batch020.certificate414).beta,(WitnessCertificates.Batch020.certificate415).L,none,(CutFailureCertificates.Budget020.certificate414).bound,(CutFailureCertificates.Budget020.certificate415).bound,0⟩
theorem numericValid207 : certificate207.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound207 : certificate207.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch020.certificate414 H MomentCertificates.Batch010.valid207.1 GeometryCertificates.Batch020.valid414 GeometryCertificates.Batch020.sound414 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch020.certificate415 H MomentCertificates.Batch010.valid207.1 GeometryCertificates.Batch020.valid415 GeometryCertificates.Batch020.sound415 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound207 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound207 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate207 GeometryCertificates.Batch020.certificate414 numericValid207
    MomentCertificates.Batch010.valid207 DegreeCertificates.Batch010.valid207 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate207,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate208 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate208,DegreeCertificates.Batch010.certificate208,(WitnessCertificates.Batch020.certificate416).beta,(WitnessCertificates.Batch020.certificate417).L,none,(CutFailureCertificates.Budget020.certificate416).bound,(CutFailureCertificates.Budget020.certificate417).bound,0⟩
theorem numericValid208 : certificate208.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound208 : certificate208.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch020.certificate416 H MomentCertificates.Batch010.valid208.1 GeometryCertificates.Batch020.valid416 GeometryCertificates.Batch020.sound416 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch020.certificate417 H MomentCertificates.Batch010.valid208.1 GeometryCertificates.Batch020.valid417 GeometryCertificates.Batch020.sound417 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound208 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound208 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate208 GeometryCertificates.Batch020.certificate416 numericValid208
    MomentCertificates.Batch010.valid208 DegreeCertificates.Batch010.valid208 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate208,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate209 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate209,DegreeCertificates.Batch010.certificate209,(WitnessCertificates.Batch020.certificate418).beta,(WitnessCertificates.Batch020.certificate419).L,none,(CutFailureCertificates.Budget020.certificate418).bound,(CutFailureCertificates.Budget020.certificate419).bound,0⟩
theorem numericValid209 : certificate209.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound209 : certificate209.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch020.certificate418 H MomentCertificates.Batch010.valid209.1 GeometryCertificates.Batch020.valid418 GeometryCertificates.Batch020.sound418 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch020.certificate419 H MomentCertificates.Batch010.valid209.1 GeometryCertificates.Batch020.valid419 GeometryCertificates.Batch020.sound419 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound209 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound209 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate209 GeometryCertificates.Batch020.certificate418 numericValid209
    MomentCertificates.Batch010.valid209 DegreeCertificates.Batch010.valid209 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate209,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate210 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate210,DegreeCertificates.Batch010.certificate210,(WitnessCertificates.Batch021.certificate420).beta,(WitnessCertificates.Batch021.certificate421).L,none,(CutFailureCertificates.Budget021.certificate420).bound,(CutFailureCertificates.Budget021.certificate421).bound,0⟩
theorem numericValid210 : certificate210.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound210 : certificate210.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch021.certificate420 H MomentCertificates.Batch010.valid210.1 GeometryCertificates.Batch021.valid420 GeometryCertificates.Batch021.sound420 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch021.certificate421 H MomentCertificates.Batch010.valid210.1 GeometryCertificates.Batch021.valid421 GeometryCertificates.Batch021.sound421 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound210 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound210 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate210 GeometryCertificates.Batch021.certificate420 numericValid210
    MomentCertificates.Batch010.valid210 DegreeCertificates.Batch010.valid210 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate210,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate211 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate211,DegreeCertificates.Batch010.certificate211,(WitnessCertificates.Batch021.certificate422).beta,(WitnessCertificates.Batch021.certificate423).L,none,(CutFailureCertificates.Budget021.certificate422).bound,(CutFailureCertificates.Budget021.certificate423).bound,0⟩
theorem numericValid211 : certificate211.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound211 : certificate211.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch021.certificate422 H MomentCertificates.Batch010.valid211.1 GeometryCertificates.Batch021.valid422 GeometryCertificates.Batch021.sound422 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch021.certificate423 H MomentCertificates.Batch010.valid211.1 GeometryCertificates.Batch021.valid423 GeometryCertificates.Batch021.sound423 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound211 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound211 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate211 GeometryCertificates.Batch021.certificate422 numericValid211
    MomentCertificates.Batch010.valid211 DegreeCertificates.Batch010.valid211 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate211,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate212 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate212,DegreeCertificates.Batch010.certificate212,(WitnessCertificates.Batch021.certificate424).beta,(WitnessCertificates.Batch021.certificate425).L,none,(CutFailureCertificates.Budget021.certificate424).bound,(CutFailureCertificates.Budget021.certificate425).bound,0⟩
theorem numericValid212 : certificate212.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound212 : certificate212.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch021.certificate424 H MomentCertificates.Batch010.valid212.1 GeometryCertificates.Batch021.valid424 GeometryCertificates.Batch021.sound424 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch021.certificate425 H MomentCertificates.Batch010.valid212.1 GeometryCertificates.Batch021.valid425 GeometryCertificates.Batch021.sound425 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound212 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound212 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate212 GeometryCertificates.Batch021.certificate424 numericValid212
    MomentCertificates.Batch010.valid212 DegreeCertificates.Batch010.valid212 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate212,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate213 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate213,DegreeCertificates.Batch010.certificate213,(WitnessCertificates.Batch021.certificate426).beta,(WitnessCertificates.Batch021.certificate427).L,none,(CutFailureCertificates.Budget021.certificate426).bound,(CutFailureCertificates.Budget021.certificate427).bound,0⟩
theorem numericValid213 : certificate213.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound213 : certificate213.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch021.certificate426 H MomentCertificates.Batch010.valid213.1 GeometryCertificates.Batch021.valid426 GeometryCertificates.Batch021.sound426 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch021.certificate427 H MomentCertificates.Batch010.valid213.1 GeometryCertificates.Batch021.valid427 GeometryCertificates.Batch021.sound427 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound213 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound213 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate213 GeometryCertificates.Batch021.certificate426 numericValid213
    MomentCertificates.Batch010.valid213 DegreeCertificates.Batch010.valid213 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate213,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate214 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate214,DegreeCertificates.Batch010.certificate214,(WitnessCertificates.Batch021.certificate428).beta,(WitnessCertificates.Batch021.certificate429).L,none,(CutFailureCertificates.Budget021.certificate428).bound,(CutFailureCertificates.Budget021.certificate429).bound,0⟩
theorem numericValid214 : certificate214.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound214 : certificate214.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch021.certificate428 H MomentCertificates.Batch010.valid214.1 GeometryCertificates.Batch021.valid428 GeometryCertificates.Batch021.sound428 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch021.certificate429 H MomentCertificates.Batch010.valid214.1 GeometryCertificates.Batch021.valid429 GeometryCertificates.Batch021.sound429 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound214 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound214 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate214 GeometryCertificates.Batch021.certificate428 numericValid214
    MomentCertificates.Batch010.valid214 DegreeCertificates.Batch010.valid214 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate214,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate215 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate215,DegreeCertificates.Batch010.certificate215,(WitnessCertificates.Batch021.certificate430).beta,(WitnessCertificates.Batch021.certificate431).L,none,(CutFailureCertificates.Budget021.certificate430).bound,(CutFailureCertificates.Budget021.certificate431).bound,0⟩
theorem numericValid215 : certificate215.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound215 : certificate215.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch021.certificate430 H MomentCertificates.Batch010.valid215.1 GeometryCertificates.Batch021.valid430 GeometryCertificates.Batch021.sound430 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch021.certificate431 H MomentCertificates.Batch010.valid215.1 GeometryCertificates.Batch021.valid431 GeometryCertificates.Batch021.sound431 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound215 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound215 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate215 GeometryCertificates.Batch021.certificate430 numericValid215
    MomentCertificates.Batch010.valid215 DegreeCertificates.Batch010.valid215 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate215,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate216 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate216,DegreeCertificates.Batch010.certificate216,(WitnessCertificates.Batch021.certificate432).beta,(WitnessCertificates.Batch021.certificate433).L,none,(CutFailureCertificates.Budget021.certificate432).bound,(CutFailureCertificates.Budget021.certificate433).bound,0⟩
theorem numericValid216 : certificate216.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound216 : certificate216.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch021.certificate432 H MomentCertificates.Batch010.valid216.1 GeometryCertificates.Batch021.valid432 GeometryCertificates.Batch021.sound432 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch021.certificate433 H MomentCertificates.Batch010.valid216.1 GeometryCertificates.Batch021.valid433 GeometryCertificates.Batch021.sound433 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound216 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound216 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate216 GeometryCertificates.Batch021.certificate432 numericValid216
    MomentCertificates.Batch010.valid216 DegreeCertificates.Batch010.valid216 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate216,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate217 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate217,DegreeCertificates.Batch010.certificate217,(WitnessCertificates.Batch021.certificate434).beta,(WitnessCertificates.Batch021.certificate435).L,none,(CutFailureCertificates.Budget021.certificate434).bound,(CutFailureCertificates.Budget021.certificate435).bound,0⟩
theorem numericValid217 : certificate217.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound217 : certificate217.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch021.certificate434 H MomentCertificates.Batch010.valid217.1 GeometryCertificates.Batch021.valid434 GeometryCertificates.Batch021.sound434 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch021.certificate435 H MomentCertificates.Batch010.valid217.1 GeometryCertificates.Batch021.valid435 GeometryCertificates.Batch021.sound435 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound217 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound217 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate217 GeometryCertificates.Batch021.certificate434 numericValid217
    MomentCertificates.Batch010.valid217 DegreeCertificates.Batch010.valid217 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate217,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate218 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate218,DegreeCertificates.Batch010.certificate218,(WitnessCertificates.Batch021.certificate436).beta,(WitnessCertificates.Batch021.certificate437).L,none,(CutFailureCertificates.Budget021.certificate436).bound,(CutFailureCertificates.Budget021.certificate437).bound,0⟩
theorem numericValid218 : certificate218.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound218 : certificate218.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch021.certificate436 H MomentCertificates.Batch010.valid218.1 GeometryCertificates.Batch021.valid436 GeometryCertificates.Batch021.sound436 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch021.certificate437 H MomentCertificates.Batch010.valid218.1 GeometryCertificates.Batch021.valid437 GeometryCertificates.Batch021.sound437 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound218 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound218 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate218 GeometryCertificates.Batch021.certificate436 numericValid218
    MomentCertificates.Batch010.valid218 DegreeCertificates.Batch010.valid218 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate218,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate219 : RatSamplerCase := ⟨MomentCertificates.Batch010.certificate219,DegreeCertificates.Batch010.certificate219,(WitnessCertificates.Batch021.certificate438).beta,(WitnessCertificates.Batch021.certificate439).L,none,(CutFailureCertificates.Budget021.certificate438).bound,(CutFailureCertificates.Budget021.certificate439).bound,0⟩
theorem numericValid219 : certificate219.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound219 : certificate219.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch021.certificate438 H MomentCertificates.Batch010.valid219.1 GeometryCertificates.Batch021.valid438 GeometryCertificates.Batch021.sound438 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch021.certificate439 H MomentCertificates.Batch010.valid219.1 GeometryCertificates.Batch021.valid439 GeometryCertificates.Batch021.sound439 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch010.probabilityBound219 H st hI
  have hanchor := CertifiedAnchorFailures.Batch010.probabilityBound219 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate219 GeometryCertificates.Batch021.certificate438 numericValid219
    MomentCertificates.Batch010.valid219 DegreeCertificates.Batch010.valid219 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate219,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate200,certificate201,certificate202,certificate203,certificate204,certificate205,certificate206,certificate207,certificate208,certificate209,certificate210,certificate211,certificate212,certificate213,certificate214,certificate215,certificate216,certificate217,certificate218,certificate219]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound200,List.forall_mem_cons.mpr ⟨sound201,List.forall_mem_cons.mpr ⟨sound202,List.forall_mem_cons.mpr ⟨sound203,List.forall_mem_cons.mpr ⟨sound204,List.forall_mem_cons.mpr ⟨sound205,List.forall_mem_cons.mpr ⟨sound206,List.forall_mem_cons.mpr ⟨sound207,List.forall_mem_cons.mpr ⟨sound208,List.forall_mem_cons.mpr ⟨sound209,List.forall_mem_cons.mpr ⟨sound210,List.forall_mem_cons.mpr ⟨sound211,List.forall_mem_cons.mpr ⟨sound212,List.forall_mem_cons.mpr ⟨sound213,List.forall_mem_cons.mpr ⟨sound214,List.forall_mem_cons.mpr ⟨sound215,List.forall_mem_cons.mpr ⟨sound216,List.forall_mem_cons.mpr ⟨sound217,List.forall_mem_cons.mpr ⟨sound218,List.forall_mem_cons.mpr ⟨sound219,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch010
