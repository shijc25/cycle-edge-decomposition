import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch002
import Cycle12.CertifiedGlobalFailures.Batch002
import Cycle12.CutFailureCertificates.Budget004
import Cycle12.CutFailureCertificates.Budget005
import Cycle12.DegreeCertificates.Batch002
import Cycle12.GeometryCertificates.Batch004
import Cycle12.GeometryCertificates.Batch005
import Cycle12.MomentCertificates.Batch002
import Cycle12.WitnessCertificates.Batch004
import Cycle12.WitnessCertificates.Batch005

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch002
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate40 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate40,DegreeCertificates.Batch002.certificate40,(WitnessCertificates.Batch004.certificate80).beta,(WitnessCertificates.Batch004.certificate81).L,none,(CutFailureCertificates.Budget004.certificate80).bound,(CutFailureCertificates.Budget004.certificate81).bound,0⟩
theorem numericValid40 : certificate40.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound40 : certificate40.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch004.certificate80 H MomentCertificates.Batch002.valid40.1 GeometryCertificates.Batch004.valid80 GeometryCertificates.Batch004.sound80 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch004.certificate81 H MomentCertificates.Batch002.valid40.1 GeometryCertificates.Batch004.valid81 GeometryCertificates.Batch004.sound81 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound40 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound40 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate40 GeometryCertificates.Batch004.certificate80 numericValid40
    MomentCertificates.Batch002.valid40 DegreeCertificates.Batch002.valid40 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate40,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate41 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate41,DegreeCertificates.Batch002.certificate41,(WitnessCertificates.Batch004.certificate82).beta,(WitnessCertificates.Batch004.certificate83).L,none,(CutFailureCertificates.Budget004.certificate82).bound,(CutFailureCertificates.Budget004.certificate83).bound,0⟩
theorem numericValid41 : certificate41.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound41 : certificate41.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch004.certificate82 H MomentCertificates.Batch002.valid41.1 GeometryCertificates.Batch004.valid82 GeometryCertificates.Batch004.sound82 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch004.certificate83 H MomentCertificates.Batch002.valid41.1 GeometryCertificates.Batch004.valid83 GeometryCertificates.Batch004.sound83 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound41 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound41 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate41 GeometryCertificates.Batch004.certificate82 numericValid41
    MomentCertificates.Batch002.valid41 DegreeCertificates.Batch002.valid41 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate41,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate42 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate42,DegreeCertificates.Batch002.certificate42,(WitnessCertificates.Batch004.certificate84).beta,(WitnessCertificates.Batch004.certificate85).L,none,(CutFailureCertificates.Budget004.certificate84).bound,(CutFailureCertificates.Budget004.certificate85).bound,0⟩
theorem numericValid42 : certificate42.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound42 : certificate42.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch004.certificate84 H MomentCertificates.Batch002.valid42.1 GeometryCertificates.Batch004.valid84 GeometryCertificates.Batch004.sound84 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch004.certificate85 H MomentCertificates.Batch002.valid42.1 GeometryCertificates.Batch004.valid85 GeometryCertificates.Batch004.sound85 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound42 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound42 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate42 GeometryCertificates.Batch004.certificate84 numericValid42
    MomentCertificates.Batch002.valid42 DegreeCertificates.Batch002.valid42 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate42,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate43 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate43,DegreeCertificates.Batch002.certificate43,(WitnessCertificates.Batch004.certificate86).beta,(WitnessCertificates.Batch004.certificate87).L,none,(CutFailureCertificates.Budget004.certificate86).bound,(CutFailureCertificates.Budget004.certificate87).bound,0⟩
theorem numericValid43 : certificate43.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound43 : certificate43.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch004.certificate86 H MomentCertificates.Batch002.valid43.1 GeometryCertificates.Batch004.valid86 GeometryCertificates.Batch004.sound86 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch004.certificate87 H MomentCertificates.Batch002.valid43.1 GeometryCertificates.Batch004.valid87 GeometryCertificates.Batch004.sound87 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound43 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound43 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate43 GeometryCertificates.Batch004.certificate86 numericValid43
    MomentCertificates.Batch002.valid43 DegreeCertificates.Batch002.valid43 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate43,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate44 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate44,DegreeCertificates.Batch002.certificate44,(WitnessCertificates.Batch004.certificate88).beta,(WitnessCertificates.Batch004.certificate89).L,none,(CutFailureCertificates.Budget004.certificate88).bound,(CutFailureCertificates.Budget004.certificate89).bound,0⟩
theorem numericValid44 : certificate44.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound44 : certificate44.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch004.certificate88 H MomentCertificates.Batch002.valid44.1 GeometryCertificates.Batch004.valid88 GeometryCertificates.Batch004.sound88 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch004.certificate89 H MomentCertificates.Batch002.valid44.1 GeometryCertificates.Batch004.valid89 GeometryCertificates.Batch004.sound89 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound44 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound44 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate44 GeometryCertificates.Batch004.certificate88 numericValid44
    MomentCertificates.Batch002.valid44 DegreeCertificates.Batch002.valid44 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate44,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate45 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate45,DegreeCertificates.Batch002.certificate45,(WitnessCertificates.Batch004.certificate90).beta,(WitnessCertificates.Batch004.certificate91).L,none,(CutFailureCertificates.Budget004.certificate90).bound,(CutFailureCertificates.Budget004.certificate91).bound,0⟩
theorem numericValid45 : certificate45.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound45 : certificate45.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch004.certificate90 H MomentCertificates.Batch002.valid45.1 GeometryCertificates.Batch004.valid90 GeometryCertificates.Batch004.sound90 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch004.certificate91 H MomentCertificates.Batch002.valid45.1 GeometryCertificates.Batch004.valid91 GeometryCertificates.Batch004.sound91 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound45 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound45 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate45 GeometryCertificates.Batch004.certificate90 numericValid45
    MomentCertificates.Batch002.valid45 DegreeCertificates.Batch002.valid45 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate45,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate46 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate46,DegreeCertificates.Batch002.certificate46,(WitnessCertificates.Batch004.certificate92).beta,(WitnessCertificates.Batch004.certificate93).L,none,(CutFailureCertificates.Budget004.certificate92).bound,(CutFailureCertificates.Budget004.certificate93).bound,0⟩
theorem numericValid46 : certificate46.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound46 : certificate46.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch004.certificate92 H MomentCertificates.Batch002.valid46.1 GeometryCertificates.Batch004.valid92 GeometryCertificates.Batch004.sound92 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch004.certificate93 H MomentCertificates.Batch002.valid46.1 GeometryCertificates.Batch004.valid93 GeometryCertificates.Batch004.sound93 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound46 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound46 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate46 GeometryCertificates.Batch004.certificate92 numericValid46
    MomentCertificates.Batch002.valid46 DegreeCertificates.Batch002.valid46 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate46,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate47 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate47,DegreeCertificates.Batch002.certificate47,(WitnessCertificates.Batch004.certificate94).beta,(WitnessCertificates.Batch004.certificate95).L,none,(CutFailureCertificates.Budget004.certificate94).bound,(CutFailureCertificates.Budget004.certificate95).bound,0⟩
theorem numericValid47 : certificate47.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound47 : certificate47.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch004.certificate94 H MomentCertificates.Batch002.valid47.1 GeometryCertificates.Batch004.valid94 GeometryCertificates.Batch004.sound94 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch004.certificate95 H MomentCertificates.Batch002.valid47.1 GeometryCertificates.Batch004.valid95 GeometryCertificates.Batch004.sound95 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound47 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound47 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate47 GeometryCertificates.Batch004.certificate94 numericValid47
    MomentCertificates.Batch002.valid47 DegreeCertificates.Batch002.valid47 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate47,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate48 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate48,DegreeCertificates.Batch002.certificate48,(WitnessCertificates.Batch004.certificate96).beta,(WitnessCertificates.Batch004.certificate97).L,none,(CutFailureCertificates.Budget004.certificate96).bound,(CutFailureCertificates.Budget004.certificate97).bound,0⟩
theorem numericValid48 : certificate48.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound48 : certificate48.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch004.certificate96 H MomentCertificates.Batch002.valid48.1 GeometryCertificates.Batch004.valid96 GeometryCertificates.Batch004.sound96 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch004.certificate97 H MomentCertificates.Batch002.valid48.1 GeometryCertificates.Batch004.valid97 GeometryCertificates.Batch004.sound97 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound48 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound48 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate48 GeometryCertificates.Batch004.certificate96 numericValid48
    MomentCertificates.Batch002.valid48 DegreeCertificates.Batch002.valid48 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate48,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate49 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate49,DegreeCertificates.Batch002.certificate49,(WitnessCertificates.Batch004.certificate98).beta,(WitnessCertificates.Batch004.certificate99).L,none,(CutFailureCertificates.Budget004.certificate98).bound,(CutFailureCertificates.Budget004.certificate99).bound,0⟩
theorem numericValid49 : certificate49.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound49 : certificate49.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch004.certificate98 H MomentCertificates.Batch002.valid49.1 GeometryCertificates.Batch004.valid98 GeometryCertificates.Batch004.sound98 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch004.certificate99 H MomentCertificates.Batch002.valid49.1 GeometryCertificates.Batch004.valid99 GeometryCertificates.Batch004.sound99 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound49 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound49 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate49 GeometryCertificates.Batch004.certificate98 numericValid49
    MomentCertificates.Batch002.valid49 DegreeCertificates.Batch002.valid49 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate49,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate50 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate50,DegreeCertificates.Batch002.certificate50,(WitnessCertificates.Batch005.certificate100).beta,(WitnessCertificates.Batch005.certificate101).L,none,(CutFailureCertificates.Budget005.certificate100).bound,(CutFailureCertificates.Budget005.certificate101).bound,0⟩
theorem numericValid50 : certificate50.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound50 : certificate50.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch005.certificate100 H MomentCertificates.Batch002.valid50.1 GeometryCertificates.Batch005.valid100 GeometryCertificates.Batch005.sound100 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch005.certificate101 H MomentCertificates.Batch002.valid50.1 GeometryCertificates.Batch005.valid101 GeometryCertificates.Batch005.sound101 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound50 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound50 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate50 GeometryCertificates.Batch005.certificate100 numericValid50
    MomentCertificates.Batch002.valid50 DegreeCertificates.Batch002.valid50 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate50,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate51 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate51,DegreeCertificates.Batch002.certificate51,(WitnessCertificates.Batch005.certificate102).beta,(WitnessCertificates.Batch005.certificate103).L,none,(CutFailureCertificates.Budget005.certificate102).bound,(CutFailureCertificates.Budget005.certificate103).bound,0⟩
theorem numericValid51 : certificate51.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound51 : certificate51.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch005.certificate102 H MomentCertificates.Batch002.valid51.1 GeometryCertificates.Batch005.valid102 GeometryCertificates.Batch005.sound102 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch005.certificate103 H MomentCertificates.Batch002.valid51.1 GeometryCertificates.Batch005.valid103 GeometryCertificates.Batch005.sound103 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound51 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound51 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate51 GeometryCertificates.Batch005.certificate102 numericValid51
    MomentCertificates.Batch002.valid51 DegreeCertificates.Batch002.valid51 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate51,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate52 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate52,DegreeCertificates.Batch002.certificate52,(WitnessCertificates.Batch005.certificate104).beta,(WitnessCertificates.Batch005.certificate105).L,none,(CutFailureCertificates.Budget005.certificate104).bound,(CutFailureCertificates.Budget005.certificate105).bound,0⟩
theorem numericValid52 : certificate52.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound52 : certificate52.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch005.certificate104 H MomentCertificates.Batch002.valid52.1 GeometryCertificates.Batch005.valid104 GeometryCertificates.Batch005.sound104 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch005.certificate105 H MomentCertificates.Batch002.valid52.1 GeometryCertificates.Batch005.valid105 GeometryCertificates.Batch005.sound105 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound52 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound52 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate52 GeometryCertificates.Batch005.certificate104 numericValid52
    MomentCertificates.Batch002.valid52 DegreeCertificates.Batch002.valid52 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate52,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate53 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate53,DegreeCertificates.Batch002.certificate53,(WitnessCertificates.Batch005.certificate106).beta,(WitnessCertificates.Batch005.certificate107).L,none,(CutFailureCertificates.Budget005.certificate106).bound,(CutFailureCertificates.Budget005.certificate107).bound,0⟩
theorem numericValid53 : certificate53.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound53 : certificate53.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch005.certificate106 H MomentCertificates.Batch002.valid53.1 GeometryCertificates.Batch005.valid106 GeometryCertificates.Batch005.sound106 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch005.certificate107 H MomentCertificates.Batch002.valid53.1 GeometryCertificates.Batch005.valid107 GeometryCertificates.Batch005.sound107 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound53 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound53 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate53 GeometryCertificates.Batch005.certificate106 numericValid53
    MomentCertificates.Batch002.valid53 DegreeCertificates.Batch002.valid53 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate53,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate54 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate54,DegreeCertificates.Batch002.certificate54,(WitnessCertificates.Batch005.certificate108).beta,(WitnessCertificates.Batch005.certificate109).L,none,(CutFailureCertificates.Budget005.certificate108).bound,(CutFailureCertificates.Budget005.certificate109).bound,0⟩
theorem numericValid54 : certificate54.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound54 : certificate54.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch005.certificate108 H MomentCertificates.Batch002.valid54.1 GeometryCertificates.Batch005.valid108 GeometryCertificates.Batch005.sound108 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch005.certificate109 H MomentCertificates.Batch002.valid54.1 GeometryCertificates.Batch005.valid109 GeometryCertificates.Batch005.sound109 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound54 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound54 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate54 GeometryCertificates.Batch005.certificate108 numericValid54
    MomentCertificates.Batch002.valid54 DegreeCertificates.Batch002.valid54 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate54,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate55 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate55,DegreeCertificates.Batch002.certificate55,(WitnessCertificates.Batch005.certificate110).beta,(WitnessCertificates.Batch005.certificate111).L,none,(CutFailureCertificates.Budget005.certificate110).bound,(CutFailureCertificates.Budget005.certificate111).bound,0⟩
theorem numericValid55 : certificate55.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound55 : certificate55.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch005.certificate110 H MomentCertificates.Batch002.valid55.1 GeometryCertificates.Batch005.valid110 GeometryCertificates.Batch005.sound110 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch005.certificate111 H MomentCertificates.Batch002.valid55.1 GeometryCertificates.Batch005.valid111 GeometryCertificates.Batch005.sound111 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound55 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound55 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate55 GeometryCertificates.Batch005.certificate110 numericValid55
    MomentCertificates.Batch002.valid55 DegreeCertificates.Batch002.valid55 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate55,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate56 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate56,DegreeCertificates.Batch002.certificate56,(WitnessCertificates.Batch005.certificate112).beta,(WitnessCertificates.Batch005.certificate113).L,none,(CutFailureCertificates.Budget005.certificate112).bound,(CutFailureCertificates.Budget005.certificate113).bound,0⟩
theorem numericValid56 : certificate56.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound56 : certificate56.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch005.certificate112 H MomentCertificates.Batch002.valid56.1 GeometryCertificates.Batch005.valid112 GeometryCertificates.Batch005.sound112 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch005.certificate113 H MomentCertificates.Batch002.valid56.1 GeometryCertificates.Batch005.valid113 GeometryCertificates.Batch005.sound113 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound56 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound56 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate56 GeometryCertificates.Batch005.certificate112 numericValid56
    MomentCertificates.Batch002.valid56 DegreeCertificates.Batch002.valid56 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate56,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate57 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate57,DegreeCertificates.Batch002.certificate57,(WitnessCertificates.Batch005.certificate114).beta,(WitnessCertificates.Batch005.certificate115).L,none,(CutFailureCertificates.Budget005.certificate114).bound,(CutFailureCertificates.Budget005.certificate115).bound,0⟩
theorem numericValid57 : certificate57.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound57 : certificate57.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch005.certificate114 H MomentCertificates.Batch002.valid57.1 GeometryCertificates.Batch005.valid114 GeometryCertificates.Batch005.sound114 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch005.certificate115 H MomentCertificates.Batch002.valid57.1 GeometryCertificates.Batch005.valid115 GeometryCertificates.Batch005.sound115 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound57 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound57 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate57 GeometryCertificates.Batch005.certificate114 numericValid57
    MomentCertificates.Batch002.valid57 DegreeCertificates.Batch002.valid57 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate57,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate58 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate58,DegreeCertificates.Batch002.certificate58,(WitnessCertificates.Batch005.certificate116).beta,(WitnessCertificates.Batch005.certificate117).L,none,(CutFailureCertificates.Budget005.certificate116).bound,(CutFailureCertificates.Budget005.certificate117).bound,0⟩
theorem numericValid58 : certificate58.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound58 : certificate58.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch005.certificate116 H MomentCertificates.Batch002.valid58.1 GeometryCertificates.Batch005.valid116 GeometryCertificates.Batch005.sound116 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch005.certificate117 H MomentCertificates.Batch002.valid58.1 GeometryCertificates.Batch005.valid117 GeometryCertificates.Batch005.sound117 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound58 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound58 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate58 GeometryCertificates.Batch005.certificate116 numericValid58
    MomentCertificates.Batch002.valid58 DegreeCertificates.Batch002.valid58 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate58,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate59 : RatSamplerCase := ⟨MomentCertificates.Batch002.certificate59,DegreeCertificates.Batch002.certificate59,(WitnessCertificates.Batch005.certificate118).beta,(WitnessCertificates.Batch005.certificate119).L,none,(CutFailureCertificates.Budget005.certificate118).bound,(CutFailureCertificates.Budget005.certificate119).bound,0⟩
theorem numericValid59 : certificate59.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound59 : certificate59.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch005.certificate118 H MomentCertificates.Batch002.valid59.1 GeometryCertificates.Batch005.valid118 GeometryCertificates.Batch005.sound118 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch005.certificate119 H MomentCertificates.Batch002.valid59.1 GeometryCertificates.Batch005.valid119 GeometryCertificates.Batch005.sound119 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch002.probabilityBound59 H st hI
  have hanchor := CertifiedAnchorFailures.Batch002.probabilityBound59 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate59 GeometryCertificates.Batch005.certificate118 numericValid59
    MomentCertificates.Batch002.valid59 DegreeCertificates.Batch002.valid59 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate59,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate40,certificate41,certificate42,certificate43,certificate44,certificate45,certificate46,certificate47,certificate48,certificate49,certificate50,certificate51,certificate52,certificate53,certificate54,certificate55,certificate56,certificate57,certificate58,certificate59]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound40,List.forall_mem_cons.mpr ⟨sound41,List.forall_mem_cons.mpr ⟨sound42,List.forall_mem_cons.mpr ⟨sound43,List.forall_mem_cons.mpr ⟨sound44,List.forall_mem_cons.mpr ⟨sound45,List.forall_mem_cons.mpr ⟨sound46,List.forall_mem_cons.mpr ⟨sound47,List.forall_mem_cons.mpr ⟨sound48,List.forall_mem_cons.mpr ⟨sound49,List.forall_mem_cons.mpr ⟨sound50,List.forall_mem_cons.mpr ⟨sound51,List.forall_mem_cons.mpr ⟨sound52,List.forall_mem_cons.mpr ⟨sound53,List.forall_mem_cons.mpr ⟨sound54,List.forall_mem_cons.mpr ⟨sound55,List.forall_mem_cons.mpr ⟨sound56,List.forall_mem_cons.mpr ⟨sound57,List.forall_mem_cons.mpr ⟨sound58,List.forall_mem_cons.mpr ⟨sound59,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch002
