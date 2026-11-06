import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch020
import Cycle12.CertifiedGlobalFailures.Batch020
import Cycle12.CertifiedLocalFailures.Batch000
import Cycle12.CutFailureCertificates.Budget040
import Cycle12.CutFailureCertificates.Budget041
import Cycle12.CutFailureCertificates.Budget042
import Cycle12.DegreeCertificates.Batch020
import Cycle12.GeometryCertificates.Batch040
import Cycle12.GeometryCertificates.Batch041
import Cycle12.GeometryCertificates.Batch042
import Cycle12.MomentCertificates.Batch020
import Cycle12.WitnessCertificates.Batch040
import Cycle12.WitnessCertificates.Batch041
import Cycle12.WitnessCertificates.Batch042

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch020
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate400 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate400,DegreeCertificates.Batch020.certificate400,(WitnessCertificates.Batch040.certificate800).beta,(WitnessCertificates.Batch040.certificate801).L,none,(CutFailureCertificates.Budget040.certificate800).bound,(CutFailureCertificates.Budget040.certificate801).bound,0⟩
theorem numericValid400 : certificate400.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound400 : certificate400.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch040.certificate800 H MomentCertificates.Batch020.valid400.1 GeometryCertificates.Batch040.valid800 GeometryCertificates.Batch040.sound800 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch040.certificate801 H MomentCertificates.Batch020.valid400.1 GeometryCertificates.Batch040.valid801 GeometryCertificates.Batch040.sound801 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound400 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound400 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate400 GeometryCertificates.Batch040.certificate800 numericValid400
    MomentCertificates.Batch020.valid400 DegreeCertificates.Batch020.valid400 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate400,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate401 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate401,DegreeCertificates.Batch020.certificate401,(WitnessCertificates.Batch040.certificate802).beta,(WitnessCertificates.Batch040.certificate803).L,none,(CutFailureCertificates.Budget040.certificate802).bound,(CutFailureCertificates.Budget040.certificate803).bound,0⟩
theorem numericValid401 : certificate401.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound401 : certificate401.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch040.certificate802 H MomentCertificates.Batch020.valid401.1 GeometryCertificates.Batch040.valid802 GeometryCertificates.Batch040.sound802 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch040.certificate803 H MomentCertificates.Batch020.valid401.1 GeometryCertificates.Batch040.valid803 GeometryCertificates.Batch040.sound803 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound401 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound401 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate401 GeometryCertificates.Batch040.certificate802 numericValid401
    MomentCertificates.Batch020.valid401 DegreeCertificates.Batch020.valid401 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate401,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate402 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate402,DegreeCertificates.Batch020.certificate402,(WitnessCertificates.Batch040.certificate804).beta,(WitnessCertificates.Batch040.certificate805).L,none,(CutFailureCertificates.Budget040.certificate804).bound,(CutFailureCertificates.Budget040.certificate805).bound,0⟩
theorem numericValid402 : certificate402.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound402 : certificate402.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch040.certificate804 H MomentCertificates.Batch020.valid402.1 GeometryCertificates.Batch040.valid804 GeometryCertificates.Batch040.sound804 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch040.certificate805 H MomentCertificates.Batch020.valid402.1 GeometryCertificates.Batch040.valid805 GeometryCertificates.Batch040.sound805 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound402 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound402 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate402 GeometryCertificates.Batch040.certificate804 numericValid402
    MomentCertificates.Batch020.valid402 DegreeCertificates.Batch020.valid402 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate402,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate403 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate403,DegreeCertificates.Batch020.certificate403,(WitnessCertificates.Batch040.certificate806).beta,(WitnessCertificates.Batch040.certificate807).L,none,(CutFailureCertificates.Budget040.certificate806).bound,(CutFailureCertificates.Budget040.certificate807).bound,0⟩
theorem numericValid403 : certificate403.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound403 : certificate403.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch040.certificate806 H MomentCertificates.Batch020.valid403.1 GeometryCertificates.Batch040.valid806 GeometryCertificates.Batch040.sound806 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch040.certificate807 H MomentCertificates.Batch020.valid403.1 GeometryCertificates.Batch040.valid807 GeometryCertificates.Batch040.sound807 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound403 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound403 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate403 GeometryCertificates.Batch040.certificate806 numericValid403
    MomentCertificates.Batch020.valid403 DegreeCertificates.Batch020.valid403 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate403,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate404 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate404,DegreeCertificates.Batch020.certificate404,(WitnessCertificates.Batch040.certificate808).beta,(WitnessCertificates.Batch040.certificate809).L,none,(CutFailureCertificates.Budget040.certificate808).bound,(CutFailureCertificates.Budget040.certificate809).bound,0⟩
theorem numericValid404 : certificate404.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound404 : certificate404.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch040.certificate808 H MomentCertificates.Batch020.valid404.1 GeometryCertificates.Batch040.valid808 GeometryCertificates.Batch040.sound808 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch040.certificate809 H MomentCertificates.Batch020.valid404.1 GeometryCertificates.Batch040.valid809 GeometryCertificates.Batch040.sound809 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound404 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound404 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate404 GeometryCertificates.Batch040.certificate808 numericValid404
    MomentCertificates.Batch020.valid404 DegreeCertificates.Batch020.valid404 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate404,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate405 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate405,DegreeCertificates.Batch020.certificate405,(WitnessCertificates.Batch040.certificate810).beta,(WitnessCertificates.Batch040.certificate811).L,none,(CutFailureCertificates.Budget040.certificate810).bound,(CutFailureCertificates.Budget040.certificate811).bound,0⟩
theorem numericValid405 : certificate405.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound405 : certificate405.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch040.certificate810 H MomentCertificates.Batch020.valid405.1 GeometryCertificates.Batch040.valid810 GeometryCertificates.Batch040.sound810 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch040.certificate811 H MomentCertificates.Batch020.valid405.1 GeometryCertificates.Batch040.valid811 GeometryCertificates.Batch040.sound811 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound405 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound405 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate405 GeometryCertificates.Batch040.certificate810 numericValid405
    MomentCertificates.Batch020.valid405 DegreeCertificates.Batch020.valid405 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate405,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate406 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate406,DegreeCertificates.Batch020.certificate406,(WitnessCertificates.Batch040.certificate812).beta,(WitnessCertificates.Batch040.certificate813).L,none,(CutFailureCertificates.Budget040.certificate812).bound,(CutFailureCertificates.Budget040.certificate813).bound,0⟩
theorem numericValid406 : certificate406.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound406 : certificate406.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch040.certificate812 H MomentCertificates.Batch020.valid406.1 GeometryCertificates.Batch040.valid812 GeometryCertificates.Batch040.sound812 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch040.certificate813 H MomentCertificates.Batch020.valid406.1 GeometryCertificates.Batch040.valid813 GeometryCertificates.Batch040.sound813 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound406 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound406 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate406 GeometryCertificates.Batch040.certificate812 numericValid406
    MomentCertificates.Batch020.valid406 DegreeCertificates.Batch020.valid406 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate406,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate407 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate407,DegreeCertificates.Batch020.certificate407,(WitnessCertificates.Batch040.certificate814).beta,(WitnessCertificates.Batch040.certificate815).L,none,(CutFailureCertificates.Budget040.certificate814).bound,(CutFailureCertificates.Budget040.certificate815).bound,0⟩
theorem numericValid407 : certificate407.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound407 : certificate407.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch040.certificate814 H MomentCertificates.Batch020.valid407.1 GeometryCertificates.Batch040.valid814 GeometryCertificates.Batch040.sound814 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch040.certificate815 H MomentCertificates.Batch020.valid407.1 GeometryCertificates.Batch040.valid815 GeometryCertificates.Batch040.sound815 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound407 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound407 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate407 GeometryCertificates.Batch040.certificate814 numericValid407
    MomentCertificates.Batch020.valid407 DegreeCertificates.Batch020.valid407 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate407,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate408 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate408,DegreeCertificates.Batch020.certificate408,(WitnessCertificates.Batch040.certificate816).beta,(WitnessCertificates.Batch040.certificate817).L,none,(CutFailureCertificates.Budget040.certificate816).bound,(CutFailureCertificates.Budget040.certificate817).bound,0⟩
theorem numericValid408 : certificate408.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound408 : certificate408.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch040.certificate816 H MomentCertificates.Batch020.valid408.1 GeometryCertificates.Batch040.valid816 GeometryCertificates.Batch040.sound816 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch040.certificate817 H MomentCertificates.Batch020.valid408.1 GeometryCertificates.Batch040.valid817 GeometryCertificates.Batch040.sound817 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound408 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound408 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate408 GeometryCertificates.Batch040.certificate816 numericValid408
    MomentCertificates.Batch020.valid408 DegreeCertificates.Batch020.valid408 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate408,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate409 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate409,DegreeCertificates.Batch020.certificate409,(WitnessCertificates.Batch040.certificate818).beta,(WitnessCertificates.Batch040.certificate819).L,none,(CutFailureCertificates.Budget040.certificate818).bound,(CutFailureCertificates.Budget040.certificate819).bound,0⟩
theorem numericValid409 : certificate409.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound409 : certificate409.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch040.certificate818 H MomentCertificates.Batch020.valid409.1 GeometryCertificates.Batch040.valid818 GeometryCertificates.Batch040.sound818 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch040.certificate819 H MomentCertificates.Batch020.valid409.1 GeometryCertificates.Batch040.valid819 GeometryCertificates.Batch040.sound819 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound409 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound409 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate409 GeometryCertificates.Batch040.certificate818 numericValid409
    MomentCertificates.Batch020.valid409 DegreeCertificates.Batch020.valid409 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate409,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate410 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate410,DegreeCertificates.Batch020.certificate410,(WitnessCertificates.Batch041.certificate820).beta,(WitnessCertificates.Batch041.certificate821).L,none,(CutFailureCertificates.Budget041.certificate820).bound,(CutFailureCertificates.Budget041.certificate821).bound,0⟩
theorem numericValid410 : certificate410.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound410 : certificate410.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch041.certificate820 H MomentCertificates.Batch020.valid410.1 GeometryCertificates.Batch041.valid820 GeometryCertificates.Batch041.sound820 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch041.certificate821 H MomentCertificates.Batch020.valid410.1 GeometryCertificates.Batch041.valid821 GeometryCertificates.Batch041.sound821 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound410 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound410 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate410 GeometryCertificates.Batch041.certificate820 numericValid410
    MomentCertificates.Batch020.valid410 DegreeCertificates.Batch020.valid410 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate410,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate411 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate411,DegreeCertificates.Batch020.certificate411,(WitnessCertificates.Batch041.certificate822).beta,(WitnessCertificates.Batch041.certificate823).L,none,(CutFailureCertificates.Budget041.certificate822).bound,(CutFailureCertificates.Budget041.certificate823).bound,0⟩
theorem numericValid411 : certificate411.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound411 : certificate411.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch041.certificate822 H MomentCertificates.Batch020.valid411.1 GeometryCertificates.Batch041.valid822 GeometryCertificates.Batch041.sound822 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch041.certificate823 H MomentCertificates.Batch020.valid411.1 GeometryCertificates.Batch041.valid823 GeometryCertificates.Batch041.sound823 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound411 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound411 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate411 GeometryCertificates.Batch041.certificate822 numericValid411
    MomentCertificates.Batch020.valid411 DegreeCertificates.Batch020.valid411 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate411,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate412 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate412,DegreeCertificates.Batch020.certificate412,(WitnessCertificates.Batch041.certificate824).beta,(WitnessCertificates.Batch041.certificate825).L,none,(CutFailureCertificates.Budget041.certificate824).bound,(CutFailureCertificates.Budget041.certificate825).bound,0⟩
theorem numericValid412 : certificate412.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound412 : certificate412.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch041.certificate824 H MomentCertificates.Batch020.valid412.1 GeometryCertificates.Batch041.valid824 GeometryCertificates.Batch041.sound824 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch041.certificate825 H MomentCertificates.Batch020.valid412.1 GeometryCertificates.Batch041.valid825 GeometryCertificates.Batch041.sound825 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound412 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound412 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate412 GeometryCertificates.Batch041.certificate824 numericValid412
    MomentCertificates.Batch020.valid412 DegreeCertificates.Batch020.valid412 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate412,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate413 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate413,DegreeCertificates.Batch020.certificate413,(WitnessCertificates.Batch041.certificate826).beta,(WitnessCertificates.Batch041.certificate827).L,none,(CutFailureCertificates.Budget041.certificate826).bound,(CutFailureCertificates.Budget041.certificate827).bound,0⟩
theorem numericValid413 : certificate413.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound413 : certificate413.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch041.certificate826 H MomentCertificates.Batch020.valid413.1 GeometryCertificates.Batch041.valid826 GeometryCertificates.Batch041.sound826 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch041.certificate827 H MomentCertificates.Batch020.valid413.1 GeometryCertificates.Batch041.valid827 GeometryCertificates.Batch041.sound827 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound413 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound413 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate413 GeometryCertificates.Batch041.certificate826 numericValid413
    MomentCertificates.Batch020.valid413 DegreeCertificates.Batch020.valid413 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate413,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate414 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate414,DegreeCertificates.Batch020.certificate414,(WitnessCertificates.Batch041.certificate828).beta,(WitnessCertificates.Batch041.certificate829).L,none,(CutFailureCertificates.Budget041.certificate828).bound,(CutFailureCertificates.Budget041.certificate829).bound,0⟩
theorem numericValid414 : certificate414.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound414 : certificate414.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch041.certificate828 H MomentCertificates.Batch020.valid414.1 GeometryCertificates.Batch041.valid828 GeometryCertificates.Batch041.sound828 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch041.certificate829 H MomentCertificates.Batch020.valid414.1 GeometryCertificates.Batch041.valid829 GeometryCertificates.Batch041.sound829 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound414 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound414 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate414 GeometryCertificates.Batch041.certificate828 numericValid414
    MomentCertificates.Batch020.valid414 DegreeCertificates.Batch020.valid414 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate414,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate415 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate415,DegreeCertificates.Batch020.certificate415,(WitnessCertificates.Batch041.certificate830).beta,(WitnessCertificates.Batch041.certificate831).L,(some (WitnessCertificates.Batch041.certificate832).beta),(CutFailureCertificates.Budget041.certificate830).bound,(CutFailureCertificates.Budget041.certificate831).bound,(CutFailureCertificates.Budget041.certificate832).bound⟩
theorem numericValid415 : certificate415.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound415 : certificate415.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch041.certificate830 H MomentCertificates.Batch020.valid415.1 GeometryCertificates.Batch041.valid830 GeometryCertificates.Batch041.sound830 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch041.certificate831 H MomentCertificates.Batch020.valid415.1 GeometryCertificates.Batch041.valid831 GeometryCertificates.Batch041.sound831 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound415 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound415 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch041.certificate832 H MomentCertificates.Batch020.valid415.1 GeometryCertificates.Batch041.valid832 GeometryCertificates.Batch041.sound832 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound0 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch041.certificate832).dm = (DegreeCertificates.Batch020.certificate415).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate415 GeometryCertificates.Batch041.certificate830 numericValid415
    MomentCertificates.Batch020.valid415 DegreeCertificates.Batch020.valid415 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate415,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate416 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate416,DegreeCertificates.Batch020.certificate416,(WitnessCertificates.Batch041.certificate833).beta,(WitnessCertificates.Batch041.certificate834).L,(some (WitnessCertificates.Batch041.certificate835).beta),(CutFailureCertificates.Budget041.certificate833).bound,(CutFailureCertificates.Budget041.certificate834).bound,(CutFailureCertificates.Budget041.certificate835).bound⟩
theorem numericValid416 : certificate416.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound416 : certificate416.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch041.certificate833 H MomentCertificates.Batch020.valid416.1 GeometryCertificates.Batch041.valid833 GeometryCertificates.Batch041.sound833 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch041.certificate834 H MomentCertificates.Batch020.valid416.1 GeometryCertificates.Batch041.valid834 GeometryCertificates.Batch041.sound834 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound416 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound416 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch041.certificate835 H MomentCertificates.Batch020.valid416.1 GeometryCertificates.Batch041.valid835 GeometryCertificates.Batch041.sound835 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound1 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch041.certificate835).dm = (DegreeCertificates.Batch020.certificate416).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate416 GeometryCertificates.Batch041.certificate833 numericValid416
    MomentCertificates.Batch020.valid416 DegreeCertificates.Batch020.valid416 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate416,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate417 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate417,DegreeCertificates.Batch020.certificate417,(WitnessCertificates.Batch041.certificate836).beta,(WitnessCertificates.Batch041.certificate837).L,(some (WitnessCertificates.Batch041.certificate838).beta),(CutFailureCertificates.Budget041.certificate836).bound,(CutFailureCertificates.Budget041.certificate837).bound,(CutFailureCertificates.Budget041.certificate838).bound⟩
theorem numericValid417 : certificate417.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound417 : certificate417.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch041.certificate836 H MomentCertificates.Batch020.valid417.1 GeometryCertificates.Batch041.valid836 GeometryCertificates.Batch041.sound836 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch041.certificate837 H MomentCertificates.Batch020.valid417.1 GeometryCertificates.Batch041.valid837 GeometryCertificates.Batch041.sound837 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound417 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound417 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch041.certificate838 H MomentCertificates.Batch020.valid417.1 GeometryCertificates.Batch041.valid838 GeometryCertificates.Batch041.sound838 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound2 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch041.certificate838).dm = (DegreeCertificates.Batch020.certificate417).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate417 GeometryCertificates.Batch041.certificate836 numericValid417
    MomentCertificates.Batch020.valid417 DegreeCertificates.Batch020.valid417 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate417,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate418 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate418,DegreeCertificates.Batch020.certificate418,(WitnessCertificates.Batch041.certificate839).beta,(WitnessCertificates.Batch042.certificate840).L,(some (WitnessCertificates.Batch042.certificate841).beta),(CutFailureCertificates.Budget041.certificate839).bound,(CutFailureCertificates.Budget042.certificate840).bound,(CutFailureCertificates.Budget042.certificate841).bound⟩
theorem numericValid418 : certificate418.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound418 : certificate418.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch041.certificate839 H MomentCertificates.Batch020.valid418.1 GeometryCertificates.Batch041.valid839 GeometryCertificates.Batch041.sound839 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch042.certificate840 H MomentCertificates.Batch020.valid418.1 GeometryCertificates.Batch042.valid840 GeometryCertificates.Batch042.sound840 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound418 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound418 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch042.certificate841 H MomentCertificates.Batch020.valid418.1 GeometryCertificates.Batch042.valid841 GeometryCertificates.Batch042.sound841 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound3 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch042.certificate841).dm = (DegreeCertificates.Batch020.certificate418).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate418 GeometryCertificates.Batch041.certificate839 numericValid418
    MomentCertificates.Batch020.valid418 DegreeCertificates.Batch020.valid418 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate418,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate419 : RatSamplerCase := ⟨MomentCertificates.Batch020.certificate419,DegreeCertificates.Batch020.certificate419,(WitnessCertificates.Batch042.certificate842).beta,(WitnessCertificates.Batch042.certificate843).L,(some (WitnessCertificates.Batch042.certificate844).beta),(CutFailureCertificates.Budget042.certificate842).bound,(CutFailureCertificates.Budget042.certificate843).bound,(CutFailureCertificates.Budget042.certificate844).bound⟩
theorem numericValid419 : certificate419.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound419 : certificate419.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch042.certificate842 H MomentCertificates.Batch020.valid419.1 GeometryCertificates.Batch042.valid842 GeometryCertificates.Batch042.sound842 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch042.certificate843 H MomentCertificates.Batch020.valid419.1 GeometryCertificates.Batch042.valid843 GeometryCertificates.Batch042.sound843 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch020.probabilityBound419 H st hI
  have hanchor := CertifiedAnchorFailures.Batch020.probabilityBound419 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch042.certificate844 H MomentCertificates.Batch020.valid419.1 GeometryCertificates.Batch042.valid844 GeometryCertificates.Batch042.sound844 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound4 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch042.certificate844).dm = (DegreeCertificates.Batch020.certificate419).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate419 GeometryCertificates.Batch042.certificate842 numericValid419
    MomentCertificates.Batch020.valid419 DegreeCertificates.Batch020.valid419 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate419,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate400,certificate401,certificate402,certificate403,certificate404,certificate405,certificate406,certificate407,certificate408,certificate409,certificate410,certificate411,certificate412,certificate413,certificate414,certificate415,certificate416,certificate417,certificate418,certificate419]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound400,List.forall_mem_cons.mpr ⟨sound401,List.forall_mem_cons.mpr ⟨sound402,List.forall_mem_cons.mpr ⟨sound403,List.forall_mem_cons.mpr ⟨sound404,List.forall_mem_cons.mpr ⟨sound405,List.forall_mem_cons.mpr ⟨sound406,List.forall_mem_cons.mpr ⟨sound407,List.forall_mem_cons.mpr ⟨sound408,List.forall_mem_cons.mpr ⟨sound409,List.forall_mem_cons.mpr ⟨sound410,List.forall_mem_cons.mpr ⟨sound411,List.forall_mem_cons.mpr ⟨sound412,List.forall_mem_cons.mpr ⟨sound413,List.forall_mem_cons.mpr ⟨sound414,List.forall_mem_cons.mpr ⟨sound415,List.forall_mem_cons.mpr ⟨sound416,List.forall_mem_cons.mpr ⟨sound417,List.forall_mem_cons.mpr ⟨sound418,List.forall_mem_cons.mpr ⟨sound419,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch020
