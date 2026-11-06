import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch006
import Cycle12.CertifiedGlobalFailures.Batch006
import Cycle12.CutFailureCertificates.Budget012
import Cycle12.CutFailureCertificates.Budget013
import Cycle12.DegreeCertificates.Batch006
import Cycle12.GeometryCertificates.Batch012
import Cycle12.GeometryCertificates.Batch013
import Cycle12.MomentCertificates.Batch006
import Cycle12.WitnessCertificates.Batch012
import Cycle12.WitnessCertificates.Batch013

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch006
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate120 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate120,DegreeCertificates.Batch006.certificate120,(WitnessCertificates.Batch012.certificate240).beta,(WitnessCertificates.Batch012.certificate241).L,none,(CutFailureCertificates.Budget012.certificate240).bound,(CutFailureCertificates.Budget012.certificate241).bound,0⟩
theorem numericValid120 : certificate120.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound120 : certificate120.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch012.certificate240 H MomentCertificates.Batch006.valid120.1 GeometryCertificates.Batch012.valid240 GeometryCertificates.Batch012.sound240 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch012.certificate241 H MomentCertificates.Batch006.valid120.1 GeometryCertificates.Batch012.valid241 GeometryCertificates.Batch012.sound241 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound120 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound120 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate120 GeometryCertificates.Batch012.certificate240 numericValid120
    MomentCertificates.Batch006.valid120 DegreeCertificates.Batch006.valid120 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate120,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate121 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate121,DegreeCertificates.Batch006.certificate121,(WitnessCertificates.Batch012.certificate242).beta,(WitnessCertificates.Batch012.certificate243).L,none,(CutFailureCertificates.Budget012.certificate242).bound,(CutFailureCertificates.Budget012.certificate243).bound,0⟩
theorem numericValid121 : certificate121.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound121 : certificate121.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch012.certificate242 H MomentCertificates.Batch006.valid121.1 GeometryCertificates.Batch012.valid242 GeometryCertificates.Batch012.sound242 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch012.certificate243 H MomentCertificates.Batch006.valid121.1 GeometryCertificates.Batch012.valid243 GeometryCertificates.Batch012.sound243 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound121 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound121 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate121 GeometryCertificates.Batch012.certificate242 numericValid121
    MomentCertificates.Batch006.valid121 DegreeCertificates.Batch006.valid121 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate121,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate122 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate122,DegreeCertificates.Batch006.certificate122,(WitnessCertificates.Batch012.certificate244).beta,(WitnessCertificates.Batch012.certificate245).L,none,(CutFailureCertificates.Budget012.certificate244).bound,(CutFailureCertificates.Budget012.certificate245).bound,0⟩
theorem numericValid122 : certificate122.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound122 : certificate122.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch012.certificate244 H MomentCertificates.Batch006.valid122.1 GeometryCertificates.Batch012.valid244 GeometryCertificates.Batch012.sound244 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch012.certificate245 H MomentCertificates.Batch006.valid122.1 GeometryCertificates.Batch012.valid245 GeometryCertificates.Batch012.sound245 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound122 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound122 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate122 GeometryCertificates.Batch012.certificate244 numericValid122
    MomentCertificates.Batch006.valid122 DegreeCertificates.Batch006.valid122 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate122,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate123 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate123,DegreeCertificates.Batch006.certificate123,(WitnessCertificates.Batch012.certificate246).beta,(WitnessCertificates.Batch012.certificate247).L,none,(CutFailureCertificates.Budget012.certificate246).bound,(CutFailureCertificates.Budget012.certificate247).bound,0⟩
theorem numericValid123 : certificate123.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound123 : certificate123.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch012.certificate246 H MomentCertificates.Batch006.valid123.1 GeometryCertificates.Batch012.valid246 GeometryCertificates.Batch012.sound246 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch012.certificate247 H MomentCertificates.Batch006.valid123.1 GeometryCertificates.Batch012.valid247 GeometryCertificates.Batch012.sound247 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound123 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound123 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate123 GeometryCertificates.Batch012.certificate246 numericValid123
    MomentCertificates.Batch006.valid123 DegreeCertificates.Batch006.valid123 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate123,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate124 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate124,DegreeCertificates.Batch006.certificate124,(WitnessCertificates.Batch012.certificate248).beta,(WitnessCertificates.Batch012.certificate249).L,none,(CutFailureCertificates.Budget012.certificate248).bound,(CutFailureCertificates.Budget012.certificate249).bound,0⟩
theorem numericValid124 : certificate124.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound124 : certificate124.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch012.certificate248 H MomentCertificates.Batch006.valid124.1 GeometryCertificates.Batch012.valid248 GeometryCertificates.Batch012.sound248 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch012.certificate249 H MomentCertificates.Batch006.valid124.1 GeometryCertificates.Batch012.valid249 GeometryCertificates.Batch012.sound249 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound124 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound124 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate124 GeometryCertificates.Batch012.certificate248 numericValid124
    MomentCertificates.Batch006.valid124 DegreeCertificates.Batch006.valid124 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate124,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate125 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate125,DegreeCertificates.Batch006.certificate125,(WitnessCertificates.Batch012.certificate250).beta,(WitnessCertificates.Batch012.certificate251).L,none,(CutFailureCertificates.Budget012.certificate250).bound,(CutFailureCertificates.Budget012.certificate251).bound,0⟩
theorem numericValid125 : certificate125.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound125 : certificate125.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch012.certificate250 H MomentCertificates.Batch006.valid125.1 GeometryCertificates.Batch012.valid250 GeometryCertificates.Batch012.sound250 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch012.certificate251 H MomentCertificates.Batch006.valid125.1 GeometryCertificates.Batch012.valid251 GeometryCertificates.Batch012.sound251 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound125 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound125 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate125 GeometryCertificates.Batch012.certificate250 numericValid125
    MomentCertificates.Batch006.valid125 DegreeCertificates.Batch006.valid125 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate125,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate126 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate126,DegreeCertificates.Batch006.certificate126,(WitnessCertificates.Batch012.certificate252).beta,(WitnessCertificates.Batch012.certificate253).L,none,(CutFailureCertificates.Budget012.certificate252).bound,(CutFailureCertificates.Budget012.certificate253).bound,0⟩
theorem numericValid126 : certificate126.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound126 : certificate126.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch012.certificate252 H MomentCertificates.Batch006.valid126.1 GeometryCertificates.Batch012.valid252 GeometryCertificates.Batch012.sound252 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch012.certificate253 H MomentCertificates.Batch006.valid126.1 GeometryCertificates.Batch012.valid253 GeometryCertificates.Batch012.sound253 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound126 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound126 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate126 GeometryCertificates.Batch012.certificate252 numericValid126
    MomentCertificates.Batch006.valid126 DegreeCertificates.Batch006.valid126 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate126,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate127 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate127,DegreeCertificates.Batch006.certificate127,(WitnessCertificates.Batch012.certificate254).beta,(WitnessCertificates.Batch012.certificate255).L,none,(CutFailureCertificates.Budget012.certificate254).bound,(CutFailureCertificates.Budget012.certificate255).bound,0⟩
theorem numericValid127 : certificate127.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound127 : certificate127.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch012.certificate254 H MomentCertificates.Batch006.valid127.1 GeometryCertificates.Batch012.valid254 GeometryCertificates.Batch012.sound254 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch012.certificate255 H MomentCertificates.Batch006.valid127.1 GeometryCertificates.Batch012.valid255 GeometryCertificates.Batch012.sound255 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound127 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound127 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate127 GeometryCertificates.Batch012.certificate254 numericValid127
    MomentCertificates.Batch006.valid127 DegreeCertificates.Batch006.valid127 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate127,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate128 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate128,DegreeCertificates.Batch006.certificate128,(WitnessCertificates.Batch012.certificate256).beta,(WitnessCertificates.Batch012.certificate257).L,none,(CutFailureCertificates.Budget012.certificate256).bound,(CutFailureCertificates.Budget012.certificate257).bound,0⟩
theorem numericValid128 : certificate128.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound128 : certificate128.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch012.certificate256 H MomentCertificates.Batch006.valid128.1 GeometryCertificates.Batch012.valid256 GeometryCertificates.Batch012.sound256 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch012.certificate257 H MomentCertificates.Batch006.valid128.1 GeometryCertificates.Batch012.valid257 GeometryCertificates.Batch012.sound257 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound128 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound128 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate128 GeometryCertificates.Batch012.certificate256 numericValid128
    MomentCertificates.Batch006.valid128 DegreeCertificates.Batch006.valid128 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate128,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate129 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate129,DegreeCertificates.Batch006.certificate129,(WitnessCertificates.Batch012.certificate258).beta,(WitnessCertificates.Batch012.certificate259).L,none,(CutFailureCertificates.Budget012.certificate258).bound,(CutFailureCertificates.Budget012.certificate259).bound,0⟩
theorem numericValid129 : certificate129.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound129 : certificate129.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch012.certificate258 H MomentCertificates.Batch006.valid129.1 GeometryCertificates.Batch012.valid258 GeometryCertificates.Batch012.sound258 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch012.certificate259 H MomentCertificates.Batch006.valid129.1 GeometryCertificates.Batch012.valid259 GeometryCertificates.Batch012.sound259 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound129 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound129 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate129 GeometryCertificates.Batch012.certificate258 numericValid129
    MomentCertificates.Batch006.valid129 DegreeCertificates.Batch006.valid129 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate129,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate130 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate130,DegreeCertificates.Batch006.certificate130,(WitnessCertificates.Batch013.certificate260).beta,(WitnessCertificates.Batch013.certificate261).L,none,(CutFailureCertificates.Budget013.certificate260).bound,(CutFailureCertificates.Budget013.certificate261).bound,0⟩
theorem numericValid130 : certificate130.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound130 : certificate130.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch013.certificate260 H MomentCertificates.Batch006.valid130.1 GeometryCertificates.Batch013.valid260 GeometryCertificates.Batch013.sound260 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch013.certificate261 H MomentCertificates.Batch006.valid130.1 GeometryCertificates.Batch013.valid261 GeometryCertificates.Batch013.sound261 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound130 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound130 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate130 GeometryCertificates.Batch013.certificate260 numericValid130
    MomentCertificates.Batch006.valid130 DegreeCertificates.Batch006.valid130 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate130,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate131 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate131,DegreeCertificates.Batch006.certificate131,(WitnessCertificates.Batch013.certificate262).beta,(WitnessCertificates.Batch013.certificate263).L,none,(CutFailureCertificates.Budget013.certificate262).bound,(CutFailureCertificates.Budget013.certificate263).bound,0⟩
theorem numericValid131 : certificate131.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound131 : certificate131.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch013.certificate262 H MomentCertificates.Batch006.valid131.1 GeometryCertificates.Batch013.valid262 GeometryCertificates.Batch013.sound262 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch013.certificate263 H MomentCertificates.Batch006.valid131.1 GeometryCertificates.Batch013.valid263 GeometryCertificates.Batch013.sound263 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound131 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound131 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate131 GeometryCertificates.Batch013.certificate262 numericValid131
    MomentCertificates.Batch006.valid131 DegreeCertificates.Batch006.valid131 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate131,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate132 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate132,DegreeCertificates.Batch006.certificate132,(WitnessCertificates.Batch013.certificate264).beta,(WitnessCertificates.Batch013.certificate265).L,none,(CutFailureCertificates.Budget013.certificate264).bound,(CutFailureCertificates.Budget013.certificate265).bound,0⟩
theorem numericValid132 : certificate132.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound132 : certificate132.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch013.certificate264 H MomentCertificates.Batch006.valid132.1 GeometryCertificates.Batch013.valid264 GeometryCertificates.Batch013.sound264 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch013.certificate265 H MomentCertificates.Batch006.valid132.1 GeometryCertificates.Batch013.valid265 GeometryCertificates.Batch013.sound265 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound132 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound132 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate132 GeometryCertificates.Batch013.certificate264 numericValid132
    MomentCertificates.Batch006.valid132 DegreeCertificates.Batch006.valid132 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate132,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate133 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate133,DegreeCertificates.Batch006.certificate133,(WitnessCertificates.Batch013.certificate266).beta,(WitnessCertificates.Batch013.certificate267).L,none,(CutFailureCertificates.Budget013.certificate266).bound,(CutFailureCertificates.Budget013.certificate267).bound,0⟩
theorem numericValid133 : certificate133.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound133 : certificate133.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch013.certificate266 H MomentCertificates.Batch006.valid133.1 GeometryCertificates.Batch013.valid266 GeometryCertificates.Batch013.sound266 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch013.certificate267 H MomentCertificates.Batch006.valid133.1 GeometryCertificates.Batch013.valid267 GeometryCertificates.Batch013.sound267 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound133 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound133 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate133 GeometryCertificates.Batch013.certificate266 numericValid133
    MomentCertificates.Batch006.valid133 DegreeCertificates.Batch006.valid133 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate133,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate134 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate134,DegreeCertificates.Batch006.certificate134,(WitnessCertificates.Batch013.certificate268).beta,(WitnessCertificates.Batch013.certificate269).L,none,(CutFailureCertificates.Budget013.certificate268).bound,(CutFailureCertificates.Budget013.certificate269).bound,0⟩
theorem numericValid134 : certificate134.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound134 : certificate134.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch013.certificate268 H MomentCertificates.Batch006.valid134.1 GeometryCertificates.Batch013.valid268 GeometryCertificates.Batch013.sound268 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch013.certificate269 H MomentCertificates.Batch006.valid134.1 GeometryCertificates.Batch013.valid269 GeometryCertificates.Batch013.sound269 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound134 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound134 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate134 GeometryCertificates.Batch013.certificate268 numericValid134
    MomentCertificates.Batch006.valid134 DegreeCertificates.Batch006.valid134 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate134,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate135 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate135,DegreeCertificates.Batch006.certificate135,(WitnessCertificates.Batch013.certificate270).beta,(WitnessCertificates.Batch013.certificate271).L,none,(CutFailureCertificates.Budget013.certificate270).bound,(CutFailureCertificates.Budget013.certificate271).bound,0⟩
theorem numericValid135 : certificate135.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound135 : certificate135.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch013.certificate270 H MomentCertificates.Batch006.valid135.1 GeometryCertificates.Batch013.valid270 GeometryCertificates.Batch013.sound270 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch013.certificate271 H MomentCertificates.Batch006.valid135.1 GeometryCertificates.Batch013.valid271 GeometryCertificates.Batch013.sound271 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound135 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound135 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate135 GeometryCertificates.Batch013.certificate270 numericValid135
    MomentCertificates.Batch006.valid135 DegreeCertificates.Batch006.valid135 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate135,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate136 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate136,DegreeCertificates.Batch006.certificate136,(WitnessCertificates.Batch013.certificate272).beta,(WitnessCertificates.Batch013.certificate273).L,none,(CutFailureCertificates.Budget013.certificate272).bound,(CutFailureCertificates.Budget013.certificate273).bound,0⟩
theorem numericValid136 : certificate136.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound136 : certificate136.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch013.certificate272 H MomentCertificates.Batch006.valid136.1 GeometryCertificates.Batch013.valid272 GeometryCertificates.Batch013.sound272 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch013.certificate273 H MomentCertificates.Batch006.valid136.1 GeometryCertificates.Batch013.valid273 GeometryCertificates.Batch013.sound273 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound136 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound136 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate136 GeometryCertificates.Batch013.certificate272 numericValid136
    MomentCertificates.Batch006.valid136 DegreeCertificates.Batch006.valid136 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate136,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate137 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate137,DegreeCertificates.Batch006.certificate137,(WitnessCertificates.Batch013.certificate274).beta,(WitnessCertificates.Batch013.certificate275).L,none,(CutFailureCertificates.Budget013.certificate274).bound,(CutFailureCertificates.Budget013.certificate275).bound,0⟩
theorem numericValid137 : certificate137.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound137 : certificate137.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch013.certificate274 H MomentCertificates.Batch006.valid137.1 GeometryCertificates.Batch013.valid274 GeometryCertificates.Batch013.sound274 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch013.certificate275 H MomentCertificates.Batch006.valid137.1 GeometryCertificates.Batch013.valid275 GeometryCertificates.Batch013.sound275 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound137 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound137 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate137 GeometryCertificates.Batch013.certificate274 numericValid137
    MomentCertificates.Batch006.valid137 DegreeCertificates.Batch006.valid137 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate137,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate138 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate138,DegreeCertificates.Batch006.certificate138,(WitnessCertificates.Batch013.certificate276).beta,(WitnessCertificates.Batch013.certificate277).L,none,(CutFailureCertificates.Budget013.certificate276).bound,(CutFailureCertificates.Budget013.certificate277).bound,0⟩
theorem numericValid138 : certificate138.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound138 : certificate138.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch013.certificate276 H MomentCertificates.Batch006.valid138.1 GeometryCertificates.Batch013.valid276 GeometryCertificates.Batch013.sound276 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch013.certificate277 H MomentCertificates.Batch006.valid138.1 GeometryCertificates.Batch013.valid277 GeometryCertificates.Batch013.sound277 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound138 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound138 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate138 GeometryCertificates.Batch013.certificate276 numericValid138
    MomentCertificates.Batch006.valid138 DegreeCertificates.Batch006.valid138 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate138,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate139 : RatSamplerCase := ⟨MomentCertificates.Batch006.certificate139,DegreeCertificates.Batch006.certificate139,(WitnessCertificates.Batch013.certificate278).beta,(WitnessCertificates.Batch013.certificate279).L,none,(CutFailureCertificates.Budget013.certificate278).bound,(CutFailureCertificates.Budget013.certificate279).bound,0⟩
theorem numericValid139 : certificate139.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound139 : certificate139.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch013.certificate278 H MomentCertificates.Batch006.valid139.1 GeometryCertificates.Batch013.valid278 GeometryCertificates.Batch013.sound278 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch013.certificate279 H MomentCertificates.Batch006.valid139.1 GeometryCertificates.Batch013.valid279 GeometryCertificates.Batch013.sound279 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch006.probabilityBound139 H st hI
  have hanchor := CertifiedAnchorFailures.Batch006.probabilityBound139 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate139 GeometryCertificates.Batch013.certificate278 numericValid139
    MomentCertificates.Batch006.valid139 DegreeCertificates.Batch006.valid139 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate139,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate120,certificate121,certificate122,certificate123,certificate124,certificate125,certificate126,certificate127,certificate128,certificate129,certificate130,certificate131,certificate132,certificate133,certificate134,certificate135,certificate136,certificate137,certificate138,certificate139]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound120,List.forall_mem_cons.mpr ⟨sound121,List.forall_mem_cons.mpr ⟨sound122,List.forall_mem_cons.mpr ⟨sound123,List.forall_mem_cons.mpr ⟨sound124,List.forall_mem_cons.mpr ⟨sound125,List.forall_mem_cons.mpr ⟨sound126,List.forall_mem_cons.mpr ⟨sound127,List.forall_mem_cons.mpr ⟨sound128,List.forall_mem_cons.mpr ⟨sound129,List.forall_mem_cons.mpr ⟨sound130,List.forall_mem_cons.mpr ⟨sound131,List.forall_mem_cons.mpr ⟨sound132,List.forall_mem_cons.mpr ⟨sound133,List.forall_mem_cons.mpr ⟨sound134,List.forall_mem_cons.mpr ⟨sound135,List.forall_mem_cons.mpr ⟨sound136,List.forall_mem_cons.mpr ⟨sound137,List.forall_mem_cons.mpr ⟨sound138,List.forall_mem_cons.mpr ⟨sound139,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch006
