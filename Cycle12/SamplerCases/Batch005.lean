import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch005
import Cycle12.CertifiedGlobalFailures.Batch005
import Cycle12.CutFailureCertificates.Budget010
import Cycle12.CutFailureCertificates.Budget011
import Cycle12.DegreeCertificates.Batch005
import Cycle12.GeometryCertificates.Batch010
import Cycle12.GeometryCertificates.Batch011
import Cycle12.MomentCertificates.Batch005
import Cycle12.WitnessCertificates.Batch010
import Cycle12.WitnessCertificates.Batch011

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch005
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate100 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate100,DegreeCertificates.Batch005.certificate100,(WitnessCertificates.Batch010.certificate200).beta,(WitnessCertificates.Batch010.certificate201).L,none,(CutFailureCertificates.Budget010.certificate200).bound,(CutFailureCertificates.Budget010.certificate201).bound,0⟩
theorem numericValid100 : certificate100.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound100 : certificate100.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch010.certificate200 H MomentCertificates.Batch005.valid100.1 GeometryCertificates.Batch010.valid200 GeometryCertificates.Batch010.sound200 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch010.certificate201 H MomentCertificates.Batch005.valid100.1 GeometryCertificates.Batch010.valid201 GeometryCertificates.Batch010.sound201 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound100 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound100 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate100 GeometryCertificates.Batch010.certificate200 numericValid100
    MomentCertificates.Batch005.valid100 DegreeCertificates.Batch005.valid100 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate100,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate101 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate101,DegreeCertificates.Batch005.certificate101,(WitnessCertificates.Batch010.certificate202).beta,(WitnessCertificates.Batch010.certificate203).L,none,(CutFailureCertificates.Budget010.certificate202).bound,(CutFailureCertificates.Budget010.certificate203).bound,0⟩
theorem numericValid101 : certificate101.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound101 : certificate101.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch010.certificate202 H MomentCertificates.Batch005.valid101.1 GeometryCertificates.Batch010.valid202 GeometryCertificates.Batch010.sound202 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch010.certificate203 H MomentCertificates.Batch005.valid101.1 GeometryCertificates.Batch010.valid203 GeometryCertificates.Batch010.sound203 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound101 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound101 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate101 GeometryCertificates.Batch010.certificate202 numericValid101
    MomentCertificates.Batch005.valid101 DegreeCertificates.Batch005.valid101 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate101,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate102 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate102,DegreeCertificates.Batch005.certificate102,(WitnessCertificates.Batch010.certificate204).beta,(WitnessCertificates.Batch010.certificate205).L,none,(CutFailureCertificates.Budget010.certificate204).bound,(CutFailureCertificates.Budget010.certificate205).bound,0⟩
theorem numericValid102 : certificate102.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound102 : certificate102.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch010.certificate204 H MomentCertificates.Batch005.valid102.1 GeometryCertificates.Batch010.valid204 GeometryCertificates.Batch010.sound204 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch010.certificate205 H MomentCertificates.Batch005.valid102.1 GeometryCertificates.Batch010.valid205 GeometryCertificates.Batch010.sound205 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound102 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound102 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate102 GeometryCertificates.Batch010.certificate204 numericValid102
    MomentCertificates.Batch005.valid102 DegreeCertificates.Batch005.valid102 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate102,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate103 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate103,DegreeCertificates.Batch005.certificate103,(WitnessCertificates.Batch010.certificate206).beta,(WitnessCertificates.Batch010.certificate207).L,none,(CutFailureCertificates.Budget010.certificate206).bound,(CutFailureCertificates.Budget010.certificate207).bound,0⟩
theorem numericValid103 : certificate103.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound103 : certificate103.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch010.certificate206 H MomentCertificates.Batch005.valid103.1 GeometryCertificates.Batch010.valid206 GeometryCertificates.Batch010.sound206 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch010.certificate207 H MomentCertificates.Batch005.valid103.1 GeometryCertificates.Batch010.valid207 GeometryCertificates.Batch010.sound207 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound103 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound103 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate103 GeometryCertificates.Batch010.certificate206 numericValid103
    MomentCertificates.Batch005.valid103 DegreeCertificates.Batch005.valid103 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate103,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate104 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate104,DegreeCertificates.Batch005.certificate104,(WitnessCertificates.Batch010.certificate208).beta,(WitnessCertificates.Batch010.certificate209).L,none,(CutFailureCertificates.Budget010.certificate208).bound,(CutFailureCertificates.Budget010.certificate209).bound,0⟩
theorem numericValid104 : certificate104.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound104 : certificate104.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch010.certificate208 H MomentCertificates.Batch005.valid104.1 GeometryCertificates.Batch010.valid208 GeometryCertificates.Batch010.sound208 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch010.certificate209 H MomentCertificates.Batch005.valid104.1 GeometryCertificates.Batch010.valid209 GeometryCertificates.Batch010.sound209 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound104 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound104 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate104 GeometryCertificates.Batch010.certificate208 numericValid104
    MomentCertificates.Batch005.valid104 DegreeCertificates.Batch005.valid104 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate104,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate105 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate105,DegreeCertificates.Batch005.certificate105,(WitnessCertificates.Batch010.certificate210).beta,(WitnessCertificates.Batch010.certificate211).L,none,(CutFailureCertificates.Budget010.certificate210).bound,(CutFailureCertificates.Budget010.certificate211).bound,0⟩
theorem numericValid105 : certificate105.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound105 : certificate105.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch010.certificate210 H MomentCertificates.Batch005.valid105.1 GeometryCertificates.Batch010.valid210 GeometryCertificates.Batch010.sound210 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch010.certificate211 H MomentCertificates.Batch005.valid105.1 GeometryCertificates.Batch010.valid211 GeometryCertificates.Batch010.sound211 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound105 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound105 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate105 GeometryCertificates.Batch010.certificate210 numericValid105
    MomentCertificates.Batch005.valid105 DegreeCertificates.Batch005.valid105 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate105,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate106 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate106,DegreeCertificates.Batch005.certificate106,(WitnessCertificates.Batch010.certificate212).beta,(WitnessCertificates.Batch010.certificate213).L,none,(CutFailureCertificates.Budget010.certificate212).bound,(CutFailureCertificates.Budget010.certificate213).bound,0⟩
theorem numericValid106 : certificate106.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound106 : certificate106.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch010.certificate212 H MomentCertificates.Batch005.valid106.1 GeometryCertificates.Batch010.valid212 GeometryCertificates.Batch010.sound212 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch010.certificate213 H MomentCertificates.Batch005.valid106.1 GeometryCertificates.Batch010.valid213 GeometryCertificates.Batch010.sound213 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound106 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound106 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate106 GeometryCertificates.Batch010.certificate212 numericValid106
    MomentCertificates.Batch005.valid106 DegreeCertificates.Batch005.valid106 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate106,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate107 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate107,DegreeCertificates.Batch005.certificate107,(WitnessCertificates.Batch010.certificate214).beta,(WitnessCertificates.Batch010.certificate215).L,none,(CutFailureCertificates.Budget010.certificate214).bound,(CutFailureCertificates.Budget010.certificate215).bound,0⟩
theorem numericValid107 : certificate107.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound107 : certificate107.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch010.certificate214 H MomentCertificates.Batch005.valid107.1 GeometryCertificates.Batch010.valid214 GeometryCertificates.Batch010.sound214 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch010.certificate215 H MomentCertificates.Batch005.valid107.1 GeometryCertificates.Batch010.valid215 GeometryCertificates.Batch010.sound215 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound107 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound107 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate107 GeometryCertificates.Batch010.certificate214 numericValid107
    MomentCertificates.Batch005.valid107 DegreeCertificates.Batch005.valid107 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate107,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate108 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate108,DegreeCertificates.Batch005.certificate108,(WitnessCertificates.Batch010.certificate216).beta,(WitnessCertificates.Batch010.certificate217).L,none,(CutFailureCertificates.Budget010.certificate216).bound,(CutFailureCertificates.Budget010.certificate217).bound,0⟩
theorem numericValid108 : certificate108.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound108 : certificate108.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch010.certificate216 H MomentCertificates.Batch005.valid108.1 GeometryCertificates.Batch010.valid216 GeometryCertificates.Batch010.sound216 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch010.certificate217 H MomentCertificates.Batch005.valid108.1 GeometryCertificates.Batch010.valid217 GeometryCertificates.Batch010.sound217 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound108 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound108 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate108 GeometryCertificates.Batch010.certificate216 numericValid108
    MomentCertificates.Batch005.valid108 DegreeCertificates.Batch005.valid108 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate108,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate109 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate109,DegreeCertificates.Batch005.certificate109,(WitnessCertificates.Batch010.certificate218).beta,(WitnessCertificates.Batch010.certificate219).L,none,(CutFailureCertificates.Budget010.certificate218).bound,(CutFailureCertificates.Budget010.certificate219).bound,0⟩
theorem numericValid109 : certificate109.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound109 : certificate109.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch010.certificate218 H MomentCertificates.Batch005.valid109.1 GeometryCertificates.Batch010.valid218 GeometryCertificates.Batch010.sound218 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch010.certificate219 H MomentCertificates.Batch005.valid109.1 GeometryCertificates.Batch010.valid219 GeometryCertificates.Batch010.sound219 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound109 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound109 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate109 GeometryCertificates.Batch010.certificate218 numericValid109
    MomentCertificates.Batch005.valid109 DegreeCertificates.Batch005.valid109 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate109,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate110 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate110,DegreeCertificates.Batch005.certificate110,(WitnessCertificates.Batch011.certificate220).beta,(WitnessCertificates.Batch011.certificate221).L,none,(CutFailureCertificates.Budget011.certificate220).bound,(CutFailureCertificates.Budget011.certificate221).bound,0⟩
theorem numericValid110 : certificate110.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound110 : certificate110.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch011.certificate220 H MomentCertificates.Batch005.valid110.1 GeometryCertificates.Batch011.valid220 GeometryCertificates.Batch011.sound220 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch011.certificate221 H MomentCertificates.Batch005.valid110.1 GeometryCertificates.Batch011.valid221 GeometryCertificates.Batch011.sound221 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound110 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound110 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate110 GeometryCertificates.Batch011.certificate220 numericValid110
    MomentCertificates.Batch005.valid110 DegreeCertificates.Batch005.valid110 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate110,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate111 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate111,DegreeCertificates.Batch005.certificate111,(WitnessCertificates.Batch011.certificate222).beta,(WitnessCertificates.Batch011.certificate223).L,none,(CutFailureCertificates.Budget011.certificate222).bound,(CutFailureCertificates.Budget011.certificate223).bound,0⟩
theorem numericValid111 : certificate111.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound111 : certificate111.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch011.certificate222 H MomentCertificates.Batch005.valid111.1 GeometryCertificates.Batch011.valid222 GeometryCertificates.Batch011.sound222 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch011.certificate223 H MomentCertificates.Batch005.valid111.1 GeometryCertificates.Batch011.valid223 GeometryCertificates.Batch011.sound223 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound111 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound111 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate111 GeometryCertificates.Batch011.certificate222 numericValid111
    MomentCertificates.Batch005.valid111 DegreeCertificates.Batch005.valid111 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate111,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate112 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate112,DegreeCertificates.Batch005.certificate112,(WitnessCertificates.Batch011.certificate224).beta,(WitnessCertificates.Batch011.certificate225).L,none,(CutFailureCertificates.Budget011.certificate224).bound,(CutFailureCertificates.Budget011.certificate225).bound,0⟩
theorem numericValid112 : certificate112.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound112 : certificate112.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch011.certificate224 H MomentCertificates.Batch005.valid112.1 GeometryCertificates.Batch011.valid224 GeometryCertificates.Batch011.sound224 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch011.certificate225 H MomentCertificates.Batch005.valid112.1 GeometryCertificates.Batch011.valid225 GeometryCertificates.Batch011.sound225 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound112 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound112 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate112 GeometryCertificates.Batch011.certificate224 numericValid112
    MomentCertificates.Batch005.valid112 DegreeCertificates.Batch005.valid112 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate112,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate113 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate113,DegreeCertificates.Batch005.certificate113,(WitnessCertificates.Batch011.certificate226).beta,(WitnessCertificates.Batch011.certificate227).L,none,(CutFailureCertificates.Budget011.certificate226).bound,(CutFailureCertificates.Budget011.certificate227).bound,0⟩
theorem numericValid113 : certificate113.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound113 : certificate113.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch011.certificate226 H MomentCertificates.Batch005.valid113.1 GeometryCertificates.Batch011.valid226 GeometryCertificates.Batch011.sound226 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch011.certificate227 H MomentCertificates.Batch005.valid113.1 GeometryCertificates.Batch011.valid227 GeometryCertificates.Batch011.sound227 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound113 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound113 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate113 GeometryCertificates.Batch011.certificate226 numericValid113
    MomentCertificates.Batch005.valid113 DegreeCertificates.Batch005.valid113 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate113,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate114 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate114,DegreeCertificates.Batch005.certificate114,(WitnessCertificates.Batch011.certificate228).beta,(WitnessCertificates.Batch011.certificate229).L,none,(CutFailureCertificates.Budget011.certificate228).bound,(CutFailureCertificates.Budget011.certificate229).bound,0⟩
theorem numericValid114 : certificate114.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound114 : certificate114.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch011.certificate228 H MomentCertificates.Batch005.valid114.1 GeometryCertificates.Batch011.valid228 GeometryCertificates.Batch011.sound228 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch011.certificate229 H MomentCertificates.Batch005.valid114.1 GeometryCertificates.Batch011.valid229 GeometryCertificates.Batch011.sound229 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound114 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound114 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate114 GeometryCertificates.Batch011.certificate228 numericValid114
    MomentCertificates.Batch005.valid114 DegreeCertificates.Batch005.valid114 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate114,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate115 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate115,DegreeCertificates.Batch005.certificate115,(WitnessCertificates.Batch011.certificate230).beta,(WitnessCertificates.Batch011.certificate231).L,none,(CutFailureCertificates.Budget011.certificate230).bound,(CutFailureCertificates.Budget011.certificate231).bound,0⟩
theorem numericValid115 : certificate115.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound115 : certificate115.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch011.certificate230 H MomentCertificates.Batch005.valid115.1 GeometryCertificates.Batch011.valid230 GeometryCertificates.Batch011.sound230 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch011.certificate231 H MomentCertificates.Batch005.valid115.1 GeometryCertificates.Batch011.valid231 GeometryCertificates.Batch011.sound231 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound115 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound115 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate115 GeometryCertificates.Batch011.certificate230 numericValid115
    MomentCertificates.Batch005.valid115 DegreeCertificates.Batch005.valid115 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate115,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate116 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate116,DegreeCertificates.Batch005.certificate116,(WitnessCertificates.Batch011.certificate232).beta,(WitnessCertificates.Batch011.certificate233).L,none,(CutFailureCertificates.Budget011.certificate232).bound,(CutFailureCertificates.Budget011.certificate233).bound,0⟩
theorem numericValid116 : certificate116.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound116 : certificate116.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch011.certificate232 H MomentCertificates.Batch005.valid116.1 GeometryCertificates.Batch011.valid232 GeometryCertificates.Batch011.sound232 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch011.certificate233 H MomentCertificates.Batch005.valid116.1 GeometryCertificates.Batch011.valid233 GeometryCertificates.Batch011.sound233 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound116 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound116 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate116 GeometryCertificates.Batch011.certificate232 numericValid116
    MomentCertificates.Batch005.valid116 DegreeCertificates.Batch005.valid116 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate116,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate117 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate117,DegreeCertificates.Batch005.certificate117,(WitnessCertificates.Batch011.certificate234).beta,(WitnessCertificates.Batch011.certificate235).L,none,(CutFailureCertificates.Budget011.certificate234).bound,(CutFailureCertificates.Budget011.certificate235).bound,0⟩
theorem numericValid117 : certificate117.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound117 : certificate117.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch011.certificate234 H MomentCertificates.Batch005.valid117.1 GeometryCertificates.Batch011.valid234 GeometryCertificates.Batch011.sound234 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch011.certificate235 H MomentCertificates.Batch005.valid117.1 GeometryCertificates.Batch011.valid235 GeometryCertificates.Batch011.sound235 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound117 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound117 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate117 GeometryCertificates.Batch011.certificate234 numericValid117
    MomentCertificates.Batch005.valid117 DegreeCertificates.Batch005.valid117 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate117,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate118 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate118,DegreeCertificates.Batch005.certificate118,(WitnessCertificates.Batch011.certificate236).beta,(WitnessCertificates.Batch011.certificate237).L,none,(CutFailureCertificates.Budget011.certificate236).bound,(CutFailureCertificates.Budget011.certificate237).bound,0⟩
theorem numericValid118 : certificate118.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound118 : certificate118.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch011.certificate236 H MomentCertificates.Batch005.valid118.1 GeometryCertificates.Batch011.valid236 GeometryCertificates.Batch011.sound236 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch011.certificate237 H MomentCertificates.Batch005.valid118.1 GeometryCertificates.Batch011.valid237 GeometryCertificates.Batch011.sound237 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound118 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound118 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate118 GeometryCertificates.Batch011.certificate236 numericValid118
    MomentCertificates.Batch005.valid118 DegreeCertificates.Batch005.valid118 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate118,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate119 : RatSamplerCase := ⟨MomentCertificates.Batch005.certificate119,DegreeCertificates.Batch005.certificate119,(WitnessCertificates.Batch011.certificate238).beta,(WitnessCertificates.Batch011.certificate239).L,none,(CutFailureCertificates.Budget011.certificate238).bound,(CutFailureCertificates.Budget011.certificate239).bound,0⟩
theorem numericValid119 : certificate119.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound119 : certificate119.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch011.certificate238 H MomentCertificates.Batch005.valid119.1 GeometryCertificates.Batch011.valid238 GeometryCertificates.Batch011.sound238 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch011.certificate239 H MomentCertificates.Batch005.valid119.1 GeometryCertificates.Batch011.valid239 GeometryCertificates.Batch011.sound239 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch005.probabilityBound119 H st hI
  have hanchor := CertifiedAnchorFailures.Batch005.probabilityBound119 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate119 GeometryCertificates.Batch011.certificate238 numericValid119
    MomentCertificates.Batch005.valid119 DegreeCertificates.Batch005.valid119 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate119,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate100,certificate101,certificate102,certificate103,certificate104,certificate105,certificate106,certificate107,certificate108,certificate109,certificate110,certificate111,certificate112,certificate113,certificate114,certificate115,certificate116,certificate117,certificate118,certificate119]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound100,List.forall_mem_cons.mpr ⟨sound101,List.forall_mem_cons.mpr ⟨sound102,List.forall_mem_cons.mpr ⟨sound103,List.forall_mem_cons.mpr ⟨sound104,List.forall_mem_cons.mpr ⟨sound105,List.forall_mem_cons.mpr ⟨sound106,List.forall_mem_cons.mpr ⟨sound107,List.forall_mem_cons.mpr ⟨sound108,List.forall_mem_cons.mpr ⟨sound109,List.forall_mem_cons.mpr ⟨sound110,List.forall_mem_cons.mpr ⟨sound111,List.forall_mem_cons.mpr ⟨sound112,List.forall_mem_cons.mpr ⟨sound113,List.forall_mem_cons.mpr ⟨sound114,List.forall_mem_cons.mpr ⟨sound115,List.forall_mem_cons.mpr ⟨sound116,List.forall_mem_cons.mpr ⟨sound117,List.forall_mem_cons.mpr ⟨sound118,List.forall_mem_cons.mpr ⟨sound119,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch005
