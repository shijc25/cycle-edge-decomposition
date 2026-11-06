import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch000
import Cycle12.CertifiedGlobalFailures.Batch000
import Cycle12.CutFailureCertificates.Budget000
import Cycle12.CutFailureCertificates.Budget001
import Cycle12.DegreeCertificates.Batch000
import Cycle12.GeometryCertificates.Batch000
import Cycle12.GeometryCertificates.Batch001
import Cycle12.MomentCertificates.Batch000
import Cycle12.WitnessCertificates.Batch000
import Cycle12.WitnessCertificates.Batch001

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch000
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate0 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate0,DegreeCertificates.Batch000.certificate0,(WitnessCertificates.Batch000.certificate0).beta,(WitnessCertificates.Batch000.certificate1).L,none,(CutFailureCertificates.Budget000.certificate0).bound,(CutFailureCertificates.Budget000.certificate1).bound,0⟩
theorem numericValid0 : certificate0.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound0 : certificate0.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch000.certificate0 H MomentCertificates.Batch000.valid0.1 GeometryCertificates.Batch000.valid0 GeometryCertificates.Batch000.sound0 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch000.certificate1 H MomentCertificates.Batch000.valid0.1 GeometryCertificates.Batch000.valid1 GeometryCertificates.Batch000.sound1 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound0 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound0 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate0 GeometryCertificates.Batch000.certificate0 numericValid0
    MomentCertificates.Batch000.valid0 DegreeCertificates.Batch000.valid0 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate0,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate1 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate1,DegreeCertificates.Batch000.certificate1,(WitnessCertificates.Batch000.certificate2).beta,(WitnessCertificates.Batch000.certificate3).L,none,(CutFailureCertificates.Budget000.certificate2).bound,(CutFailureCertificates.Budget000.certificate3).bound,0⟩
theorem numericValid1 : certificate1.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound1 : certificate1.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch000.certificate2 H MomentCertificates.Batch000.valid1.1 GeometryCertificates.Batch000.valid2 GeometryCertificates.Batch000.sound2 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch000.certificate3 H MomentCertificates.Batch000.valid1.1 GeometryCertificates.Batch000.valid3 GeometryCertificates.Batch000.sound3 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound1 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound1 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate1 GeometryCertificates.Batch000.certificate2 numericValid1
    MomentCertificates.Batch000.valid1 DegreeCertificates.Batch000.valid1 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate1,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate2 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate2,DegreeCertificates.Batch000.certificate2,(WitnessCertificates.Batch000.certificate4).beta,(WitnessCertificates.Batch000.certificate5).L,none,(CutFailureCertificates.Budget000.certificate4).bound,(CutFailureCertificates.Budget000.certificate5).bound,0⟩
theorem numericValid2 : certificate2.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound2 : certificate2.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch000.certificate4 H MomentCertificates.Batch000.valid2.1 GeometryCertificates.Batch000.valid4 GeometryCertificates.Batch000.sound4 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch000.certificate5 H MomentCertificates.Batch000.valid2.1 GeometryCertificates.Batch000.valid5 GeometryCertificates.Batch000.sound5 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound2 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound2 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate2 GeometryCertificates.Batch000.certificate4 numericValid2
    MomentCertificates.Batch000.valid2 DegreeCertificates.Batch000.valid2 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate2,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate3 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate3,DegreeCertificates.Batch000.certificate3,(WitnessCertificates.Batch000.certificate6).beta,(WitnessCertificates.Batch000.certificate7).L,none,(CutFailureCertificates.Budget000.certificate6).bound,(CutFailureCertificates.Budget000.certificate7).bound,0⟩
theorem numericValid3 : certificate3.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound3 : certificate3.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch000.certificate6 H MomentCertificates.Batch000.valid3.1 GeometryCertificates.Batch000.valid6 GeometryCertificates.Batch000.sound6 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch000.certificate7 H MomentCertificates.Batch000.valid3.1 GeometryCertificates.Batch000.valid7 GeometryCertificates.Batch000.sound7 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound3 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound3 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate3 GeometryCertificates.Batch000.certificate6 numericValid3
    MomentCertificates.Batch000.valid3 DegreeCertificates.Batch000.valid3 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate3,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate4 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate4,DegreeCertificates.Batch000.certificate4,(WitnessCertificates.Batch000.certificate8).beta,(WitnessCertificates.Batch000.certificate9).L,none,(CutFailureCertificates.Budget000.certificate8).bound,(CutFailureCertificates.Budget000.certificate9).bound,0⟩
theorem numericValid4 : certificate4.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound4 : certificate4.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch000.certificate8 H MomentCertificates.Batch000.valid4.1 GeometryCertificates.Batch000.valid8 GeometryCertificates.Batch000.sound8 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch000.certificate9 H MomentCertificates.Batch000.valid4.1 GeometryCertificates.Batch000.valid9 GeometryCertificates.Batch000.sound9 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound4 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound4 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate4 GeometryCertificates.Batch000.certificate8 numericValid4
    MomentCertificates.Batch000.valid4 DegreeCertificates.Batch000.valid4 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate4,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate5 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate5,DegreeCertificates.Batch000.certificate5,(WitnessCertificates.Batch000.certificate10).beta,(WitnessCertificates.Batch000.certificate11).L,none,(CutFailureCertificates.Budget000.certificate10).bound,(CutFailureCertificates.Budget000.certificate11).bound,0⟩
theorem numericValid5 : certificate5.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound5 : certificate5.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch000.certificate10 H MomentCertificates.Batch000.valid5.1 GeometryCertificates.Batch000.valid10 GeometryCertificates.Batch000.sound10 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch000.certificate11 H MomentCertificates.Batch000.valid5.1 GeometryCertificates.Batch000.valid11 GeometryCertificates.Batch000.sound11 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound5 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound5 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate5 GeometryCertificates.Batch000.certificate10 numericValid5
    MomentCertificates.Batch000.valid5 DegreeCertificates.Batch000.valid5 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate5,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate6 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate6,DegreeCertificates.Batch000.certificate6,(WitnessCertificates.Batch000.certificate12).beta,(WitnessCertificates.Batch000.certificate13).L,none,(CutFailureCertificates.Budget000.certificate12).bound,(CutFailureCertificates.Budget000.certificate13).bound,0⟩
theorem numericValid6 : certificate6.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound6 : certificate6.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch000.certificate12 H MomentCertificates.Batch000.valid6.1 GeometryCertificates.Batch000.valid12 GeometryCertificates.Batch000.sound12 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch000.certificate13 H MomentCertificates.Batch000.valid6.1 GeometryCertificates.Batch000.valid13 GeometryCertificates.Batch000.sound13 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound6 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound6 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate6 GeometryCertificates.Batch000.certificate12 numericValid6
    MomentCertificates.Batch000.valid6 DegreeCertificates.Batch000.valid6 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate6,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate7 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate7,DegreeCertificates.Batch000.certificate7,(WitnessCertificates.Batch000.certificate14).beta,(WitnessCertificates.Batch000.certificate15).L,none,(CutFailureCertificates.Budget000.certificate14).bound,(CutFailureCertificates.Budget000.certificate15).bound,0⟩
theorem numericValid7 : certificate7.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound7 : certificate7.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch000.certificate14 H MomentCertificates.Batch000.valid7.1 GeometryCertificates.Batch000.valid14 GeometryCertificates.Batch000.sound14 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch000.certificate15 H MomentCertificates.Batch000.valid7.1 GeometryCertificates.Batch000.valid15 GeometryCertificates.Batch000.sound15 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound7 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound7 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate7 GeometryCertificates.Batch000.certificate14 numericValid7
    MomentCertificates.Batch000.valid7 DegreeCertificates.Batch000.valid7 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate7,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate8 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate8,DegreeCertificates.Batch000.certificate8,(WitnessCertificates.Batch000.certificate16).beta,(WitnessCertificates.Batch000.certificate17).L,none,(CutFailureCertificates.Budget000.certificate16).bound,(CutFailureCertificates.Budget000.certificate17).bound,0⟩
theorem numericValid8 : certificate8.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound8 : certificate8.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch000.certificate16 H MomentCertificates.Batch000.valid8.1 GeometryCertificates.Batch000.valid16 GeometryCertificates.Batch000.sound16 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch000.certificate17 H MomentCertificates.Batch000.valid8.1 GeometryCertificates.Batch000.valid17 GeometryCertificates.Batch000.sound17 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound8 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound8 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate8 GeometryCertificates.Batch000.certificate16 numericValid8
    MomentCertificates.Batch000.valid8 DegreeCertificates.Batch000.valid8 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate8,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate9 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate9,DegreeCertificates.Batch000.certificate9,(WitnessCertificates.Batch000.certificate18).beta,(WitnessCertificates.Batch000.certificate19).L,none,(CutFailureCertificates.Budget000.certificate18).bound,(CutFailureCertificates.Budget000.certificate19).bound,0⟩
theorem numericValid9 : certificate9.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound9 : certificate9.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch000.certificate18 H MomentCertificates.Batch000.valid9.1 GeometryCertificates.Batch000.valid18 GeometryCertificates.Batch000.sound18 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch000.certificate19 H MomentCertificates.Batch000.valid9.1 GeometryCertificates.Batch000.valid19 GeometryCertificates.Batch000.sound19 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound9 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound9 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate9 GeometryCertificates.Batch000.certificate18 numericValid9
    MomentCertificates.Batch000.valid9 DegreeCertificates.Batch000.valid9 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate9,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate10 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate10,DegreeCertificates.Batch000.certificate10,(WitnessCertificates.Batch001.certificate20).beta,(WitnessCertificates.Batch001.certificate21).L,none,(CutFailureCertificates.Budget001.certificate20).bound,(CutFailureCertificates.Budget001.certificate21).bound,0⟩
theorem numericValid10 : certificate10.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound10 : certificate10.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch001.certificate20 H MomentCertificates.Batch000.valid10.1 GeometryCertificates.Batch001.valid20 GeometryCertificates.Batch001.sound20 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch001.certificate21 H MomentCertificates.Batch000.valid10.1 GeometryCertificates.Batch001.valid21 GeometryCertificates.Batch001.sound21 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound10 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound10 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate10 GeometryCertificates.Batch001.certificate20 numericValid10
    MomentCertificates.Batch000.valid10 DegreeCertificates.Batch000.valid10 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate10,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate11 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate11,DegreeCertificates.Batch000.certificate11,(WitnessCertificates.Batch001.certificate22).beta,(WitnessCertificates.Batch001.certificate23).L,none,(CutFailureCertificates.Budget001.certificate22).bound,(CutFailureCertificates.Budget001.certificate23).bound,0⟩
theorem numericValid11 : certificate11.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound11 : certificate11.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch001.certificate22 H MomentCertificates.Batch000.valid11.1 GeometryCertificates.Batch001.valid22 GeometryCertificates.Batch001.sound22 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch001.certificate23 H MomentCertificates.Batch000.valid11.1 GeometryCertificates.Batch001.valid23 GeometryCertificates.Batch001.sound23 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound11 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound11 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate11 GeometryCertificates.Batch001.certificate22 numericValid11
    MomentCertificates.Batch000.valid11 DegreeCertificates.Batch000.valid11 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate11,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate12 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate12,DegreeCertificates.Batch000.certificate12,(WitnessCertificates.Batch001.certificate24).beta,(WitnessCertificates.Batch001.certificate25).L,none,(CutFailureCertificates.Budget001.certificate24).bound,(CutFailureCertificates.Budget001.certificate25).bound,0⟩
theorem numericValid12 : certificate12.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound12 : certificate12.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch001.certificate24 H MomentCertificates.Batch000.valid12.1 GeometryCertificates.Batch001.valid24 GeometryCertificates.Batch001.sound24 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch001.certificate25 H MomentCertificates.Batch000.valid12.1 GeometryCertificates.Batch001.valid25 GeometryCertificates.Batch001.sound25 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound12 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound12 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate12 GeometryCertificates.Batch001.certificate24 numericValid12
    MomentCertificates.Batch000.valid12 DegreeCertificates.Batch000.valid12 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate12,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate13 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate13,DegreeCertificates.Batch000.certificate13,(WitnessCertificates.Batch001.certificate26).beta,(WitnessCertificates.Batch001.certificate27).L,none,(CutFailureCertificates.Budget001.certificate26).bound,(CutFailureCertificates.Budget001.certificate27).bound,0⟩
theorem numericValid13 : certificate13.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound13 : certificate13.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch001.certificate26 H MomentCertificates.Batch000.valid13.1 GeometryCertificates.Batch001.valid26 GeometryCertificates.Batch001.sound26 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch001.certificate27 H MomentCertificates.Batch000.valid13.1 GeometryCertificates.Batch001.valid27 GeometryCertificates.Batch001.sound27 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound13 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound13 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate13 GeometryCertificates.Batch001.certificate26 numericValid13
    MomentCertificates.Batch000.valid13 DegreeCertificates.Batch000.valid13 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate13,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate14 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate14,DegreeCertificates.Batch000.certificate14,(WitnessCertificates.Batch001.certificate28).beta,(WitnessCertificates.Batch001.certificate29).L,none,(CutFailureCertificates.Budget001.certificate28).bound,(CutFailureCertificates.Budget001.certificate29).bound,0⟩
theorem numericValid14 : certificate14.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound14 : certificate14.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch001.certificate28 H MomentCertificates.Batch000.valid14.1 GeometryCertificates.Batch001.valid28 GeometryCertificates.Batch001.sound28 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch001.certificate29 H MomentCertificates.Batch000.valid14.1 GeometryCertificates.Batch001.valid29 GeometryCertificates.Batch001.sound29 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound14 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound14 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate14 GeometryCertificates.Batch001.certificate28 numericValid14
    MomentCertificates.Batch000.valid14 DegreeCertificates.Batch000.valid14 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate14,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate15 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate15,DegreeCertificates.Batch000.certificate15,(WitnessCertificates.Batch001.certificate30).beta,(WitnessCertificates.Batch001.certificate31).L,none,(CutFailureCertificates.Budget001.certificate30).bound,(CutFailureCertificates.Budget001.certificate31).bound,0⟩
theorem numericValid15 : certificate15.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound15 : certificate15.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch001.certificate30 H MomentCertificates.Batch000.valid15.1 GeometryCertificates.Batch001.valid30 GeometryCertificates.Batch001.sound30 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch001.certificate31 H MomentCertificates.Batch000.valid15.1 GeometryCertificates.Batch001.valid31 GeometryCertificates.Batch001.sound31 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound15 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound15 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate15 GeometryCertificates.Batch001.certificate30 numericValid15
    MomentCertificates.Batch000.valid15 DegreeCertificates.Batch000.valid15 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate15,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate16 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate16,DegreeCertificates.Batch000.certificate16,(WitnessCertificates.Batch001.certificate32).beta,(WitnessCertificates.Batch001.certificate33).L,none,(CutFailureCertificates.Budget001.certificate32).bound,(CutFailureCertificates.Budget001.certificate33).bound,0⟩
theorem numericValid16 : certificate16.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound16 : certificate16.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch001.certificate32 H MomentCertificates.Batch000.valid16.1 GeometryCertificates.Batch001.valid32 GeometryCertificates.Batch001.sound32 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch001.certificate33 H MomentCertificates.Batch000.valid16.1 GeometryCertificates.Batch001.valid33 GeometryCertificates.Batch001.sound33 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound16 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound16 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate16 GeometryCertificates.Batch001.certificate32 numericValid16
    MomentCertificates.Batch000.valid16 DegreeCertificates.Batch000.valid16 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate16,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate17 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate17,DegreeCertificates.Batch000.certificate17,(WitnessCertificates.Batch001.certificate34).beta,(WitnessCertificates.Batch001.certificate35).L,none,(CutFailureCertificates.Budget001.certificate34).bound,(CutFailureCertificates.Budget001.certificate35).bound,0⟩
theorem numericValid17 : certificate17.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound17 : certificate17.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch001.certificate34 H MomentCertificates.Batch000.valid17.1 GeometryCertificates.Batch001.valid34 GeometryCertificates.Batch001.sound34 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch001.certificate35 H MomentCertificates.Batch000.valid17.1 GeometryCertificates.Batch001.valid35 GeometryCertificates.Batch001.sound35 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound17 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound17 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate17 GeometryCertificates.Batch001.certificate34 numericValid17
    MomentCertificates.Batch000.valid17 DegreeCertificates.Batch000.valid17 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate17,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate18 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate18,DegreeCertificates.Batch000.certificate18,(WitnessCertificates.Batch001.certificate36).beta,(WitnessCertificates.Batch001.certificate37).L,none,(CutFailureCertificates.Budget001.certificate36).bound,(CutFailureCertificates.Budget001.certificate37).bound,0⟩
theorem numericValid18 : certificate18.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound18 : certificate18.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch001.certificate36 H MomentCertificates.Batch000.valid18.1 GeometryCertificates.Batch001.valid36 GeometryCertificates.Batch001.sound36 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch001.certificate37 H MomentCertificates.Batch000.valid18.1 GeometryCertificates.Batch001.valid37 GeometryCertificates.Batch001.sound37 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound18 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound18 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate18 GeometryCertificates.Batch001.certificate36 numericValid18
    MomentCertificates.Batch000.valid18 DegreeCertificates.Batch000.valid18 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate18,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate19 : RatSamplerCase := ⟨MomentCertificates.Batch000.certificate19,DegreeCertificates.Batch000.certificate19,(WitnessCertificates.Batch001.certificate38).beta,(WitnessCertificates.Batch001.certificate39).L,none,(CutFailureCertificates.Budget001.certificate38).bound,(CutFailureCertificates.Budget001.certificate39).bound,0⟩
theorem numericValid19 : certificate19.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound19 : certificate19.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch001.certificate38 H MomentCertificates.Batch000.valid19.1 GeometryCertificates.Batch001.valid38 GeometryCertificates.Batch001.sound38 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch001.certificate39 H MomentCertificates.Batch000.valid19.1 GeometryCertificates.Batch001.valid39 GeometryCertificates.Batch001.sound39 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch000.probabilityBound19 H st hI
  have hanchor := CertifiedAnchorFailures.Batch000.probabilityBound19 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate19 GeometryCertificates.Batch001.certificate38 numericValid19
    MomentCertificates.Batch000.valid19 DegreeCertificates.Batch000.valid19 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate19,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate0,certificate1,certificate2,certificate3,certificate4,certificate5,certificate6,certificate7,certificate8,certificate9,certificate10,certificate11,certificate12,certificate13,certificate14,certificate15,certificate16,certificate17,certificate18,certificate19]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound0,List.forall_mem_cons.mpr ⟨sound1,List.forall_mem_cons.mpr ⟨sound2,List.forall_mem_cons.mpr ⟨sound3,List.forall_mem_cons.mpr ⟨sound4,List.forall_mem_cons.mpr ⟨sound5,List.forall_mem_cons.mpr ⟨sound6,List.forall_mem_cons.mpr ⟨sound7,List.forall_mem_cons.mpr ⟨sound8,List.forall_mem_cons.mpr ⟨sound9,List.forall_mem_cons.mpr ⟨sound10,List.forall_mem_cons.mpr ⟨sound11,List.forall_mem_cons.mpr ⟨sound12,List.forall_mem_cons.mpr ⟨sound13,List.forall_mem_cons.mpr ⟨sound14,List.forall_mem_cons.mpr ⟨sound15,List.forall_mem_cons.mpr ⟨sound16,List.forall_mem_cons.mpr ⟨sound17,List.forall_mem_cons.mpr ⟨sound18,List.forall_mem_cons.mpr ⟨sound19,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch000
