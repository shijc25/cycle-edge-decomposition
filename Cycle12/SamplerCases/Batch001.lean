import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch001
import Cycle12.CertifiedGlobalFailures.Batch001
import Cycle12.CutFailureCertificates.Budget002
import Cycle12.CutFailureCertificates.Budget003
import Cycle12.DegreeCertificates.Batch001
import Cycle12.GeometryCertificates.Batch002
import Cycle12.GeometryCertificates.Batch003
import Cycle12.MomentCertificates.Batch001
import Cycle12.WitnessCertificates.Batch002
import Cycle12.WitnessCertificates.Batch003

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch001
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate20 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate20,DegreeCertificates.Batch001.certificate20,(WitnessCertificates.Batch002.certificate40).beta,(WitnessCertificates.Batch002.certificate41).L,none,(CutFailureCertificates.Budget002.certificate40).bound,(CutFailureCertificates.Budget002.certificate41).bound,0⟩
theorem numericValid20 : certificate20.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound20 : certificate20.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch002.certificate40 H MomentCertificates.Batch001.valid20.1 GeometryCertificates.Batch002.valid40 GeometryCertificates.Batch002.sound40 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch002.certificate41 H MomentCertificates.Batch001.valid20.1 GeometryCertificates.Batch002.valid41 GeometryCertificates.Batch002.sound41 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound20 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound20 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate20 GeometryCertificates.Batch002.certificate40 numericValid20
    MomentCertificates.Batch001.valid20 DegreeCertificates.Batch001.valid20 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate20,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate21 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate21,DegreeCertificates.Batch001.certificate21,(WitnessCertificates.Batch002.certificate42).beta,(WitnessCertificates.Batch002.certificate43).L,none,(CutFailureCertificates.Budget002.certificate42).bound,(CutFailureCertificates.Budget002.certificate43).bound,0⟩
theorem numericValid21 : certificate21.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound21 : certificate21.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch002.certificate42 H MomentCertificates.Batch001.valid21.1 GeometryCertificates.Batch002.valid42 GeometryCertificates.Batch002.sound42 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch002.certificate43 H MomentCertificates.Batch001.valid21.1 GeometryCertificates.Batch002.valid43 GeometryCertificates.Batch002.sound43 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound21 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound21 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate21 GeometryCertificates.Batch002.certificate42 numericValid21
    MomentCertificates.Batch001.valid21 DegreeCertificates.Batch001.valid21 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate21,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate22 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate22,DegreeCertificates.Batch001.certificate22,(WitnessCertificates.Batch002.certificate44).beta,(WitnessCertificates.Batch002.certificate45).L,none,(CutFailureCertificates.Budget002.certificate44).bound,(CutFailureCertificates.Budget002.certificate45).bound,0⟩
theorem numericValid22 : certificate22.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound22 : certificate22.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch002.certificate44 H MomentCertificates.Batch001.valid22.1 GeometryCertificates.Batch002.valid44 GeometryCertificates.Batch002.sound44 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch002.certificate45 H MomentCertificates.Batch001.valid22.1 GeometryCertificates.Batch002.valid45 GeometryCertificates.Batch002.sound45 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound22 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound22 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate22 GeometryCertificates.Batch002.certificate44 numericValid22
    MomentCertificates.Batch001.valid22 DegreeCertificates.Batch001.valid22 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate22,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate23 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate23,DegreeCertificates.Batch001.certificate23,(WitnessCertificates.Batch002.certificate46).beta,(WitnessCertificates.Batch002.certificate47).L,none,(CutFailureCertificates.Budget002.certificate46).bound,(CutFailureCertificates.Budget002.certificate47).bound,0⟩
theorem numericValid23 : certificate23.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound23 : certificate23.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch002.certificate46 H MomentCertificates.Batch001.valid23.1 GeometryCertificates.Batch002.valid46 GeometryCertificates.Batch002.sound46 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch002.certificate47 H MomentCertificates.Batch001.valid23.1 GeometryCertificates.Batch002.valid47 GeometryCertificates.Batch002.sound47 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound23 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound23 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate23 GeometryCertificates.Batch002.certificate46 numericValid23
    MomentCertificates.Batch001.valid23 DegreeCertificates.Batch001.valid23 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate23,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate24 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate24,DegreeCertificates.Batch001.certificate24,(WitnessCertificates.Batch002.certificate48).beta,(WitnessCertificates.Batch002.certificate49).L,none,(CutFailureCertificates.Budget002.certificate48).bound,(CutFailureCertificates.Budget002.certificate49).bound,0⟩
theorem numericValid24 : certificate24.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound24 : certificate24.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch002.certificate48 H MomentCertificates.Batch001.valid24.1 GeometryCertificates.Batch002.valid48 GeometryCertificates.Batch002.sound48 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch002.certificate49 H MomentCertificates.Batch001.valid24.1 GeometryCertificates.Batch002.valid49 GeometryCertificates.Batch002.sound49 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound24 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound24 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate24 GeometryCertificates.Batch002.certificate48 numericValid24
    MomentCertificates.Batch001.valid24 DegreeCertificates.Batch001.valid24 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate24,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate25 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate25,DegreeCertificates.Batch001.certificate25,(WitnessCertificates.Batch002.certificate50).beta,(WitnessCertificates.Batch002.certificate51).L,none,(CutFailureCertificates.Budget002.certificate50).bound,(CutFailureCertificates.Budget002.certificate51).bound,0⟩
theorem numericValid25 : certificate25.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound25 : certificate25.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch002.certificate50 H MomentCertificates.Batch001.valid25.1 GeometryCertificates.Batch002.valid50 GeometryCertificates.Batch002.sound50 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch002.certificate51 H MomentCertificates.Batch001.valid25.1 GeometryCertificates.Batch002.valid51 GeometryCertificates.Batch002.sound51 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound25 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound25 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate25 GeometryCertificates.Batch002.certificate50 numericValid25
    MomentCertificates.Batch001.valid25 DegreeCertificates.Batch001.valid25 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate25,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate26 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate26,DegreeCertificates.Batch001.certificate26,(WitnessCertificates.Batch002.certificate52).beta,(WitnessCertificates.Batch002.certificate53).L,none,(CutFailureCertificates.Budget002.certificate52).bound,(CutFailureCertificates.Budget002.certificate53).bound,0⟩
theorem numericValid26 : certificate26.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound26 : certificate26.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch002.certificate52 H MomentCertificates.Batch001.valid26.1 GeometryCertificates.Batch002.valid52 GeometryCertificates.Batch002.sound52 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch002.certificate53 H MomentCertificates.Batch001.valid26.1 GeometryCertificates.Batch002.valid53 GeometryCertificates.Batch002.sound53 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound26 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound26 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate26 GeometryCertificates.Batch002.certificate52 numericValid26
    MomentCertificates.Batch001.valid26 DegreeCertificates.Batch001.valid26 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate26,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate27 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate27,DegreeCertificates.Batch001.certificate27,(WitnessCertificates.Batch002.certificate54).beta,(WitnessCertificates.Batch002.certificate55).L,none,(CutFailureCertificates.Budget002.certificate54).bound,(CutFailureCertificates.Budget002.certificate55).bound,0⟩
theorem numericValid27 : certificate27.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound27 : certificate27.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch002.certificate54 H MomentCertificates.Batch001.valid27.1 GeometryCertificates.Batch002.valid54 GeometryCertificates.Batch002.sound54 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch002.certificate55 H MomentCertificates.Batch001.valid27.1 GeometryCertificates.Batch002.valid55 GeometryCertificates.Batch002.sound55 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound27 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound27 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate27 GeometryCertificates.Batch002.certificate54 numericValid27
    MomentCertificates.Batch001.valid27 DegreeCertificates.Batch001.valid27 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate27,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate28 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate28,DegreeCertificates.Batch001.certificate28,(WitnessCertificates.Batch002.certificate56).beta,(WitnessCertificates.Batch002.certificate57).L,none,(CutFailureCertificates.Budget002.certificate56).bound,(CutFailureCertificates.Budget002.certificate57).bound,0⟩
theorem numericValid28 : certificate28.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound28 : certificate28.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch002.certificate56 H MomentCertificates.Batch001.valid28.1 GeometryCertificates.Batch002.valid56 GeometryCertificates.Batch002.sound56 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch002.certificate57 H MomentCertificates.Batch001.valid28.1 GeometryCertificates.Batch002.valid57 GeometryCertificates.Batch002.sound57 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound28 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound28 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate28 GeometryCertificates.Batch002.certificate56 numericValid28
    MomentCertificates.Batch001.valid28 DegreeCertificates.Batch001.valid28 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate28,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate29 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate29,DegreeCertificates.Batch001.certificate29,(WitnessCertificates.Batch002.certificate58).beta,(WitnessCertificates.Batch002.certificate59).L,none,(CutFailureCertificates.Budget002.certificate58).bound,(CutFailureCertificates.Budget002.certificate59).bound,0⟩
theorem numericValid29 : certificate29.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound29 : certificate29.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch002.certificate58 H MomentCertificates.Batch001.valid29.1 GeometryCertificates.Batch002.valid58 GeometryCertificates.Batch002.sound58 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch002.certificate59 H MomentCertificates.Batch001.valid29.1 GeometryCertificates.Batch002.valid59 GeometryCertificates.Batch002.sound59 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound29 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound29 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate29 GeometryCertificates.Batch002.certificate58 numericValid29
    MomentCertificates.Batch001.valid29 DegreeCertificates.Batch001.valid29 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate29,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate30 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate30,DegreeCertificates.Batch001.certificate30,(WitnessCertificates.Batch003.certificate60).beta,(WitnessCertificates.Batch003.certificate61).L,none,(CutFailureCertificates.Budget003.certificate60).bound,(CutFailureCertificates.Budget003.certificate61).bound,0⟩
theorem numericValid30 : certificate30.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound30 : certificate30.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch003.certificate60 H MomentCertificates.Batch001.valid30.1 GeometryCertificates.Batch003.valid60 GeometryCertificates.Batch003.sound60 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch003.certificate61 H MomentCertificates.Batch001.valid30.1 GeometryCertificates.Batch003.valid61 GeometryCertificates.Batch003.sound61 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound30 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound30 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate30 GeometryCertificates.Batch003.certificate60 numericValid30
    MomentCertificates.Batch001.valid30 DegreeCertificates.Batch001.valid30 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate30,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate31 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate31,DegreeCertificates.Batch001.certificate31,(WitnessCertificates.Batch003.certificate62).beta,(WitnessCertificates.Batch003.certificate63).L,none,(CutFailureCertificates.Budget003.certificate62).bound,(CutFailureCertificates.Budget003.certificate63).bound,0⟩
theorem numericValid31 : certificate31.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound31 : certificate31.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch003.certificate62 H MomentCertificates.Batch001.valid31.1 GeometryCertificates.Batch003.valid62 GeometryCertificates.Batch003.sound62 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch003.certificate63 H MomentCertificates.Batch001.valid31.1 GeometryCertificates.Batch003.valid63 GeometryCertificates.Batch003.sound63 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound31 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound31 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate31 GeometryCertificates.Batch003.certificate62 numericValid31
    MomentCertificates.Batch001.valid31 DegreeCertificates.Batch001.valid31 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate31,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate32 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate32,DegreeCertificates.Batch001.certificate32,(WitnessCertificates.Batch003.certificate64).beta,(WitnessCertificates.Batch003.certificate65).L,none,(CutFailureCertificates.Budget003.certificate64).bound,(CutFailureCertificates.Budget003.certificate65).bound,0⟩
theorem numericValid32 : certificate32.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound32 : certificate32.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch003.certificate64 H MomentCertificates.Batch001.valid32.1 GeometryCertificates.Batch003.valid64 GeometryCertificates.Batch003.sound64 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch003.certificate65 H MomentCertificates.Batch001.valid32.1 GeometryCertificates.Batch003.valid65 GeometryCertificates.Batch003.sound65 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound32 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound32 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate32 GeometryCertificates.Batch003.certificate64 numericValid32
    MomentCertificates.Batch001.valid32 DegreeCertificates.Batch001.valid32 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate32,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate33 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate33,DegreeCertificates.Batch001.certificate33,(WitnessCertificates.Batch003.certificate66).beta,(WitnessCertificates.Batch003.certificate67).L,none,(CutFailureCertificates.Budget003.certificate66).bound,(CutFailureCertificates.Budget003.certificate67).bound,0⟩
theorem numericValid33 : certificate33.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound33 : certificate33.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch003.certificate66 H MomentCertificates.Batch001.valid33.1 GeometryCertificates.Batch003.valid66 GeometryCertificates.Batch003.sound66 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch003.certificate67 H MomentCertificates.Batch001.valid33.1 GeometryCertificates.Batch003.valid67 GeometryCertificates.Batch003.sound67 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound33 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound33 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate33 GeometryCertificates.Batch003.certificate66 numericValid33
    MomentCertificates.Batch001.valid33 DegreeCertificates.Batch001.valid33 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate33,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate34 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate34,DegreeCertificates.Batch001.certificate34,(WitnessCertificates.Batch003.certificate68).beta,(WitnessCertificates.Batch003.certificate69).L,none,(CutFailureCertificates.Budget003.certificate68).bound,(CutFailureCertificates.Budget003.certificate69).bound,0⟩
theorem numericValid34 : certificate34.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound34 : certificate34.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch003.certificate68 H MomentCertificates.Batch001.valid34.1 GeometryCertificates.Batch003.valid68 GeometryCertificates.Batch003.sound68 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch003.certificate69 H MomentCertificates.Batch001.valid34.1 GeometryCertificates.Batch003.valid69 GeometryCertificates.Batch003.sound69 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound34 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound34 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate34 GeometryCertificates.Batch003.certificate68 numericValid34
    MomentCertificates.Batch001.valid34 DegreeCertificates.Batch001.valid34 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate34,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate35 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate35,DegreeCertificates.Batch001.certificate35,(WitnessCertificates.Batch003.certificate70).beta,(WitnessCertificates.Batch003.certificate71).L,none,(CutFailureCertificates.Budget003.certificate70).bound,(CutFailureCertificates.Budget003.certificate71).bound,0⟩
theorem numericValid35 : certificate35.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound35 : certificate35.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch003.certificate70 H MomentCertificates.Batch001.valid35.1 GeometryCertificates.Batch003.valid70 GeometryCertificates.Batch003.sound70 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch003.certificate71 H MomentCertificates.Batch001.valid35.1 GeometryCertificates.Batch003.valid71 GeometryCertificates.Batch003.sound71 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound35 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound35 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate35 GeometryCertificates.Batch003.certificate70 numericValid35
    MomentCertificates.Batch001.valid35 DegreeCertificates.Batch001.valid35 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate35,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate36 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate36,DegreeCertificates.Batch001.certificate36,(WitnessCertificates.Batch003.certificate72).beta,(WitnessCertificates.Batch003.certificate73).L,none,(CutFailureCertificates.Budget003.certificate72).bound,(CutFailureCertificates.Budget003.certificate73).bound,0⟩
theorem numericValid36 : certificate36.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound36 : certificate36.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch003.certificate72 H MomentCertificates.Batch001.valid36.1 GeometryCertificates.Batch003.valid72 GeometryCertificates.Batch003.sound72 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch003.certificate73 H MomentCertificates.Batch001.valid36.1 GeometryCertificates.Batch003.valid73 GeometryCertificates.Batch003.sound73 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound36 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound36 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate36 GeometryCertificates.Batch003.certificate72 numericValid36
    MomentCertificates.Batch001.valid36 DegreeCertificates.Batch001.valid36 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate36,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate37 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate37,DegreeCertificates.Batch001.certificate37,(WitnessCertificates.Batch003.certificate74).beta,(WitnessCertificates.Batch003.certificate75).L,none,(CutFailureCertificates.Budget003.certificate74).bound,(CutFailureCertificates.Budget003.certificate75).bound,0⟩
theorem numericValid37 : certificate37.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound37 : certificate37.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch003.certificate74 H MomentCertificates.Batch001.valid37.1 GeometryCertificates.Batch003.valid74 GeometryCertificates.Batch003.sound74 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch003.certificate75 H MomentCertificates.Batch001.valid37.1 GeometryCertificates.Batch003.valid75 GeometryCertificates.Batch003.sound75 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound37 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound37 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate37 GeometryCertificates.Batch003.certificate74 numericValid37
    MomentCertificates.Batch001.valid37 DegreeCertificates.Batch001.valid37 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate37,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate38 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate38,DegreeCertificates.Batch001.certificate38,(WitnessCertificates.Batch003.certificate76).beta,(WitnessCertificates.Batch003.certificate77).L,none,(CutFailureCertificates.Budget003.certificate76).bound,(CutFailureCertificates.Budget003.certificate77).bound,0⟩
theorem numericValid38 : certificate38.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound38 : certificate38.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch003.certificate76 H MomentCertificates.Batch001.valid38.1 GeometryCertificates.Batch003.valid76 GeometryCertificates.Batch003.sound76 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch003.certificate77 H MomentCertificates.Batch001.valid38.1 GeometryCertificates.Batch003.valid77 GeometryCertificates.Batch003.sound77 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound38 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound38 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate38 GeometryCertificates.Batch003.certificate76 numericValid38
    MomentCertificates.Batch001.valid38 DegreeCertificates.Batch001.valid38 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate38,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate39 : RatSamplerCase := ⟨MomentCertificates.Batch001.certificate39,DegreeCertificates.Batch001.certificate39,(WitnessCertificates.Batch003.certificate78).beta,(WitnessCertificates.Batch003.certificate79).L,none,(CutFailureCertificates.Budget003.certificate78).bound,(CutFailureCertificates.Budget003.certificate79).bound,0⟩
theorem numericValid39 : certificate39.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound39 : certificate39.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch003.certificate78 H MomentCertificates.Batch001.valid39.1 GeometryCertificates.Batch003.valid78 GeometryCertificates.Batch003.sound78 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch003.certificate79 H MomentCertificates.Batch001.valid39.1 GeometryCertificates.Batch003.valid79 GeometryCertificates.Batch003.sound79 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch001.probabilityBound39 H st hI
  have hanchor := CertifiedAnchorFailures.Batch001.probabilityBound39 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate39 GeometryCertificates.Batch003.certificate78 numericValid39
    MomentCertificates.Batch001.valid39 DegreeCertificates.Batch001.valid39 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate39,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate20,certificate21,certificate22,certificate23,certificate24,certificate25,certificate26,certificate27,certificate28,certificate29,certificate30,certificate31,certificate32,certificate33,certificate34,certificate35,certificate36,certificate37,certificate38,certificate39]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound20,List.forall_mem_cons.mpr ⟨sound21,List.forall_mem_cons.mpr ⟨sound22,List.forall_mem_cons.mpr ⟨sound23,List.forall_mem_cons.mpr ⟨sound24,List.forall_mem_cons.mpr ⟨sound25,List.forall_mem_cons.mpr ⟨sound26,List.forall_mem_cons.mpr ⟨sound27,List.forall_mem_cons.mpr ⟨sound28,List.forall_mem_cons.mpr ⟨sound29,List.forall_mem_cons.mpr ⟨sound30,List.forall_mem_cons.mpr ⟨sound31,List.forall_mem_cons.mpr ⟨sound32,List.forall_mem_cons.mpr ⟨sound33,List.forall_mem_cons.mpr ⟨sound34,List.forall_mem_cons.mpr ⟨sound35,List.forall_mem_cons.mpr ⟨sound36,List.forall_mem_cons.mpr ⟨sound37,List.forall_mem_cons.mpr ⟨sound38,List.forall_mem_cons.mpr ⟨sound39,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch001
