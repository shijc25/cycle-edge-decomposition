import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch003
import Cycle12.CertifiedGlobalFailures.Batch003
import Cycle12.CutFailureCertificates.Budget006
import Cycle12.CutFailureCertificates.Budget007
import Cycle12.DegreeCertificates.Batch003
import Cycle12.GeometryCertificates.Batch006
import Cycle12.GeometryCertificates.Batch007
import Cycle12.MomentCertificates.Batch003
import Cycle12.WitnessCertificates.Batch006
import Cycle12.WitnessCertificates.Batch007

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch003
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate60 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate60,DegreeCertificates.Batch003.certificate60,(WitnessCertificates.Batch006.certificate120).beta,(WitnessCertificates.Batch006.certificate121).L,none,(CutFailureCertificates.Budget006.certificate120).bound,(CutFailureCertificates.Budget006.certificate121).bound,0⟩
theorem numericValid60 : certificate60.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound60 : certificate60.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch006.certificate120 H MomentCertificates.Batch003.valid60.1 GeometryCertificates.Batch006.valid120 GeometryCertificates.Batch006.sound120 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch006.certificate121 H MomentCertificates.Batch003.valid60.1 GeometryCertificates.Batch006.valid121 GeometryCertificates.Batch006.sound121 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound60 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound60 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate60 GeometryCertificates.Batch006.certificate120 numericValid60
    MomentCertificates.Batch003.valid60 DegreeCertificates.Batch003.valid60 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate60,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate61 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate61,DegreeCertificates.Batch003.certificate61,(WitnessCertificates.Batch006.certificate122).beta,(WitnessCertificates.Batch006.certificate123).L,none,(CutFailureCertificates.Budget006.certificate122).bound,(CutFailureCertificates.Budget006.certificate123).bound,0⟩
theorem numericValid61 : certificate61.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound61 : certificate61.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch006.certificate122 H MomentCertificates.Batch003.valid61.1 GeometryCertificates.Batch006.valid122 GeometryCertificates.Batch006.sound122 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch006.certificate123 H MomentCertificates.Batch003.valid61.1 GeometryCertificates.Batch006.valid123 GeometryCertificates.Batch006.sound123 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound61 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound61 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate61 GeometryCertificates.Batch006.certificate122 numericValid61
    MomentCertificates.Batch003.valid61 DegreeCertificates.Batch003.valid61 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate61,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate62 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate62,DegreeCertificates.Batch003.certificate62,(WitnessCertificates.Batch006.certificate124).beta,(WitnessCertificates.Batch006.certificate125).L,none,(CutFailureCertificates.Budget006.certificate124).bound,(CutFailureCertificates.Budget006.certificate125).bound,0⟩
theorem numericValid62 : certificate62.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound62 : certificate62.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch006.certificate124 H MomentCertificates.Batch003.valid62.1 GeometryCertificates.Batch006.valid124 GeometryCertificates.Batch006.sound124 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch006.certificate125 H MomentCertificates.Batch003.valid62.1 GeometryCertificates.Batch006.valid125 GeometryCertificates.Batch006.sound125 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound62 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound62 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate62 GeometryCertificates.Batch006.certificate124 numericValid62
    MomentCertificates.Batch003.valid62 DegreeCertificates.Batch003.valid62 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate62,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate63 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate63,DegreeCertificates.Batch003.certificate63,(WitnessCertificates.Batch006.certificate126).beta,(WitnessCertificates.Batch006.certificate127).L,none,(CutFailureCertificates.Budget006.certificate126).bound,(CutFailureCertificates.Budget006.certificate127).bound,0⟩
theorem numericValid63 : certificate63.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound63 : certificate63.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch006.certificate126 H MomentCertificates.Batch003.valid63.1 GeometryCertificates.Batch006.valid126 GeometryCertificates.Batch006.sound126 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch006.certificate127 H MomentCertificates.Batch003.valid63.1 GeometryCertificates.Batch006.valid127 GeometryCertificates.Batch006.sound127 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound63 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound63 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate63 GeometryCertificates.Batch006.certificate126 numericValid63
    MomentCertificates.Batch003.valid63 DegreeCertificates.Batch003.valid63 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate63,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate64 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate64,DegreeCertificates.Batch003.certificate64,(WitnessCertificates.Batch006.certificate128).beta,(WitnessCertificates.Batch006.certificate129).L,none,(CutFailureCertificates.Budget006.certificate128).bound,(CutFailureCertificates.Budget006.certificate129).bound,0⟩
theorem numericValid64 : certificate64.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound64 : certificate64.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch006.certificate128 H MomentCertificates.Batch003.valid64.1 GeometryCertificates.Batch006.valid128 GeometryCertificates.Batch006.sound128 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch006.certificate129 H MomentCertificates.Batch003.valid64.1 GeometryCertificates.Batch006.valid129 GeometryCertificates.Batch006.sound129 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound64 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound64 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate64 GeometryCertificates.Batch006.certificate128 numericValid64
    MomentCertificates.Batch003.valid64 DegreeCertificates.Batch003.valid64 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate64,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate65 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate65,DegreeCertificates.Batch003.certificate65,(WitnessCertificates.Batch006.certificate130).beta,(WitnessCertificates.Batch006.certificate131).L,none,(CutFailureCertificates.Budget006.certificate130).bound,(CutFailureCertificates.Budget006.certificate131).bound,0⟩
theorem numericValid65 : certificate65.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound65 : certificate65.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch006.certificate130 H MomentCertificates.Batch003.valid65.1 GeometryCertificates.Batch006.valid130 GeometryCertificates.Batch006.sound130 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch006.certificate131 H MomentCertificates.Batch003.valid65.1 GeometryCertificates.Batch006.valid131 GeometryCertificates.Batch006.sound131 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound65 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound65 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate65 GeometryCertificates.Batch006.certificate130 numericValid65
    MomentCertificates.Batch003.valid65 DegreeCertificates.Batch003.valid65 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate65,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate66 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate66,DegreeCertificates.Batch003.certificate66,(WitnessCertificates.Batch006.certificate132).beta,(WitnessCertificates.Batch006.certificate133).L,none,(CutFailureCertificates.Budget006.certificate132).bound,(CutFailureCertificates.Budget006.certificate133).bound,0⟩
theorem numericValid66 : certificate66.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound66 : certificate66.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch006.certificate132 H MomentCertificates.Batch003.valid66.1 GeometryCertificates.Batch006.valid132 GeometryCertificates.Batch006.sound132 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch006.certificate133 H MomentCertificates.Batch003.valid66.1 GeometryCertificates.Batch006.valid133 GeometryCertificates.Batch006.sound133 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound66 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound66 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate66 GeometryCertificates.Batch006.certificate132 numericValid66
    MomentCertificates.Batch003.valid66 DegreeCertificates.Batch003.valid66 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate66,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate67 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate67,DegreeCertificates.Batch003.certificate67,(WitnessCertificates.Batch006.certificate134).beta,(WitnessCertificates.Batch006.certificate135).L,none,(CutFailureCertificates.Budget006.certificate134).bound,(CutFailureCertificates.Budget006.certificate135).bound,0⟩
theorem numericValid67 : certificate67.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound67 : certificate67.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch006.certificate134 H MomentCertificates.Batch003.valid67.1 GeometryCertificates.Batch006.valid134 GeometryCertificates.Batch006.sound134 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch006.certificate135 H MomentCertificates.Batch003.valid67.1 GeometryCertificates.Batch006.valid135 GeometryCertificates.Batch006.sound135 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound67 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound67 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate67 GeometryCertificates.Batch006.certificate134 numericValid67
    MomentCertificates.Batch003.valid67 DegreeCertificates.Batch003.valid67 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate67,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate68 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate68,DegreeCertificates.Batch003.certificate68,(WitnessCertificates.Batch006.certificate136).beta,(WitnessCertificates.Batch006.certificate137).L,none,(CutFailureCertificates.Budget006.certificate136).bound,(CutFailureCertificates.Budget006.certificate137).bound,0⟩
theorem numericValid68 : certificate68.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound68 : certificate68.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch006.certificate136 H MomentCertificates.Batch003.valid68.1 GeometryCertificates.Batch006.valid136 GeometryCertificates.Batch006.sound136 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch006.certificate137 H MomentCertificates.Batch003.valid68.1 GeometryCertificates.Batch006.valid137 GeometryCertificates.Batch006.sound137 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound68 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound68 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate68 GeometryCertificates.Batch006.certificate136 numericValid68
    MomentCertificates.Batch003.valid68 DegreeCertificates.Batch003.valid68 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate68,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate69 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate69,DegreeCertificates.Batch003.certificate69,(WitnessCertificates.Batch006.certificate138).beta,(WitnessCertificates.Batch006.certificate139).L,none,(CutFailureCertificates.Budget006.certificate138).bound,(CutFailureCertificates.Budget006.certificate139).bound,0⟩
theorem numericValid69 : certificate69.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound69 : certificate69.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch006.certificate138 H MomentCertificates.Batch003.valid69.1 GeometryCertificates.Batch006.valid138 GeometryCertificates.Batch006.sound138 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch006.certificate139 H MomentCertificates.Batch003.valid69.1 GeometryCertificates.Batch006.valid139 GeometryCertificates.Batch006.sound139 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound69 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound69 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate69 GeometryCertificates.Batch006.certificate138 numericValid69
    MomentCertificates.Batch003.valid69 DegreeCertificates.Batch003.valid69 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate69,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate70 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate70,DegreeCertificates.Batch003.certificate70,(WitnessCertificates.Batch007.certificate140).beta,(WitnessCertificates.Batch007.certificate141).L,none,(CutFailureCertificates.Budget007.certificate140).bound,(CutFailureCertificates.Budget007.certificate141).bound,0⟩
theorem numericValid70 : certificate70.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound70 : certificate70.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch007.certificate140 H MomentCertificates.Batch003.valid70.1 GeometryCertificates.Batch007.valid140 GeometryCertificates.Batch007.sound140 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch007.certificate141 H MomentCertificates.Batch003.valid70.1 GeometryCertificates.Batch007.valid141 GeometryCertificates.Batch007.sound141 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound70 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound70 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate70 GeometryCertificates.Batch007.certificate140 numericValid70
    MomentCertificates.Batch003.valid70 DegreeCertificates.Batch003.valid70 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate70,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate71 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate71,DegreeCertificates.Batch003.certificate71,(WitnessCertificates.Batch007.certificate142).beta,(WitnessCertificates.Batch007.certificate143).L,none,(CutFailureCertificates.Budget007.certificate142).bound,(CutFailureCertificates.Budget007.certificate143).bound,0⟩
theorem numericValid71 : certificate71.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound71 : certificate71.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch007.certificate142 H MomentCertificates.Batch003.valid71.1 GeometryCertificates.Batch007.valid142 GeometryCertificates.Batch007.sound142 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch007.certificate143 H MomentCertificates.Batch003.valid71.1 GeometryCertificates.Batch007.valid143 GeometryCertificates.Batch007.sound143 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound71 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound71 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate71 GeometryCertificates.Batch007.certificate142 numericValid71
    MomentCertificates.Batch003.valid71 DegreeCertificates.Batch003.valid71 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate71,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate72 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate72,DegreeCertificates.Batch003.certificate72,(WitnessCertificates.Batch007.certificate144).beta,(WitnessCertificates.Batch007.certificate145).L,none,(CutFailureCertificates.Budget007.certificate144).bound,(CutFailureCertificates.Budget007.certificate145).bound,0⟩
theorem numericValid72 : certificate72.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound72 : certificate72.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch007.certificate144 H MomentCertificates.Batch003.valid72.1 GeometryCertificates.Batch007.valid144 GeometryCertificates.Batch007.sound144 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch007.certificate145 H MomentCertificates.Batch003.valid72.1 GeometryCertificates.Batch007.valid145 GeometryCertificates.Batch007.sound145 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound72 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound72 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate72 GeometryCertificates.Batch007.certificate144 numericValid72
    MomentCertificates.Batch003.valid72 DegreeCertificates.Batch003.valid72 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate72,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate73 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate73,DegreeCertificates.Batch003.certificate73,(WitnessCertificates.Batch007.certificate146).beta,(WitnessCertificates.Batch007.certificate147).L,none,(CutFailureCertificates.Budget007.certificate146).bound,(CutFailureCertificates.Budget007.certificate147).bound,0⟩
theorem numericValid73 : certificate73.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound73 : certificate73.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch007.certificate146 H MomentCertificates.Batch003.valid73.1 GeometryCertificates.Batch007.valid146 GeometryCertificates.Batch007.sound146 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch007.certificate147 H MomentCertificates.Batch003.valid73.1 GeometryCertificates.Batch007.valid147 GeometryCertificates.Batch007.sound147 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound73 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound73 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate73 GeometryCertificates.Batch007.certificate146 numericValid73
    MomentCertificates.Batch003.valid73 DegreeCertificates.Batch003.valid73 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate73,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate74 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate74,DegreeCertificates.Batch003.certificate74,(WitnessCertificates.Batch007.certificate148).beta,(WitnessCertificates.Batch007.certificate149).L,none,(CutFailureCertificates.Budget007.certificate148).bound,(CutFailureCertificates.Budget007.certificate149).bound,0⟩
theorem numericValid74 : certificate74.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound74 : certificate74.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch007.certificate148 H MomentCertificates.Batch003.valid74.1 GeometryCertificates.Batch007.valid148 GeometryCertificates.Batch007.sound148 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch007.certificate149 H MomentCertificates.Batch003.valid74.1 GeometryCertificates.Batch007.valid149 GeometryCertificates.Batch007.sound149 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound74 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound74 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate74 GeometryCertificates.Batch007.certificate148 numericValid74
    MomentCertificates.Batch003.valid74 DegreeCertificates.Batch003.valid74 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate74,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate75 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate75,DegreeCertificates.Batch003.certificate75,(WitnessCertificates.Batch007.certificate150).beta,(WitnessCertificates.Batch007.certificate151).L,none,(CutFailureCertificates.Budget007.certificate150).bound,(CutFailureCertificates.Budget007.certificate151).bound,0⟩
theorem numericValid75 : certificate75.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound75 : certificate75.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch007.certificate150 H MomentCertificates.Batch003.valid75.1 GeometryCertificates.Batch007.valid150 GeometryCertificates.Batch007.sound150 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch007.certificate151 H MomentCertificates.Batch003.valid75.1 GeometryCertificates.Batch007.valid151 GeometryCertificates.Batch007.sound151 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound75 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound75 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate75 GeometryCertificates.Batch007.certificate150 numericValid75
    MomentCertificates.Batch003.valid75 DegreeCertificates.Batch003.valid75 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate75,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate76 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate76,DegreeCertificates.Batch003.certificate76,(WitnessCertificates.Batch007.certificate152).beta,(WitnessCertificates.Batch007.certificate153).L,none,(CutFailureCertificates.Budget007.certificate152).bound,(CutFailureCertificates.Budget007.certificate153).bound,0⟩
theorem numericValid76 : certificate76.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound76 : certificate76.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch007.certificate152 H MomentCertificates.Batch003.valid76.1 GeometryCertificates.Batch007.valid152 GeometryCertificates.Batch007.sound152 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch007.certificate153 H MomentCertificates.Batch003.valid76.1 GeometryCertificates.Batch007.valid153 GeometryCertificates.Batch007.sound153 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound76 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound76 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate76 GeometryCertificates.Batch007.certificate152 numericValid76
    MomentCertificates.Batch003.valid76 DegreeCertificates.Batch003.valid76 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate76,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate77 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate77,DegreeCertificates.Batch003.certificate77,(WitnessCertificates.Batch007.certificate154).beta,(WitnessCertificates.Batch007.certificate155).L,none,(CutFailureCertificates.Budget007.certificate154).bound,(CutFailureCertificates.Budget007.certificate155).bound,0⟩
theorem numericValid77 : certificate77.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound77 : certificate77.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch007.certificate154 H MomentCertificates.Batch003.valid77.1 GeometryCertificates.Batch007.valid154 GeometryCertificates.Batch007.sound154 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch007.certificate155 H MomentCertificates.Batch003.valid77.1 GeometryCertificates.Batch007.valid155 GeometryCertificates.Batch007.sound155 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound77 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound77 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate77 GeometryCertificates.Batch007.certificate154 numericValid77
    MomentCertificates.Batch003.valid77 DegreeCertificates.Batch003.valid77 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate77,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate78 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate78,DegreeCertificates.Batch003.certificate78,(WitnessCertificates.Batch007.certificate156).beta,(WitnessCertificates.Batch007.certificate157).L,none,(CutFailureCertificates.Budget007.certificate156).bound,(CutFailureCertificates.Budget007.certificate157).bound,0⟩
theorem numericValid78 : certificate78.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound78 : certificate78.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch007.certificate156 H MomentCertificates.Batch003.valid78.1 GeometryCertificates.Batch007.valid156 GeometryCertificates.Batch007.sound156 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch007.certificate157 H MomentCertificates.Batch003.valid78.1 GeometryCertificates.Batch007.valid157 GeometryCertificates.Batch007.sound157 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound78 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound78 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate78 GeometryCertificates.Batch007.certificate156 numericValid78
    MomentCertificates.Batch003.valid78 DegreeCertificates.Batch003.valid78 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate78,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate79 : RatSamplerCase := ⟨MomentCertificates.Batch003.certificate79,DegreeCertificates.Batch003.certificate79,(WitnessCertificates.Batch007.certificate158).beta,(WitnessCertificates.Batch007.certificate159).L,none,(CutFailureCertificates.Budget007.certificate158).bound,(CutFailureCertificates.Budget007.certificate159).bound,0⟩
theorem numericValid79 : certificate79.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound79 : certificate79.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch007.certificate158 H MomentCertificates.Batch003.valid79.1 GeometryCertificates.Batch007.valid158 GeometryCertificates.Batch007.sound158 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch007.certificate159 H MomentCertificates.Batch003.valid79.1 GeometryCertificates.Batch007.valid159 GeometryCertificates.Batch007.sound159 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch003.probabilityBound79 H st hI
  have hanchor := CertifiedAnchorFailures.Batch003.probabilityBound79 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate79 GeometryCertificates.Batch007.certificate158 numericValid79
    MomentCertificates.Batch003.valid79 DegreeCertificates.Batch003.valid79 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate79,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate60,certificate61,certificate62,certificate63,certificate64,certificate65,certificate66,certificate67,certificate68,certificate69,certificate70,certificate71,certificate72,certificate73,certificate74,certificate75,certificate76,certificate77,certificate78,certificate79]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound60,List.forall_mem_cons.mpr ⟨sound61,List.forall_mem_cons.mpr ⟨sound62,List.forall_mem_cons.mpr ⟨sound63,List.forall_mem_cons.mpr ⟨sound64,List.forall_mem_cons.mpr ⟨sound65,List.forall_mem_cons.mpr ⟨sound66,List.forall_mem_cons.mpr ⟨sound67,List.forall_mem_cons.mpr ⟨sound68,List.forall_mem_cons.mpr ⟨sound69,List.forall_mem_cons.mpr ⟨sound70,List.forall_mem_cons.mpr ⟨sound71,List.forall_mem_cons.mpr ⟨sound72,List.forall_mem_cons.mpr ⟨sound73,List.forall_mem_cons.mpr ⟨sound74,List.forall_mem_cons.mpr ⟨sound75,List.forall_mem_cons.mpr ⟨sound76,List.forall_mem_cons.mpr ⟨sound77,List.forall_mem_cons.mpr ⟨sound78,List.forall_mem_cons.mpr ⟨sound79,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch003
