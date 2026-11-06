import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch024
import Cycle12.CertifiedGlobalFailures.Batch024
import Cycle12.CertifiedLocalFailures.Batch003
import Cycle12.CutFailureCertificates.Budget051
import Cycle12.CutFailureCertificates.Budget052
import Cycle12.CutFailureCertificates.Budget053
import Cycle12.DegreeCertificates.Batch024
import Cycle12.GeometryCertificates.Batch051
import Cycle12.GeometryCertificates.Batch052
import Cycle12.GeometryCertificates.Batch053
import Cycle12.MomentCertificates.Batch024
import Cycle12.WitnessCertificates.Batch051
import Cycle12.WitnessCertificates.Batch052
import Cycle12.WitnessCertificates.Batch053

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch024
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate480 : RatSamplerCase := ⟨MomentCertificates.Batch024.certificate480,DegreeCertificates.Batch024.certificate480,(WitnessCertificates.Batch051.certificate1025).beta,(WitnessCertificates.Batch051.certificate1026).L,(some (WitnessCertificates.Batch051.certificate1027).beta),(CutFailureCertificates.Budget051.certificate1025).bound,(CutFailureCertificates.Budget051.certificate1026).bound,(CutFailureCertificates.Budget051.certificate1027).bound⟩
theorem numericValid480 : certificate480.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound480 : certificate480.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch051.certificate1025 H MomentCertificates.Batch024.valid480.1 GeometryCertificates.Batch051.valid1025 GeometryCertificates.Batch051.sound1025 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch051.certificate1026 H MomentCertificates.Batch024.valid480.1 GeometryCertificates.Batch051.valid1026 GeometryCertificates.Batch051.sound1026 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch024.probabilityBound480 H st hI
  have hanchor := CertifiedAnchorFailures.Batch024.probabilityBound480 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch051.certificate1027 H MomentCertificates.Batch024.valid480.1 GeometryCertificates.Batch051.valid1027 GeometryCertificates.Batch051.sound1027 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound65 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch051.certificate1027).dm = (DegreeCertificates.Batch024.certificate480).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate480 GeometryCertificates.Batch051.certificate1025 numericValid480
    MomentCertificates.Batch024.valid480 DegreeCertificates.Batch024.valid480 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate480,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate481 : RatSamplerCase := ⟨MomentCertificates.Batch024.certificate481,DegreeCertificates.Batch024.certificate481,(WitnessCertificates.Batch051.certificate1028).beta,(WitnessCertificates.Batch051.certificate1029).L,(some (WitnessCertificates.Batch051.certificate1030).beta),(CutFailureCertificates.Budget051.certificate1028).bound,(CutFailureCertificates.Budget051.certificate1029).bound,(CutFailureCertificates.Budget051.certificate1030).bound⟩
theorem numericValid481 : certificate481.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound481 : certificate481.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch051.certificate1028 H MomentCertificates.Batch024.valid481.1 GeometryCertificates.Batch051.valid1028 GeometryCertificates.Batch051.sound1028 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch051.certificate1029 H MomentCertificates.Batch024.valid481.1 GeometryCertificates.Batch051.valid1029 GeometryCertificates.Batch051.sound1029 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch024.probabilityBound481 H st hI
  have hanchor := CertifiedAnchorFailures.Batch024.probabilityBound481 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch051.certificate1030 H MomentCertificates.Batch024.valid481.1 GeometryCertificates.Batch051.valid1030 GeometryCertificates.Batch051.sound1030 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound66 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch051.certificate1030).dm = (DegreeCertificates.Batch024.certificate481).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate481 GeometryCertificates.Batch051.certificate1028 numericValid481
    MomentCertificates.Batch024.valid481 DegreeCertificates.Batch024.valid481 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate481,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate482 : RatSamplerCase := ⟨MomentCertificates.Batch024.certificate482,DegreeCertificates.Batch024.certificate482,(WitnessCertificates.Batch051.certificate1031).beta,(WitnessCertificates.Batch051.certificate1032).L,(some (WitnessCertificates.Batch051.certificate1033).beta),(CutFailureCertificates.Budget051.certificate1031).bound,(CutFailureCertificates.Budget051.certificate1032).bound,(CutFailureCertificates.Budget051.certificate1033).bound⟩
theorem numericValid482 : certificate482.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound482 : certificate482.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch051.certificate1031 H MomentCertificates.Batch024.valid482.1 GeometryCertificates.Batch051.valid1031 GeometryCertificates.Batch051.sound1031 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch051.certificate1032 H MomentCertificates.Batch024.valid482.1 GeometryCertificates.Batch051.valid1032 GeometryCertificates.Batch051.sound1032 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch024.probabilityBound482 H st hI
  have hanchor := CertifiedAnchorFailures.Batch024.probabilityBound482 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch051.certificate1033 H MomentCertificates.Batch024.valid482.1 GeometryCertificates.Batch051.valid1033 GeometryCertificates.Batch051.sound1033 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound67 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch051.certificate1033).dm = (DegreeCertificates.Batch024.certificate482).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate482 GeometryCertificates.Batch051.certificate1031 numericValid482
    MomentCertificates.Batch024.valid482 DegreeCertificates.Batch024.valid482 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate482,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate483 : RatSamplerCase := ⟨MomentCertificates.Batch024.certificate483,DegreeCertificates.Batch024.certificate483,(WitnessCertificates.Batch051.certificate1034).beta,(WitnessCertificates.Batch051.certificate1035).L,(some (WitnessCertificates.Batch051.certificate1036).beta),(CutFailureCertificates.Budget051.certificate1034).bound,(CutFailureCertificates.Budget051.certificate1035).bound,(CutFailureCertificates.Budget051.certificate1036).bound⟩
theorem numericValid483 : certificate483.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound483 : certificate483.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch051.certificate1034 H MomentCertificates.Batch024.valid483.1 GeometryCertificates.Batch051.valid1034 GeometryCertificates.Batch051.sound1034 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch051.certificate1035 H MomentCertificates.Batch024.valid483.1 GeometryCertificates.Batch051.valid1035 GeometryCertificates.Batch051.sound1035 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch024.probabilityBound483 H st hI
  have hanchor := CertifiedAnchorFailures.Batch024.probabilityBound483 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch051.certificate1036 H MomentCertificates.Batch024.valid483.1 GeometryCertificates.Batch051.valid1036 GeometryCertificates.Batch051.sound1036 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound68 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch051.certificate1036).dm = (DegreeCertificates.Batch024.certificate483).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate483 GeometryCertificates.Batch051.certificate1034 numericValid483
    MomentCertificates.Batch024.valid483 DegreeCertificates.Batch024.valid483 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate483,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate484 : RatSamplerCase := ⟨MomentCertificates.Batch024.certificate484,DegreeCertificates.Batch024.certificate484,(WitnessCertificates.Batch051.certificate1037).beta,(WitnessCertificates.Batch051.certificate1038).L,(some (WitnessCertificates.Batch051.certificate1039).beta),(CutFailureCertificates.Budget051.certificate1037).bound,(CutFailureCertificates.Budget051.certificate1038).bound,(CutFailureCertificates.Budget051.certificate1039).bound⟩
theorem numericValid484 : certificate484.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound484 : certificate484.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch051.certificate1037 H MomentCertificates.Batch024.valid484.1 GeometryCertificates.Batch051.valid1037 GeometryCertificates.Batch051.sound1037 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch051.certificate1038 H MomentCertificates.Batch024.valid484.1 GeometryCertificates.Batch051.valid1038 GeometryCertificates.Batch051.sound1038 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch024.probabilityBound484 H st hI
  have hanchor := CertifiedAnchorFailures.Batch024.probabilityBound484 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch051.certificate1039 H MomentCertificates.Batch024.valid484.1 GeometryCertificates.Batch051.valid1039 GeometryCertificates.Batch051.sound1039 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound69 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch051.certificate1039).dm = (DegreeCertificates.Batch024.certificate484).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate484 GeometryCertificates.Batch051.certificate1037 numericValid484
    MomentCertificates.Batch024.valid484 DegreeCertificates.Batch024.valid484 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate484,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate485 : RatSamplerCase := ⟨MomentCertificates.Batch024.certificate485,DegreeCertificates.Batch024.certificate485,(WitnessCertificates.Batch052.certificate1040).beta,(WitnessCertificates.Batch052.certificate1041).L,(some (WitnessCertificates.Batch052.certificate1042).beta),(CutFailureCertificates.Budget052.certificate1040).bound,(CutFailureCertificates.Budget052.certificate1041).bound,(CutFailureCertificates.Budget052.certificate1042).bound⟩
theorem numericValid485 : certificate485.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound485 : certificate485.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch052.certificate1040 H MomentCertificates.Batch024.valid485.1 GeometryCertificates.Batch052.valid1040 GeometryCertificates.Batch052.sound1040 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch052.certificate1041 H MomentCertificates.Batch024.valid485.1 GeometryCertificates.Batch052.valid1041 GeometryCertificates.Batch052.sound1041 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch024.probabilityBound485 H st hI
  have hanchor := CertifiedAnchorFailures.Batch024.probabilityBound485 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch052.certificate1042 H MomentCertificates.Batch024.valid485.1 GeometryCertificates.Batch052.valid1042 GeometryCertificates.Batch052.sound1042 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound70 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch052.certificate1042).dm = (DegreeCertificates.Batch024.certificate485).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate485 GeometryCertificates.Batch052.certificate1040 numericValid485
    MomentCertificates.Batch024.valid485 DegreeCertificates.Batch024.valid485 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate485,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate486 : RatSamplerCase := ⟨MomentCertificates.Batch024.certificate486,DegreeCertificates.Batch024.certificate486,(WitnessCertificates.Batch052.certificate1043).beta,(WitnessCertificates.Batch052.certificate1044).L,(some (WitnessCertificates.Batch052.certificate1045).beta),(CutFailureCertificates.Budget052.certificate1043).bound,(CutFailureCertificates.Budget052.certificate1044).bound,(CutFailureCertificates.Budget052.certificate1045).bound⟩
theorem numericValid486 : certificate486.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound486 : certificate486.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch052.certificate1043 H MomentCertificates.Batch024.valid486.1 GeometryCertificates.Batch052.valid1043 GeometryCertificates.Batch052.sound1043 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch052.certificate1044 H MomentCertificates.Batch024.valid486.1 GeometryCertificates.Batch052.valid1044 GeometryCertificates.Batch052.sound1044 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch024.probabilityBound486 H st hI
  have hanchor := CertifiedAnchorFailures.Batch024.probabilityBound486 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch052.certificate1045 H MomentCertificates.Batch024.valid486.1 GeometryCertificates.Batch052.valid1045 GeometryCertificates.Batch052.sound1045 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound71 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch052.certificate1045).dm = (DegreeCertificates.Batch024.certificate486).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate486 GeometryCertificates.Batch052.certificate1043 numericValid486
    MomentCertificates.Batch024.valid486 DegreeCertificates.Batch024.valid486 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate486,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate487 : RatSamplerCase := ⟨MomentCertificates.Batch024.certificate487,DegreeCertificates.Batch024.certificate487,(WitnessCertificates.Batch052.certificate1046).beta,(WitnessCertificates.Batch052.certificate1047).L,(some (WitnessCertificates.Batch052.certificate1048).beta),(CutFailureCertificates.Budget052.certificate1046).bound,(CutFailureCertificates.Budget052.certificate1047).bound,(CutFailureCertificates.Budget052.certificate1048).bound⟩
theorem numericValid487 : certificate487.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound487 : certificate487.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch052.certificate1046 H MomentCertificates.Batch024.valid487.1 GeometryCertificates.Batch052.valid1046 GeometryCertificates.Batch052.sound1046 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch052.certificate1047 H MomentCertificates.Batch024.valid487.1 GeometryCertificates.Batch052.valid1047 GeometryCertificates.Batch052.sound1047 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch024.probabilityBound487 H st hI
  have hanchor := CertifiedAnchorFailures.Batch024.probabilityBound487 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch052.certificate1048 H MomentCertificates.Batch024.valid487.1 GeometryCertificates.Batch052.valid1048 GeometryCertificates.Batch052.sound1048 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound72 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch052.certificate1048).dm = (DegreeCertificates.Batch024.certificate487).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate487 GeometryCertificates.Batch052.certificate1046 numericValid487
    MomentCertificates.Batch024.valid487 DegreeCertificates.Batch024.valid487 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate487,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate488 : RatSamplerCase := ⟨MomentCertificates.Batch024.certificate488,DegreeCertificates.Batch024.certificate488,(WitnessCertificates.Batch052.certificate1049).beta,(WitnessCertificates.Batch052.certificate1050).L,(some (WitnessCertificates.Batch052.certificate1051).beta),(CutFailureCertificates.Budget052.certificate1049).bound,(CutFailureCertificates.Budget052.certificate1050).bound,(CutFailureCertificates.Budget052.certificate1051).bound⟩
theorem numericValid488 : certificate488.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound488 : certificate488.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch052.certificate1049 H MomentCertificates.Batch024.valid488.1 GeometryCertificates.Batch052.valid1049 GeometryCertificates.Batch052.sound1049 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch052.certificate1050 H MomentCertificates.Batch024.valid488.1 GeometryCertificates.Batch052.valid1050 GeometryCertificates.Batch052.sound1050 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch024.probabilityBound488 H st hI
  have hanchor := CertifiedAnchorFailures.Batch024.probabilityBound488 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch052.certificate1051 H MomentCertificates.Batch024.valid488.1 GeometryCertificates.Batch052.valid1051 GeometryCertificates.Batch052.sound1051 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound73 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch052.certificate1051).dm = (DegreeCertificates.Batch024.certificate488).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate488 GeometryCertificates.Batch052.certificate1049 numericValid488
    MomentCertificates.Batch024.valid488 DegreeCertificates.Batch024.valid488 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate488,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate489 : RatSamplerCase := ⟨MomentCertificates.Batch024.certificate489,DegreeCertificates.Batch024.certificate489,(WitnessCertificates.Batch052.certificate1052).beta,(WitnessCertificates.Batch052.certificate1053).L,(some (WitnessCertificates.Batch052.certificate1054).beta),(CutFailureCertificates.Budget052.certificate1052).bound,(CutFailureCertificates.Budget052.certificate1053).bound,(CutFailureCertificates.Budget052.certificate1054).bound⟩
theorem numericValid489 : certificate489.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound489 : certificate489.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch052.certificate1052 H MomentCertificates.Batch024.valid489.1 GeometryCertificates.Batch052.valid1052 GeometryCertificates.Batch052.sound1052 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch052.certificate1053 H MomentCertificates.Batch024.valid489.1 GeometryCertificates.Batch052.valid1053 GeometryCertificates.Batch052.sound1053 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch024.probabilityBound489 H st hI
  have hanchor := CertifiedAnchorFailures.Batch024.probabilityBound489 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch052.certificate1054 H MomentCertificates.Batch024.valid489.1 GeometryCertificates.Batch052.valid1054 GeometryCertificates.Batch052.sound1054 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound74 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch052.certificate1054).dm = (DegreeCertificates.Batch024.certificate489).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate489 GeometryCertificates.Batch052.certificate1052 numericValid489
    MomentCertificates.Batch024.valid489 DegreeCertificates.Batch024.valid489 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate489,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate490 : RatSamplerCase := ⟨MomentCertificates.Batch024.certificate490,DegreeCertificates.Batch024.certificate490,(WitnessCertificates.Batch052.certificate1055).beta,(WitnessCertificates.Batch052.certificate1056).L,(some (WitnessCertificates.Batch052.certificate1057).beta),(CutFailureCertificates.Budget052.certificate1055).bound,(CutFailureCertificates.Budget052.certificate1056).bound,(CutFailureCertificates.Budget052.certificate1057).bound⟩
theorem numericValid490 : certificate490.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound490 : certificate490.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch052.certificate1055 H MomentCertificates.Batch024.valid490.1 GeometryCertificates.Batch052.valid1055 GeometryCertificates.Batch052.sound1055 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch052.certificate1056 H MomentCertificates.Batch024.valid490.1 GeometryCertificates.Batch052.valid1056 GeometryCertificates.Batch052.sound1056 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch024.probabilityBound490 H st hI
  have hanchor := CertifiedAnchorFailures.Batch024.probabilityBound490 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch052.certificate1057 H MomentCertificates.Batch024.valid490.1 GeometryCertificates.Batch052.valid1057 GeometryCertificates.Batch052.sound1057 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound75 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch052.certificate1057).dm = (DegreeCertificates.Batch024.certificate490).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate490 GeometryCertificates.Batch052.certificate1055 numericValid490
    MomentCertificates.Batch024.valid490 DegreeCertificates.Batch024.valid490 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate490,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate491 : RatSamplerCase := ⟨MomentCertificates.Batch024.certificate491,DegreeCertificates.Batch024.certificate491,(WitnessCertificates.Batch052.certificate1058).beta,(WitnessCertificates.Batch052.certificate1059).L,(some (WitnessCertificates.Batch053.certificate1060).beta),(CutFailureCertificates.Budget052.certificate1058).bound,(CutFailureCertificates.Budget052.certificate1059).bound,(CutFailureCertificates.Budget053.certificate1060).bound⟩
theorem numericValid491 : certificate491.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound491 : certificate491.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch052.certificate1058 H MomentCertificates.Batch024.valid491.1 GeometryCertificates.Batch052.valid1058 GeometryCertificates.Batch052.sound1058 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch052.certificate1059 H MomentCertificates.Batch024.valid491.1 GeometryCertificates.Batch052.valid1059 GeometryCertificates.Batch052.sound1059 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch024.probabilityBound491 H st hI
  have hanchor := CertifiedAnchorFailures.Batch024.probabilityBound491 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch053.certificate1060 H MomentCertificates.Batch024.valid491.1 GeometryCertificates.Batch053.valid1060 GeometryCertificates.Batch053.sound1060 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound76 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch053.certificate1060).dm = (DegreeCertificates.Batch024.certificate491).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate491 GeometryCertificates.Batch052.certificate1058 numericValid491
    MomentCertificates.Batch024.valid491 DegreeCertificates.Batch024.valid491 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate491,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate492 : RatSamplerCase := ⟨MomentCertificates.Batch024.certificate492,DegreeCertificates.Batch024.certificate492,(WitnessCertificates.Batch053.certificate1061).beta,(WitnessCertificates.Batch053.certificate1062).L,(some (WitnessCertificates.Batch053.certificate1063).beta),(CutFailureCertificates.Budget053.certificate1061).bound,(CutFailureCertificates.Budget053.certificate1062).bound,(CutFailureCertificates.Budget053.certificate1063).bound⟩
theorem numericValid492 : certificate492.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound492 : certificate492.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch053.certificate1061 H MomentCertificates.Batch024.valid492.1 GeometryCertificates.Batch053.valid1061 GeometryCertificates.Batch053.sound1061 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch053.certificate1062 H MomentCertificates.Batch024.valid492.1 GeometryCertificates.Batch053.valid1062 GeometryCertificates.Batch053.sound1062 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch024.probabilityBound492 H st hI
  have hanchor := CertifiedAnchorFailures.Batch024.probabilityBound492 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch053.certificate1063 H MomentCertificates.Batch024.valid492.1 GeometryCertificates.Batch053.valid1063 GeometryCertificates.Batch053.sound1063 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound77 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch053.certificate1063).dm = (DegreeCertificates.Batch024.certificate492).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate492 GeometryCertificates.Batch053.certificate1061 numericValid492
    MomentCertificates.Batch024.valid492 DegreeCertificates.Batch024.valid492 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate492,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate493 : RatSamplerCase := ⟨MomentCertificates.Batch024.certificate493,DegreeCertificates.Batch024.certificate493,(WitnessCertificates.Batch053.certificate1064).beta,(WitnessCertificates.Batch053.certificate1065).L,(some (WitnessCertificates.Batch053.certificate1066).beta),(CutFailureCertificates.Budget053.certificate1064).bound,(CutFailureCertificates.Budget053.certificate1065).bound,(CutFailureCertificates.Budget053.certificate1066).bound⟩
theorem numericValid493 : certificate493.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound493 : certificate493.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch053.certificate1064 H MomentCertificates.Batch024.valid493.1 GeometryCertificates.Batch053.valid1064 GeometryCertificates.Batch053.sound1064 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch053.certificate1065 H MomentCertificates.Batch024.valid493.1 GeometryCertificates.Batch053.valid1065 GeometryCertificates.Batch053.sound1065 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch024.probabilityBound493 H st hI
  have hanchor := CertifiedAnchorFailures.Batch024.probabilityBound493 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch053.certificate1066 H MomentCertificates.Batch024.valid493.1 GeometryCertificates.Batch053.valid1066 GeometryCertificates.Batch053.sound1066 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound78 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch053.certificate1066).dm = (DegreeCertificates.Batch024.certificate493).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate493 GeometryCertificates.Batch053.certificate1064 numericValid493
    MomentCertificates.Batch024.valid493 DegreeCertificates.Batch024.valid493 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate493,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate480,certificate481,certificate482,certificate483,certificate484,certificate485,certificate486,certificate487,certificate488,certificate489,certificate490,certificate491,certificate492,certificate493]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound480,List.forall_mem_cons.mpr ⟨sound481,List.forall_mem_cons.mpr ⟨sound482,List.forall_mem_cons.mpr ⟨sound483,List.forall_mem_cons.mpr ⟨sound484,List.forall_mem_cons.mpr ⟨sound485,List.forall_mem_cons.mpr ⟨sound486,List.forall_mem_cons.mpr ⟨sound487,List.forall_mem_cons.mpr ⟨sound488,List.forall_mem_cons.mpr ⟨sound489,List.forall_mem_cons.mpr ⟨sound490,List.forall_mem_cons.mpr ⟨sound491,List.forall_mem_cons.mpr ⟨sound492,List.forall_mem_cons.mpr ⟨sound493,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch024
