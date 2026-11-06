import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch015
import Cycle12.CertifiedGlobalFailures.Batch015
import Cycle12.CutFailureCertificates.Budget030
import Cycle12.CutFailureCertificates.Budget031
import Cycle12.DegreeCertificates.Batch015
import Cycle12.GeometryCertificates.Batch030
import Cycle12.GeometryCertificates.Batch031
import Cycle12.MomentCertificates.Batch015
import Cycle12.WitnessCertificates.Batch030
import Cycle12.WitnessCertificates.Batch031

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch015
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate300 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate300,DegreeCertificates.Batch015.certificate300,(WitnessCertificates.Batch030.certificate600).beta,(WitnessCertificates.Batch030.certificate601).L,none,(CutFailureCertificates.Budget030.certificate600).bound,(CutFailureCertificates.Budget030.certificate601).bound,0⟩
theorem numericValid300 : certificate300.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound300 : certificate300.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch030.certificate600 H MomentCertificates.Batch015.valid300.1 GeometryCertificates.Batch030.valid600 GeometryCertificates.Batch030.sound600 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch030.certificate601 H MomentCertificates.Batch015.valid300.1 GeometryCertificates.Batch030.valid601 GeometryCertificates.Batch030.sound601 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound300 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound300 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate300 GeometryCertificates.Batch030.certificate600 numericValid300
    MomentCertificates.Batch015.valid300 DegreeCertificates.Batch015.valid300 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate300,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate301 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate301,DegreeCertificates.Batch015.certificate301,(WitnessCertificates.Batch030.certificate602).beta,(WitnessCertificates.Batch030.certificate603).L,none,(CutFailureCertificates.Budget030.certificate602).bound,(CutFailureCertificates.Budget030.certificate603).bound,0⟩
theorem numericValid301 : certificate301.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound301 : certificate301.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch030.certificate602 H MomentCertificates.Batch015.valid301.1 GeometryCertificates.Batch030.valid602 GeometryCertificates.Batch030.sound602 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch030.certificate603 H MomentCertificates.Batch015.valid301.1 GeometryCertificates.Batch030.valid603 GeometryCertificates.Batch030.sound603 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound301 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound301 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate301 GeometryCertificates.Batch030.certificate602 numericValid301
    MomentCertificates.Batch015.valid301 DegreeCertificates.Batch015.valid301 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate301,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate302 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate302,DegreeCertificates.Batch015.certificate302,(WitnessCertificates.Batch030.certificate604).beta,(WitnessCertificates.Batch030.certificate605).L,none,(CutFailureCertificates.Budget030.certificate604).bound,(CutFailureCertificates.Budget030.certificate605).bound,0⟩
theorem numericValid302 : certificate302.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound302 : certificate302.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch030.certificate604 H MomentCertificates.Batch015.valid302.1 GeometryCertificates.Batch030.valid604 GeometryCertificates.Batch030.sound604 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch030.certificate605 H MomentCertificates.Batch015.valid302.1 GeometryCertificates.Batch030.valid605 GeometryCertificates.Batch030.sound605 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound302 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound302 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate302 GeometryCertificates.Batch030.certificate604 numericValid302
    MomentCertificates.Batch015.valid302 DegreeCertificates.Batch015.valid302 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate302,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate303 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate303,DegreeCertificates.Batch015.certificate303,(WitnessCertificates.Batch030.certificate606).beta,(WitnessCertificates.Batch030.certificate607).L,none,(CutFailureCertificates.Budget030.certificate606).bound,(CutFailureCertificates.Budget030.certificate607).bound,0⟩
theorem numericValid303 : certificate303.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound303 : certificate303.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch030.certificate606 H MomentCertificates.Batch015.valid303.1 GeometryCertificates.Batch030.valid606 GeometryCertificates.Batch030.sound606 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch030.certificate607 H MomentCertificates.Batch015.valid303.1 GeometryCertificates.Batch030.valid607 GeometryCertificates.Batch030.sound607 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound303 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound303 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate303 GeometryCertificates.Batch030.certificate606 numericValid303
    MomentCertificates.Batch015.valid303 DegreeCertificates.Batch015.valid303 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate303,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate304 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate304,DegreeCertificates.Batch015.certificate304,(WitnessCertificates.Batch030.certificate608).beta,(WitnessCertificates.Batch030.certificate609).L,none,(CutFailureCertificates.Budget030.certificate608).bound,(CutFailureCertificates.Budget030.certificate609).bound,0⟩
theorem numericValid304 : certificate304.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound304 : certificate304.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch030.certificate608 H MomentCertificates.Batch015.valid304.1 GeometryCertificates.Batch030.valid608 GeometryCertificates.Batch030.sound608 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch030.certificate609 H MomentCertificates.Batch015.valid304.1 GeometryCertificates.Batch030.valid609 GeometryCertificates.Batch030.sound609 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound304 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound304 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate304 GeometryCertificates.Batch030.certificate608 numericValid304
    MomentCertificates.Batch015.valid304 DegreeCertificates.Batch015.valid304 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate304,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate305 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate305,DegreeCertificates.Batch015.certificate305,(WitnessCertificates.Batch030.certificate610).beta,(WitnessCertificates.Batch030.certificate611).L,none,(CutFailureCertificates.Budget030.certificate610).bound,(CutFailureCertificates.Budget030.certificate611).bound,0⟩
theorem numericValid305 : certificate305.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound305 : certificate305.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch030.certificate610 H MomentCertificates.Batch015.valid305.1 GeometryCertificates.Batch030.valid610 GeometryCertificates.Batch030.sound610 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch030.certificate611 H MomentCertificates.Batch015.valid305.1 GeometryCertificates.Batch030.valid611 GeometryCertificates.Batch030.sound611 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound305 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound305 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate305 GeometryCertificates.Batch030.certificate610 numericValid305
    MomentCertificates.Batch015.valid305 DegreeCertificates.Batch015.valid305 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate305,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate306 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate306,DegreeCertificates.Batch015.certificate306,(WitnessCertificates.Batch030.certificate612).beta,(WitnessCertificates.Batch030.certificate613).L,none,(CutFailureCertificates.Budget030.certificate612).bound,(CutFailureCertificates.Budget030.certificate613).bound,0⟩
theorem numericValid306 : certificate306.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound306 : certificate306.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch030.certificate612 H MomentCertificates.Batch015.valid306.1 GeometryCertificates.Batch030.valid612 GeometryCertificates.Batch030.sound612 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch030.certificate613 H MomentCertificates.Batch015.valid306.1 GeometryCertificates.Batch030.valid613 GeometryCertificates.Batch030.sound613 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound306 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound306 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate306 GeometryCertificates.Batch030.certificate612 numericValid306
    MomentCertificates.Batch015.valid306 DegreeCertificates.Batch015.valid306 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate306,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate307 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate307,DegreeCertificates.Batch015.certificate307,(WitnessCertificates.Batch030.certificate614).beta,(WitnessCertificates.Batch030.certificate615).L,none,(CutFailureCertificates.Budget030.certificate614).bound,(CutFailureCertificates.Budget030.certificate615).bound,0⟩
theorem numericValid307 : certificate307.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound307 : certificate307.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch030.certificate614 H MomentCertificates.Batch015.valid307.1 GeometryCertificates.Batch030.valid614 GeometryCertificates.Batch030.sound614 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch030.certificate615 H MomentCertificates.Batch015.valid307.1 GeometryCertificates.Batch030.valid615 GeometryCertificates.Batch030.sound615 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound307 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound307 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate307 GeometryCertificates.Batch030.certificate614 numericValid307
    MomentCertificates.Batch015.valid307 DegreeCertificates.Batch015.valid307 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate307,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate308 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate308,DegreeCertificates.Batch015.certificate308,(WitnessCertificates.Batch030.certificate616).beta,(WitnessCertificates.Batch030.certificate617).L,none,(CutFailureCertificates.Budget030.certificate616).bound,(CutFailureCertificates.Budget030.certificate617).bound,0⟩
theorem numericValid308 : certificate308.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound308 : certificate308.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch030.certificate616 H MomentCertificates.Batch015.valid308.1 GeometryCertificates.Batch030.valid616 GeometryCertificates.Batch030.sound616 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch030.certificate617 H MomentCertificates.Batch015.valid308.1 GeometryCertificates.Batch030.valid617 GeometryCertificates.Batch030.sound617 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound308 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound308 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate308 GeometryCertificates.Batch030.certificate616 numericValid308
    MomentCertificates.Batch015.valid308 DegreeCertificates.Batch015.valid308 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate308,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate309 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate309,DegreeCertificates.Batch015.certificate309,(WitnessCertificates.Batch030.certificate618).beta,(WitnessCertificates.Batch030.certificate619).L,none,(CutFailureCertificates.Budget030.certificate618).bound,(CutFailureCertificates.Budget030.certificate619).bound,0⟩
theorem numericValid309 : certificate309.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound309 : certificate309.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch030.certificate618 H MomentCertificates.Batch015.valid309.1 GeometryCertificates.Batch030.valid618 GeometryCertificates.Batch030.sound618 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch030.certificate619 H MomentCertificates.Batch015.valid309.1 GeometryCertificates.Batch030.valid619 GeometryCertificates.Batch030.sound619 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound309 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound309 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate309 GeometryCertificates.Batch030.certificate618 numericValid309
    MomentCertificates.Batch015.valid309 DegreeCertificates.Batch015.valid309 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate309,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate310 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate310,DegreeCertificates.Batch015.certificate310,(WitnessCertificates.Batch031.certificate620).beta,(WitnessCertificates.Batch031.certificate621).L,none,(CutFailureCertificates.Budget031.certificate620).bound,(CutFailureCertificates.Budget031.certificate621).bound,0⟩
theorem numericValid310 : certificate310.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound310 : certificate310.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch031.certificate620 H MomentCertificates.Batch015.valid310.1 GeometryCertificates.Batch031.valid620 GeometryCertificates.Batch031.sound620 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch031.certificate621 H MomentCertificates.Batch015.valid310.1 GeometryCertificates.Batch031.valid621 GeometryCertificates.Batch031.sound621 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound310 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound310 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate310 GeometryCertificates.Batch031.certificate620 numericValid310
    MomentCertificates.Batch015.valid310 DegreeCertificates.Batch015.valid310 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate310,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate311 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate311,DegreeCertificates.Batch015.certificate311,(WitnessCertificates.Batch031.certificate622).beta,(WitnessCertificates.Batch031.certificate623).L,none,(CutFailureCertificates.Budget031.certificate622).bound,(CutFailureCertificates.Budget031.certificate623).bound,0⟩
theorem numericValid311 : certificate311.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound311 : certificate311.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch031.certificate622 H MomentCertificates.Batch015.valid311.1 GeometryCertificates.Batch031.valid622 GeometryCertificates.Batch031.sound622 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch031.certificate623 H MomentCertificates.Batch015.valid311.1 GeometryCertificates.Batch031.valid623 GeometryCertificates.Batch031.sound623 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound311 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound311 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate311 GeometryCertificates.Batch031.certificate622 numericValid311
    MomentCertificates.Batch015.valid311 DegreeCertificates.Batch015.valid311 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate311,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate312 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate312,DegreeCertificates.Batch015.certificate312,(WitnessCertificates.Batch031.certificate624).beta,(WitnessCertificates.Batch031.certificate625).L,none,(CutFailureCertificates.Budget031.certificate624).bound,(CutFailureCertificates.Budget031.certificate625).bound,0⟩
theorem numericValid312 : certificate312.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound312 : certificate312.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch031.certificate624 H MomentCertificates.Batch015.valid312.1 GeometryCertificates.Batch031.valid624 GeometryCertificates.Batch031.sound624 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch031.certificate625 H MomentCertificates.Batch015.valid312.1 GeometryCertificates.Batch031.valid625 GeometryCertificates.Batch031.sound625 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound312 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound312 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate312 GeometryCertificates.Batch031.certificate624 numericValid312
    MomentCertificates.Batch015.valid312 DegreeCertificates.Batch015.valid312 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate312,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate313 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate313,DegreeCertificates.Batch015.certificate313,(WitnessCertificates.Batch031.certificate626).beta,(WitnessCertificates.Batch031.certificate627).L,none,(CutFailureCertificates.Budget031.certificate626).bound,(CutFailureCertificates.Budget031.certificate627).bound,0⟩
theorem numericValid313 : certificate313.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound313 : certificate313.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch031.certificate626 H MomentCertificates.Batch015.valid313.1 GeometryCertificates.Batch031.valid626 GeometryCertificates.Batch031.sound626 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch031.certificate627 H MomentCertificates.Batch015.valid313.1 GeometryCertificates.Batch031.valid627 GeometryCertificates.Batch031.sound627 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound313 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound313 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate313 GeometryCertificates.Batch031.certificate626 numericValid313
    MomentCertificates.Batch015.valid313 DegreeCertificates.Batch015.valid313 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate313,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate314 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate314,DegreeCertificates.Batch015.certificate314,(WitnessCertificates.Batch031.certificate628).beta,(WitnessCertificates.Batch031.certificate629).L,none,(CutFailureCertificates.Budget031.certificate628).bound,(CutFailureCertificates.Budget031.certificate629).bound,0⟩
theorem numericValid314 : certificate314.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound314 : certificate314.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch031.certificate628 H MomentCertificates.Batch015.valid314.1 GeometryCertificates.Batch031.valid628 GeometryCertificates.Batch031.sound628 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch031.certificate629 H MomentCertificates.Batch015.valid314.1 GeometryCertificates.Batch031.valid629 GeometryCertificates.Batch031.sound629 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound314 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound314 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate314 GeometryCertificates.Batch031.certificate628 numericValid314
    MomentCertificates.Batch015.valid314 DegreeCertificates.Batch015.valid314 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate314,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate315 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate315,DegreeCertificates.Batch015.certificate315,(WitnessCertificates.Batch031.certificate630).beta,(WitnessCertificates.Batch031.certificate631).L,none,(CutFailureCertificates.Budget031.certificate630).bound,(CutFailureCertificates.Budget031.certificate631).bound,0⟩
theorem numericValid315 : certificate315.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound315 : certificate315.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch031.certificate630 H MomentCertificates.Batch015.valid315.1 GeometryCertificates.Batch031.valid630 GeometryCertificates.Batch031.sound630 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch031.certificate631 H MomentCertificates.Batch015.valid315.1 GeometryCertificates.Batch031.valid631 GeometryCertificates.Batch031.sound631 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound315 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound315 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate315 GeometryCertificates.Batch031.certificate630 numericValid315
    MomentCertificates.Batch015.valid315 DegreeCertificates.Batch015.valid315 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate315,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate316 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate316,DegreeCertificates.Batch015.certificate316,(WitnessCertificates.Batch031.certificate632).beta,(WitnessCertificates.Batch031.certificate633).L,none,(CutFailureCertificates.Budget031.certificate632).bound,(CutFailureCertificates.Budget031.certificate633).bound,0⟩
theorem numericValid316 : certificate316.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound316 : certificate316.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch031.certificate632 H MomentCertificates.Batch015.valid316.1 GeometryCertificates.Batch031.valid632 GeometryCertificates.Batch031.sound632 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch031.certificate633 H MomentCertificates.Batch015.valid316.1 GeometryCertificates.Batch031.valid633 GeometryCertificates.Batch031.sound633 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound316 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound316 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate316 GeometryCertificates.Batch031.certificate632 numericValid316
    MomentCertificates.Batch015.valid316 DegreeCertificates.Batch015.valid316 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate316,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate317 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate317,DegreeCertificates.Batch015.certificate317,(WitnessCertificates.Batch031.certificate634).beta,(WitnessCertificates.Batch031.certificate635).L,none,(CutFailureCertificates.Budget031.certificate634).bound,(CutFailureCertificates.Budget031.certificate635).bound,0⟩
theorem numericValid317 : certificate317.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound317 : certificate317.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch031.certificate634 H MomentCertificates.Batch015.valid317.1 GeometryCertificates.Batch031.valid634 GeometryCertificates.Batch031.sound634 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch031.certificate635 H MomentCertificates.Batch015.valid317.1 GeometryCertificates.Batch031.valid635 GeometryCertificates.Batch031.sound635 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound317 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound317 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate317 GeometryCertificates.Batch031.certificate634 numericValid317
    MomentCertificates.Batch015.valid317 DegreeCertificates.Batch015.valid317 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate317,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate318 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate318,DegreeCertificates.Batch015.certificate318,(WitnessCertificates.Batch031.certificate636).beta,(WitnessCertificates.Batch031.certificate637).L,none,(CutFailureCertificates.Budget031.certificate636).bound,(CutFailureCertificates.Budget031.certificate637).bound,0⟩
theorem numericValid318 : certificate318.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound318 : certificate318.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch031.certificate636 H MomentCertificates.Batch015.valid318.1 GeometryCertificates.Batch031.valid636 GeometryCertificates.Batch031.sound636 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch031.certificate637 H MomentCertificates.Batch015.valid318.1 GeometryCertificates.Batch031.valid637 GeometryCertificates.Batch031.sound637 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound318 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound318 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate318 GeometryCertificates.Batch031.certificate636 numericValid318
    MomentCertificates.Batch015.valid318 DegreeCertificates.Batch015.valid318 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate318,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate319 : RatSamplerCase := ⟨MomentCertificates.Batch015.certificate319,DegreeCertificates.Batch015.certificate319,(WitnessCertificates.Batch031.certificate638).beta,(WitnessCertificates.Batch031.certificate639).L,none,(CutFailureCertificates.Budget031.certificate638).bound,(CutFailureCertificates.Budget031.certificate639).bound,0⟩
theorem numericValid319 : certificate319.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound319 : certificate319.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch031.certificate638 H MomentCertificates.Batch015.valid319.1 GeometryCertificates.Batch031.valid638 GeometryCertificates.Batch031.sound638 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch031.certificate639 H MomentCertificates.Batch015.valid319.1 GeometryCertificates.Batch031.valid639 GeometryCertificates.Batch031.sound639 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch015.probabilityBound319 H st hI
  have hanchor := CertifiedAnchorFailures.Batch015.probabilityBound319 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate319 GeometryCertificates.Batch031.certificate638 numericValid319
    MomentCertificates.Batch015.valid319 DegreeCertificates.Batch015.valid319 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate319,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate300,certificate301,certificate302,certificate303,certificate304,certificate305,certificate306,certificate307,certificate308,certificate309,certificate310,certificate311,certificate312,certificate313,certificate314,certificate315,certificate316,certificate317,certificate318,certificate319]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound300,List.forall_mem_cons.mpr ⟨sound301,List.forall_mem_cons.mpr ⟨sound302,List.forall_mem_cons.mpr ⟨sound303,List.forall_mem_cons.mpr ⟨sound304,List.forall_mem_cons.mpr ⟨sound305,List.forall_mem_cons.mpr ⟨sound306,List.forall_mem_cons.mpr ⟨sound307,List.forall_mem_cons.mpr ⟨sound308,List.forall_mem_cons.mpr ⟨sound309,List.forall_mem_cons.mpr ⟨sound310,List.forall_mem_cons.mpr ⟨sound311,List.forall_mem_cons.mpr ⟨sound312,List.forall_mem_cons.mpr ⟨sound313,List.forall_mem_cons.mpr ⟨sound314,List.forall_mem_cons.mpr ⟨sound315,List.forall_mem_cons.mpr ⟨sound316,List.forall_mem_cons.mpr ⟨sound317,List.forall_mem_cons.mpr ⟨sound318,List.forall_mem_cons.mpr ⟨sound319,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch015
