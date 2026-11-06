import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch017
import Cycle12.CertifiedGlobalFailures.Batch017
import Cycle12.CutFailureCertificates.Budget034
import Cycle12.CutFailureCertificates.Budget035
import Cycle12.DegreeCertificates.Batch017
import Cycle12.GeometryCertificates.Batch034
import Cycle12.GeometryCertificates.Batch035
import Cycle12.MomentCertificates.Batch017
import Cycle12.WitnessCertificates.Batch034
import Cycle12.WitnessCertificates.Batch035

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch017
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate340 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate340,DegreeCertificates.Batch017.certificate340,(WitnessCertificates.Batch034.certificate680).beta,(WitnessCertificates.Batch034.certificate681).L,none,(CutFailureCertificates.Budget034.certificate680).bound,(CutFailureCertificates.Budget034.certificate681).bound,0⟩
theorem numericValid340 : certificate340.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound340 : certificate340.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch034.certificate680 H MomentCertificates.Batch017.valid340.1 GeometryCertificates.Batch034.valid680 GeometryCertificates.Batch034.sound680 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch034.certificate681 H MomentCertificates.Batch017.valid340.1 GeometryCertificates.Batch034.valid681 GeometryCertificates.Batch034.sound681 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound340 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound340 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate340 GeometryCertificates.Batch034.certificate680 numericValid340
    MomentCertificates.Batch017.valid340 DegreeCertificates.Batch017.valid340 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate340,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate341 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate341,DegreeCertificates.Batch017.certificate341,(WitnessCertificates.Batch034.certificate682).beta,(WitnessCertificates.Batch034.certificate683).L,none,(CutFailureCertificates.Budget034.certificate682).bound,(CutFailureCertificates.Budget034.certificate683).bound,0⟩
theorem numericValid341 : certificate341.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound341 : certificate341.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch034.certificate682 H MomentCertificates.Batch017.valid341.1 GeometryCertificates.Batch034.valid682 GeometryCertificates.Batch034.sound682 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch034.certificate683 H MomentCertificates.Batch017.valid341.1 GeometryCertificates.Batch034.valid683 GeometryCertificates.Batch034.sound683 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound341 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound341 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate341 GeometryCertificates.Batch034.certificate682 numericValid341
    MomentCertificates.Batch017.valid341 DegreeCertificates.Batch017.valid341 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate341,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate342 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate342,DegreeCertificates.Batch017.certificate342,(WitnessCertificates.Batch034.certificate684).beta,(WitnessCertificates.Batch034.certificate685).L,none,(CutFailureCertificates.Budget034.certificate684).bound,(CutFailureCertificates.Budget034.certificate685).bound,0⟩
theorem numericValid342 : certificate342.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound342 : certificate342.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch034.certificate684 H MomentCertificates.Batch017.valid342.1 GeometryCertificates.Batch034.valid684 GeometryCertificates.Batch034.sound684 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch034.certificate685 H MomentCertificates.Batch017.valid342.1 GeometryCertificates.Batch034.valid685 GeometryCertificates.Batch034.sound685 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound342 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound342 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate342 GeometryCertificates.Batch034.certificate684 numericValid342
    MomentCertificates.Batch017.valid342 DegreeCertificates.Batch017.valid342 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate342,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate343 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate343,DegreeCertificates.Batch017.certificate343,(WitnessCertificates.Batch034.certificate686).beta,(WitnessCertificates.Batch034.certificate687).L,none,(CutFailureCertificates.Budget034.certificate686).bound,(CutFailureCertificates.Budget034.certificate687).bound,0⟩
theorem numericValid343 : certificate343.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound343 : certificate343.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch034.certificate686 H MomentCertificates.Batch017.valid343.1 GeometryCertificates.Batch034.valid686 GeometryCertificates.Batch034.sound686 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch034.certificate687 H MomentCertificates.Batch017.valid343.1 GeometryCertificates.Batch034.valid687 GeometryCertificates.Batch034.sound687 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound343 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound343 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate343 GeometryCertificates.Batch034.certificate686 numericValid343
    MomentCertificates.Batch017.valid343 DegreeCertificates.Batch017.valid343 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate343,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate344 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate344,DegreeCertificates.Batch017.certificate344,(WitnessCertificates.Batch034.certificate688).beta,(WitnessCertificates.Batch034.certificate689).L,none,(CutFailureCertificates.Budget034.certificate688).bound,(CutFailureCertificates.Budget034.certificate689).bound,0⟩
theorem numericValid344 : certificate344.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound344 : certificate344.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch034.certificate688 H MomentCertificates.Batch017.valid344.1 GeometryCertificates.Batch034.valid688 GeometryCertificates.Batch034.sound688 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch034.certificate689 H MomentCertificates.Batch017.valid344.1 GeometryCertificates.Batch034.valid689 GeometryCertificates.Batch034.sound689 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound344 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound344 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate344 GeometryCertificates.Batch034.certificate688 numericValid344
    MomentCertificates.Batch017.valid344 DegreeCertificates.Batch017.valid344 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate344,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate345 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate345,DegreeCertificates.Batch017.certificate345,(WitnessCertificates.Batch034.certificate690).beta,(WitnessCertificates.Batch034.certificate691).L,none,(CutFailureCertificates.Budget034.certificate690).bound,(CutFailureCertificates.Budget034.certificate691).bound,0⟩
theorem numericValid345 : certificate345.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound345 : certificate345.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch034.certificate690 H MomentCertificates.Batch017.valid345.1 GeometryCertificates.Batch034.valid690 GeometryCertificates.Batch034.sound690 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch034.certificate691 H MomentCertificates.Batch017.valid345.1 GeometryCertificates.Batch034.valid691 GeometryCertificates.Batch034.sound691 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound345 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound345 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate345 GeometryCertificates.Batch034.certificate690 numericValid345
    MomentCertificates.Batch017.valid345 DegreeCertificates.Batch017.valid345 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate345,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate346 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate346,DegreeCertificates.Batch017.certificate346,(WitnessCertificates.Batch034.certificate692).beta,(WitnessCertificates.Batch034.certificate693).L,none,(CutFailureCertificates.Budget034.certificate692).bound,(CutFailureCertificates.Budget034.certificate693).bound,0⟩
theorem numericValid346 : certificate346.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound346 : certificate346.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch034.certificate692 H MomentCertificates.Batch017.valid346.1 GeometryCertificates.Batch034.valid692 GeometryCertificates.Batch034.sound692 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch034.certificate693 H MomentCertificates.Batch017.valid346.1 GeometryCertificates.Batch034.valid693 GeometryCertificates.Batch034.sound693 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound346 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound346 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate346 GeometryCertificates.Batch034.certificate692 numericValid346
    MomentCertificates.Batch017.valid346 DegreeCertificates.Batch017.valid346 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate346,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate347 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate347,DegreeCertificates.Batch017.certificate347,(WitnessCertificates.Batch034.certificate694).beta,(WitnessCertificates.Batch034.certificate695).L,none,(CutFailureCertificates.Budget034.certificate694).bound,(CutFailureCertificates.Budget034.certificate695).bound,0⟩
theorem numericValid347 : certificate347.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound347 : certificate347.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch034.certificate694 H MomentCertificates.Batch017.valid347.1 GeometryCertificates.Batch034.valid694 GeometryCertificates.Batch034.sound694 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch034.certificate695 H MomentCertificates.Batch017.valid347.1 GeometryCertificates.Batch034.valid695 GeometryCertificates.Batch034.sound695 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound347 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound347 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate347 GeometryCertificates.Batch034.certificate694 numericValid347
    MomentCertificates.Batch017.valid347 DegreeCertificates.Batch017.valid347 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate347,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate348 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate348,DegreeCertificates.Batch017.certificate348,(WitnessCertificates.Batch034.certificate696).beta,(WitnessCertificates.Batch034.certificate697).L,none,(CutFailureCertificates.Budget034.certificate696).bound,(CutFailureCertificates.Budget034.certificate697).bound,0⟩
theorem numericValid348 : certificate348.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound348 : certificate348.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch034.certificate696 H MomentCertificates.Batch017.valid348.1 GeometryCertificates.Batch034.valid696 GeometryCertificates.Batch034.sound696 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch034.certificate697 H MomentCertificates.Batch017.valid348.1 GeometryCertificates.Batch034.valid697 GeometryCertificates.Batch034.sound697 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound348 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound348 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate348 GeometryCertificates.Batch034.certificate696 numericValid348
    MomentCertificates.Batch017.valid348 DegreeCertificates.Batch017.valid348 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate348,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate349 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate349,DegreeCertificates.Batch017.certificate349,(WitnessCertificates.Batch034.certificate698).beta,(WitnessCertificates.Batch034.certificate699).L,none,(CutFailureCertificates.Budget034.certificate698).bound,(CutFailureCertificates.Budget034.certificate699).bound,0⟩
theorem numericValid349 : certificate349.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound349 : certificate349.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch034.certificate698 H MomentCertificates.Batch017.valid349.1 GeometryCertificates.Batch034.valid698 GeometryCertificates.Batch034.sound698 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch034.certificate699 H MomentCertificates.Batch017.valid349.1 GeometryCertificates.Batch034.valid699 GeometryCertificates.Batch034.sound699 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound349 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound349 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate349 GeometryCertificates.Batch034.certificate698 numericValid349
    MomentCertificates.Batch017.valid349 DegreeCertificates.Batch017.valid349 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate349,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate350 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate350,DegreeCertificates.Batch017.certificate350,(WitnessCertificates.Batch035.certificate700).beta,(WitnessCertificates.Batch035.certificate701).L,none,(CutFailureCertificates.Budget035.certificate700).bound,(CutFailureCertificates.Budget035.certificate701).bound,0⟩
theorem numericValid350 : certificate350.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound350 : certificate350.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch035.certificate700 H MomentCertificates.Batch017.valid350.1 GeometryCertificates.Batch035.valid700 GeometryCertificates.Batch035.sound700 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch035.certificate701 H MomentCertificates.Batch017.valid350.1 GeometryCertificates.Batch035.valid701 GeometryCertificates.Batch035.sound701 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound350 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound350 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate350 GeometryCertificates.Batch035.certificate700 numericValid350
    MomentCertificates.Batch017.valid350 DegreeCertificates.Batch017.valid350 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate350,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate351 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate351,DegreeCertificates.Batch017.certificate351,(WitnessCertificates.Batch035.certificate702).beta,(WitnessCertificates.Batch035.certificate703).L,none,(CutFailureCertificates.Budget035.certificate702).bound,(CutFailureCertificates.Budget035.certificate703).bound,0⟩
theorem numericValid351 : certificate351.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound351 : certificate351.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch035.certificate702 H MomentCertificates.Batch017.valid351.1 GeometryCertificates.Batch035.valid702 GeometryCertificates.Batch035.sound702 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch035.certificate703 H MomentCertificates.Batch017.valid351.1 GeometryCertificates.Batch035.valid703 GeometryCertificates.Batch035.sound703 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound351 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound351 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate351 GeometryCertificates.Batch035.certificate702 numericValid351
    MomentCertificates.Batch017.valid351 DegreeCertificates.Batch017.valid351 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate351,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate352 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate352,DegreeCertificates.Batch017.certificate352,(WitnessCertificates.Batch035.certificate704).beta,(WitnessCertificates.Batch035.certificate705).L,none,(CutFailureCertificates.Budget035.certificate704).bound,(CutFailureCertificates.Budget035.certificate705).bound,0⟩
theorem numericValid352 : certificate352.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound352 : certificate352.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch035.certificate704 H MomentCertificates.Batch017.valid352.1 GeometryCertificates.Batch035.valid704 GeometryCertificates.Batch035.sound704 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch035.certificate705 H MomentCertificates.Batch017.valid352.1 GeometryCertificates.Batch035.valid705 GeometryCertificates.Batch035.sound705 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound352 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound352 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate352 GeometryCertificates.Batch035.certificate704 numericValid352
    MomentCertificates.Batch017.valid352 DegreeCertificates.Batch017.valid352 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate352,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate353 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate353,DegreeCertificates.Batch017.certificate353,(WitnessCertificates.Batch035.certificate706).beta,(WitnessCertificates.Batch035.certificate707).L,none,(CutFailureCertificates.Budget035.certificate706).bound,(CutFailureCertificates.Budget035.certificate707).bound,0⟩
theorem numericValid353 : certificate353.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound353 : certificate353.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch035.certificate706 H MomentCertificates.Batch017.valid353.1 GeometryCertificates.Batch035.valid706 GeometryCertificates.Batch035.sound706 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch035.certificate707 H MomentCertificates.Batch017.valid353.1 GeometryCertificates.Batch035.valid707 GeometryCertificates.Batch035.sound707 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound353 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound353 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate353 GeometryCertificates.Batch035.certificate706 numericValid353
    MomentCertificates.Batch017.valid353 DegreeCertificates.Batch017.valid353 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate353,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate354 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate354,DegreeCertificates.Batch017.certificate354,(WitnessCertificates.Batch035.certificate708).beta,(WitnessCertificates.Batch035.certificate709).L,none,(CutFailureCertificates.Budget035.certificate708).bound,(CutFailureCertificates.Budget035.certificate709).bound,0⟩
theorem numericValid354 : certificate354.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound354 : certificate354.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch035.certificate708 H MomentCertificates.Batch017.valid354.1 GeometryCertificates.Batch035.valid708 GeometryCertificates.Batch035.sound708 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch035.certificate709 H MomentCertificates.Batch017.valid354.1 GeometryCertificates.Batch035.valid709 GeometryCertificates.Batch035.sound709 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound354 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound354 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate354 GeometryCertificates.Batch035.certificate708 numericValid354
    MomentCertificates.Batch017.valid354 DegreeCertificates.Batch017.valid354 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate354,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate355 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate355,DegreeCertificates.Batch017.certificate355,(WitnessCertificates.Batch035.certificate710).beta,(WitnessCertificates.Batch035.certificate711).L,none,(CutFailureCertificates.Budget035.certificate710).bound,(CutFailureCertificates.Budget035.certificate711).bound,0⟩
theorem numericValid355 : certificate355.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound355 : certificate355.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch035.certificate710 H MomentCertificates.Batch017.valid355.1 GeometryCertificates.Batch035.valid710 GeometryCertificates.Batch035.sound710 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch035.certificate711 H MomentCertificates.Batch017.valid355.1 GeometryCertificates.Batch035.valid711 GeometryCertificates.Batch035.sound711 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound355 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound355 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate355 GeometryCertificates.Batch035.certificate710 numericValid355
    MomentCertificates.Batch017.valid355 DegreeCertificates.Batch017.valid355 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate355,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate356 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate356,DegreeCertificates.Batch017.certificate356,(WitnessCertificates.Batch035.certificate712).beta,(WitnessCertificates.Batch035.certificate713).L,none,(CutFailureCertificates.Budget035.certificate712).bound,(CutFailureCertificates.Budget035.certificate713).bound,0⟩
theorem numericValid356 : certificate356.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound356 : certificate356.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch035.certificate712 H MomentCertificates.Batch017.valid356.1 GeometryCertificates.Batch035.valid712 GeometryCertificates.Batch035.sound712 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch035.certificate713 H MomentCertificates.Batch017.valid356.1 GeometryCertificates.Batch035.valid713 GeometryCertificates.Batch035.sound713 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound356 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound356 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate356 GeometryCertificates.Batch035.certificate712 numericValid356
    MomentCertificates.Batch017.valid356 DegreeCertificates.Batch017.valid356 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate356,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate357 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate357,DegreeCertificates.Batch017.certificate357,(WitnessCertificates.Batch035.certificate714).beta,(WitnessCertificates.Batch035.certificate715).L,none,(CutFailureCertificates.Budget035.certificate714).bound,(CutFailureCertificates.Budget035.certificate715).bound,0⟩
theorem numericValid357 : certificate357.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound357 : certificate357.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch035.certificate714 H MomentCertificates.Batch017.valid357.1 GeometryCertificates.Batch035.valid714 GeometryCertificates.Batch035.sound714 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch035.certificate715 H MomentCertificates.Batch017.valid357.1 GeometryCertificates.Batch035.valid715 GeometryCertificates.Batch035.sound715 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound357 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound357 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate357 GeometryCertificates.Batch035.certificate714 numericValid357
    MomentCertificates.Batch017.valid357 DegreeCertificates.Batch017.valid357 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate357,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate358 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate358,DegreeCertificates.Batch017.certificate358,(WitnessCertificates.Batch035.certificate716).beta,(WitnessCertificates.Batch035.certificate717).L,none,(CutFailureCertificates.Budget035.certificate716).bound,(CutFailureCertificates.Budget035.certificate717).bound,0⟩
theorem numericValid358 : certificate358.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound358 : certificate358.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch035.certificate716 H MomentCertificates.Batch017.valid358.1 GeometryCertificates.Batch035.valid716 GeometryCertificates.Batch035.sound716 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch035.certificate717 H MomentCertificates.Batch017.valid358.1 GeometryCertificates.Batch035.valid717 GeometryCertificates.Batch035.sound717 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound358 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound358 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate358 GeometryCertificates.Batch035.certificate716 numericValid358
    MomentCertificates.Batch017.valid358 DegreeCertificates.Batch017.valid358 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate358,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate359 : RatSamplerCase := ⟨MomentCertificates.Batch017.certificate359,DegreeCertificates.Batch017.certificate359,(WitnessCertificates.Batch035.certificate718).beta,(WitnessCertificates.Batch035.certificate719).L,none,(CutFailureCertificates.Budget035.certificate718).bound,(CutFailureCertificates.Budget035.certificate719).bound,0⟩
theorem numericValid359 : certificate359.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound359 : certificate359.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch035.certificate718 H MomentCertificates.Batch017.valid359.1 GeometryCertificates.Batch035.valid718 GeometryCertificates.Batch035.sound718 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch035.certificate719 H MomentCertificates.Batch017.valid359.1 GeometryCertificates.Batch035.valid719 GeometryCertificates.Batch035.sound719 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch017.probabilityBound359 H st hI
  have hanchor := CertifiedAnchorFailures.Batch017.probabilityBound359 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate359 GeometryCertificates.Batch035.certificate718 numericValid359
    MomentCertificates.Batch017.valid359 DegreeCertificates.Batch017.valid359 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate359,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate340,certificate341,certificate342,certificate343,certificate344,certificate345,certificate346,certificate347,certificate348,certificate349,certificate350,certificate351,certificate352,certificate353,certificate354,certificate355,certificate356,certificate357,certificate358,certificate359]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound340,List.forall_mem_cons.mpr ⟨sound341,List.forall_mem_cons.mpr ⟨sound342,List.forall_mem_cons.mpr ⟨sound343,List.forall_mem_cons.mpr ⟨sound344,List.forall_mem_cons.mpr ⟨sound345,List.forall_mem_cons.mpr ⟨sound346,List.forall_mem_cons.mpr ⟨sound347,List.forall_mem_cons.mpr ⟨sound348,List.forall_mem_cons.mpr ⟨sound349,List.forall_mem_cons.mpr ⟨sound350,List.forall_mem_cons.mpr ⟨sound351,List.forall_mem_cons.mpr ⟨sound352,List.forall_mem_cons.mpr ⟨sound353,List.forall_mem_cons.mpr ⟨sound354,List.forall_mem_cons.mpr ⟨sound355,List.forall_mem_cons.mpr ⟨sound356,List.forall_mem_cons.mpr ⟨sound357,List.forall_mem_cons.mpr ⟨sound358,List.forall_mem_cons.mpr ⟨sound359,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch017
