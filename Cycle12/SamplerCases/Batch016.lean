import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch016
import Cycle12.CertifiedGlobalFailures.Batch016
import Cycle12.CutFailureCertificates.Budget032
import Cycle12.CutFailureCertificates.Budget033
import Cycle12.DegreeCertificates.Batch016
import Cycle12.GeometryCertificates.Batch032
import Cycle12.GeometryCertificates.Batch033
import Cycle12.MomentCertificates.Batch016
import Cycle12.WitnessCertificates.Batch032
import Cycle12.WitnessCertificates.Batch033

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch016
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate320 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate320,DegreeCertificates.Batch016.certificate320,(WitnessCertificates.Batch032.certificate640).beta,(WitnessCertificates.Batch032.certificate641).L,none,(CutFailureCertificates.Budget032.certificate640).bound,(CutFailureCertificates.Budget032.certificate641).bound,0⟩
theorem numericValid320 : certificate320.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound320 : certificate320.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch032.certificate640 H MomentCertificates.Batch016.valid320.1 GeometryCertificates.Batch032.valid640 GeometryCertificates.Batch032.sound640 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch032.certificate641 H MomentCertificates.Batch016.valid320.1 GeometryCertificates.Batch032.valid641 GeometryCertificates.Batch032.sound641 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound320 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound320 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate320 GeometryCertificates.Batch032.certificate640 numericValid320
    MomentCertificates.Batch016.valid320 DegreeCertificates.Batch016.valid320 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate320,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate321 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate321,DegreeCertificates.Batch016.certificate321,(WitnessCertificates.Batch032.certificate642).beta,(WitnessCertificates.Batch032.certificate643).L,none,(CutFailureCertificates.Budget032.certificate642).bound,(CutFailureCertificates.Budget032.certificate643).bound,0⟩
theorem numericValid321 : certificate321.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound321 : certificate321.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch032.certificate642 H MomentCertificates.Batch016.valid321.1 GeometryCertificates.Batch032.valid642 GeometryCertificates.Batch032.sound642 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch032.certificate643 H MomentCertificates.Batch016.valid321.1 GeometryCertificates.Batch032.valid643 GeometryCertificates.Batch032.sound643 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound321 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound321 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate321 GeometryCertificates.Batch032.certificate642 numericValid321
    MomentCertificates.Batch016.valid321 DegreeCertificates.Batch016.valid321 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate321,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate322 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate322,DegreeCertificates.Batch016.certificate322,(WitnessCertificates.Batch032.certificate644).beta,(WitnessCertificates.Batch032.certificate645).L,none,(CutFailureCertificates.Budget032.certificate644).bound,(CutFailureCertificates.Budget032.certificate645).bound,0⟩
theorem numericValid322 : certificate322.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound322 : certificate322.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch032.certificate644 H MomentCertificates.Batch016.valid322.1 GeometryCertificates.Batch032.valid644 GeometryCertificates.Batch032.sound644 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch032.certificate645 H MomentCertificates.Batch016.valid322.1 GeometryCertificates.Batch032.valid645 GeometryCertificates.Batch032.sound645 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound322 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound322 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate322 GeometryCertificates.Batch032.certificate644 numericValid322
    MomentCertificates.Batch016.valid322 DegreeCertificates.Batch016.valid322 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate322,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate323 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate323,DegreeCertificates.Batch016.certificate323,(WitnessCertificates.Batch032.certificate646).beta,(WitnessCertificates.Batch032.certificate647).L,none,(CutFailureCertificates.Budget032.certificate646).bound,(CutFailureCertificates.Budget032.certificate647).bound,0⟩
theorem numericValid323 : certificate323.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound323 : certificate323.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch032.certificate646 H MomentCertificates.Batch016.valid323.1 GeometryCertificates.Batch032.valid646 GeometryCertificates.Batch032.sound646 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch032.certificate647 H MomentCertificates.Batch016.valid323.1 GeometryCertificates.Batch032.valid647 GeometryCertificates.Batch032.sound647 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound323 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound323 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate323 GeometryCertificates.Batch032.certificate646 numericValid323
    MomentCertificates.Batch016.valid323 DegreeCertificates.Batch016.valid323 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate323,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate324 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate324,DegreeCertificates.Batch016.certificate324,(WitnessCertificates.Batch032.certificate648).beta,(WitnessCertificates.Batch032.certificate649).L,none,(CutFailureCertificates.Budget032.certificate648).bound,(CutFailureCertificates.Budget032.certificate649).bound,0⟩
theorem numericValid324 : certificate324.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound324 : certificate324.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch032.certificate648 H MomentCertificates.Batch016.valid324.1 GeometryCertificates.Batch032.valid648 GeometryCertificates.Batch032.sound648 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch032.certificate649 H MomentCertificates.Batch016.valid324.1 GeometryCertificates.Batch032.valid649 GeometryCertificates.Batch032.sound649 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound324 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound324 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate324 GeometryCertificates.Batch032.certificate648 numericValid324
    MomentCertificates.Batch016.valid324 DegreeCertificates.Batch016.valid324 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate324,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate325 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate325,DegreeCertificates.Batch016.certificate325,(WitnessCertificates.Batch032.certificate650).beta,(WitnessCertificates.Batch032.certificate651).L,none,(CutFailureCertificates.Budget032.certificate650).bound,(CutFailureCertificates.Budget032.certificate651).bound,0⟩
theorem numericValid325 : certificate325.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound325 : certificate325.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch032.certificate650 H MomentCertificates.Batch016.valid325.1 GeometryCertificates.Batch032.valid650 GeometryCertificates.Batch032.sound650 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch032.certificate651 H MomentCertificates.Batch016.valid325.1 GeometryCertificates.Batch032.valid651 GeometryCertificates.Batch032.sound651 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound325 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound325 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate325 GeometryCertificates.Batch032.certificate650 numericValid325
    MomentCertificates.Batch016.valid325 DegreeCertificates.Batch016.valid325 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate325,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate326 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate326,DegreeCertificates.Batch016.certificate326,(WitnessCertificates.Batch032.certificate652).beta,(WitnessCertificates.Batch032.certificate653).L,none,(CutFailureCertificates.Budget032.certificate652).bound,(CutFailureCertificates.Budget032.certificate653).bound,0⟩
theorem numericValid326 : certificate326.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound326 : certificate326.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch032.certificate652 H MomentCertificates.Batch016.valid326.1 GeometryCertificates.Batch032.valid652 GeometryCertificates.Batch032.sound652 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch032.certificate653 H MomentCertificates.Batch016.valid326.1 GeometryCertificates.Batch032.valid653 GeometryCertificates.Batch032.sound653 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound326 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound326 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate326 GeometryCertificates.Batch032.certificate652 numericValid326
    MomentCertificates.Batch016.valid326 DegreeCertificates.Batch016.valid326 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate326,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate327 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate327,DegreeCertificates.Batch016.certificate327,(WitnessCertificates.Batch032.certificate654).beta,(WitnessCertificates.Batch032.certificate655).L,none,(CutFailureCertificates.Budget032.certificate654).bound,(CutFailureCertificates.Budget032.certificate655).bound,0⟩
theorem numericValid327 : certificate327.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound327 : certificate327.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch032.certificate654 H MomentCertificates.Batch016.valid327.1 GeometryCertificates.Batch032.valid654 GeometryCertificates.Batch032.sound654 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch032.certificate655 H MomentCertificates.Batch016.valid327.1 GeometryCertificates.Batch032.valid655 GeometryCertificates.Batch032.sound655 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound327 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound327 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate327 GeometryCertificates.Batch032.certificate654 numericValid327
    MomentCertificates.Batch016.valid327 DegreeCertificates.Batch016.valid327 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate327,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate328 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate328,DegreeCertificates.Batch016.certificate328,(WitnessCertificates.Batch032.certificate656).beta,(WitnessCertificates.Batch032.certificate657).L,none,(CutFailureCertificates.Budget032.certificate656).bound,(CutFailureCertificates.Budget032.certificate657).bound,0⟩
theorem numericValid328 : certificate328.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound328 : certificate328.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch032.certificate656 H MomentCertificates.Batch016.valid328.1 GeometryCertificates.Batch032.valid656 GeometryCertificates.Batch032.sound656 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch032.certificate657 H MomentCertificates.Batch016.valid328.1 GeometryCertificates.Batch032.valid657 GeometryCertificates.Batch032.sound657 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound328 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound328 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate328 GeometryCertificates.Batch032.certificate656 numericValid328
    MomentCertificates.Batch016.valid328 DegreeCertificates.Batch016.valid328 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate328,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate329 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate329,DegreeCertificates.Batch016.certificate329,(WitnessCertificates.Batch032.certificate658).beta,(WitnessCertificates.Batch032.certificate659).L,none,(CutFailureCertificates.Budget032.certificate658).bound,(CutFailureCertificates.Budget032.certificate659).bound,0⟩
theorem numericValid329 : certificate329.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound329 : certificate329.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch032.certificate658 H MomentCertificates.Batch016.valid329.1 GeometryCertificates.Batch032.valid658 GeometryCertificates.Batch032.sound658 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch032.certificate659 H MomentCertificates.Batch016.valid329.1 GeometryCertificates.Batch032.valid659 GeometryCertificates.Batch032.sound659 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound329 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound329 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate329 GeometryCertificates.Batch032.certificate658 numericValid329
    MomentCertificates.Batch016.valid329 DegreeCertificates.Batch016.valid329 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate329,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate330 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate330,DegreeCertificates.Batch016.certificate330,(WitnessCertificates.Batch033.certificate660).beta,(WitnessCertificates.Batch033.certificate661).L,none,(CutFailureCertificates.Budget033.certificate660).bound,(CutFailureCertificates.Budget033.certificate661).bound,0⟩
theorem numericValid330 : certificate330.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound330 : certificate330.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch033.certificate660 H MomentCertificates.Batch016.valid330.1 GeometryCertificates.Batch033.valid660 GeometryCertificates.Batch033.sound660 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch033.certificate661 H MomentCertificates.Batch016.valid330.1 GeometryCertificates.Batch033.valid661 GeometryCertificates.Batch033.sound661 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound330 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound330 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate330 GeometryCertificates.Batch033.certificate660 numericValid330
    MomentCertificates.Batch016.valid330 DegreeCertificates.Batch016.valid330 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate330,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate331 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate331,DegreeCertificates.Batch016.certificate331,(WitnessCertificates.Batch033.certificate662).beta,(WitnessCertificates.Batch033.certificate663).L,none,(CutFailureCertificates.Budget033.certificate662).bound,(CutFailureCertificates.Budget033.certificate663).bound,0⟩
theorem numericValid331 : certificate331.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound331 : certificate331.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch033.certificate662 H MomentCertificates.Batch016.valid331.1 GeometryCertificates.Batch033.valid662 GeometryCertificates.Batch033.sound662 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch033.certificate663 H MomentCertificates.Batch016.valid331.1 GeometryCertificates.Batch033.valid663 GeometryCertificates.Batch033.sound663 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound331 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound331 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate331 GeometryCertificates.Batch033.certificate662 numericValid331
    MomentCertificates.Batch016.valid331 DegreeCertificates.Batch016.valid331 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate331,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate332 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate332,DegreeCertificates.Batch016.certificate332,(WitnessCertificates.Batch033.certificate664).beta,(WitnessCertificates.Batch033.certificate665).L,none,(CutFailureCertificates.Budget033.certificate664).bound,(CutFailureCertificates.Budget033.certificate665).bound,0⟩
theorem numericValid332 : certificate332.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound332 : certificate332.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch033.certificate664 H MomentCertificates.Batch016.valid332.1 GeometryCertificates.Batch033.valid664 GeometryCertificates.Batch033.sound664 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch033.certificate665 H MomentCertificates.Batch016.valid332.1 GeometryCertificates.Batch033.valid665 GeometryCertificates.Batch033.sound665 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound332 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound332 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate332 GeometryCertificates.Batch033.certificate664 numericValid332
    MomentCertificates.Batch016.valid332 DegreeCertificates.Batch016.valid332 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate332,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate333 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate333,DegreeCertificates.Batch016.certificate333,(WitnessCertificates.Batch033.certificate666).beta,(WitnessCertificates.Batch033.certificate667).L,none,(CutFailureCertificates.Budget033.certificate666).bound,(CutFailureCertificates.Budget033.certificate667).bound,0⟩
theorem numericValid333 : certificate333.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound333 : certificate333.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch033.certificate666 H MomentCertificates.Batch016.valid333.1 GeometryCertificates.Batch033.valid666 GeometryCertificates.Batch033.sound666 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch033.certificate667 H MomentCertificates.Batch016.valid333.1 GeometryCertificates.Batch033.valid667 GeometryCertificates.Batch033.sound667 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound333 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound333 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate333 GeometryCertificates.Batch033.certificate666 numericValid333
    MomentCertificates.Batch016.valid333 DegreeCertificates.Batch016.valid333 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate333,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate334 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate334,DegreeCertificates.Batch016.certificate334,(WitnessCertificates.Batch033.certificate668).beta,(WitnessCertificates.Batch033.certificate669).L,none,(CutFailureCertificates.Budget033.certificate668).bound,(CutFailureCertificates.Budget033.certificate669).bound,0⟩
theorem numericValid334 : certificate334.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound334 : certificate334.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch033.certificate668 H MomentCertificates.Batch016.valid334.1 GeometryCertificates.Batch033.valid668 GeometryCertificates.Batch033.sound668 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch033.certificate669 H MomentCertificates.Batch016.valid334.1 GeometryCertificates.Batch033.valid669 GeometryCertificates.Batch033.sound669 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound334 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound334 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate334 GeometryCertificates.Batch033.certificate668 numericValid334
    MomentCertificates.Batch016.valid334 DegreeCertificates.Batch016.valid334 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate334,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate335 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate335,DegreeCertificates.Batch016.certificate335,(WitnessCertificates.Batch033.certificate670).beta,(WitnessCertificates.Batch033.certificate671).L,none,(CutFailureCertificates.Budget033.certificate670).bound,(CutFailureCertificates.Budget033.certificate671).bound,0⟩
theorem numericValid335 : certificate335.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound335 : certificate335.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch033.certificate670 H MomentCertificates.Batch016.valid335.1 GeometryCertificates.Batch033.valid670 GeometryCertificates.Batch033.sound670 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch033.certificate671 H MomentCertificates.Batch016.valid335.1 GeometryCertificates.Batch033.valid671 GeometryCertificates.Batch033.sound671 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound335 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound335 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate335 GeometryCertificates.Batch033.certificate670 numericValid335
    MomentCertificates.Batch016.valid335 DegreeCertificates.Batch016.valid335 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate335,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate336 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate336,DegreeCertificates.Batch016.certificate336,(WitnessCertificates.Batch033.certificate672).beta,(WitnessCertificates.Batch033.certificate673).L,none,(CutFailureCertificates.Budget033.certificate672).bound,(CutFailureCertificates.Budget033.certificate673).bound,0⟩
theorem numericValid336 : certificate336.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound336 : certificate336.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch033.certificate672 H MomentCertificates.Batch016.valid336.1 GeometryCertificates.Batch033.valid672 GeometryCertificates.Batch033.sound672 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch033.certificate673 H MomentCertificates.Batch016.valid336.1 GeometryCertificates.Batch033.valid673 GeometryCertificates.Batch033.sound673 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound336 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound336 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate336 GeometryCertificates.Batch033.certificate672 numericValid336
    MomentCertificates.Batch016.valid336 DegreeCertificates.Batch016.valid336 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate336,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate337 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate337,DegreeCertificates.Batch016.certificate337,(WitnessCertificates.Batch033.certificate674).beta,(WitnessCertificates.Batch033.certificate675).L,none,(CutFailureCertificates.Budget033.certificate674).bound,(CutFailureCertificates.Budget033.certificate675).bound,0⟩
theorem numericValid337 : certificate337.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound337 : certificate337.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch033.certificate674 H MomentCertificates.Batch016.valid337.1 GeometryCertificates.Batch033.valid674 GeometryCertificates.Batch033.sound674 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch033.certificate675 H MomentCertificates.Batch016.valid337.1 GeometryCertificates.Batch033.valid675 GeometryCertificates.Batch033.sound675 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound337 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound337 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate337 GeometryCertificates.Batch033.certificate674 numericValid337
    MomentCertificates.Batch016.valid337 DegreeCertificates.Batch016.valid337 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate337,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate338 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate338,DegreeCertificates.Batch016.certificate338,(WitnessCertificates.Batch033.certificate676).beta,(WitnessCertificates.Batch033.certificate677).L,none,(CutFailureCertificates.Budget033.certificate676).bound,(CutFailureCertificates.Budget033.certificate677).bound,0⟩
theorem numericValid338 : certificate338.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound338 : certificate338.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch033.certificate676 H MomentCertificates.Batch016.valid338.1 GeometryCertificates.Batch033.valid676 GeometryCertificates.Batch033.sound676 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch033.certificate677 H MomentCertificates.Batch016.valid338.1 GeometryCertificates.Batch033.valid677 GeometryCertificates.Batch033.sound677 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound338 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound338 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate338 GeometryCertificates.Batch033.certificate676 numericValid338
    MomentCertificates.Batch016.valid338 DegreeCertificates.Batch016.valid338 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate338,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate339 : RatSamplerCase := ⟨MomentCertificates.Batch016.certificate339,DegreeCertificates.Batch016.certificate339,(WitnessCertificates.Batch033.certificate678).beta,(WitnessCertificates.Batch033.certificate679).L,none,(CutFailureCertificates.Budget033.certificate678).bound,(CutFailureCertificates.Budget033.certificate679).bound,0⟩
theorem numericValid339 : certificate339.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound339 : certificate339.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch033.certificate678 H MomentCertificates.Batch016.valid339.1 GeometryCertificates.Batch033.valid678 GeometryCertificates.Batch033.sound678 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch033.certificate679 H MomentCertificates.Batch016.valid339.1 GeometryCertificates.Batch033.valid679 GeometryCertificates.Batch033.sound679 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch016.probabilityBound339 H st hI
  have hanchor := CertifiedAnchorFailures.Batch016.probabilityBound339 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate339 GeometryCertificates.Batch033.certificate678 numericValid339
    MomentCertificates.Batch016.valid339 DegreeCertificates.Batch016.valid339 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate339,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate320,certificate321,certificate322,certificate323,certificate324,certificate325,certificate326,certificate327,certificate328,certificate329,certificate330,certificate331,certificate332,certificate333,certificate334,certificate335,certificate336,certificate337,certificate338,certificate339]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound320,List.forall_mem_cons.mpr ⟨sound321,List.forall_mem_cons.mpr ⟨sound322,List.forall_mem_cons.mpr ⟨sound323,List.forall_mem_cons.mpr ⟨sound324,List.forall_mem_cons.mpr ⟨sound325,List.forall_mem_cons.mpr ⟨sound326,List.forall_mem_cons.mpr ⟨sound327,List.forall_mem_cons.mpr ⟨sound328,List.forall_mem_cons.mpr ⟨sound329,List.forall_mem_cons.mpr ⟨sound330,List.forall_mem_cons.mpr ⟨sound331,List.forall_mem_cons.mpr ⟨sound332,List.forall_mem_cons.mpr ⟨sound333,List.forall_mem_cons.mpr ⟨sound334,List.forall_mem_cons.mpr ⟨sound335,List.forall_mem_cons.mpr ⟨sound336,List.forall_mem_cons.mpr ⟨sound337,List.forall_mem_cons.mpr ⟨sound338,List.forall_mem_cons.mpr ⟨sound339,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch016
