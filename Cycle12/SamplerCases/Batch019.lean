import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch019
import Cycle12.CertifiedGlobalFailures.Batch019
import Cycle12.CutFailureCertificates.Budget038
import Cycle12.CutFailureCertificates.Budget039
import Cycle12.DegreeCertificates.Batch019
import Cycle12.GeometryCertificates.Batch038
import Cycle12.GeometryCertificates.Batch039
import Cycle12.MomentCertificates.Batch019
import Cycle12.WitnessCertificates.Batch038
import Cycle12.WitnessCertificates.Batch039

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch019
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate380 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate380,DegreeCertificates.Batch019.certificate380,(WitnessCertificates.Batch038.certificate760).beta,(WitnessCertificates.Batch038.certificate761).L,none,(CutFailureCertificates.Budget038.certificate760).bound,(CutFailureCertificates.Budget038.certificate761).bound,0⟩
theorem numericValid380 : certificate380.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound380 : certificate380.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch038.certificate760 H MomentCertificates.Batch019.valid380.1 GeometryCertificates.Batch038.valid760 GeometryCertificates.Batch038.sound760 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch038.certificate761 H MomentCertificates.Batch019.valid380.1 GeometryCertificates.Batch038.valid761 GeometryCertificates.Batch038.sound761 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound380 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound380 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate380 GeometryCertificates.Batch038.certificate760 numericValid380
    MomentCertificates.Batch019.valid380 DegreeCertificates.Batch019.valid380 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate380,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate381 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate381,DegreeCertificates.Batch019.certificate381,(WitnessCertificates.Batch038.certificate762).beta,(WitnessCertificates.Batch038.certificate763).L,none,(CutFailureCertificates.Budget038.certificate762).bound,(CutFailureCertificates.Budget038.certificate763).bound,0⟩
theorem numericValid381 : certificate381.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound381 : certificate381.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch038.certificate762 H MomentCertificates.Batch019.valid381.1 GeometryCertificates.Batch038.valid762 GeometryCertificates.Batch038.sound762 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch038.certificate763 H MomentCertificates.Batch019.valid381.1 GeometryCertificates.Batch038.valid763 GeometryCertificates.Batch038.sound763 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound381 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound381 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate381 GeometryCertificates.Batch038.certificate762 numericValid381
    MomentCertificates.Batch019.valid381 DegreeCertificates.Batch019.valid381 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate381,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate382 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate382,DegreeCertificates.Batch019.certificate382,(WitnessCertificates.Batch038.certificate764).beta,(WitnessCertificates.Batch038.certificate765).L,none,(CutFailureCertificates.Budget038.certificate764).bound,(CutFailureCertificates.Budget038.certificate765).bound,0⟩
theorem numericValid382 : certificate382.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound382 : certificate382.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch038.certificate764 H MomentCertificates.Batch019.valid382.1 GeometryCertificates.Batch038.valid764 GeometryCertificates.Batch038.sound764 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch038.certificate765 H MomentCertificates.Batch019.valid382.1 GeometryCertificates.Batch038.valid765 GeometryCertificates.Batch038.sound765 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound382 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound382 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate382 GeometryCertificates.Batch038.certificate764 numericValid382
    MomentCertificates.Batch019.valid382 DegreeCertificates.Batch019.valid382 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate382,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate383 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate383,DegreeCertificates.Batch019.certificate383,(WitnessCertificates.Batch038.certificate766).beta,(WitnessCertificates.Batch038.certificate767).L,none,(CutFailureCertificates.Budget038.certificate766).bound,(CutFailureCertificates.Budget038.certificate767).bound,0⟩
theorem numericValid383 : certificate383.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound383 : certificate383.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch038.certificate766 H MomentCertificates.Batch019.valid383.1 GeometryCertificates.Batch038.valid766 GeometryCertificates.Batch038.sound766 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch038.certificate767 H MomentCertificates.Batch019.valid383.1 GeometryCertificates.Batch038.valid767 GeometryCertificates.Batch038.sound767 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound383 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound383 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate383 GeometryCertificates.Batch038.certificate766 numericValid383
    MomentCertificates.Batch019.valid383 DegreeCertificates.Batch019.valid383 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate383,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate384 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate384,DegreeCertificates.Batch019.certificate384,(WitnessCertificates.Batch038.certificate768).beta,(WitnessCertificates.Batch038.certificate769).L,none,(CutFailureCertificates.Budget038.certificate768).bound,(CutFailureCertificates.Budget038.certificate769).bound,0⟩
theorem numericValid384 : certificate384.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound384 : certificate384.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch038.certificate768 H MomentCertificates.Batch019.valid384.1 GeometryCertificates.Batch038.valid768 GeometryCertificates.Batch038.sound768 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch038.certificate769 H MomentCertificates.Batch019.valid384.1 GeometryCertificates.Batch038.valid769 GeometryCertificates.Batch038.sound769 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound384 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound384 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate384 GeometryCertificates.Batch038.certificate768 numericValid384
    MomentCertificates.Batch019.valid384 DegreeCertificates.Batch019.valid384 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate384,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate385 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate385,DegreeCertificates.Batch019.certificate385,(WitnessCertificates.Batch038.certificate770).beta,(WitnessCertificates.Batch038.certificate771).L,none,(CutFailureCertificates.Budget038.certificate770).bound,(CutFailureCertificates.Budget038.certificate771).bound,0⟩
theorem numericValid385 : certificate385.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound385 : certificate385.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch038.certificate770 H MomentCertificates.Batch019.valid385.1 GeometryCertificates.Batch038.valid770 GeometryCertificates.Batch038.sound770 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch038.certificate771 H MomentCertificates.Batch019.valid385.1 GeometryCertificates.Batch038.valid771 GeometryCertificates.Batch038.sound771 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound385 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound385 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate385 GeometryCertificates.Batch038.certificate770 numericValid385
    MomentCertificates.Batch019.valid385 DegreeCertificates.Batch019.valid385 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate385,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate386 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate386,DegreeCertificates.Batch019.certificate386,(WitnessCertificates.Batch038.certificate772).beta,(WitnessCertificates.Batch038.certificate773).L,none,(CutFailureCertificates.Budget038.certificate772).bound,(CutFailureCertificates.Budget038.certificate773).bound,0⟩
theorem numericValid386 : certificate386.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound386 : certificate386.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch038.certificate772 H MomentCertificates.Batch019.valid386.1 GeometryCertificates.Batch038.valid772 GeometryCertificates.Batch038.sound772 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch038.certificate773 H MomentCertificates.Batch019.valid386.1 GeometryCertificates.Batch038.valid773 GeometryCertificates.Batch038.sound773 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound386 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound386 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate386 GeometryCertificates.Batch038.certificate772 numericValid386
    MomentCertificates.Batch019.valid386 DegreeCertificates.Batch019.valid386 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate386,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate387 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate387,DegreeCertificates.Batch019.certificate387,(WitnessCertificates.Batch038.certificate774).beta,(WitnessCertificates.Batch038.certificate775).L,none,(CutFailureCertificates.Budget038.certificate774).bound,(CutFailureCertificates.Budget038.certificate775).bound,0⟩
theorem numericValid387 : certificate387.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound387 : certificate387.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch038.certificate774 H MomentCertificates.Batch019.valid387.1 GeometryCertificates.Batch038.valid774 GeometryCertificates.Batch038.sound774 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch038.certificate775 H MomentCertificates.Batch019.valid387.1 GeometryCertificates.Batch038.valid775 GeometryCertificates.Batch038.sound775 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound387 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound387 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate387 GeometryCertificates.Batch038.certificate774 numericValid387
    MomentCertificates.Batch019.valid387 DegreeCertificates.Batch019.valid387 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate387,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate388 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate388,DegreeCertificates.Batch019.certificate388,(WitnessCertificates.Batch038.certificate776).beta,(WitnessCertificates.Batch038.certificate777).L,none,(CutFailureCertificates.Budget038.certificate776).bound,(CutFailureCertificates.Budget038.certificate777).bound,0⟩
theorem numericValid388 : certificate388.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound388 : certificate388.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch038.certificate776 H MomentCertificates.Batch019.valid388.1 GeometryCertificates.Batch038.valid776 GeometryCertificates.Batch038.sound776 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch038.certificate777 H MomentCertificates.Batch019.valid388.1 GeometryCertificates.Batch038.valid777 GeometryCertificates.Batch038.sound777 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound388 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound388 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate388 GeometryCertificates.Batch038.certificate776 numericValid388
    MomentCertificates.Batch019.valid388 DegreeCertificates.Batch019.valid388 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate388,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate389 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate389,DegreeCertificates.Batch019.certificate389,(WitnessCertificates.Batch038.certificate778).beta,(WitnessCertificates.Batch038.certificate779).L,none,(CutFailureCertificates.Budget038.certificate778).bound,(CutFailureCertificates.Budget038.certificate779).bound,0⟩
theorem numericValid389 : certificate389.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound389 : certificate389.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch038.certificate778 H MomentCertificates.Batch019.valid389.1 GeometryCertificates.Batch038.valid778 GeometryCertificates.Batch038.sound778 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch038.certificate779 H MomentCertificates.Batch019.valid389.1 GeometryCertificates.Batch038.valid779 GeometryCertificates.Batch038.sound779 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound389 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound389 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate389 GeometryCertificates.Batch038.certificate778 numericValid389
    MomentCertificates.Batch019.valid389 DegreeCertificates.Batch019.valid389 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate389,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate390 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate390,DegreeCertificates.Batch019.certificate390,(WitnessCertificates.Batch039.certificate780).beta,(WitnessCertificates.Batch039.certificate781).L,none,(CutFailureCertificates.Budget039.certificate780).bound,(CutFailureCertificates.Budget039.certificate781).bound,0⟩
theorem numericValid390 : certificate390.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound390 : certificate390.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch039.certificate780 H MomentCertificates.Batch019.valid390.1 GeometryCertificates.Batch039.valid780 GeometryCertificates.Batch039.sound780 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch039.certificate781 H MomentCertificates.Batch019.valid390.1 GeometryCertificates.Batch039.valid781 GeometryCertificates.Batch039.sound781 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound390 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound390 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate390 GeometryCertificates.Batch039.certificate780 numericValid390
    MomentCertificates.Batch019.valid390 DegreeCertificates.Batch019.valid390 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate390,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate391 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate391,DegreeCertificates.Batch019.certificate391,(WitnessCertificates.Batch039.certificate782).beta,(WitnessCertificates.Batch039.certificate783).L,none,(CutFailureCertificates.Budget039.certificate782).bound,(CutFailureCertificates.Budget039.certificate783).bound,0⟩
theorem numericValid391 : certificate391.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound391 : certificate391.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch039.certificate782 H MomentCertificates.Batch019.valid391.1 GeometryCertificates.Batch039.valid782 GeometryCertificates.Batch039.sound782 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch039.certificate783 H MomentCertificates.Batch019.valid391.1 GeometryCertificates.Batch039.valid783 GeometryCertificates.Batch039.sound783 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound391 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound391 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate391 GeometryCertificates.Batch039.certificate782 numericValid391
    MomentCertificates.Batch019.valid391 DegreeCertificates.Batch019.valid391 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate391,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate392 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate392,DegreeCertificates.Batch019.certificate392,(WitnessCertificates.Batch039.certificate784).beta,(WitnessCertificates.Batch039.certificate785).L,none,(CutFailureCertificates.Budget039.certificate784).bound,(CutFailureCertificates.Budget039.certificate785).bound,0⟩
theorem numericValid392 : certificate392.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound392 : certificate392.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch039.certificate784 H MomentCertificates.Batch019.valid392.1 GeometryCertificates.Batch039.valid784 GeometryCertificates.Batch039.sound784 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch039.certificate785 H MomentCertificates.Batch019.valid392.1 GeometryCertificates.Batch039.valid785 GeometryCertificates.Batch039.sound785 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound392 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound392 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate392 GeometryCertificates.Batch039.certificate784 numericValid392
    MomentCertificates.Batch019.valid392 DegreeCertificates.Batch019.valid392 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate392,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate393 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate393,DegreeCertificates.Batch019.certificate393,(WitnessCertificates.Batch039.certificate786).beta,(WitnessCertificates.Batch039.certificate787).L,none,(CutFailureCertificates.Budget039.certificate786).bound,(CutFailureCertificates.Budget039.certificate787).bound,0⟩
theorem numericValid393 : certificate393.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound393 : certificate393.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch039.certificate786 H MomentCertificates.Batch019.valid393.1 GeometryCertificates.Batch039.valid786 GeometryCertificates.Batch039.sound786 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch039.certificate787 H MomentCertificates.Batch019.valid393.1 GeometryCertificates.Batch039.valid787 GeometryCertificates.Batch039.sound787 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound393 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound393 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate393 GeometryCertificates.Batch039.certificate786 numericValid393
    MomentCertificates.Batch019.valid393 DegreeCertificates.Batch019.valid393 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate393,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate394 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate394,DegreeCertificates.Batch019.certificate394,(WitnessCertificates.Batch039.certificate788).beta,(WitnessCertificates.Batch039.certificate789).L,none,(CutFailureCertificates.Budget039.certificate788).bound,(CutFailureCertificates.Budget039.certificate789).bound,0⟩
theorem numericValid394 : certificate394.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound394 : certificate394.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch039.certificate788 H MomentCertificates.Batch019.valid394.1 GeometryCertificates.Batch039.valid788 GeometryCertificates.Batch039.sound788 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch039.certificate789 H MomentCertificates.Batch019.valid394.1 GeometryCertificates.Batch039.valid789 GeometryCertificates.Batch039.sound789 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound394 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound394 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate394 GeometryCertificates.Batch039.certificate788 numericValid394
    MomentCertificates.Batch019.valid394 DegreeCertificates.Batch019.valid394 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate394,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate395 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate395,DegreeCertificates.Batch019.certificate395,(WitnessCertificates.Batch039.certificate790).beta,(WitnessCertificates.Batch039.certificate791).L,none,(CutFailureCertificates.Budget039.certificate790).bound,(CutFailureCertificates.Budget039.certificate791).bound,0⟩
theorem numericValid395 : certificate395.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound395 : certificate395.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch039.certificate790 H MomentCertificates.Batch019.valid395.1 GeometryCertificates.Batch039.valid790 GeometryCertificates.Batch039.sound790 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch039.certificate791 H MomentCertificates.Batch019.valid395.1 GeometryCertificates.Batch039.valid791 GeometryCertificates.Batch039.sound791 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound395 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound395 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate395 GeometryCertificates.Batch039.certificate790 numericValid395
    MomentCertificates.Batch019.valid395 DegreeCertificates.Batch019.valid395 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate395,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate396 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate396,DegreeCertificates.Batch019.certificate396,(WitnessCertificates.Batch039.certificate792).beta,(WitnessCertificates.Batch039.certificate793).L,none,(CutFailureCertificates.Budget039.certificate792).bound,(CutFailureCertificates.Budget039.certificate793).bound,0⟩
theorem numericValid396 : certificate396.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound396 : certificate396.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch039.certificate792 H MomentCertificates.Batch019.valid396.1 GeometryCertificates.Batch039.valid792 GeometryCertificates.Batch039.sound792 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch039.certificate793 H MomentCertificates.Batch019.valid396.1 GeometryCertificates.Batch039.valid793 GeometryCertificates.Batch039.sound793 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound396 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound396 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate396 GeometryCertificates.Batch039.certificate792 numericValid396
    MomentCertificates.Batch019.valid396 DegreeCertificates.Batch019.valid396 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate396,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate397 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate397,DegreeCertificates.Batch019.certificate397,(WitnessCertificates.Batch039.certificate794).beta,(WitnessCertificates.Batch039.certificate795).L,none,(CutFailureCertificates.Budget039.certificate794).bound,(CutFailureCertificates.Budget039.certificate795).bound,0⟩
theorem numericValid397 : certificate397.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound397 : certificate397.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch039.certificate794 H MomentCertificates.Batch019.valid397.1 GeometryCertificates.Batch039.valid794 GeometryCertificates.Batch039.sound794 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch039.certificate795 H MomentCertificates.Batch019.valid397.1 GeometryCertificates.Batch039.valid795 GeometryCertificates.Batch039.sound795 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound397 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound397 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate397 GeometryCertificates.Batch039.certificate794 numericValid397
    MomentCertificates.Batch019.valid397 DegreeCertificates.Batch019.valid397 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate397,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate398 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate398,DegreeCertificates.Batch019.certificate398,(WitnessCertificates.Batch039.certificate796).beta,(WitnessCertificates.Batch039.certificate797).L,none,(CutFailureCertificates.Budget039.certificate796).bound,(CutFailureCertificates.Budget039.certificate797).bound,0⟩
theorem numericValid398 : certificate398.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound398 : certificate398.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch039.certificate796 H MomentCertificates.Batch019.valid398.1 GeometryCertificates.Batch039.valid796 GeometryCertificates.Batch039.sound796 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch039.certificate797 H MomentCertificates.Batch019.valid398.1 GeometryCertificates.Batch039.valid797 GeometryCertificates.Batch039.sound797 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound398 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound398 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate398 GeometryCertificates.Batch039.certificate796 numericValid398
    MomentCertificates.Batch019.valid398 DegreeCertificates.Batch019.valid398 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate398,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate399 : RatSamplerCase := ⟨MomentCertificates.Batch019.certificate399,DegreeCertificates.Batch019.certificate399,(WitnessCertificates.Batch039.certificate798).beta,(WitnessCertificates.Batch039.certificate799).L,none,(CutFailureCertificates.Budget039.certificate798).bound,(CutFailureCertificates.Budget039.certificate799).bound,0⟩
theorem numericValid399 : certificate399.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound399 : certificate399.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch039.certificate798 H MomentCertificates.Batch019.valid399.1 GeometryCertificates.Batch039.valid798 GeometryCertificates.Batch039.sound798 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch039.certificate799 H MomentCertificates.Batch019.valid399.1 GeometryCertificates.Batch039.valid799 GeometryCertificates.Batch039.sound799 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch019.probabilityBound399 H st hI
  have hanchor := CertifiedAnchorFailures.Batch019.probabilityBound399 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate399 GeometryCertificates.Batch039.certificate798 numericValid399
    MomentCertificates.Batch019.valid399 DegreeCertificates.Batch019.valid399 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate399,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate380,certificate381,certificate382,certificate383,certificate384,certificate385,certificate386,certificate387,certificate388,certificate389,certificate390,certificate391,certificate392,certificate393,certificate394,certificate395,certificate396,certificate397,certificate398,certificate399]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound380,List.forall_mem_cons.mpr ⟨sound381,List.forall_mem_cons.mpr ⟨sound382,List.forall_mem_cons.mpr ⟨sound383,List.forall_mem_cons.mpr ⟨sound384,List.forall_mem_cons.mpr ⟨sound385,List.forall_mem_cons.mpr ⟨sound386,List.forall_mem_cons.mpr ⟨sound387,List.forall_mem_cons.mpr ⟨sound388,List.forall_mem_cons.mpr ⟨sound389,List.forall_mem_cons.mpr ⟨sound390,List.forall_mem_cons.mpr ⟨sound391,List.forall_mem_cons.mpr ⟨sound392,List.forall_mem_cons.mpr ⟨sound393,List.forall_mem_cons.mpr ⟨sound394,List.forall_mem_cons.mpr ⟨sound395,List.forall_mem_cons.mpr ⟨sound396,List.forall_mem_cons.mpr ⟨sound397,List.forall_mem_cons.mpr ⟨sound398,List.forall_mem_cons.mpr ⟨sound399,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch019
