import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch018
import Cycle12.CertifiedGlobalFailures.Batch018
import Cycle12.CutFailureCertificates.Budget036
import Cycle12.CutFailureCertificates.Budget037
import Cycle12.DegreeCertificates.Batch018
import Cycle12.GeometryCertificates.Batch036
import Cycle12.GeometryCertificates.Batch037
import Cycle12.MomentCertificates.Batch018
import Cycle12.WitnessCertificates.Batch036
import Cycle12.WitnessCertificates.Batch037

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch018
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate360 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate360,DegreeCertificates.Batch018.certificate360,(WitnessCertificates.Batch036.certificate720).beta,(WitnessCertificates.Batch036.certificate721).L,none,(CutFailureCertificates.Budget036.certificate720).bound,(CutFailureCertificates.Budget036.certificate721).bound,0⟩
theorem numericValid360 : certificate360.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound360 : certificate360.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch036.certificate720 H MomentCertificates.Batch018.valid360.1 GeometryCertificates.Batch036.valid720 GeometryCertificates.Batch036.sound720 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch036.certificate721 H MomentCertificates.Batch018.valid360.1 GeometryCertificates.Batch036.valid721 GeometryCertificates.Batch036.sound721 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound360 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound360 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate360 GeometryCertificates.Batch036.certificate720 numericValid360
    MomentCertificates.Batch018.valid360 DegreeCertificates.Batch018.valid360 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate360,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate361 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate361,DegreeCertificates.Batch018.certificate361,(WitnessCertificates.Batch036.certificate722).beta,(WitnessCertificates.Batch036.certificate723).L,none,(CutFailureCertificates.Budget036.certificate722).bound,(CutFailureCertificates.Budget036.certificate723).bound,0⟩
theorem numericValid361 : certificate361.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound361 : certificate361.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch036.certificate722 H MomentCertificates.Batch018.valid361.1 GeometryCertificates.Batch036.valid722 GeometryCertificates.Batch036.sound722 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch036.certificate723 H MomentCertificates.Batch018.valid361.1 GeometryCertificates.Batch036.valid723 GeometryCertificates.Batch036.sound723 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound361 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound361 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate361 GeometryCertificates.Batch036.certificate722 numericValid361
    MomentCertificates.Batch018.valid361 DegreeCertificates.Batch018.valid361 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate361,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate362 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate362,DegreeCertificates.Batch018.certificate362,(WitnessCertificates.Batch036.certificate724).beta,(WitnessCertificates.Batch036.certificate725).L,none,(CutFailureCertificates.Budget036.certificate724).bound,(CutFailureCertificates.Budget036.certificate725).bound,0⟩
theorem numericValid362 : certificate362.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound362 : certificate362.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch036.certificate724 H MomentCertificates.Batch018.valid362.1 GeometryCertificates.Batch036.valid724 GeometryCertificates.Batch036.sound724 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch036.certificate725 H MomentCertificates.Batch018.valid362.1 GeometryCertificates.Batch036.valid725 GeometryCertificates.Batch036.sound725 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound362 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound362 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate362 GeometryCertificates.Batch036.certificate724 numericValid362
    MomentCertificates.Batch018.valid362 DegreeCertificates.Batch018.valid362 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate362,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate363 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate363,DegreeCertificates.Batch018.certificate363,(WitnessCertificates.Batch036.certificate726).beta,(WitnessCertificates.Batch036.certificate727).L,none,(CutFailureCertificates.Budget036.certificate726).bound,(CutFailureCertificates.Budget036.certificate727).bound,0⟩
theorem numericValid363 : certificate363.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound363 : certificate363.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch036.certificate726 H MomentCertificates.Batch018.valid363.1 GeometryCertificates.Batch036.valid726 GeometryCertificates.Batch036.sound726 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch036.certificate727 H MomentCertificates.Batch018.valid363.1 GeometryCertificates.Batch036.valid727 GeometryCertificates.Batch036.sound727 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound363 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound363 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate363 GeometryCertificates.Batch036.certificate726 numericValid363
    MomentCertificates.Batch018.valid363 DegreeCertificates.Batch018.valid363 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate363,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate364 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate364,DegreeCertificates.Batch018.certificate364,(WitnessCertificates.Batch036.certificate728).beta,(WitnessCertificates.Batch036.certificate729).L,none,(CutFailureCertificates.Budget036.certificate728).bound,(CutFailureCertificates.Budget036.certificate729).bound,0⟩
theorem numericValid364 : certificate364.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound364 : certificate364.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch036.certificate728 H MomentCertificates.Batch018.valid364.1 GeometryCertificates.Batch036.valid728 GeometryCertificates.Batch036.sound728 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch036.certificate729 H MomentCertificates.Batch018.valid364.1 GeometryCertificates.Batch036.valid729 GeometryCertificates.Batch036.sound729 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound364 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound364 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate364 GeometryCertificates.Batch036.certificate728 numericValid364
    MomentCertificates.Batch018.valid364 DegreeCertificates.Batch018.valid364 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate364,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate365 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate365,DegreeCertificates.Batch018.certificate365,(WitnessCertificates.Batch036.certificate730).beta,(WitnessCertificates.Batch036.certificate731).L,none,(CutFailureCertificates.Budget036.certificate730).bound,(CutFailureCertificates.Budget036.certificate731).bound,0⟩
theorem numericValid365 : certificate365.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound365 : certificate365.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch036.certificate730 H MomentCertificates.Batch018.valid365.1 GeometryCertificates.Batch036.valid730 GeometryCertificates.Batch036.sound730 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch036.certificate731 H MomentCertificates.Batch018.valid365.1 GeometryCertificates.Batch036.valid731 GeometryCertificates.Batch036.sound731 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound365 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound365 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate365 GeometryCertificates.Batch036.certificate730 numericValid365
    MomentCertificates.Batch018.valid365 DegreeCertificates.Batch018.valid365 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate365,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate366 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate366,DegreeCertificates.Batch018.certificate366,(WitnessCertificates.Batch036.certificate732).beta,(WitnessCertificates.Batch036.certificate733).L,none,(CutFailureCertificates.Budget036.certificate732).bound,(CutFailureCertificates.Budget036.certificate733).bound,0⟩
theorem numericValid366 : certificate366.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound366 : certificate366.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch036.certificate732 H MomentCertificates.Batch018.valid366.1 GeometryCertificates.Batch036.valid732 GeometryCertificates.Batch036.sound732 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch036.certificate733 H MomentCertificates.Batch018.valid366.1 GeometryCertificates.Batch036.valid733 GeometryCertificates.Batch036.sound733 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound366 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound366 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate366 GeometryCertificates.Batch036.certificate732 numericValid366
    MomentCertificates.Batch018.valid366 DegreeCertificates.Batch018.valid366 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate366,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate367 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate367,DegreeCertificates.Batch018.certificate367,(WitnessCertificates.Batch036.certificate734).beta,(WitnessCertificates.Batch036.certificate735).L,none,(CutFailureCertificates.Budget036.certificate734).bound,(CutFailureCertificates.Budget036.certificate735).bound,0⟩
theorem numericValid367 : certificate367.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound367 : certificate367.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch036.certificate734 H MomentCertificates.Batch018.valid367.1 GeometryCertificates.Batch036.valid734 GeometryCertificates.Batch036.sound734 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch036.certificate735 H MomentCertificates.Batch018.valid367.1 GeometryCertificates.Batch036.valid735 GeometryCertificates.Batch036.sound735 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound367 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound367 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate367 GeometryCertificates.Batch036.certificate734 numericValid367
    MomentCertificates.Batch018.valid367 DegreeCertificates.Batch018.valid367 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate367,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate368 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate368,DegreeCertificates.Batch018.certificate368,(WitnessCertificates.Batch036.certificate736).beta,(WitnessCertificates.Batch036.certificate737).L,none,(CutFailureCertificates.Budget036.certificate736).bound,(CutFailureCertificates.Budget036.certificate737).bound,0⟩
theorem numericValid368 : certificate368.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound368 : certificate368.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch036.certificate736 H MomentCertificates.Batch018.valid368.1 GeometryCertificates.Batch036.valid736 GeometryCertificates.Batch036.sound736 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch036.certificate737 H MomentCertificates.Batch018.valid368.1 GeometryCertificates.Batch036.valid737 GeometryCertificates.Batch036.sound737 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound368 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound368 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate368 GeometryCertificates.Batch036.certificate736 numericValid368
    MomentCertificates.Batch018.valid368 DegreeCertificates.Batch018.valid368 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate368,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate369 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate369,DegreeCertificates.Batch018.certificate369,(WitnessCertificates.Batch036.certificate738).beta,(WitnessCertificates.Batch036.certificate739).L,none,(CutFailureCertificates.Budget036.certificate738).bound,(CutFailureCertificates.Budget036.certificate739).bound,0⟩
theorem numericValid369 : certificate369.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound369 : certificate369.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch036.certificate738 H MomentCertificates.Batch018.valid369.1 GeometryCertificates.Batch036.valid738 GeometryCertificates.Batch036.sound738 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch036.certificate739 H MomentCertificates.Batch018.valid369.1 GeometryCertificates.Batch036.valid739 GeometryCertificates.Batch036.sound739 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound369 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound369 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate369 GeometryCertificates.Batch036.certificate738 numericValid369
    MomentCertificates.Batch018.valid369 DegreeCertificates.Batch018.valid369 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate369,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate370 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate370,DegreeCertificates.Batch018.certificate370,(WitnessCertificates.Batch037.certificate740).beta,(WitnessCertificates.Batch037.certificate741).L,none,(CutFailureCertificates.Budget037.certificate740).bound,(CutFailureCertificates.Budget037.certificate741).bound,0⟩
theorem numericValid370 : certificate370.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound370 : certificate370.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch037.certificate740 H MomentCertificates.Batch018.valid370.1 GeometryCertificates.Batch037.valid740 GeometryCertificates.Batch037.sound740 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch037.certificate741 H MomentCertificates.Batch018.valid370.1 GeometryCertificates.Batch037.valid741 GeometryCertificates.Batch037.sound741 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound370 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound370 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate370 GeometryCertificates.Batch037.certificate740 numericValid370
    MomentCertificates.Batch018.valid370 DegreeCertificates.Batch018.valid370 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate370,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate371 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate371,DegreeCertificates.Batch018.certificate371,(WitnessCertificates.Batch037.certificate742).beta,(WitnessCertificates.Batch037.certificate743).L,none,(CutFailureCertificates.Budget037.certificate742).bound,(CutFailureCertificates.Budget037.certificate743).bound,0⟩
theorem numericValid371 : certificate371.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound371 : certificate371.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch037.certificate742 H MomentCertificates.Batch018.valid371.1 GeometryCertificates.Batch037.valid742 GeometryCertificates.Batch037.sound742 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch037.certificate743 H MomentCertificates.Batch018.valid371.1 GeometryCertificates.Batch037.valid743 GeometryCertificates.Batch037.sound743 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound371 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound371 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate371 GeometryCertificates.Batch037.certificate742 numericValid371
    MomentCertificates.Batch018.valid371 DegreeCertificates.Batch018.valid371 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate371,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate372 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate372,DegreeCertificates.Batch018.certificate372,(WitnessCertificates.Batch037.certificate744).beta,(WitnessCertificates.Batch037.certificate745).L,none,(CutFailureCertificates.Budget037.certificate744).bound,(CutFailureCertificates.Budget037.certificate745).bound,0⟩
theorem numericValid372 : certificate372.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound372 : certificate372.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch037.certificate744 H MomentCertificates.Batch018.valid372.1 GeometryCertificates.Batch037.valid744 GeometryCertificates.Batch037.sound744 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch037.certificate745 H MomentCertificates.Batch018.valid372.1 GeometryCertificates.Batch037.valid745 GeometryCertificates.Batch037.sound745 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound372 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound372 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate372 GeometryCertificates.Batch037.certificate744 numericValid372
    MomentCertificates.Batch018.valid372 DegreeCertificates.Batch018.valid372 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate372,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate373 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate373,DegreeCertificates.Batch018.certificate373,(WitnessCertificates.Batch037.certificate746).beta,(WitnessCertificates.Batch037.certificate747).L,none,(CutFailureCertificates.Budget037.certificate746).bound,(CutFailureCertificates.Budget037.certificate747).bound,0⟩
theorem numericValid373 : certificate373.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound373 : certificate373.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch037.certificate746 H MomentCertificates.Batch018.valid373.1 GeometryCertificates.Batch037.valid746 GeometryCertificates.Batch037.sound746 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch037.certificate747 H MomentCertificates.Batch018.valid373.1 GeometryCertificates.Batch037.valid747 GeometryCertificates.Batch037.sound747 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound373 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound373 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate373 GeometryCertificates.Batch037.certificate746 numericValid373
    MomentCertificates.Batch018.valid373 DegreeCertificates.Batch018.valid373 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate373,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate374 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate374,DegreeCertificates.Batch018.certificate374,(WitnessCertificates.Batch037.certificate748).beta,(WitnessCertificates.Batch037.certificate749).L,none,(CutFailureCertificates.Budget037.certificate748).bound,(CutFailureCertificates.Budget037.certificate749).bound,0⟩
theorem numericValid374 : certificate374.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound374 : certificate374.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch037.certificate748 H MomentCertificates.Batch018.valid374.1 GeometryCertificates.Batch037.valid748 GeometryCertificates.Batch037.sound748 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch037.certificate749 H MomentCertificates.Batch018.valid374.1 GeometryCertificates.Batch037.valid749 GeometryCertificates.Batch037.sound749 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound374 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound374 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate374 GeometryCertificates.Batch037.certificate748 numericValid374
    MomentCertificates.Batch018.valid374 DegreeCertificates.Batch018.valid374 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate374,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate375 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate375,DegreeCertificates.Batch018.certificate375,(WitnessCertificates.Batch037.certificate750).beta,(WitnessCertificates.Batch037.certificate751).L,none,(CutFailureCertificates.Budget037.certificate750).bound,(CutFailureCertificates.Budget037.certificate751).bound,0⟩
theorem numericValid375 : certificate375.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound375 : certificate375.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch037.certificate750 H MomentCertificates.Batch018.valid375.1 GeometryCertificates.Batch037.valid750 GeometryCertificates.Batch037.sound750 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch037.certificate751 H MomentCertificates.Batch018.valid375.1 GeometryCertificates.Batch037.valid751 GeometryCertificates.Batch037.sound751 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound375 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound375 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate375 GeometryCertificates.Batch037.certificate750 numericValid375
    MomentCertificates.Batch018.valid375 DegreeCertificates.Batch018.valid375 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate375,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate376 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate376,DegreeCertificates.Batch018.certificate376,(WitnessCertificates.Batch037.certificate752).beta,(WitnessCertificates.Batch037.certificate753).L,none,(CutFailureCertificates.Budget037.certificate752).bound,(CutFailureCertificates.Budget037.certificate753).bound,0⟩
theorem numericValid376 : certificate376.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound376 : certificate376.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch037.certificate752 H MomentCertificates.Batch018.valid376.1 GeometryCertificates.Batch037.valid752 GeometryCertificates.Batch037.sound752 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch037.certificate753 H MomentCertificates.Batch018.valid376.1 GeometryCertificates.Batch037.valid753 GeometryCertificates.Batch037.sound753 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound376 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound376 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate376 GeometryCertificates.Batch037.certificate752 numericValid376
    MomentCertificates.Batch018.valid376 DegreeCertificates.Batch018.valid376 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate376,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate377 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate377,DegreeCertificates.Batch018.certificate377,(WitnessCertificates.Batch037.certificate754).beta,(WitnessCertificates.Batch037.certificate755).L,none,(CutFailureCertificates.Budget037.certificate754).bound,(CutFailureCertificates.Budget037.certificate755).bound,0⟩
theorem numericValid377 : certificate377.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound377 : certificate377.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch037.certificate754 H MomentCertificates.Batch018.valid377.1 GeometryCertificates.Batch037.valid754 GeometryCertificates.Batch037.sound754 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch037.certificate755 H MomentCertificates.Batch018.valid377.1 GeometryCertificates.Batch037.valid755 GeometryCertificates.Batch037.sound755 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound377 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound377 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate377 GeometryCertificates.Batch037.certificate754 numericValid377
    MomentCertificates.Batch018.valid377 DegreeCertificates.Batch018.valid377 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate377,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate378 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate378,DegreeCertificates.Batch018.certificate378,(WitnessCertificates.Batch037.certificate756).beta,(WitnessCertificates.Batch037.certificate757).L,none,(CutFailureCertificates.Budget037.certificate756).bound,(CutFailureCertificates.Budget037.certificate757).bound,0⟩
theorem numericValid378 : certificate378.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound378 : certificate378.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch037.certificate756 H MomentCertificates.Batch018.valid378.1 GeometryCertificates.Batch037.valid756 GeometryCertificates.Batch037.sound756 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch037.certificate757 H MomentCertificates.Batch018.valid378.1 GeometryCertificates.Batch037.valid757 GeometryCertificates.Batch037.sound757 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound378 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound378 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate378 GeometryCertificates.Batch037.certificate756 numericValid378
    MomentCertificates.Batch018.valid378 DegreeCertificates.Batch018.valid378 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate378,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate379 : RatSamplerCase := ⟨MomentCertificates.Batch018.certificate379,DegreeCertificates.Batch018.certificate379,(WitnessCertificates.Batch037.certificate758).beta,(WitnessCertificates.Batch037.certificate759).L,none,(CutFailureCertificates.Budget037.certificate758).bound,(CutFailureCertificates.Budget037.certificate759).bound,0⟩
theorem numericValid379 : certificate379.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound379 : certificate379.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch037.certificate758 H MomentCertificates.Batch018.valid379.1 GeometryCertificates.Batch037.valid758 GeometryCertificates.Batch037.sound758 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch037.certificate759 H MomentCertificates.Batch018.valid379.1 GeometryCertificates.Batch037.valid759 GeometryCertificates.Batch037.sound759 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch018.probabilityBound379 H st hI
  have hanchor := CertifiedAnchorFailures.Batch018.probabilityBound379 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate379 GeometryCertificates.Batch037.certificate758 numericValid379
    MomentCertificates.Batch018.valid379 DegreeCertificates.Batch018.valid379 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate379,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate360,certificate361,certificate362,certificate363,certificate364,certificate365,certificate366,certificate367,certificate368,certificate369,certificate370,certificate371,certificate372,certificate373,certificate374,certificate375,certificate376,certificate377,certificate378,certificate379]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound360,List.forall_mem_cons.mpr ⟨sound361,List.forall_mem_cons.mpr ⟨sound362,List.forall_mem_cons.mpr ⟨sound363,List.forall_mem_cons.mpr ⟨sound364,List.forall_mem_cons.mpr ⟨sound365,List.forall_mem_cons.mpr ⟨sound366,List.forall_mem_cons.mpr ⟨sound367,List.forall_mem_cons.mpr ⟨sound368,List.forall_mem_cons.mpr ⟨sound369,List.forall_mem_cons.mpr ⟨sound370,List.forall_mem_cons.mpr ⟨sound371,List.forall_mem_cons.mpr ⟨sound372,List.forall_mem_cons.mpr ⟨sound373,List.forall_mem_cons.mpr ⟨sound374,List.forall_mem_cons.mpr ⟨sound375,List.forall_mem_cons.mpr ⟨sound376,List.forall_mem_cons.mpr ⟨sound377,List.forall_mem_cons.mpr ⟨sound378,List.forall_mem_cons.mpr ⟨sound379,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch018
