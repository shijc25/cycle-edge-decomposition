import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch011
import Cycle12.CertifiedGlobalFailures.Batch011
import Cycle12.CutFailureCertificates.Budget022
import Cycle12.CutFailureCertificates.Budget023
import Cycle12.DegreeCertificates.Batch011
import Cycle12.GeometryCertificates.Batch022
import Cycle12.GeometryCertificates.Batch023
import Cycle12.MomentCertificates.Batch011
import Cycle12.WitnessCertificates.Batch022
import Cycle12.WitnessCertificates.Batch023

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch011
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate220 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate220,DegreeCertificates.Batch011.certificate220,(WitnessCertificates.Batch022.certificate440).beta,(WitnessCertificates.Batch022.certificate441).L,none,(CutFailureCertificates.Budget022.certificate440).bound,(CutFailureCertificates.Budget022.certificate441).bound,0⟩
theorem numericValid220 : certificate220.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound220 : certificate220.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch022.certificate440 H MomentCertificates.Batch011.valid220.1 GeometryCertificates.Batch022.valid440 GeometryCertificates.Batch022.sound440 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch022.certificate441 H MomentCertificates.Batch011.valid220.1 GeometryCertificates.Batch022.valid441 GeometryCertificates.Batch022.sound441 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound220 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound220 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate220 GeometryCertificates.Batch022.certificate440 numericValid220
    MomentCertificates.Batch011.valid220 DegreeCertificates.Batch011.valid220 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate220,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate221 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate221,DegreeCertificates.Batch011.certificate221,(WitnessCertificates.Batch022.certificate442).beta,(WitnessCertificates.Batch022.certificate443).L,none,(CutFailureCertificates.Budget022.certificate442).bound,(CutFailureCertificates.Budget022.certificate443).bound,0⟩
theorem numericValid221 : certificate221.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound221 : certificate221.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch022.certificate442 H MomentCertificates.Batch011.valid221.1 GeometryCertificates.Batch022.valid442 GeometryCertificates.Batch022.sound442 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch022.certificate443 H MomentCertificates.Batch011.valid221.1 GeometryCertificates.Batch022.valid443 GeometryCertificates.Batch022.sound443 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound221 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound221 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate221 GeometryCertificates.Batch022.certificate442 numericValid221
    MomentCertificates.Batch011.valid221 DegreeCertificates.Batch011.valid221 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate221,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate222 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate222,DegreeCertificates.Batch011.certificate222,(WitnessCertificates.Batch022.certificate444).beta,(WitnessCertificates.Batch022.certificate445).L,none,(CutFailureCertificates.Budget022.certificate444).bound,(CutFailureCertificates.Budget022.certificate445).bound,0⟩
theorem numericValid222 : certificate222.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound222 : certificate222.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch022.certificate444 H MomentCertificates.Batch011.valid222.1 GeometryCertificates.Batch022.valid444 GeometryCertificates.Batch022.sound444 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch022.certificate445 H MomentCertificates.Batch011.valid222.1 GeometryCertificates.Batch022.valid445 GeometryCertificates.Batch022.sound445 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound222 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound222 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate222 GeometryCertificates.Batch022.certificate444 numericValid222
    MomentCertificates.Batch011.valid222 DegreeCertificates.Batch011.valid222 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate222,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate223 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate223,DegreeCertificates.Batch011.certificate223,(WitnessCertificates.Batch022.certificate446).beta,(WitnessCertificates.Batch022.certificate447).L,none,(CutFailureCertificates.Budget022.certificate446).bound,(CutFailureCertificates.Budget022.certificate447).bound,0⟩
theorem numericValid223 : certificate223.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound223 : certificate223.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch022.certificate446 H MomentCertificates.Batch011.valid223.1 GeometryCertificates.Batch022.valid446 GeometryCertificates.Batch022.sound446 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch022.certificate447 H MomentCertificates.Batch011.valid223.1 GeometryCertificates.Batch022.valid447 GeometryCertificates.Batch022.sound447 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound223 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound223 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate223 GeometryCertificates.Batch022.certificate446 numericValid223
    MomentCertificates.Batch011.valid223 DegreeCertificates.Batch011.valid223 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate223,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate224 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate224,DegreeCertificates.Batch011.certificate224,(WitnessCertificates.Batch022.certificate448).beta,(WitnessCertificates.Batch022.certificate449).L,none,(CutFailureCertificates.Budget022.certificate448).bound,(CutFailureCertificates.Budget022.certificate449).bound,0⟩
theorem numericValid224 : certificate224.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound224 : certificate224.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch022.certificate448 H MomentCertificates.Batch011.valid224.1 GeometryCertificates.Batch022.valid448 GeometryCertificates.Batch022.sound448 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch022.certificate449 H MomentCertificates.Batch011.valid224.1 GeometryCertificates.Batch022.valid449 GeometryCertificates.Batch022.sound449 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound224 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound224 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate224 GeometryCertificates.Batch022.certificate448 numericValid224
    MomentCertificates.Batch011.valid224 DegreeCertificates.Batch011.valid224 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate224,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate225 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate225,DegreeCertificates.Batch011.certificate225,(WitnessCertificates.Batch022.certificate450).beta,(WitnessCertificates.Batch022.certificate451).L,none,(CutFailureCertificates.Budget022.certificate450).bound,(CutFailureCertificates.Budget022.certificate451).bound,0⟩
theorem numericValid225 : certificate225.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound225 : certificate225.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch022.certificate450 H MomentCertificates.Batch011.valid225.1 GeometryCertificates.Batch022.valid450 GeometryCertificates.Batch022.sound450 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch022.certificate451 H MomentCertificates.Batch011.valid225.1 GeometryCertificates.Batch022.valid451 GeometryCertificates.Batch022.sound451 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound225 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound225 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate225 GeometryCertificates.Batch022.certificate450 numericValid225
    MomentCertificates.Batch011.valid225 DegreeCertificates.Batch011.valid225 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate225,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate226 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate226,DegreeCertificates.Batch011.certificate226,(WitnessCertificates.Batch022.certificate452).beta,(WitnessCertificates.Batch022.certificate453).L,none,(CutFailureCertificates.Budget022.certificate452).bound,(CutFailureCertificates.Budget022.certificate453).bound,0⟩
theorem numericValid226 : certificate226.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound226 : certificate226.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch022.certificate452 H MomentCertificates.Batch011.valid226.1 GeometryCertificates.Batch022.valid452 GeometryCertificates.Batch022.sound452 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch022.certificate453 H MomentCertificates.Batch011.valid226.1 GeometryCertificates.Batch022.valid453 GeometryCertificates.Batch022.sound453 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound226 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound226 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate226 GeometryCertificates.Batch022.certificate452 numericValid226
    MomentCertificates.Batch011.valid226 DegreeCertificates.Batch011.valid226 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate226,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate227 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate227,DegreeCertificates.Batch011.certificate227,(WitnessCertificates.Batch022.certificate454).beta,(WitnessCertificates.Batch022.certificate455).L,none,(CutFailureCertificates.Budget022.certificate454).bound,(CutFailureCertificates.Budget022.certificate455).bound,0⟩
theorem numericValid227 : certificate227.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound227 : certificate227.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch022.certificate454 H MomentCertificates.Batch011.valid227.1 GeometryCertificates.Batch022.valid454 GeometryCertificates.Batch022.sound454 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch022.certificate455 H MomentCertificates.Batch011.valid227.1 GeometryCertificates.Batch022.valid455 GeometryCertificates.Batch022.sound455 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound227 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound227 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate227 GeometryCertificates.Batch022.certificate454 numericValid227
    MomentCertificates.Batch011.valid227 DegreeCertificates.Batch011.valid227 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate227,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate228 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate228,DegreeCertificates.Batch011.certificate228,(WitnessCertificates.Batch022.certificate456).beta,(WitnessCertificates.Batch022.certificate457).L,none,(CutFailureCertificates.Budget022.certificate456).bound,(CutFailureCertificates.Budget022.certificate457).bound,0⟩
theorem numericValid228 : certificate228.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound228 : certificate228.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch022.certificate456 H MomentCertificates.Batch011.valid228.1 GeometryCertificates.Batch022.valid456 GeometryCertificates.Batch022.sound456 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch022.certificate457 H MomentCertificates.Batch011.valid228.1 GeometryCertificates.Batch022.valid457 GeometryCertificates.Batch022.sound457 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound228 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound228 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate228 GeometryCertificates.Batch022.certificate456 numericValid228
    MomentCertificates.Batch011.valid228 DegreeCertificates.Batch011.valid228 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate228,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate229 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate229,DegreeCertificates.Batch011.certificate229,(WitnessCertificates.Batch022.certificate458).beta,(WitnessCertificates.Batch022.certificate459).L,none,(CutFailureCertificates.Budget022.certificate458).bound,(CutFailureCertificates.Budget022.certificate459).bound,0⟩
theorem numericValid229 : certificate229.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound229 : certificate229.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch022.certificate458 H MomentCertificates.Batch011.valid229.1 GeometryCertificates.Batch022.valid458 GeometryCertificates.Batch022.sound458 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch022.certificate459 H MomentCertificates.Batch011.valid229.1 GeometryCertificates.Batch022.valid459 GeometryCertificates.Batch022.sound459 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound229 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound229 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate229 GeometryCertificates.Batch022.certificate458 numericValid229
    MomentCertificates.Batch011.valid229 DegreeCertificates.Batch011.valid229 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate229,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate230 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate230,DegreeCertificates.Batch011.certificate230,(WitnessCertificates.Batch023.certificate460).beta,(WitnessCertificates.Batch023.certificate461).L,none,(CutFailureCertificates.Budget023.certificate460).bound,(CutFailureCertificates.Budget023.certificate461).bound,0⟩
theorem numericValid230 : certificate230.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound230 : certificate230.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch023.certificate460 H MomentCertificates.Batch011.valid230.1 GeometryCertificates.Batch023.valid460 GeometryCertificates.Batch023.sound460 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch023.certificate461 H MomentCertificates.Batch011.valid230.1 GeometryCertificates.Batch023.valid461 GeometryCertificates.Batch023.sound461 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound230 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound230 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate230 GeometryCertificates.Batch023.certificate460 numericValid230
    MomentCertificates.Batch011.valid230 DegreeCertificates.Batch011.valid230 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate230,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate231 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate231,DegreeCertificates.Batch011.certificate231,(WitnessCertificates.Batch023.certificate462).beta,(WitnessCertificates.Batch023.certificate463).L,none,(CutFailureCertificates.Budget023.certificate462).bound,(CutFailureCertificates.Budget023.certificate463).bound,0⟩
theorem numericValid231 : certificate231.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound231 : certificate231.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch023.certificate462 H MomentCertificates.Batch011.valid231.1 GeometryCertificates.Batch023.valid462 GeometryCertificates.Batch023.sound462 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch023.certificate463 H MomentCertificates.Batch011.valid231.1 GeometryCertificates.Batch023.valid463 GeometryCertificates.Batch023.sound463 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound231 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound231 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate231 GeometryCertificates.Batch023.certificate462 numericValid231
    MomentCertificates.Batch011.valid231 DegreeCertificates.Batch011.valid231 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate231,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate232 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate232,DegreeCertificates.Batch011.certificate232,(WitnessCertificates.Batch023.certificate464).beta,(WitnessCertificates.Batch023.certificate465).L,none,(CutFailureCertificates.Budget023.certificate464).bound,(CutFailureCertificates.Budget023.certificate465).bound,0⟩
theorem numericValid232 : certificate232.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound232 : certificate232.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch023.certificate464 H MomentCertificates.Batch011.valid232.1 GeometryCertificates.Batch023.valid464 GeometryCertificates.Batch023.sound464 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch023.certificate465 H MomentCertificates.Batch011.valid232.1 GeometryCertificates.Batch023.valid465 GeometryCertificates.Batch023.sound465 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound232 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound232 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate232 GeometryCertificates.Batch023.certificate464 numericValid232
    MomentCertificates.Batch011.valid232 DegreeCertificates.Batch011.valid232 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate232,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate233 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate233,DegreeCertificates.Batch011.certificate233,(WitnessCertificates.Batch023.certificate466).beta,(WitnessCertificates.Batch023.certificate467).L,none,(CutFailureCertificates.Budget023.certificate466).bound,(CutFailureCertificates.Budget023.certificate467).bound,0⟩
theorem numericValid233 : certificate233.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound233 : certificate233.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch023.certificate466 H MomentCertificates.Batch011.valid233.1 GeometryCertificates.Batch023.valid466 GeometryCertificates.Batch023.sound466 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch023.certificate467 H MomentCertificates.Batch011.valid233.1 GeometryCertificates.Batch023.valid467 GeometryCertificates.Batch023.sound467 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound233 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound233 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate233 GeometryCertificates.Batch023.certificate466 numericValid233
    MomentCertificates.Batch011.valid233 DegreeCertificates.Batch011.valid233 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate233,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate234 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate234,DegreeCertificates.Batch011.certificate234,(WitnessCertificates.Batch023.certificate468).beta,(WitnessCertificates.Batch023.certificate469).L,none,(CutFailureCertificates.Budget023.certificate468).bound,(CutFailureCertificates.Budget023.certificate469).bound,0⟩
theorem numericValid234 : certificate234.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound234 : certificate234.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch023.certificate468 H MomentCertificates.Batch011.valid234.1 GeometryCertificates.Batch023.valid468 GeometryCertificates.Batch023.sound468 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch023.certificate469 H MomentCertificates.Batch011.valid234.1 GeometryCertificates.Batch023.valid469 GeometryCertificates.Batch023.sound469 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound234 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound234 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate234 GeometryCertificates.Batch023.certificate468 numericValid234
    MomentCertificates.Batch011.valid234 DegreeCertificates.Batch011.valid234 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate234,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate235 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate235,DegreeCertificates.Batch011.certificate235,(WitnessCertificates.Batch023.certificate470).beta,(WitnessCertificates.Batch023.certificate471).L,none,(CutFailureCertificates.Budget023.certificate470).bound,(CutFailureCertificates.Budget023.certificate471).bound,0⟩
theorem numericValid235 : certificate235.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound235 : certificate235.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch023.certificate470 H MomentCertificates.Batch011.valid235.1 GeometryCertificates.Batch023.valid470 GeometryCertificates.Batch023.sound470 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch023.certificate471 H MomentCertificates.Batch011.valid235.1 GeometryCertificates.Batch023.valid471 GeometryCertificates.Batch023.sound471 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound235 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound235 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate235 GeometryCertificates.Batch023.certificate470 numericValid235
    MomentCertificates.Batch011.valid235 DegreeCertificates.Batch011.valid235 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate235,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate236 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate236,DegreeCertificates.Batch011.certificate236,(WitnessCertificates.Batch023.certificate472).beta,(WitnessCertificates.Batch023.certificate473).L,none,(CutFailureCertificates.Budget023.certificate472).bound,(CutFailureCertificates.Budget023.certificate473).bound,0⟩
theorem numericValid236 : certificate236.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound236 : certificate236.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch023.certificate472 H MomentCertificates.Batch011.valid236.1 GeometryCertificates.Batch023.valid472 GeometryCertificates.Batch023.sound472 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch023.certificate473 H MomentCertificates.Batch011.valid236.1 GeometryCertificates.Batch023.valid473 GeometryCertificates.Batch023.sound473 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound236 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound236 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate236 GeometryCertificates.Batch023.certificate472 numericValid236
    MomentCertificates.Batch011.valid236 DegreeCertificates.Batch011.valid236 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate236,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate237 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate237,DegreeCertificates.Batch011.certificate237,(WitnessCertificates.Batch023.certificate474).beta,(WitnessCertificates.Batch023.certificate475).L,none,(CutFailureCertificates.Budget023.certificate474).bound,(CutFailureCertificates.Budget023.certificate475).bound,0⟩
theorem numericValid237 : certificate237.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound237 : certificate237.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch023.certificate474 H MomentCertificates.Batch011.valid237.1 GeometryCertificates.Batch023.valid474 GeometryCertificates.Batch023.sound474 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch023.certificate475 H MomentCertificates.Batch011.valid237.1 GeometryCertificates.Batch023.valid475 GeometryCertificates.Batch023.sound475 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound237 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound237 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate237 GeometryCertificates.Batch023.certificate474 numericValid237
    MomentCertificates.Batch011.valid237 DegreeCertificates.Batch011.valid237 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate237,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate238 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate238,DegreeCertificates.Batch011.certificate238,(WitnessCertificates.Batch023.certificate476).beta,(WitnessCertificates.Batch023.certificate477).L,none,(CutFailureCertificates.Budget023.certificate476).bound,(CutFailureCertificates.Budget023.certificate477).bound,0⟩
theorem numericValid238 : certificate238.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound238 : certificate238.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch023.certificate476 H MomentCertificates.Batch011.valid238.1 GeometryCertificates.Batch023.valid476 GeometryCertificates.Batch023.sound476 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch023.certificate477 H MomentCertificates.Batch011.valid238.1 GeometryCertificates.Batch023.valid477 GeometryCertificates.Batch023.sound477 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound238 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound238 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate238 GeometryCertificates.Batch023.certificate476 numericValid238
    MomentCertificates.Batch011.valid238 DegreeCertificates.Batch011.valid238 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate238,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate239 : RatSamplerCase := ⟨MomentCertificates.Batch011.certificate239,DegreeCertificates.Batch011.certificate239,(WitnessCertificates.Batch023.certificate478).beta,(WitnessCertificates.Batch023.certificate479).L,none,(CutFailureCertificates.Budget023.certificate478).bound,(CutFailureCertificates.Budget023.certificate479).bound,0⟩
theorem numericValid239 : certificate239.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound239 : certificate239.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch023.certificate478 H MomentCertificates.Batch011.valid239.1 GeometryCertificates.Batch023.valid478 GeometryCertificates.Batch023.sound478 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch023.certificate479 H MomentCertificates.Batch011.valid239.1 GeometryCertificates.Batch023.valid479 GeometryCertificates.Batch023.sound479 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch011.probabilityBound239 H st hI
  have hanchor := CertifiedAnchorFailures.Batch011.probabilityBound239 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate239 GeometryCertificates.Batch023.certificate478 numericValid239
    MomentCertificates.Batch011.valid239 DegreeCertificates.Batch011.valid239 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate239,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate220,certificate221,certificate222,certificate223,certificate224,certificate225,certificate226,certificate227,certificate228,certificate229,certificate230,certificate231,certificate232,certificate233,certificate234,certificate235,certificate236,certificate237,certificate238,certificate239]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound220,List.forall_mem_cons.mpr ⟨sound221,List.forall_mem_cons.mpr ⟨sound222,List.forall_mem_cons.mpr ⟨sound223,List.forall_mem_cons.mpr ⟨sound224,List.forall_mem_cons.mpr ⟨sound225,List.forall_mem_cons.mpr ⟨sound226,List.forall_mem_cons.mpr ⟨sound227,List.forall_mem_cons.mpr ⟨sound228,List.forall_mem_cons.mpr ⟨sound229,List.forall_mem_cons.mpr ⟨sound230,List.forall_mem_cons.mpr ⟨sound231,List.forall_mem_cons.mpr ⟨sound232,List.forall_mem_cons.mpr ⟨sound233,List.forall_mem_cons.mpr ⟨sound234,List.forall_mem_cons.mpr ⟨sound235,List.forall_mem_cons.mpr ⟨sound236,List.forall_mem_cons.mpr ⟨sound237,List.forall_mem_cons.mpr ⟨sound238,List.forall_mem_cons.mpr ⟨sound239,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch011
