import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch013
import Cycle12.CertifiedGlobalFailures.Batch013
import Cycle12.CutFailureCertificates.Budget026
import Cycle12.CutFailureCertificates.Budget027
import Cycle12.DegreeCertificates.Batch013
import Cycle12.GeometryCertificates.Batch026
import Cycle12.GeometryCertificates.Batch027
import Cycle12.MomentCertificates.Batch013
import Cycle12.WitnessCertificates.Batch026
import Cycle12.WitnessCertificates.Batch027

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch013
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate260 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate260,DegreeCertificates.Batch013.certificate260,(WitnessCertificates.Batch026.certificate520).beta,(WitnessCertificates.Batch026.certificate521).L,none,(CutFailureCertificates.Budget026.certificate520).bound,(CutFailureCertificates.Budget026.certificate521).bound,0⟩
theorem numericValid260 : certificate260.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound260 : certificate260.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch026.certificate520 H MomentCertificates.Batch013.valid260.1 GeometryCertificates.Batch026.valid520 GeometryCertificates.Batch026.sound520 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch026.certificate521 H MomentCertificates.Batch013.valid260.1 GeometryCertificates.Batch026.valid521 GeometryCertificates.Batch026.sound521 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound260 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound260 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate260 GeometryCertificates.Batch026.certificate520 numericValid260
    MomentCertificates.Batch013.valid260 DegreeCertificates.Batch013.valid260 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate260,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate261 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate261,DegreeCertificates.Batch013.certificate261,(WitnessCertificates.Batch026.certificate522).beta,(WitnessCertificates.Batch026.certificate523).L,none,(CutFailureCertificates.Budget026.certificate522).bound,(CutFailureCertificates.Budget026.certificate523).bound,0⟩
theorem numericValid261 : certificate261.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound261 : certificate261.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch026.certificate522 H MomentCertificates.Batch013.valid261.1 GeometryCertificates.Batch026.valid522 GeometryCertificates.Batch026.sound522 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch026.certificate523 H MomentCertificates.Batch013.valid261.1 GeometryCertificates.Batch026.valid523 GeometryCertificates.Batch026.sound523 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound261 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound261 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate261 GeometryCertificates.Batch026.certificate522 numericValid261
    MomentCertificates.Batch013.valid261 DegreeCertificates.Batch013.valid261 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate261,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate262 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate262,DegreeCertificates.Batch013.certificate262,(WitnessCertificates.Batch026.certificate524).beta,(WitnessCertificates.Batch026.certificate525).L,none,(CutFailureCertificates.Budget026.certificate524).bound,(CutFailureCertificates.Budget026.certificate525).bound,0⟩
theorem numericValid262 : certificate262.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound262 : certificate262.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch026.certificate524 H MomentCertificates.Batch013.valid262.1 GeometryCertificates.Batch026.valid524 GeometryCertificates.Batch026.sound524 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch026.certificate525 H MomentCertificates.Batch013.valid262.1 GeometryCertificates.Batch026.valid525 GeometryCertificates.Batch026.sound525 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound262 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound262 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate262 GeometryCertificates.Batch026.certificate524 numericValid262
    MomentCertificates.Batch013.valid262 DegreeCertificates.Batch013.valid262 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate262,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate263 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate263,DegreeCertificates.Batch013.certificate263,(WitnessCertificates.Batch026.certificate526).beta,(WitnessCertificates.Batch026.certificate527).L,none,(CutFailureCertificates.Budget026.certificate526).bound,(CutFailureCertificates.Budget026.certificate527).bound,0⟩
theorem numericValid263 : certificate263.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound263 : certificate263.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch026.certificate526 H MomentCertificates.Batch013.valid263.1 GeometryCertificates.Batch026.valid526 GeometryCertificates.Batch026.sound526 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch026.certificate527 H MomentCertificates.Batch013.valid263.1 GeometryCertificates.Batch026.valid527 GeometryCertificates.Batch026.sound527 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound263 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound263 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate263 GeometryCertificates.Batch026.certificate526 numericValid263
    MomentCertificates.Batch013.valid263 DegreeCertificates.Batch013.valid263 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate263,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate264 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate264,DegreeCertificates.Batch013.certificate264,(WitnessCertificates.Batch026.certificate528).beta,(WitnessCertificates.Batch026.certificate529).L,none,(CutFailureCertificates.Budget026.certificate528).bound,(CutFailureCertificates.Budget026.certificate529).bound,0⟩
theorem numericValid264 : certificate264.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound264 : certificate264.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch026.certificate528 H MomentCertificates.Batch013.valid264.1 GeometryCertificates.Batch026.valid528 GeometryCertificates.Batch026.sound528 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch026.certificate529 H MomentCertificates.Batch013.valid264.1 GeometryCertificates.Batch026.valid529 GeometryCertificates.Batch026.sound529 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound264 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound264 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate264 GeometryCertificates.Batch026.certificate528 numericValid264
    MomentCertificates.Batch013.valid264 DegreeCertificates.Batch013.valid264 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate264,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate265 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate265,DegreeCertificates.Batch013.certificate265,(WitnessCertificates.Batch026.certificate530).beta,(WitnessCertificates.Batch026.certificate531).L,none,(CutFailureCertificates.Budget026.certificate530).bound,(CutFailureCertificates.Budget026.certificate531).bound,0⟩
theorem numericValid265 : certificate265.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound265 : certificate265.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch026.certificate530 H MomentCertificates.Batch013.valid265.1 GeometryCertificates.Batch026.valid530 GeometryCertificates.Batch026.sound530 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch026.certificate531 H MomentCertificates.Batch013.valid265.1 GeometryCertificates.Batch026.valid531 GeometryCertificates.Batch026.sound531 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound265 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound265 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate265 GeometryCertificates.Batch026.certificate530 numericValid265
    MomentCertificates.Batch013.valid265 DegreeCertificates.Batch013.valid265 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate265,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate266 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate266,DegreeCertificates.Batch013.certificate266,(WitnessCertificates.Batch026.certificate532).beta,(WitnessCertificates.Batch026.certificate533).L,none,(CutFailureCertificates.Budget026.certificate532).bound,(CutFailureCertificates.Budget026.certificate533).bound,0⟩
theorem numericValid266 : certificate266.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound266 : certificate266.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch026.certificate532 H MomentCertificates.Batch013.valid266.1 GeometryCertificates.Batch026.valid532 GeometryCertificates.Batch026.sound532 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch026.certificate533 H MomentCertificates.Batch013.valid266.1 GeometryCertificates.Batch026.valid533 GeometryCertificates.Batch026.sound533 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound266 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound266 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate266 GeometryCertificates.Batch026.certificate532 numericValid266
    MomentCertificates.Batch013.valid266 DegreeCertificates.Batch013.valid266 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate266,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate267 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate267,DegreeCertificates.Batch013.certificate267,(WitnessCertificates.Batch026.certificate534).beta,(WitnessCertificates.Batch026.certificate535).L,none,(CutFailureCertificates.Budget026.certificate534).bound,(CutFailureCertificates.Budget026.certificate535).bound,0⟩
theorem numericValid267 : certificate267.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound267 : certificate267.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch026.certificate534 H MomentCertificates.Batch013.valid267.1 GeometryCertificates.Batch026.valid534 GeometryCertificates.Batch026.sound534 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch026.certificate535 H MomentCertificates.Batch013.valid267.1 GeometryCertificates.Batch026.valid535 GeometryCertificates.Batch026.sound535 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound267 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound267 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate267 GeometryCertificates.Batch026.certificate534 numericValid267
    MomentCertificates.Batch013.valid267 DegreeCertificates.Batch013.valid267 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate267,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate268 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate268,DegreeCertificates.Batch013.certificate268,(WitnessCertificates.Batch026.certificate536).beta,(WitnessCertificates.Batch026.certificate537).L,none,(CutFailureCertificates.Budget026.certificate536).bound,(CutFailureCertificates.Budget026.certificate537).bound,0⟩
theorem numericValid268 : certificate268.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound268 : certificate268.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch026.certificate536 H MomentCertificates.Batch013.valid268.1 GeometryCertificates.Batch026.valid536 GeometryCertificates.Batch026.sound536 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch026.certificate537 H MomentCertificates.Batch013.valid268.1 GeometryCertificates.Batch026.valid537 GeometryCertificates.Batch026.sound537 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound268 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound268 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate268 GeometryCertificates.Batch026.certificate536 numericValid268
    MomentCertificates.Batch013.valid268 DegreeCertificates.Batch013.valid268 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate268,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate269 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate269,DegreeCertificates.Batch013.certificate269,(WitnessCertificates.Batch026.certificate538).beta,(WitnessCertificates.Batch026.certificate539).L,none,(CutFailureCertificates.Budget026.certificate538).bound,(CutFailureCertificates.Budget026.certificate539).bound,0⟩
theorem numericValid269 : certificate269.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound269 : certificate269.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch026.certificate538 H MomentCertificates.Batch013.valid269.1 GeometryCertificates.Batch026.valid538 GeometryCertificates.Batch026.sound538 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch026.certificate539 H MomentCertificates.Batch013.valid269.1 GeometryCertificates.Batch026.valid539 GeometryCertificates.Batch026.sound539 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound269 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound269 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate269 GeometryCertificates.Batch026.certificate538 numericValid269
    MomentCertificates.Batch013.valid269 DegreeCertificates.Batch013.valid269 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate269,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate270 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate270,DegreeCertificates.Batch013.certificate270,(WitnessCertificates.Batch027.certificate540).beta,(WitnessCertificates.Batch027.certificate541).L,none,(CutFailureCertificates.Budget027.certificate540).bound,(CutFailureCertificates.Budget027.certificate541).bound,0⟩
theorem numericValid270 : certificate270.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound270 : certificate270.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch027.certificate540 H MomentCertificates.Batch013.valid270.1 GeometryCertificates.Batch027.valid540 GeometryCertificates.Batch027.sound540 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch027.certificate541 H MomentCertificates.Batch013.valid270.1 GeometryCertificates.Batch027.valid541 GeometryCertificates.Batch027.sound541 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound270 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound270 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate270 GeometryCertificates.Batch027.certificate540 numericValid270
    MomentCertificates.Batch013.valid270 DegreeCertificates.Batch013.valid270 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate270,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate271 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate271,DegreeCertificates.Batch013.certificate271,(WitnessCertificates.Batch027.certificate542).beta,(WitnessCertificates.Batch027.certificate543).L,none,(CutFailureCertificates.Budget027.certificate542).bound,(CutFailureCertificates.Budget027.certificate543).bound,0⟩
theorem numericValid271 : certificate271.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound271 : certificate271.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch027.certificate542 H MomentCertificates.Batch013.valid271.1 GeometryCertificates.Batch027.valid542 GeometryCertificates.Batch027.sound542 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch027.certificate543 H MomentCertificates.Batch013.valid271.1 GeometryCertificates.Batch027.valid543 GeometryCertificates.Batch027.sound543 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound271 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound271 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate271 GeometryCertificates.Batch027.certificate542 numericValid271
    MomentCertificates.Batch013.valid271 DegreeCertificates.Batch013.valid271 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate271,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate272 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate272,DegreeCertificates.Batch013.certificate272,(WitnessCertificates.Batch027.certificate544).beta,(WitnessCertificates.Batch027.certificate545).L,none,(CutFailureCertificates.Budget027.certificate544).bound,(CutFailureCertificates.Budget027.certificate545).bound,0⟩
theorem numericValid272 : certificate272.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound272 : certificate272.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch027.certificate544 H MomentCertificates.Batch013.valid272.1 GeometryCertificates.Batch027.valid544 GeometryCertificates.Batch027.sound544 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch027.certificate545 H MomentCertificates.Batch013.valid272.1 GeometryCertificates.Batch027.valid545 GeometryCertificates.Batch027.sound545 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound272 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound272 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate272 GeometryCertificates.Batch027.certificate544 numericValid272
    MomentCertificates.Batch013.valid272 DegreeCertificates.Batch013.valid272 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate272,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate273 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate273,DegreeCertificates.Batch013.certificate273,(WitnessCertificates.Batch027.certificate546).beta,(WitnessCertificates.Batch027.certificate547).L,none,(CutFailureCertificates.Budget027.certificate546).bound,(CutFailureCertificates.Budget027.certificate547).bound,0⟩
theorem numericValid273 : certificate273.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound273 : certificate273.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch027.certificate546 H MomentCertificates.Batch013.valid273.1 GeometryCertificates.Batch027.valid546 GeometryCertificates.Batch027.sound546 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch027.certificate547 H MomentCertificates.Batch013.valid273.1 GeometryCertificates.Batch027.valid547 GeometryCertificates.Batch027.sound547 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound273 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound273 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate273 GeometryCertificates.Batch027.certificate546 numericValid273
    MomentCertificates.Batch013.valid273 DegreeCertificates.Batch013.valid273 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate273,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate274 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate274,DegreeCertificates.Batch013.certificate274,(WitnessCertificates.Batch027.certificate548).beta,(WitnessCertificates.Batch027.certificate549).L,none,(CutFailureCertificates.Budget027.certificate548).bound,(CutFailureCertificates.Budget027.certificate549).bound,0⟩
theorem numericValid274 : certificate274.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound274 : certificate274.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch027.certificate548 H MomentCertificates.Batch013.valid274.1 GeometryCertificates.Batch027.valid548 GeometryCertificates.Batch027.sound548 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch027.certificate549 H MomentCertificates.Batch013.valid274.1 GeometryCertificates.Batch027.valid549 GeometryCertificates.Batch027.sound549 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound274 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound274 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate274 GeometryCertificates.Batch027.certificate548 numericValid274
    MomentCertificates.Batch013.valid274 DegreeCertificates.Batch013.valid274 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate274,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate275 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate275,DegreeCertificates.Batch013.certificate275,(WitnessCertificates.Batch027.certificate550).beta,(WitnessCertificates.Batch027.certificate551).L,none,(CutFailureCertificates.Budget027.certificate550).bound,(CutFailureCertificates.Budget027.certificate551).bound,0⟩
theorem numericValid275 : certificate275.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound275 : certificate275.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch027.certificate550 H MomentCertificates.Batch013.valid275.1 GeometryCertificates.Batch027.valid550 GeometryCertificates.Batch027.sound550 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch027.certificate551 H MomentCertificates.Batch013.valid275.1 GeometryCertificates.Batch027.valid551 GeometryCertificates.Batch027.sound551 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound275 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound275 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate275 GeometryCertificates.Batch027.certificate550 numericValid275
    MomentCertificates.Batch013.valid275 DegreeCertificates.Batch013.valid275 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate275,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate276 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate276,DegreeCertificates.Batch013.certificate276,(WitnessCertificates.Batch027.certificate552).beta,(WitnessCertificates.Batch027.certificate553).L,none,(CutFailureCertificates.Budget027.certificate552).bound,(CutFailureCertificates.Budget027.certificate553).bound,0⟩
theorem numericValid276 : certificate276.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound276 : certificate276.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch027.certificate552 H MomentCertificates.Batch013.valid276.1 GeometryCertificates.Batch027.valid552 GeometryCertificates.Batch027.sound552 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch027.certificate553 H MomentCertificates.Batch013.valid276.1 GeometryCertificates.Batch027.valid553 GeometryCertificates.Batch027.sound553 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound276 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound276 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate276 GeometryCertificates.Batch027.certificate552 numericValid276
    MomentCertificates.Batch013.valid276 DegreeCertificates.Batch013.valid276 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate276,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate277 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate277,DegreeCertificates.Batch013.certificate277,(WitnessCertificates.Batch027.certificate554).beta,(WitnessCertificates.Batch027.certificate555).L,none,(CutFailureCertificates.Budget027.certificate554).bound,(CutFailureCertificates.Budget027.certificate555).bound,0⟩
theorem numericValid277 : certificate277.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound277 : certificate277.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch027.certificate554 H MomentCertificates.Batch013.valid277.1 GeometryCertificates.Batch027.valid554 GeometryCertificates.Batch027.sound554 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch027.certificate555 H MomentCertificates.Batch013.valid277.1 GeometryCertificates.Batch027.valid555 GeometryCertificates.Batch027.sound555 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound277 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound277 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate277 GeometryCertificates.Batch027.certificate554 numericValid277
    MomentCertificates.Batch013.valid277 DegreeCertificates.Batch013.valid277 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate277,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate278 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate278,DegreeCertificates.Batch013.certificate278,(WitnessCertificates.Batch027.certificate556).beta,(WitnessCertificates.Batch027.certificate557).L,none,(CutFailureCertificates.Budget027.certificate556).bound,(CutFailureCertificates.Budget027.certificate557).bound,0⟩
theorem numericValid278 : certificate278.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound278 : certificate278.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch027.certificate556 H MomentCertificates.Batch013.valid278.1 GeometryCertificates.Batch027.valid556 GeometryCertificates.Batch027.sound556 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch027.certificate557 H MomentCertificates.Batch013.valid278.1 GeometryCertificates.Batch027.valid557 GeometryCertificates.Batch027.sound557 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound278 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound278 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate278 GeometryCertificates.Batch027.certificate556 numericValid278
    MomentCertificates.Batch013.valid278 DegreeCertificates.Batch013.valid278 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate278,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate279 : RatSamplerCase := ⟨MomentCertificates.Batch013.certificate279,DegreeCertificates.Batch013.certificate279,(WitnessCertificates.Batch027.certificate558).beta,(WitnessCertificates.Batch027.certificate559).L,none,(CutFailureCertificates.Budget027.certificate558).bound,(CutFailureCertificates.Budget027.certificate559).bound,0⟩
theorem numericValid279 : certificate279.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound279 : certificate279.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch027.certificate558 H MomentCertificates.Batch013.valid279.1 GeometryCertificates.Batch027.valid558 GeometryCertificates.Batch027.sound558 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch027.certificate559 H MomentCertificates.Batch013.valid279.1 GeometryCertificates.Batch027.valid559 GeometryCertificates.Batch027.sound559 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch013.probabilityBound279 H st hI
  have hanchor := CertifiedAnchorFailures.Batch013.probabilityBound279 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate279 GeometryCertificates.Batch027.certificate558 numericValid279
    MomentCertificates.Batch013.valid279 DegreeCertificates.Batch013.valid279 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate279,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate260,certificate261,certificate262,certificate263,certificate264,certificate265,certificate266,certificate267,certificate268,certificate269,certificate270,certificate271,certificate272,certificate273,certificate274,certificate275,certificate276,certificate277,certificate278,certificate279]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound260,List.forall_mem_cons.mpr ⟨sound261,List.forall_mem_cons.mpr ⟨sound262,List.forall_mem_cons.mpr ⟨sound263,List.forall_mem_cons.mpr ⟨sound264,List.forall_mem_cons.mpr ⟨sound265,List.forall_mem_cons.mpr ⟨sound266,List.forall_mem_cons.mpr ⟨sound267,List.forall_mem_cons.mpr ⟨sound268,List.forall_mem_cons.mpr ⟨sound269,List.forall_mem_cons.mpr ⟨sound270,List.forall_mem_cons.mpr ⟨sound271,List.forall_mem_cons.mpr ⟨sound272,List.forall_mem_cons.mpr ⟨sound273,List.forall_mem_cons.mpr ⟨sound274,List.forall_mem_cons.mpr ⟨sound275,List.forall_mem_cons.mpr ⟨sound276,List.forall_mem_cons.mpr ⟨sound277,List.forall_mem_cons.mpr ⟨sound278,List.forall_mem_cons.mpr ⟨sound279,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch013
