import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch012
import Cycle12.CertifiedGlobalFailures.Batch012
import Cycle12.CutFailureCertificates.Budget024
import Cycle12.CutFailureCertificates.Budget025
import Cycle12.DegreeCertificates.Batch012
import Cycle12.GeometryCertificates.Batch024
import Cycle12.GeometryCertificates.Batch025
import Cycle12.MomentCertificates.Batch012
import Cycle12.WitnessCertificates.Batch024
import Cycle12.WitnessCertificates.Batch025

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch012
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate240 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate240,DegreeCertificates.Batch012.certificate240,(WitnessCertificates.Batch024.certificate480).beta,(WitnessCertificates.Batch024.certificate481).L,none,(CutFailureCertificates.Budget024.certificate480).bound,(CutFailureCertificates.Budget024.certificate481).bound,0⟩
theorem numericValid240 : certificate240.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound240 : certificate240.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch024.certificate480 H MomentCertificates.Batch012.valid240.1 GeometryCertificates.Batch024.valid480 GeometryCertificates.Batch024.sound480 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch024.certificate481 H MomentCertificates.Batch012.valid240.1 GeometryCertificates.Batch024.valid481 GeometryCertificates.Batch024.sound481 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound240 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound240 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate240 GeometryCertificates.Batch024.certificate480 numericValid240
    MomentCertificates.Batch012.valid240 DegreeCertificates.Batch012.valid240 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate240,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate241 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate241,DegreeCertificates.Batch012.certificate241,(WitnessCertificates.Batch024.certificate482).beta,(WitnessCertificates.Batch024.certificate483).L,none,(CutFailureCertificates.Budget024.certificate482).bound,(CutFailureCertificates.Budget024.certificate483).bound,0⟩
theorem numericValid241 : certificate241.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound241 : certificate241.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch024.certificate482 H MomentCertificates.Batch012.valid241.1 GeometryCertificates.Batch024.valid482 GeometryCertificates.Batch024.sound482 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch024.certificate483 H MomentCertificates.Batch012.valid241.1 GeometryCertificates.Batch024.valid483 GeometryCertificates.Batch024.sound483 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound241 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound241 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate241 GeometryCertificates.Batch024.certificate482 numericValid241
    MomentCertificates.Batch012.valid241 DegreeCertificates.Batch012.valid241 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate241,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate242 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate242,DegreeCertificates.Batch012.certificate242,(WitnessCertificates.Batch024.certificate484).beta,(WitnessCertificates.Batch024.certificate485).L,none,(CutFailureCertificates.Budget024.certificate484).bound,(CutFailureCertificates.Budget024.certificate485).bound,0⟩
theorem numericValid242 : certificate242.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound242 : certificate242.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch024.certificate484 H MomentCertificates.Batch012.valid242.1 GeometryCertificates.Batch024.valid484 GeometryCertificates.Batch024.sound484 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch024.certificate485 H MomentCertificates.Batch012.valid242.1 GeometryCertificates.Batch024.valid485 GeometryCertificates.Batch024.sound485 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound242 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound242 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate242 GeometryCertificates.Batch024.certificate484 numericValid242
    MomentCertificates.Batch012.valid242 DegreeCertificates.Batch012.valid242 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate242,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate243 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate243,DegreeCertificates.Batch012.certificate243,(WitnessCertificates.Batch024.certificate486).beta,(WitnessCertificates.Batch024.certificate487).L,none,(CutFailureCertificates.Budget024.certificate486).bound,(CutFailureCertificates.Budget024.certificate487).bound,0⟩
theorem numericValid243 : certificate243.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound243 : certificate243.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch024.certificate486 H MomentCertificates.Batch012.valid243.1 GeometryCertificates.Batch024.valid486 GeometryCertificates.Batch024.sound486 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch024.certificate487 H MomentCertificates.Batch012.valid243.1 GeometryCertificates.Batch024.valid487 GeometryCertificates.Batch024.sound487 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound243 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound243 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate243 GeometryCertificates.Batch024.certificate486 numericValid243
    MomentCertificates.Batch012.valid243 DegreeCertificates.Batch012.valid243 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate243,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate244 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate244,DegreeCertificates.Batch012.certificate244,(WitnessCertificates.Batch024.certificate488).beta,(WitnessCertificates.Batch024.certificate489).L,none,(CutFailureCertificates.Budget024.certificate488).bound,(CutFailureCertificates.Budget024.certificate489).bound,0⟩
theorem numericValid244 : certificate244.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound244 : certificate244.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch024.certificate488 H MomentCertificates.Batch012.valid244.1 GeometryCertificates.Batch024.valid488 GeometryCertificates.Batch024.sound488 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch024.certificate489 H MomentCertificates.Batch012.valid244.1 GeometryCertificates.Batch024.valid489 GeometryCertificates.Batch024.sound489 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound244 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound244 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate244 GeometryCertificates.Batch024.certificate488 numericValid244
    MomentCertificates.Batch012.valid244 DegreeCertificates.Batch012.valid244 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate244,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate245 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate245,DegreeCertificates.Batch012.certificate245,(WitnessCertificates.Batch024.certificate490).beta,(WitnessCertificates.Batch024.certificate491).L,none,(CutFailureCertificates.Budget024.certificate490).bound,(CutFailureCertificates.Budget024.certificate491).bound,0⟩
theorem numericValid245 : certificate245.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound245 : certificate245.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch024.certificate490 H MomentCertificates.Batch012.valid245.1 GeometryCertificates.Batch024.valid490 GeometryCertificates.Batch024.sound490 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch024.certificate491 H MomentCertificates.Batch012.valid245.1 GeometryCertificates.Batch024.valid491 GeometryCertificates.Batch024.sound491 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound245 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound245 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate245 GeometryCertificates.Batch024.certificate490 numericValid245
    MomentCertificates.Batch012.valid245 DegreeCertificates.Batch012.valid245 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate245,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate246 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate246,DegreeCertificates.Batch012.certificate246,(WitnessCertificates.Batch024.certificate492).beta,(WitnessCertificates.Batch024.certificate493).L,none,(CutFailureCertificates.Budget024.certificate492).bound,(CutFailureCertificates.Budget024.certificate493).bound,0⟩
theorem numericValid246 : certificate246.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound246 : certificate246.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch024.certificate492 H MomentCertificates.Batch012.valid246.1 GeometryCertificates.Batch024.valid492 GeometryCertificates.Batch024.sound492 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch024.certificate493 H MomentCertificates.Batch012.valid246.1 GeometryCertificates.Batch024.valid493 GeometryCertificates.Batch024.sound493 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound246 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound246 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate246 GeometryCertificates.Batch024.certificate492 numericValid246
    MomentCertificates.Batch012.valid246 DegreeCertificates.Batch012.valid246 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate246,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate247 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate247,DegreeCertificates.Batch012.certificate247,(WitnessCertificates.Batch024.certificate494).beta,(WitnessCertificates.Batch024.certificate495).L,none,(CutFailureCertificates.Budget024.certificate494).bound,(CutFailureCertificates.Budget024.certificate495).bound,0⟩
theorem numericValid247 : certificate247.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound247 : certificate247.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch024.certificate494 H MomentCertificates.Batch012.valid247.1 GeometryCertificates.Batch024.valid494 GeometryCertificates.Batch024.sound494 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch024.certificate495 H MomentCertificates.Batch012.valid247.1 GeometryCertificates.Batch024.valid495 GeometryCertificates.Batch024.sound495 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound247 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound247 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate247 GeometryCertificates.Batch024.certificate494 numericValid247
    MomentCertificates.Batch012.valid247 DegreeCertificates.Batch012.valid247 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate247,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate248 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate248,DegreeCertificates.Batch012.certificate248,(WitnessCertificates.Batch024.certificate496).beta,(WitnessCertificates.Batch024.certificate497).L,none,(CutFailureCertificates.Budget024.certificate496).bound,(CutFailureCertificates.Budget024.certificate497).bound,0⟩
theorem numericValid248 : certificate248.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound248 : certificate248.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch024.certificate496 H MomentCertificates.Batch012.valid248.1 GeometryCertificates.Batch024.valid496 GeometryCertificates.Batch024.sound496 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch024.certificate497 H MomentCertificates.Batch012.valid248.1 GeometryCertificates.Batch024.valid497 GeometryCertificates.Batch024.sound497 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound248 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound248 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate248 GeometryCertificates.Batch024.certificate496 numericValid248
    MomentCertificates.Batch012.valid248 DegreeCertificates.Batch012.valid248 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate248,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate249 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate249,DegreeCertificates.Batch012.certificate249,(WitnessCertificates.Batch024.certificate498).beta,(WitnessCertificates.Batch024.certificate499).L,none,(CutFailureCertificates.Budget024.certificate498).bound,(CutFailureCertificates.Budget024.certificate499).bound,0⟩
theorem numericValid249 : certificate249.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound249 : certificate249.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch024.certificate498 H MomentCertificates.Batch012.valid249.1 GeometryCertificates.Batch024.valid498 GeometryCertificates.Batch024.sound498 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch024.certificate499 H MomentCertificates.Batch012.valid249.1 GeometryCertificates.Batch024.valid499 GeometryCertificates.Batch024.sound499 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound249 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound249 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate249 GeometryCertificates.Batch024.certificate498 numericValid249
    MomentCertificates.Batch012.valid249 DegreeCertificates.Batch012.valid249 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate249,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate250 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate250,DegreeCertificates.Batch012.certificate250,(WitnessCertificates.Batch025.certificate500).beta,(WitnessCertificates.Batch025.certificate501).L,none,(CutFailureCertificates.Budget025.certificate500).bound,(CutFailureCertificates.Budget025.certificate501).bound,0⟩
theorem numericValid250 : certificate250.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound250 : certificate250.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch025.certificate500 H MomentCertificates.Batch012.valid250.1 GeometryCertificates.Batch025.valid500 GeometryCertificates.Batch025.sound500 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch025.certificate501 H MomentCertificates.Batch012.valid250.1 GeometryCertificates.Batch025.valid501 GeometryCertificates.Batch025.sound501 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound250 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound250 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate250 GeometryCertificates.Batch025.certificate500 numericValid250
    MomentCertificates.Batch012.valid250 DegreeCertificates.Batch012.valid250 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate250,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate251 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate251,DegreeCertificates.Batch012.certificate251,(WitnessCertificates.Batch025.certificate502).beta,(WitnessCertificates.Batch025.certificate503).L,none,(CutFailureCertificates.Budget025.certificate502).bound,(CutFailureCertificates.Budget025.certificate503).bound,0⟩
theorem numericValid251 : certificate251.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound251 : certificate251.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch025.certificate502 H MomentCertificates.Batch012.valid251.1 GeometryCertificates.Batch025.valid502 GeometryCertificates.Batch025.sound502 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch025.certificate503 H MomentCertificates.Batch012.valid251.1 GeometryCertificates.Batch025.valid503 GeometryCertificates.Batch025.sound503 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound251 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound251 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate251 GeometryCertificates.Batch025.certificate502 numericValid251
    MomentCertificates.Batch012.valid251 DegreeCertificates.Batch012.valid251 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate251,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate252 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate252,DegreeCertificates.Batch012.certificate252,(WitnessCertificates.Batch025.certificate504).beta,(WitnessCertificates.Batch025.certificate505).L,none,(CutFailureCertificates.Budget025.certificate504).bound,(CutFailureCertificates.Budget025.certificate505).bound,0⟩
theorem numericValid252 : certificate252.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound252 : certificate252.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch025.certificate504 H MomentCertificates.Batch012.valid252.1 GeometryCertificates.Batch025.valid504 GeometryCertificates.Batch025.sound504 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch025.certificate505 H MomentCertificates.Batch012.valid252.1 GeometryCertificates.Batch025.valid505 GeometryCertificates.Batch025.sound505 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound252 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound252 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate252 GeometryCertificates.Batch025.certificate504 numericValid252
    MomentCertificates.Batch012.valid252 DegreeCertificates.Batch012.valid252 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate252,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate253 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate253,DegreeCertificates.Batch012.certificate253,(WitnessCertificates.Batch025.certificate506).beta,(WitnessCertificates.Batch025.certificate507).L,none,(CutFailureCertificates.Budget025.certificate506).bound,(CutFailureCertificates.Budget025.certificate507).bound,0⟩
theorem numericValid253 : certificate253.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound253 : certificate253.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch025.certificate506 H MomentCertificates.Batch012.valid253.1 GeometryCertificates.Batch025.valid506 GeometryCertificates.Batch025.sound506 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch025.certificate507 H MomentCertificates.Batch012.valid253.1 GeometryCertificates.Batch025.valid507 GeometryCertificates.Batch025.sound507 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound253 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound253 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate253 GeometryCertificates.Batch025.certificate506 numericValid253
    MomentCertificates.Batch012.valid253 DegreeCertificates.Batch012.valid253 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate253,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate254 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate254,DegreeCertificates.Batch012.certificate254,(WitnessCertificates.Batch025.certificate508).beta,(WitnessCertificates.Batch025.certificate509).L,none,(CutFailureCertificates.Budget025.certificate508).bound,(CutFailureCertificates.Budget025.certificate509).bound,0⟩
theorem numericValid254 : certificate254.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound254 : certificate254.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch025.certificate508 H MomentCertificates.Batch012.valid254.1 GeometryCertificates.Batch025.valid508 GeometryCertificates.Batch025.sound508 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch025.certificate509 H MomentCertificates.Batch012.valid254.1 GeometryCertificates.Batch025.valid509 GeometryCertificates.Batch025.sound509 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound254 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound254 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate254 GeometryCertificates.Batch025.certificate508 numericValid254
    MomentCertificates.Batch012.valid254 DegreeCertificates.Batch012.valid254 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate254,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate255 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate255,DegreeCertificates.Batch012.certificate255,(WitnessCertificates.Batch025.certificate510).beta,(WitnessCertificates.Batch025.certificate511).L,none,(CutFailureCertificates.Budget025.certificate510).bound,(CutFailureCertificates.Budget025.certificate511).bound,0⟩
theorem numericValid255 : certificate255.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound255 : certificate255.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch025.certificate510 H MomentCertificates.Batch012.valid255.1 GeometryCertificates.Batch025.valid510 GeometryCertificates.Batch025.sound510 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch025.certificate511 H MomentCertificates.Batch012.valid255.1 GeometryCertificates.Batch025.valid511 GeometryCertificates.Batch025.sound511 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound255 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound255 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate255 GeometryCertificates.Batch025.certificate510 numericValid255
    MomentCertificates.Batch012.valid255 DegreeCertificates.Batch012.valid255 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate255,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate256 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate256,DegreeCertificates.Batch012.certificate256,(WitnessCertificates.Batch025.certificate512).beta,(WitnessCertificates.Batch025.certificate513).L,none,(CutFailureCertificates.Budget025.certificate512).bound,(CutFailureCertificates.Budget025.certificate513).bound,0⟩
theorem numericValid256 : certificate256.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound256 : certificate256.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch025.certificate512 H MomentCertificates.Batch012.valid256.1 GeometryCertificates.Batch025.valid512 GeometryCertificates.Batch025.sound512 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch025.certificate513 H MomentCertificates.Batch012.valid256.1 GeometryCertificates.Batch025.valid513 GeometryCertificates.Batch025.sound513 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound256 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound256 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate256 GeometryCertificates.Batch025.certificate512 numericValid256
    MomentCertificates.Batch012.valid256 DegreeCertificates.Batch012.valid256 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate256,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate257 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate257,DegreeCertificates.Batch012.certificate257,(WitnessCertificates.Batch025.certificate514).beta,(WitnessCertificates.Batch025.certificate515).L,none,(CutFailureCertificates.Budget025.certificate514).bound,(CutFailureCertificates.Budget025.certificate515).bound,0⟩
theorem numericValid257 : certificate257.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound257 : certificate257.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch025.certificate514 H MomentCertificates.Batch012.valid257.1 GeometryCertificates.Batch025.valid514 GeometryCertificates.Batch025.sound514 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch025.certificate515 H MomentCertificates.Batch012.valid257.1 GeometryCertificates.Batch025.valid515 GeometryCertificates.Batch025.sound515 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound257 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound257 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate257 GeometryCertificates.Batch025.certificate514 numericValid257
    MomentCertificates.Batch012.valid257 DegreeCertificates.Batch012.valid257 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate257,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate258 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate258,DegreeCertificates.Batch012.certificate258,(WitnessCertificates.Batch025.certificate516).beta,(WitnessCertificates.Batch025.certificate517).L,none,(CutFailureCertificates.Budget025.certificate516).bound,(CutFailureCertificates.Budget025.certificate517).bound,0⟩
theorem numericValid258 : certificate258.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound258 : certificate258.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch025.certificate516 H MomentCertificates.Batch012.valid258.1 GeometryCertificates.Batch025.valid516 GeometryCertificates.Batch025.sound516 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch025.certificate517 H MomentCertificates.Batch012.valid258.1 GeometryCertificates.Batch025.valid517 GeometryCertificates.Batch025.sound517 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound258 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound258 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate258 GeometryCertificates.Batch025.certificate516 numericValid258
    MomentCertificates.Batch012.valid258 DegreeCertificates.Batch012.valid258 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate258,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate259 : RatSamplerCase := ⟨MomentCertificates.Batch012.certificate259,DegreeCertificates.Batch012.certificate259,(WitnessCertificates.Batch025.certificate518).beta,(WitnessCertificates.Batch025.certificate519).L,none,(CutFailureCertificates.Budget025.certificate518).bound,(CutFailureCertificates.Budget025.certificate519).bound,0⟩
theorem numericValid259 : certificate259.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound259 : certificate259.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch025.certificate518 H MomentCertificates.Batch012.valid259.1 GeometryCertificates.Batch025.valid518 GeometryCertificates.Batch025.sound518 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch025.certificate519 H MomentCertificates.Batch012.valid259.1 GeometryCertificates.Batch025.valid519 GeometryCertificates.Batch025.sound519 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch012.probabilityBound259 H st hI
  have hanchor := CertifiedAnchorFailures.Batch012.probabilityBound259 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate259 GeometryCertificates.Batch025.certificate518 numericValid259
    MomentCertificates.Batch012.valid259 DegreeCertificates.Batch012.valid259 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate259,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate240,certificate241,certificate242,certificate243,certificate244,certificate245,certificate246,certificate247,certificate248,certificate249,certificate250,certificate251,certificate252,certificate253,certificate254,certificate255,certificate256,certificate257,certificate258,certificate259]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound240,List.forall_mem_cons.mpr ⟨sound241,List.forall_mem_cons.mpr ⟨sound242,List.forall_mem_cons.mpr ⟨sound243,List.forall_mem_cons.mpr ⟨sound244,List.forall_mem_cons.mpr ⟨sound245,List.forall_mem_cons.mpr ⟨sound246,List.forall_mem_cons.mpr ⟨sound247,List.forall_mem_cons.mpr ⟨sound248,List.forall_mem_cons.mpr ⟨sound249,List.forall_mem_cons.mpr ⟨sound250,List.forall_mem_cons.mpr ⟨sound251,List.forall_mem_cons.mpr ⟨sound252,List.forall_mem_cons.mpr ⟨sound253,List.forall_mem_cons.mpr ⟨sound254,List.forall_mem_cons.mpr ⟨sound255,List.forall_mem_cons.mpr ⟨sound256,List.forall_mem_cons.mpr ⟨sound257,List.forall_mem_cons.mpr ⟨sound258,List.forall_mem_cons.mpr ⟨sound259,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch012
