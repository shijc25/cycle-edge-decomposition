import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch008
import Cycle12.CertifiedGlobalFailures.Batch008
import Cycle12.CutFailureCertificates.Budget016
import Cycle12.CutFailureCertificates.Budget017
import Cycle12.DegreeCertificates.Batch008
import Cycle12.GeometryCertificates.Batch016
import Cycle12.GeometryCertificates.Batch017
import Cycle12.MomentCertificates.Batch008
import Cycle12.WitnessCertificates.Batch016
import Cycle12.WitnessCertificates.Batch017

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch008
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate160 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate160,DegreeCertificates.Batch008.certificate160,(WitnessCertificates.Batch016.certificate320).beta,(WitnessCertificates.Batch016.certificate321).L,none,(CutFailureCertificates.Budget016.certificate320).bound,(CutFailureCertificates.Budget016.certificate321).bound,0⟩
theorem numericValid160 : certificate160.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound160 : certificate160.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch016.certificate320 H MomentCertificates.Batch008.valid160.1 GeometryCertificates.Batch016.valid320 GeometryCertificates.Batch016.sound320 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch016.certificate321 H MomentCertificates.Batch008.valid160.1 GeometryCertificates.Batch016.valid321 GeometryCertificates.Batch016.sound321 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound160 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound160 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate160 GeometryCertificates.Batch016.certificate320 numericValid160
    MomentCertificates.Batch008.valid160 DegreeCertificates.Batch008.valid160 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate160,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate161 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate161,DegreeCertificates.Batch008.certificate161,(WitnessCertificates.Batch016.certificate322).beta,(WitnessCertificates.Batch016.certificate323).L,none,(CutFailureCertificates.Budget016.certificate322).bound,(CutFailureCertificates.Budget016.certificate323).bound,0⟩
theorem numericValid161 : certificate161.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound161 : certificate161.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch016.certificate322 H MomentCertificates.Batch008.valid161.1 GeometryCertificates.Batch016.valid322 GeometryCertificates.Batch016.sound322 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch016.certificate323 H MomentCertificates.Batch008.valid161.1 GeometryCertificates.Batch016.valid323 GeometryCertificates.Batch016.sound323 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound161 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound161 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate161 GeometryCertificates.Batch016.certificate322 numericValid161
    MomentCertificates.Batch008.valid161 DegreeCertificates.Batch008.valid161 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate161,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate162 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate162,DegreeCertificates.Batch008.certificate162,(WitnessCertificates.Batch016.certificate324).beta,(WitnessCertificates.Batch016.certificate325).L,none,(CutFailureCertificates.Budget016.certificate324).bound,(CutFailureCertificates.Budget016.certificate325).bound,0⟩
theorem numericValid162 : certificate162.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound162 : certificate162.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch016.certificate324 H MomentCertificates.Batch008.valid162.1 GeometryCertificates.Batch016.valid324 GeometryCertificates.Batch016.sound324 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch016.certificate325 H MomentCertificates.Batch008.valid162.1 GeometryCertificates.Batch016.valid325 GeometryCertificates.Batch016.sound325 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound162 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound162 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate162 GeometryCertificates.Batch016.certificate324 numericValid162
    MomentCertificates.Batch008.valid162 DegreeCertificates.Batch008.valid162 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate162,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate163 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate163,DegreeCertificates.Batch008.certificate163,(WitnessCertificates.Batch016.certificate326).beta,(WitnessCertificates.Batch016.certificate327).L,none,(CutFailureCertificates.Budget016.certificate326).bound,(CutFailureCertificates.Budget016.certificate327).bound,0⟩
theorem numericValid163 : certificate163.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound163 : certificate163.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch016.certificate326 H MomentCertificates.Batch008.valid163.1 GeometryCertificates.Batch016.valid326 GeometryCertificates.Batch016.sound326 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch016.certificate327 H MomentCertificates.Batch008.valid163.1 GeometryCertificates.Batch016.valid327 GeometryCertificates.Batch016.sound327 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound163 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound163 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate163 GeometryCertificates.Batch016.certificate326 numericValid163
    MomentCertificates.Batch008.valid163 DegreeCertificates.Batch008.valid163 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate163,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate164 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate164,DegreeCertificates.Batch008.certificate164,(WitnessCertificates.Batch016.certificate328).beta,(WitnessCertificates.Batch016.certificate329).L,none,(CutFailureCertificates.Budget016.certificate328).bound,(CutFailureCertificates.Budget016.certificate329).bound,0⟩
theorem numericValid164 : certificate164.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound164 : certificate164.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch016.certificate328 H MomentCertificates.Batch008.valid164.1 GeometryCertificates.Batch016.valid328 GeometryCertificates.Batch016.sound328 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch016.certificate329 H MomentCertificates.Batch008.valid164.1 GeometryCertificates.Batch016.valid329 GeometryCertificates.Batch016.sound329 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound164 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound164 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate164 GeometryCertificates.Batch016.certificate328 numericValid164
    MomentCertificates.Batch008.valid164 DegreeCertificates.Batch008.valid164 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate164,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate165 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate165,DegreeCertificates.Batch008.certificate165,(WitnessCertificates.Batch016.certificate330).beta,(WitnessCertificates.Batch016.certificate331).L,none,(CutFailureCertificates.Budget016.certificate330).bound,(CutFailureCertificates.Budget016.certificate331).bound,0⟩
theorem numericValid165 : certificate165.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound165 : certificate165.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch016.certificate330 H MomentCertificates.Batch008.valid165.1 GeometryCertificates.Batch016.valid330 GeometryCertificates.Batch016.sound330 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch016.certificate331 H MomentCertificates.Batch008.valid165.1 GeometryCertificates.Batch016.valid331 GeometryCertificates.Batch016.sound331 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound165 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound165 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate165 GeometryCertificates.Batch016.certificate330 numericValid165
    MomentCertificates.Batch008.valid165 DegreeCertificates.Batch008.valid165 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate165,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate166 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate166,DegreeCertificates.Batch008.certificate166,(WitnessCertificates.Batch016.certificate332).beta,(WitnessCertificates.Batch016.certificate333).L,none,(CutFailureCertificates.Budget016.certificate332).bound,(CutFailureCertificates.Budget016.certificate333).bound,0⟩
theorem numericValid166 : certificate166.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound166 : certificate166.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch016.certificate332 H MomentCertificates.Batch008.valid166.1 GeometryCertificates.Batch016.valid332 GeometryCertificates.Batch016.sound332 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch016.certificate333 H MomentCertificates.Batch008.valid166.1 GeometryCertificates.Batch016.valid333 GeometryCertificates.Batch016.sound333 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound166 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound166 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate166 GeometryCertificates.Batch016.certificate332 numericValid166
    MomentCertificates.Batch008.valid166 DegreeCertificates.Batch008.valid166 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate166,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate167 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate167,DegreeCertificates.Batch008.certificate167,(WitnessCertificates.Batch016.certificate334).beta,(WitnessCertificates.Batch016.certificate335).L,none,(CutFailureCertificates.Budget016.certificate334).bound,(CutFailureCertificates.Budget016.certificate335).bound,0⟩
theorem numericValid167 : certificate167.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound167 : certificate167.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch016.certificate334 H MomentCertificates.Batch008.valid167.1 GeometryCertificates.Batch016.valid334 GeometryCertificates.Batch016.sound334 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch016.certificate335 H MomentCertificates.Batch008.valid167.1 GeometryCertificates.Batch016.valid335 GeometryCertificates.Batch016.sound335 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound167 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound167 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate167 GeometryCertificates.Batch016.certificate334 numericValid167
    MomentCertificates.Batch008.valid167 DegreeCertificates.Batch008.valid167 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate167,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate168 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate168,DegreeCertificates.Batch008.certificate168,(WitnessCertificates.Batch016.certificate336).beta,(WitnessCertificates.Batch016.certificate337).L,none,(CutFailureCertificates.Budget016.certificate336).bound,(CutFailureCertificates.Budget016.certificate337).bound,0⟩
theorem numericValid168 : certificate168.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound168 : certificate168.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch016.certificate336 H MomentCertificates.Batch008.valid168.1 GeometryCertificates.Batch016.valid336 GeometryCertificates.Batch016.sound336 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch016.certificate337 H MomentCertificates.Batch008.valid168.1 GeometryCertificates.Batch016.valid337 GeometryCertificates.Batch016.sound337 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound168 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound168 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate168 GeometryCertificates.Batch016.certificate336 numericValid168
    MomentCertificates.Batch008.valid168 DegreeCertificates.Batch008.valid168 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate168,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate169 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate169,DegreeCertificates.Batch008.certificate169,(WitnessCertificates.Batch016.certificate338).beta,(WitnessCertificates.Batch016.certificate339).L,none,(CutFailureCertificates.Budget016.certificate338).bound,(CutFailureCertificates.Budget016.certificate339).bound,0⟩
theorem numericValid169 : certificate169.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound169 : certificate169.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch016.certificate338 H MomentCertificates.Batch008.valid169.1 GeometryCertificates.Batch016.valid338 GeometryCertificates.Batch016.sound338 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch016.certificate339 H MomentCertificates.Batch008.valid169.1 GeometryCertificates.Batch016.valid339 GeometryCertificates.Batch016.sound339 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound169 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound169 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate169 GeometryCertificates.Batch016.certificate338 numericValid169
    MomentCertificates.Batch008.valid169 DegreeCertificates.Batch008.valid169 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate169,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate170 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate170,DegreeCertificates.Batch008.certificate170,(WitnessCertificates.Batch017.certificate340).beta,(WitnessCertificates.Batch017.certificate341).L,none,(CutFailureCertificates.Budget017.certificate340).bound,(CutFailureCertificates.Budget017.certificate341).bound,0⟩
theorem numericValid170 : certificate170.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound170 : certificate170.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch017.certificate340 H MomentCertificates.Batch008.valid170.1 GeometryCertificates.Batch017.valid340 GeometryCertificates.Batch017.sound340 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch017.certificate341 H MomentCertificates.Batch008.valid170.1 GeometryCertificates.Batch017.valid341 GeometryCertificates.Batch017.sound341 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound170 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound170 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate170 GeometryCertificates.Batch017.certificate340 numericValid170
    MomentCertificates.Batch008.valid170 DegreeCertificates.Batch008.valid170 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate170,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate171 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate171,DegreeCertificates.Batch008.certificate171,(WitnessCertificates.Batch017.certificate342).beta,(WitnessCertificates.Batch017.certificate343).L,none,(CutFailureCertificates.Budget017.certificate342).bound,(CutFailureCertificates.Budget017.certificate343).bound,0⟩
theorem numericValid171 : certificate171.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound171 : certificate171.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch017.certificate342 H MomentCertificates.Batch008.valid171.1 GeometryCertificates.Batch017.valid342 GeometryCertificates.Batch017.sound342 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch017.certificate343 H MomentCertificates.Batch008.valid171.1 GeometryCertificates.Batch017.valid343 GeometryCertificates.Batch017.sound343 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound171 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound171 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate171 GeometryCertificates.Batch017.certificate342 numericValid171
    MomentCertificates.Batch008.valid171 DegreeCertificates.Batch008.valid171 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate171,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate172 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate172,DegreeCertificates.Batch008.certificate172,(WitnessCertificates.Batch017.certificate344).beta,(WitnessCertificates.Batch017.certificate345).L,none,(CutFailureCertificates.Budget017.certificate344).bound,(CutFailureCertificates.Budget017.certificate345).bound,0⟩
theorem numericValid172 : certificate172.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound172 : certificate172.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch017.certificate344 H MomentCertificates.Batch008.valid172.1 GeometryCertificates.Batch017.valid344 GeometryCertificates.Batch017.sound344 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch017.certificate345 H MomentCertificates.Batch008.valid172.1 GeometryCertificates.Batch017.valid345 GeometryCertificates.Batch017.sound345 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound172 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound172 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate172 GeometryCertificates.Batch017.certificate344 numericValid172
    MomentCertificates.Batch008.valid172 DegreeCertificates.Batch008.valid172 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate172,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate173 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate173,DegreeCertificates.Batch008.certificate173,(WitnessCertificates.Batch017.certificate346).beta,(WitnessCertificates.Batch017.certificate347).L,none,(CutFailureCertificates.Budget017.certificate346).bound,(CutFailureCertificates.Budget017.certificate347).bound,0⟩
theorem numericValid173 : certificate173.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound173 : certificate173.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch017.certificate346 H MomentCertificates.Batch008.valid173.1 GeometryCertificates.Batch017.valid346 GeometryCertificates.Batch017.sound346 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch017.certificate347 H MomentCertificates.Batch008.valid173.1 GeometryCertificates.Batch017.valid347 GeometryCertificates.Batch017.sound347 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound173 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound173 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate173 GeometryCertificates.Batch017.certificate346 numericValid173
    MomentCertificates.Batch008.valid173 DegreeCertificates.Batch008.valid173 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate173,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate174 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate174,DegreeCertificates.Batch008.certificate174,(WitnessCertificates.Batch017.certificate348).beta,(WitnessCertificates.Batch017.certificate349).L,none,(CutFailureCertificates.Budget017.certificate348).bound,(CutFailureCertificates.Budget017.certificate349).bound,0⟩
theorem numericValid174 : certificate174.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound174 : certificate174.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch017.certificate348 H MomentCertificates.Batch008.valid174.1 GeometryCertificates.Batch017.valid348 GeometryCertificates.Batch017.sound348 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch017.certificate349 H MomentCertificates.Batch008.valid174.1 GeometryCertificates.Batch017.valid349 GeometryCertificates.Batch017.sound349 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound174 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound174 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate174 GeometryCertificates.Batch017.certificate348 numericValid174
    MomentCertificates.Batch008.valid174 DegreeCertificates.Batch008.valid174 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate174,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate175 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate175,DegreeCertificates.Batch008.certificate175,(WitnessCertificates.Batch017.certificate350).beta,(WitnessCertificates.Batch017.certificate351).L,none,(CutFailureCertificates.Budget017.certificate350).bound,(CutFailureCertificates.Budget017.certificate351).bound,0⟩
theorem numericValid175 : certificate175.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound175 : certificate175.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch017.certificate350 H MomentCertificates.Batch008.valid175.1 GeometryCertificates.Batch017.valid350 GeometryCertificates.Batch017.sound350 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch017.certificate351 H MomentCertificates.Batch008.valid175.1 GeometryCertificates.Batch017.valid351 GeometryCertificates.Batch017.sound351 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound175 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound175 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate175 GeometryCertificates.Batch017.certificate350 numericValid175
    MomentCertificates.Batch008.valid175 DegreeCertificates.Batch008.valid175 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate175,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate176 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate176,DegreeCertificates.Batch008.certificate176,(WitnessCertificates.Batch017.certificate352).beta,(WitnessCertificates.Batch017.certificate353).L,none,(CutFailureCertificates.Budget017.certificate352).bound,(CutFailureCertificates.Budget017.certificate353).bound,0⟩
theorem numericValid176 : certificate176.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound176 : certificate176.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch017.certificate352 H MomentCertificates.Batch008.valid176.1 GeometryCertificates.Batch017.valid352 GeometryCertificates.Batch017.sound352 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch017.certificate353 H MomentCertificates.Batch008.valid176.1 GeometryCertificates.Batch017.valid353 GeometryCertificates.Batch017.sound353 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound176 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound176 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate176 GeometryCertificates.Batch017.certificate352 numericValid176
    MomentCertificates.Batch008.valid176 DegreeCertificates.Batch008.valid176 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate176,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate177 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate177,DegreeCertificates.Batch008.certificate177,(WitnessCertificates.Batch017.certificate354).beta,(WitnessCertificates.Batch017.certificate355).L,none,(CutFailureCertificates.Budget017.certificate354).bound,(CutFailureCertificates.Budget017.certificate355).bound,0⟩
theorem numericValid177 : certificate177.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound177 : certificate177.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch017.certificate354 H MomentCertificates.Batch008.valid177.1 GeometryCertificates.Batch017.valid354 GeometryCertificates.Batch017.sound354 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch017.certificate355 H MomentCertificates.Batch008.valid177.1 GeometryCertificates.Batch017.valid355 GeometryCertificates.Batch017.sound355 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound177 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound177 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate177 GeometryCertificates.Batch017.certificate354 numericValid177
    MomentCertificates.Batch008.valid177 DegreeCertificates.Batch008.valid177 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate177,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate178 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate178,DegreeCertificates.Batch008.certificate178,(WitnessCertificates.Batch017.certificate356).beta,(WitnessCertificates.Batch017.certificate357).L,none,(CutFailureCertificates.Budget017.certificate356).bound,(CutFailureCertificates.Budget017.certificate357).bound,0⟩
theorem numericValid178 : certificate178.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound178 : certificate178.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch017.certificate356 H MomentCertificates.Batch008.valid178.1 GeometryCertificates.Batch017.valid356 GeometryCertificates.Batch017.sound356 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch017.certificate357 H MomentCertificates.Batch008.valid178.1 GeometryCertificates.Batch017.valid357 GeometryCertificates.Batch017.sound357 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound178 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound178 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate178 GeometryCertificates.Batch017.certificate356 numericValid178
    MomentCertificates.Batch008.valid178 DegreeCertificates.Batch008.valid178 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate178,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate179 : RatSamplerCase := ⟨MomentCertificates.Batch008.certificate179,DegreeCertificates.Batch008.certificate179,(WitnessCertificates.Batch017.certificate358).beta,(WitnessCertificates.Batch017.certificate359).L,none,(CutFailureCertificates.Budget017.certificate358).bound,(CutFailureCertificates.Budget017.certificate359).bound,0⟩
theorem numericValid179 : certificate179.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound179 : certificate179.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch017.certificate358 H MomentCertificates.Batch008.valid179.1 GeometryCertificates.Batch017.valid358 GeometryCertificates.Batch017.sound358 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch017.certificate359 H MomentCertificates.Batch008.valid179.1 GeometryCertificates.Batch017.valid359 GeometryCertificates.Batch017.sound359 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch008.probabilityBound179 H st hI
  have hanchor := CertifiedAnchorFailures.Batch008.probabilityBound179 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate179 GeometryCertificates.Batch017.certificate358 numericValid179
    MomentCertificates.Batch008.valid179 DegreeCertificates.Batch008.valid179 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate179,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate160,certificate161,certificate162,certificate163,certificate164,certificate165,certificate166,certificate167,certificate168,certificate169,certificate170,certificate171,certificate172,certificate173,certificate174,certificate175,certificate176,certificate177,certificate178,certificate179]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound160,List.forall_mem_cons.mpr ⟨sound161,List.forall_mem_cons.mpr ⟨sound162,List.forall_mem_cons.mpr ⟨sound163,List.forall_mem_cons.mpr ⟨sound164,List.forall_mem_cons.mpr ⟨sound165,List.forall_mem_cons.mpr ⟨sound166,List.forall_mem_cons.mpr ⟨sound167,List.forall_mem_cons.mpr ⟨sound168,List.forall_mem_cons.mpr ⟨sound169,List.forall_mem_cons.mpr ⟨sound170,List.forall_mem_cons.mpr ⟨sound171,List.forall_mem_cons.mpr ⟨sound172,List.forall_mem_cons.mpr ⟨sound173,List.forall_mem_cons.mpr ⟨sound174,List.forall_mem_cons.mpr ⟨sound175,List.forall_mem_cons.mpr ⟨sound176,List.forall_mem_cons.mpr ⟨sound177,List.forall_mem_cons.mpr ⟨sound178,List.forall_mem_cons.mpr ⟨sound179,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch008
