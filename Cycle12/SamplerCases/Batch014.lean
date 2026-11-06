import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch014
import Cycle12.CertifiedGlobalFailures.Batch014
import Cycle12.CutFailureCertificates.Budget028
import Cycle12.CutFailureCertificates.Budget029
import Cycle12.DegreeCertificates.Batch014
import Cycle12.GeometryCertificates.Batch028
import Cycle12.GeometryCertificates.Batch029
import Cycle12.MomentCertificates.Batch014
import Cycle12.WitnessCertificates.Batch028
import Cycle12.WitnessCertificates.Batch029

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch014
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate280 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate280,DegreeCertificates.Batch014.certificate280,(WitnessCertificates.Batch028.certificate560).beta,(WitnessCertificates.Batch028.certificate561).L,none,(CutFailureCertificates.Budget028.certificate560).bound,(CutFailureCertificates.Budget028.certificate561).bound,0⟩
theorem numericValid280 : certificate280.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound280 : certificate280.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch028.certificate560 H MomentCertificates.Batch014.valid280.1 GeometryCertificates.Batch028.valid560 GeometryCertificates.Batch028.sound560 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch028.certificate561 H MomentCertificates.Batch014.valid280.1 GeometryCertificates.Batch028.valid561 GeometryCertificates.Batch028.sound561 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound280 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound280 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate280 GeometryCertificates.Batch028.certificate560 numericValid280
    MomentCertificates.Batch014.valid280 DegreeCertificates.Batch014.valid280 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate280,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate281 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate281,DegreeCertificates.Batch014.certificate281,(WitnessCertificates.Batch028.certificate562).beta,(WitnessCertificates.Batch028.certificate563).L,none,(CutFailureCertificates.Budget028.certificate562).bound,(CutFailureCertificates.Budget028.certificate563).bound,0⟩
theorem numericValid281 : certificate281.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound281 : certificate281.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch028.certificate562 H MomentCertificates.Batch014.valid281.1 GeometryCertificates.Batch028.valid562 GeometryCertificates.Batch028.sound562 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch028.certificate563 H MomentCertificates.Batch014.valid281.1 GeometryCertificates.Batch028.valid563 GeometryCertificates.Batch028.sound563 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound281 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound281 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate281 GeometryCertificates.Batch028.certificate562 numericValid281
    MomentCertificates.Batch014.valid281 DegreeCertificates.Batch014.valid281 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate281,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate282 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate282,DegreeCertificates.Batch014.certificate282,(WitnessCertificates.Batch028.certificate564).beta,(WitnessCertificates.Batch028.certificate565).L,none,(CutFailureCertificates.Budget028.certificate564).bound,(CutFailureCertificates.Budget028.certificate565).bound,0⟩
theorem numericValid282 : certificate282.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound282 : certificate282.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch028.certificate564 H MomentCertificates.Batch014.valid282.1 GeometryCertificates.Batch028.valid564 GeometryCertificates.Batch028.sound564 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch028.certificate565 H MomentCertificates.Batch014.valid282.1 GeometryCertificates.Batch028.valid565 GeometryCertificates.Batch028.sound565 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound282 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound282 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate282 GeometryCertificates.Batch028.certificate564 numericValid282
    MomentCertificates.Batch014.valid282 DegreeCertificates.Batch014.valid282 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate282,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate283 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate283,DegreeCertificates.Batch014.certificate283,(WitnessCertificates.Batch028.certificate566).beta,(WitnessCertificates.Batch028.certificate567).L,none,(CutFailureCertificates.Budget028.certificate566).bound,(CutFailureCertificates.Budget028.certificate567).bound,0⟩
theorem numericValid283 : certificate283.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound283 : certificate283.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch028.certificate566 H MomentCertificates.Batch014.valid283.1 GeometryCertificates.Batch028.valid566 GeometryCertificates.Batch028.sound566 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch028.certificate567 H MomentCertificates.Batch014.valid283.1 GeometryCertificates.Batch028.valid567 GeometryCertificates.Batch028.sound567 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound283 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound283 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate283 GeometryCertificates.Batch028.certificate566 numericValid283
    MomentCertificates.Batch014.valid283 DegreeCertificates.Batch014.valid283 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate283,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate284 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate284,DegreeCertificates.Batch014.certificate284,(WitnessCertificates.Batch028.certificate568).beta,(WitnessCertificates.Batch028.certificate569).L,none,(CutFailureCertificates.Budget028.certificate568).bound,(CutFailureCertificates.Budget028.certificate569).bound,0⟩
theorem numericValid284 : certificate284.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound284 : certificate284.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch028.certificate568 H MomentCertificates.Batch014.valid284.1 GeometryCertificates.Batch028.valid568 GeometryCertificates.Batch028.sound568 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch028.certificate569 H MomentCertificates.Batch014.valid284.1 GeometryCertificates.Batch028.valid569 GeometryCertificates.Batch028.sound569 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound284 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound284 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate284 GeometryCertificates.Batch028.certificate568 numericValid284
    MomentCertificates.Batch014.valid284 DegreeCertificates.Batch014.valid284 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate284,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate285 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate285,DegreeCertificates.Batch014.certificate285,(WitnessCertificates.Batch028.certificate570).beta,(WitnessCertificates.Batch028.certificate571).L,none,(CutFailureCertificates.Budget028.certificate570).bound,(CutFailureCertificates.Budget028.certificate571).bound,0⟩
theorem numericValid285 : certificate285.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound285 : certificate285.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch028.certificate570 H MomentCertificates.Batch014.valid285.1 GeometryCertificates.Batch028.valid570 GeometryCertificates.Batch028.sound570 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch028.certificate571 H MomentCertificates.Batch014.valid285.1 GeometryCertificates.Batch028.valid571 GeometryCertificates.Batch028.sound571 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound285 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound285 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate285 GeometryCertificates.Batch028.certificate570 numericValid285
    MomentCertificates.Batch014.valid285 DegreeCertificates.Batch014.valid285 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate285,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate286 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate286,DegreeCertificates.Batch014.certificate286,(WitnessCertificates.Batch028.certificate572).beta,(WitnessCertificates.Batch028.certificate573).L,none,(CutFailureCertificates.Budget028.certificate572).bound,(CutFailureCertificates.Budget028.certificate573).bound,0⟩
theorem numericValid286 : certificate286.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound286 : certificate286.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch028.certificate572 H MomentCertificates.Batch014.valid286.1 GeometryCertificates.Batch028.valid572 GeometryCertificates.Batch028.sound572 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch028.certificate573 H MomentCertificates.Batch014.valid286.1 GeometryCertificates.Batch028.valid573 GeometryCertificates.Batch028.sound573 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound286 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound286 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate286 GeometryCertificates.Batch028.certificate572 numericValid286
    MomentCertificates.Batch014.valid286 DegreeCertificates.Batch014.valid286 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate286,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate287 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate287,DegreeCertificates.Batch014.certificate287,(WitnessCertificates.Batch028.certificate574).beta,(WitnessCertificates.Batch028.certificate575).L,none,(CutFailureCertificates.Budget028.certificate574).bound,(CutFailureCertificates.Budget028.certificate575).bound,0⟩
theorem numericValid287 : certificate287.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound287 : certificate287.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch028.certificate574 H MomentCertificates.Batch014.valid287.1 GeometryCertificates.Batch028.valid574 GeometryCertificates.Batch028.sound574 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch028.certificate575 H MomentCertificates.Batch014.valid287.1 GeometryCertificates.Batch028.valid575 GeometryCertificates.Batch028.sound575 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound287 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound287 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate287 GeometryCertificates.Batch028.certificate574 numericValid287
    MomentCertificates.Batch014.valid287 DegreeCertificates.Batch014.valid287 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate287,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate288 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate288,DegreeCertificates.Batch014.certificate288,(WitnessCertificates.Batch028.certificate576).beta,(WitnessCertificates.Batch028.certificate577).L,none,(CutFailureCertificates.Budget028.certificate576).bound,(CutFailureCertificates.Budget028.certificate577).bound,0⟩
theorem numericValid288 : certificate288.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound288 : certificate288.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch028.certificate576 H MomentCertificates.Batch014.valid288.1 GeometryCertificates.Batch028.valid576 GeometryCertificates.Batch028.sound576 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch028.certificate577 H MomentCertificates.Batch014.valid288.1 GeometryCertificates.Batch028.valid577 GeometryCertificates.Batch028.sound577 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound288 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound288 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate288 GeometryCertificates.Batch028.certificate576 numericValid288
    MomentCertificates.Batch014.valid288 DegreeCertificates.Batch014.valid288 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate288,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate289 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate289,DegreeCertificates.Batch014.certificate289,(WitnessCertificates.Batch028.certificate578).beta,(WitnessCertificates.Batch028.certificate579).L,none,(CutFailureCertificates.Budget028.certificate578).bound,(CutFailureCertificates.Budget028.certificate579).bound,0⟩
theorem numericValid289 : certificate289.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound289 : certificate289.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch028.certificate578 H MomentCertificates.Batch014.valid289.1 GeometryCertificates.Batch028.valid578 GeometryCertificates.Batch028.sound578 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch028.certificate579 H MomentCertificates.Batch014.valid289.1 GeometryCertificates.Batch028.valid579 GeometryCertificates.Batch028.sound579 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound289 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound289 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate289 GeometryCertificates.Batch028.certificate578 numericValid289
    MomentCertificates.Batch014.valid289 DegreeCertificates.Batch014.valid289 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate289,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate290 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate290,DegreeCertificates.Batch014.certificate290,(WitnessCertificates.Batch029.certificate580).beta,(WitnessCertificates.Batch029.certificate581).L,none,(CutFailureCertificates.Budget029.certificate580).bound,(CutFailureCertificates.Budget029.certificate581).bound,0⟩
theorem numericValid290 : certificate290.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound290 : certificate290.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch029.certificate580 H MomentCertificates.Batch014.valid290.1 GeometryCertificates.Batch029.valid580 GeometryCertificates.Batch029.sound580 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch029.certificate581 H MomentCertificates.Batch014.valid290.1 GeometryCertificates.Batch029.valid581 GeometryCertificates.Batch029.sound581 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound290 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound290 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate290 GeometryCertificates.Batch029.certificate580 numericValid290
    MomentCertificates.Batch014.valid290 DegreeCertificates.Batch014.valid290 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate290,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate291 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate291,DegreeCertificates.Batch014.certificate291,(WitnessCertificates.Batch029.certificate582).beta,(WitnessCertificates.Batch029.certificate583).L,none,(CutFailureCertificates.Budget029.certificate582).bound,(CutFailureCertificates.Budget029.certificate583).bound,0⟩
theorem numericValid291 : certificate291.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound291 : certificate291.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch029.certificate582 H MomentCertificates.Batch014.valid291.1 GeometryCertificates.Batch029.valid582 GeometryCertificates.Batch029.sound582 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch029.certificate583 H MomentCertificates.Batch014.valid291.1 GeometryCertificates.Batch029.valid583 GeometryCertificates.Batch029.sound583 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound291 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound291 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate291 GeometryCertificates.Batch029.certificate582 numericValid291
    MomentCertificates.Batch014.valid291 DegreeCertificates.Batch014.valid291 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate291,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate292 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate292,DegreeCertificates.Batch014.certificate292,(WitnessCertificates.Batch029.certificate584).beta,(WitnessCertificates.Batch029.certificate585).L,none,(CutFailureCertificates.Budget029.certificate584).bound,(CutFailureCertificates.Budget029.certificate585).bound,0⟩
theorem numericValid292 : certificate292.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound292 : certificate292.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch029.certificate584 H MomentCertificates.Batch014.valid292.1 GeometryCertificates.Batch029.valid584 GeometryCertificates.Batch029.sound584 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch029.certificate585 H MomentCertificates.Batch014.valid292.1 GeometryCertificates.Batch029.valid585 GeometryCertificates.Batch029.sound585 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound292 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound292 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate292 GeometryCertificates.Batch029.certificate584 numericValid292
    MomentCertificates.Batch014.valid292 DegreeCertificates.Batch014.valid292 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate292,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate293 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate293,DegreeCertificates.Batch014.certificate293,(WitnessCertificates.Batch029.certificate586).beta,(WitnessCertificates.Batch029.certificate587).L,none,(CutFailureCertificates.Budget029.certificate586).bound,(CutFailureCertificates.Budget029.certificate587).bound,0⟩
theorem numericValid293 : certificate293.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound293 : certificate293.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch029.certificate586 H MomentCertificates.Batch014.valid293.1 GeometryCertificates.Batch029.valid586 GeometryCertificates.Batch029.sound586 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch029.certificate587 H MomentCertificates.Batch014.valid293.1 GeometryCertificates.Batch029.valid587 GeometryCertificates.Batch029.sound587 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound293 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound293 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate293 GeometryCertificates.Batch029.certificate586 numericValid293
    MomentCertificates.Batch014.valid293 DegreeCertificates.Batch014.valid293 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate293,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate294 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate294,DegreeCertificates.Batch014.certificate294,(WitnessCertificates.Batch029.certificate588).beta,(WitnessCertificates.Batch029.certificate589).L,none,(CutFailureCertificates.Budget029.certificate588).bound,(CutFailureCertificates.Budget029.certificate589).bound,0⟩
theorem numericValid294 : certificate294.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound294 : certificate294.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch029.certificate588 H MomentCertificates.Batch014.valid294.1 GeometryCertificates.Batch029.valid588 GeometryCertificates.Batch029.sound588 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch029.certificate589 H MomentCertificates.Batch014.valid294.1 GeometryCertificates.Batch029.valid589 GeometryCertificates.Batch029.sound589 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound294 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound294 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate294 GeometryCertificates.Batch029.certificate588 numericValid294
    MomentCertificates.Batch014.valid294 DegreeCertificates.Batch014.valid294 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate294,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate295 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate295,DegreeCertificates.Batch014.certificate295,(WitnessCertificates.Batch029.certificate590).beta,(WitnessCertificates.Batch029.certificate591).L,none,(CutFailureCertificates.Budget029.certificate590).bound,(CutFailureCertificates.Budget029.certificate591).bound,0⟩
theorem numericValid295 : certificate295.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound295 : certificate295.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch029.certificate590 H MomentCertificates.Batch014.valid295.1 GeometryCertificates.Batch029.valid590 GeometryCertificates.Batch029.sound590 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch029.certificate591 H MomentCertificates.Batch014.valid295.1 GeometryCertificates.Batch029.valid591 GeometryCertificates.Batch029.sound591 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound295 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound295 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate295 GeometryCertificates.Batch029.certificate590 numericValid295
    MomentCertificates.Batch014.valid295 DegreeCertificates.Batch014.valid295 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate295,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate296 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate296,DegreeCertificates.Batch014.certificate296,(WitnessCertificates.Batch029.certificate592).beta,(WitnessCertificates.Batch029.certificate593).L,none,(CutFailureCertificates.Budget029.certificate592).bound,(CutFailureCertificates.Budget029.certificate593).bound,0⟩
theorem numericValid296 : certificate296.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound296 : certificate296.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch029.certificate592 H MomentCertificates.Batch014.valid296.1 GeometryCertificates.Batch029.valid592 GeometryCertificates.Batch029.sound592 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch029.certificate593 H MomentCertificates.Batch014.valid296.1 GeometryCertificates.Batch029.valid593 GeometryCertificates.Batch029.sound593 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound296 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound296 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate296 GeometryCertificates.Batch029.certificate592 numericValid296
    MomentCertificates.Batch014.valid296 DegreeCertificates.Batch014.valid296 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate296,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate297 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate297,DegreeCertificates.Batch014.certificate297,(WitnessCertificates.Batch029.certificate594).beta,(WitnessCertificates.Batch029.certificate595).L,none,(CutFailureCertificates.Budget029.certificate594).bound,(CutFailureCertificates.Budget029.certificate595).bound,0⟩
theorem numericValid297 : certificate297.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound297 : certificate297.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch029.certificate594 H MomentCertificates.Batch014.valid297.1 GeometryCertificates.Batch029.valid594 GeometryCertificates.Batch029.sound594 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch029.certificate595 H MomentCertificates.Batch014.valid297.1 GeometryCertificates.Batch029.valid595 GeometryCertificates.Batch029.sound595 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound297 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound297 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate297 GeometryCertificates.Batch029.certificate594 numericValid297
    MomentCertificates.Batch014.valid297 DegreeCertificates.Batch014.valid297 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate297,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate298 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate298,DegreeCertificates.Batch014.certificate298,(WitnessCertificates.Batch029.certificate596).beta,(WitnessCertificates.Batch029.certificate597).L,none,(CutFailureCertificates.Budget029.certificate596).bound,(CutFailureCertificates.Budget029.certificate597).bound,0⟩
theorem numericValid298 : certificate298.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound298 : certificate298.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch029.certificate596 H MomentCertificates.Batch014.valid298.1 GeometryCertificates.Batch029.valid596 GeometryCertificates.Batch029.sound596 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch029.certificate597 H MomentCertificates.Batch014.valid298.1 GeometryCertificates.Batch029.valid597 GeometryCertificates.Batch029.sound597 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound298 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound298 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate298 GeometryCertificates.Batch029.certificate596 numericValid298
    MomentCertificates.Batch014.valid298 DegreeCertificates.Batch014.valid298 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate298,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate299 : RatSamplerCase := ⟨MomentCertificates.Batch014.certificate299,DegreeCertificates.Batch014.certificate299,(WitnessCertificates.Batch029.certificate598).beta,(WitnessCertificates.Batch029.certificate599).L,none,(CutFailureCertificates.Budget029.certificate598).bound,(CutFailureCertificates.Budget029.certificate599).bound,0⟩
theorem numericValid299 : certificate299.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound299 : certificate299.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch029.certificate598 H MomentCertificates.Batch014.valid299.1 GeometryCertificates.Batch029.valid598 GeometryCertificates.Batch029.sound598 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch029.certificate599 H MomentCertificates.Batch014.valid299.1 GeometryCertificates.Batch029.valid599 GeometryCertificates.Batch029.sound599 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch014.probabilityBound299 H st hI
  have hanchor := CertifiedAnchorFailures.Batch014.probabilityBound299 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate299 GeometryCertificates.Batch029.certificate598 numericValid299
    MomentCertificates.Batch014.valid299 DegreeCertificates.Batch014.valid299 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate299,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate280,certificate281,certificate282,certificate283,certificate284,certificate285,certificate286,certificate287,certificate288,certificate289,certificate290,certificate291,certificate292,certificate293,certificate294,certificate295,certificate296,certificate297,certificate298,certificate299]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound280,List.forall_mem_cons.mpr ⟨sound281,List.forall_mem_cons.mpr ⟨sound282,List.forall_mem_cons.mpr ⟨sound283,List.forall_mem_cons.mpr ⟨sound284,List.forall_mem_cons.mpr ⟨sound285,List.forall_mem_cons.mpr ⟨sound286,List.forall_mem_cons.mpr ⟨sound287,List.forall_mem_cons.mpr ⟨sound288,List.forall_mem_cons.mpr ⟨sound289,List.forall_mem_cons.mpr ⟨sound290,List.forall_mem_cons.mpr ⟨sound291,List.forall_mem_cons.mpr ⟨sound292,List.forall_mem_cons.mpr ⟨sound293,List.forall_mem_cons.mpr ⟨sound294,List.forall_mem_cons.mpr ⟨sound295,List.forall_mem_cons.mpr ⟨sound296,List.forall_mem_cons.mpr ⟨sound297,List.forall_mem_cons.mpr ⟨sound298,List.forall_mem_cons.mpr ⟨sound299,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch014
