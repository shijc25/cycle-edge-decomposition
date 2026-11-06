import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch009
import Cycle12.CertifiedGlobalFailures.Batch009
import Cycle12.CutFailureCertificates.Budget018
import Cycle12.CutFailureCertificates.Budget019
import Cycle12.DegreeCertificates.Batch009
import Cycle12.GeometryCertificates.Batch018
import Cycle12.GeometryCertificates.Batch019
import Cycle12.MomentCertificates.Batch009
import Cycle12.WitnessCertificates.Batch018
import Cycle12.WitnessCertificates.Batch019

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch009
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate180 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate180,DegreeCertificates.Batch009.certificate180,(WitnessCertificates.Batch018.certificate360).beta,(WitnessCertificates.Batch018.certificate361).L,none,(CutFailureCertificates.Budget018.certificate360).bound,(CutFailureCertificates.Budget018.certificate361).bound,0⟩
theorem numericValid180 : certificate180.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound180 : certificate180.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch018.certificate360 H MomentCertificates.Batch009.valid180.1 GeometryCertificates.Batch018.valid360 GeometryCertificates.Batch018.sound360 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch018.certificate361 H MomentCertificates.Batch009.valid180.1 GeometryCertificates.Batch018.valid361 GeometryCertificates.Batch018.sound361 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound180 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound180 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate180 GeometryCertificates.Batch018.certificate360 numericValid180
    MomentCertificates.Batch009.valid180 DegreeCertificates.Batch009.valid180 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate180,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate181 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate181,DegreeCertificates.Batch009.certificate181,(WitnessCertificates.Batch018.certificate362).beta,(WitnessCertificates.Batch018.certificate363).L,none,(CutFailureCertificates.Budget018.certificate362).bound,(CutFailureCertificates.Budget018.certificate363).bound,0⟩
theorem numericValid181 : certificate181.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound181 : certificate181.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch018.certificate362 H MomentCertificates.Batch009.valid181.1 GeometryCertificates.Batch018.valid362 GeometryCertificates.Batch018.sound362 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch018.certificate363 H MomentCertificates.Batch009.valid181.1 GeometryCertificates.Batch018.valid363 GeometryCertificates.Batch018.sound363 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound181 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound181 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate181 GeometryCertificates.Batch018.certificate362 numericValid181
    MomentCertificates.Batch009.valid181 DegreeCertificates.Batch009.valid181 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate181,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate182 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate182,DegreeCertificates.Batch009.certificate182,(WitnessCertificates.Batch018.certificate364).beta,(WitnessCertificates.Batch018.certificate365).L,none,(CutFailureCertificates.Budget018.certificate364).bound,(CutFailureCertificates.Budget018.certificate365).bound,0⟩
theorem numericValid182 : certificate182.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound182 : certificate182.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch018.certificate364 H MomentCertificates.Batch009.valid182.1 GeometryCertificates.Batch018.valid364 GeometryCertificates.Batch018.sound364 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch018.certificate365 H MomentCertificates.Batch009.valid182.1 GeometryCertificates.Batch018.valid365 GeometryCertificates.Batch018.sound365 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound182 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound182 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate182 GeometryCertificates.Batch018.certificate364 numericValid182
    MomentCertificates.Batch009.valid182 DegreeCertificates.Batch009.valid182 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate182,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate183 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate183,DegreeCertificates.Batch009.certificate183,(WitnessCertificates.Batch018.certificate366).beta,(WitnessCertificates.Batch018.certificate367).L,none,(CutFailureCertificates.Budget018.certificate366).bound,(CutFailureCertificates.Budget018.certificate367).bound,0⟩
theorem numericValid183 : certificate183.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound183 : certificate183.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch018.certificate366 H MomentCertificates.Batch009.valid183.1 GeometryCertificates.Batch018.valid366 GeometryCertificates.Batch018.sound366 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch018.certificate367 H MomentCertificates.Batch009.valid183.1 GeometryCertificates.Batch018.valid367 GeometryCertificates.Batch018.sound367 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound183 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound183 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate183 GeometryCertificates.Batch018.certificate366 numericValid183
    MomentCertificates.Batch009.valid183 DegreeCertificates.Batch009.valid183 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate183,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate184 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate184,DegreeCertificates.Batch009.certificate184,(WitnessCertificates.Batch018.certificate368).beta,(WitnessCertificates.Batch018.certificate369).L,none,(CutFailureCertificates.Budget018.certificate368).bound,(CutFailureCertificates.Budget018.certificate369).bound,0⟩
theorem numericValid184 : certificate184.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound184 : certificate184.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch018.certificate368 H MomentCertificates.Batch009.valid184.1 GeometryCertificates.Batch018.valid368 GeometryCertificates.Batch018.sound368 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch018.certificate369 H MomentCertificates.Batch009.valid184.1 GeometryCertificates.Batch018.valid369 GeometryCertificates.Batch018.sound369 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound184 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound184 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate184 GeometryCertificates.Batch018.certificate368 numericValid184
    MomentCertificates.Batch009.valid184 DegreeCertificates.Batch009.valid184 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate184,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate185 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate185,DegreeCertificates.Batch009.certificate185,(WitnessCertificates.Batch018.certificate370).beta,(WitnessCertificates.Batch018.certificate371).L,none,(CutFailureCertificates.Budget018.certificate370).bound,(CutFailureCertificates.Budget018.certificate371).bound,0⟩
theorem numericValid185 : certificate185.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound185 : certificate185.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch018.certificate370 H MomentCertificates.Batch009.valid185.1 GeometryCertificates.Batch018.valid370 GeometryCertificates.Batch018.sound370 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch018.certificate371 H MomentCertificates.Batch009.valid185.1 GeometryCertificates.Batch018.valid371 GeometryCertificates.Batch018.sound371 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound185 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound185 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate185 GeometryCertificates.Batch018.certificate370 numericValid185
    MomentCertificates.Batch009.valid185 DegreeCertificates.Batch009.valid185 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate185,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate186 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate186,DegreeCertificates.Batch009.certificate186,(WitnessCertificates.Batch018.certificate372).beta,(WitnessCertificates.Batch018.certificate373).L,none,(CutFailureCertificates.Budget018.certificate372).bound,(CutFailureCertificates.Budget018.certificate373).bound,0⟩
theorem numericValid186 : certificate186.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound186 : certificate186.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch018.certificate372 H MomentCertificates.Batch009.valid186.1 GeometryCertificates.Batch018.valid372 GeometryCertificates.Batch018.sound372 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch018.certificate373 H MomentCertificates.Batch009.valid186.1 GeometryCertificates.Batch018.valid373 GeometryCertificates.Batch018.sound373 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound186 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound186 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate186 GeometryCertificates.Batch018.certificate372 numericValid186
    MomentCertificates.Batch009.valid186 DegreeCertificates.Batch009.valid186 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate186,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate187 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate187,DegreeCertificates.Batch009.certificate187,(WitnessCertificates.Batch018.certificate374).beta,(WitnessCertificates.Batch018.certificate375).L,none,(CutFailureCertificates.Budget018.certificate374).bound,(CutFailureCertificates.Budget018.certificate375).bound,0⟩
theorem numericValid187 : certificate187.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound187 : certificate187.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch018.certificate374 H MomentCertificates.Batch009.valid187.1 GeometryCertificates.Batch018.valid374 GeometryCertificates.Batch018.sound374 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch018.certificate375 H MomentCertificates.Batch009.valid187.1 GeometryCertificates.Batch018.valid375 GeometryCertificates.Batch018.sound375 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound187 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound187 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate187 GeometryCertificates.Batch018.certificate374 numericValid187
    MomentCertificates.Batch009.valid187 DegreeCertificates.Batch009.valid187 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate187,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate188 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate188,DegreeCertificates.Batch009.certificate188,(WitnessCertificates.Batch018.certificate376).beta,(WitnessCertificates.Batch018.certificate377).L,none,(CutFailureCertificates.Budget018.certificate376).bound,(CutFailureCertificates.Budget018.certificate377).bound,0⟩
theorem numericValid188 : certificate188.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound188 : certificate188.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch018.certificate376 H MomentCertificates.Batch009.valid188.1 GeometryCertificates.Batch018.valid376 GeometryCertificates.Batch018.sound376 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch018.certificate377 H MomentCertificates.Batch009.valid188.1 GeometryCertificates.Batch018.valid377 GeometryCertificates.Batch018.sound377 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound188 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound188 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate188 GeometryCertificates.Batch018.certificate376 numericValid188
    MomentCertificates.Batch009.valid188 DegreeCertificates.Batch009.valid188 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate188,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate189 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate189,DegreeCertificates.Batch009.certificate189,(WitnessCertificates.Batch018.certificate378).beta,(WitnessCertificates.Batch018.certificate379).L,none,(CutFailureCertificates.Budget018.certificate378).bound,(CutFailureCertificates.Budget018.certificate379).bound,0⟩
theorem numericValid189 : certificate189.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound189 : certificate189.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch018.certificate378 H MomentCertificates.Batch009.valid189.1 GeometryCertificates.Batch018.valid378 GeometryCertificates.Batch018.sound378 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch018.certificate379 H MomentCertificates.Batch009.valid189.1 GeometryCertificates.Batch018.valid379 GeometryCertificates.Batch018.sound379 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound189 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound189 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate189 GeometryCertificates.Batch018.certificate378 numericValid189
    MomentCertificates.Batch009.valid189 DegreeCertificates.Batch009.valid189 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate189,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate190 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate190,DegreeCertificates.Batch009.certificate190,(WitnessCertificates.Batch019.certificate380).beta,(WitnessCertificates.Batch019.certificate381).L,none,(CutFailureCertificates.Budget019.certificate380).bound,(CutFailureCertificates.Budget019.certificate381).bound,0⟩
theorem numericValid190 : certificate190.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound190 : certificate190.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch019.certificate380 H MomentCertificates.Batch009.valid190.1 GeometryCertificates.Batch019.valid380 GeometryCertificates.Batch019.sound380 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch019.certificate381 H MomentCertificates.Batch009.valid190.1 GeometryCertificates.Batch019.valid381 GeometryCertificates.Batch019.sound381 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound190 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound190 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate190 GeometryCertificates.Batch019.certificate380 numericValid190
    MomentCertificates.Batch009.valid190 DegreeCertificates.Batch009.valid190 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate190,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate191 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate191,DegreeCertificates.Batch009.certificate191,(WitnessCertificates.Batch019.certificate382).beta,(WitnessCertificates.Batch019.certificate383).L,none,(CutFailureCertificates.Budget019.certificate382).bound,(CutFailureCertificates.Budget019.certificate383).bound,0⟩
theorem numericValid191 : certificate191.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound191 : certificate191.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch019.certificate382 H MomentCertificates.Batch009.valid191.1 GeometryCertificates.Batch019.valid382 GeometryCertificates.Batch019.sound382 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch019.certificate383 H MomentCertificates.Batch009.valid191.1 GeometryCertificates.Batch019.valid383 GeometryCertificates.Batch019.sound383 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound191 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound191 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate191 GeometryCertificates.Batch019.certificate382 numericValid191
    MomentCertificates.Batch009.valid191 DegreeCertificates.Batch009.valid191 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate191,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate192 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate192,DegreeCertificates.Batch009.certificate192,(WitnessCertificates.Batch019.certificate384).beta,(WitnessCertificates.Batch019.certificate385).L,none,(CutFailureCertificates.Budget019.certificate384).bound,(CutFailureCertificates.Budget019.certificate385).bound,0⟩
theorem numericValid192 : certificate192.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound192 : certificate192.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch019.certificate384 H MomentCertificates.Batch009.valid192.1 GeometryCertificates.Batch019.valid384 GeometryCertificates.Batch019.sound384 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch019.certificate385 H MomentCertificates.Batch009.valid192.1 GeometryCertificates.Batch019.valid385 GeometryCertificates.Batch019.sound385 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound192 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound192 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate192 GeometryCertificates.Batch019.certificate384 numericValid192
    MomentCertificates.Batch009.valid192 DegreeCertificates.Batch009.valid192 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate192,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate193 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate193,DegreeCertificates.Batch009.certificate193,(WitnessCertificates.Batch019.certificate386).beta,(WitnessCertificates.Batch019.certificate387).L,none,(CutFailureCertificates.Budget019.certificate386).bound,(CutFailureCertificates.Budget019.certificate387).bound,0⟩
theorem numericValid193 : certificate193.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound193 : certificate193.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch019.certificate386 H MomentCertificates.Batch009.valid193.1 GeometryCertificates.Batch019.valid386 GeometryCertificates.Batch019.sound386 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch019.certificate387 H MomentCertificates.Batch009.valid193.1 GeometryCertificates.Batch019.valid387 GeometryCertificates.Batch019.sound387 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound193 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound193 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate193 GeometryCertificates.Batch019.certificate386 numericValid193
    MomentCertificates.Batch009.valid193 DegreeCertificates.Batch009.valid193 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate193,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate194 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate194,DegreeCertificates.Batch009.certificate194,(WitnessCertificates.Batch019.certificate388).beta,(WitnessCertificates.Batch019.certificate389).L,none,(CutFailureCertificates.Budget019.certificate388).bound,(CutFailureCertificates.Budget019.certificate389).bound,0⟩
theorem numericValid194 : certificate194.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound194 : certificate194.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch019.certificate388 H MomentCertificates.Batch009.valid194.1 GeometryCertificates.Batch019.valid388 GeometryCertificates.Batch019.sound388 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch019.certificate389 H MomentCertificates.Batch009.valid194.1 GeometryCertificates.Batch019.valid389 GeometryCertificates.Batch019.sound389 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound194 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound194 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate194 GeometryCertificates.Batch019.certificate388 numericValid194
    MomentCertificates.Batch009.valid194 DegreeCertificates.Batch009.valid194 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate194,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate195 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate195,DegreeCertificates.Batch009.certificate195,(WitnessCertificates.Batch019.certificate390).beta,(WitnessCertificates.Batch019.certificate391).L,none,(CutFailureCertificates.Budget019.certificate390).bound,(CutFailureCertificates.Budget019.certificate391).bound,0⟩
theorem numericValid195 : certificate195.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound195 : certificate195.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch019.certificate390 H MomentCertificates.Batch009.valid195.1 GeometryCertificates.Batch019.valid390 GeometryCertificates.Batch019.sound390 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch019.certificate391 H MomentCertificates.Batch009.valid195.1 GeometryCertificates.Batch019.valid391 GeometryCertificates.Batch019.sound391 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound195 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound195 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate195 GeometryCertificates.Batch019.certificate390 numericValid195
    MomentCertificates.Batch009.valid195 DegreeCertificates.Batch009.valid195 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate195,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate196 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate196,DegreeCertificates.Batch009.certificate196,(WitnessCertificates.Batch019.certificate392).beta,(WitnessCertificates.Batch019.certificate393).L,none,(CutFailureCertificates.Budget019.certificate392).bound,(CutFailureCertificates.Budget019.certificate393).bound,0⟩
theorem numericValid196 : certificate196.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound196 : certificate196.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch019.certificate392 H MomentCertificates.Batch009.valid196.1 GeometryCertificates.Batch019.valid392 GeometryCertificates.Batch019.sound392 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch019.certificate393 H MomentCertificates.Batch009.valid196.1 GeometryCertificates.Batch019.valid393 GeometryCertificates.Batch019.sound393 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound196 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound196 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate196 GeometryCertificates.Batch019.certificate392 numericValid196
    MomentCertificates.Batch009.valid196 DegreeCertificates.Batch009.valid196 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate196,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate197 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate197,DegreeCertificates.Batch009.certificate197,(WitnessCertificates.Batch019.certificate394).beta,(WitnessCertificates.Batch019.certificate395).L,none,(CutFailureCertificates.Budget019.certificate394).bound,(CutFailureCertificates.Budget019.certificate395).bound,0⟩
theorem numericValid197 : certificate197.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound197 : certificate197.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch019.certificate394 H MomentCertificates.Batch009.valid197.1 GeometryCertificates.Batch019.valid394 GeometryCertificates.Batch019.sound394 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch019.certificate395 H MomentCertificates.Batch009.valid197.1 GeometryCertificates.Batch019.valid395 GeometryCertificates.Batch019.sound395 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound197 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound197 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate197 GeometryCertificates.Batch019.certificate394 numericValid197
    MomentCertificates.Batch009.valid197 DegreeCertificates.Batch009.valid197 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate197,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate198 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate198,DegreeCertificates.Batch009.certificate198,(WitnessCertificates.Batch019.certificate396).beta,(WitnessCertificates.Batch019.certificate397).L,none,(CutFailureCertificates.Budget019.certificate396).bound,(CutFailureCertificates.Budget019.certificate397).bound,0⟩
theorem numericValid198 : certificate198.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound198 : certificate198.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch019.certificate396 H MomentCertificates.Batch009.valid198.1 GeometryCertificates.Batch019.valid396 GeometryCertificates.Batch019.sound396 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch019.certificate397 H MomentCertificates.Batch009.valid198.1 GeometryCertificates.Batch019.valid397 GeometryCertificates.Batch019.sound397 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound198 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound198 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate198 GeometryCertificates.Batch019.certificate396 numericValid198
    MomentCertificates.Batch009.valid198 DegreeCertificates.Batch009.valid198 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate198,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate199 : RatSamplerCase := ⟨MomentCertificates.Batch009.certificate199,DegreeCertificates.Batch009.certificate199,(WitnessCertificates.Batch019.certificate398).beta,(WitnessCertificates.Batch019.certificate399).L,none,(CutFailureCertificates.Budget019.certificate398).bound,(CutFailureCertificates.Budget019.certificate399).bound,0⟩
theorem numericValid199 : certificate199.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound199 : certificate199.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch019.certificate398 H MomentCertificates.Batch009.valid199.1 GeometryCertificates.Batch019.valid398 GeometryCertificates.Batch019.sound398 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch019.certificate399 H MomentCertificates.Batch009.valid199.1 GeometryCertificates.Batch019.valid399 GeometryCertificates.Batch019.sound399 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch009.probabilityBound199 H st hI
  have hanchor := CertifiedAnchorFailures.Batch009.probabilityBound199 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  have hextra : (fixedSizeLaw (univ:Finset V) st.N).prob (fun _ => False) ≤ (0:ℝ) := by simp [FiniteLaw.prob]
  have hgood := rat_sampler_case_good_from_cut_bounds certificate199 GeometryCertificates.Batch019.certificate398 numericValid199
    MomentCertificates.Batch009.valid199 DegreeCertificates.Batch009.valid199 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate199,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate180,certificate181,certificate182,certificate183,certificate184,certificate185,certificate186,certificate187,certificate188,certificate189,certificate190,certificate191,certificate192,certificate193,certificate194,certificate195,certificate196,certificate197,certificate198,certificate199]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound180,List.forall_mem_cons.mpr ⟨sound181,List.forall_mem_cons.mpr ⟨sound182,List.forall_mem_cons.mpr ⟨sound183,List.forall_mem_cons.mpr ⟨sound184,List.forall_mem_cons.mpr ⟨sound185,List.forall_mem_cons.mpr ⟨sound186,List.forall_mem_cons.mpr ⟨sound187,List.forall_mem_cons.mpr ⟨sound188,List.forall_mem_cons.mpr ⟨sound189,List.forall_mem_cons.mpr ⟨sound190,List.forall_mem_cons.mpr ⟨sound191,List.forall_mem_cons.mpr ⟨sound192,List.forall_mem_cons.mpr ⟨sound193,List.forall_mem_cons.mpr ⟨sound194,List.forall_mem_cons.mpr ⟨sound195,List.forall_mem_cons.mpr ⟨sound196,List.forall_mem_cons.mpr ⟨sound197,List.forall_mem_cons.mpr ⟨sound198,List.forall_mem_cons.mpr ⟨sound199,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch009
