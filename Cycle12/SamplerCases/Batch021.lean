import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch021
import Cycle12.CertifiedGlobalFailures.Batch021
import Cycle12.CertifiedLocalFailures.Batch000
import Cycle12.CertifiedLocalFailures.Batch001
import Cycle12.CutFailureCertificates.Budget042
import Cycle12.CutFailureCertificates.Budget043
import Cycle12.CutFailureCertificates.Budget044
import Cycle12.CutFailureCertificates.Budget045
import Cycle12.DegreeCertificates.Batch021
import Cycle12.GeometryCertificates.Batch042
import Cycle12.GeometryCertificates.Batch043
import Cycle12.GeometryCertificates.Batch044
import Cycle12.GeometryCertificates.Batch045
import Cycle12.MomentCertificates.Batch021
import Cycle12.WitnessCertificates.Batch042
import Cycle12.WitnessCertificates.Batch043
import Cycle12.WitnessCertificates.Batch044
import Cycle12.WitnessCertificates.Batch045

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch021
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate420 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate420,DegreeCertificates.Batch021.certificate420,(WitnessCertificates.Batch042.certificate845).beta,(WitnessCertificates.Batch042.certificate846).L,(some (WitnessCertificates.Batch042.certificate847).beta),(CutFailureCertificates.Budget042.certificate845).bound,(CutFailureCertificates.Budget042.certificate846).bound,(CutFailureCertificates.Budget042.certificate847).bound⟩
theorem numericValid420 : certificate420.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound420 : certificate420.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch042.certificate845 H MomentCertificates.Batch021.valid420.1 GeometryCertificates.Batch042.valid845 GeometryCertificates.Batch042.sound845 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch042.certificate846 H MomentCertificates.Batch021.valid420.1 GeometryCertificates.Batch042.valid846 GeometryCertificates.Batch042.sound846 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound420 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound420 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch042.certificate847 H MomentCertificates.Batch021.valid420.1 GeometryCertificates.Batch042.valid847 GeometryCertificates.Batch042.sound847 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound5 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch042.certificate847).dm = (DegreeCertificates.Batch021.certificate420).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate420 GeometryCertificates.Batch042.certificate845 numericValid420
    MomentCertificates.Batch021.valid420 DegreeCertificates.Batch021.valid420 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate420,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate421 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate421,DegreeCertificates.Batch021.certificate421,(WitnessCertificates.Batch042.certificate848).beta,(WitnessCertificates.Batch042.certificate849).L,(some (WitnessCertificates.Batch042.certificate850).beta),(CutFailureCertificates.Budget042.certificate848).bound,(CutFailureCertificates.Budget042.certificate849).bound,(CutFailureCertificates.Budget042.certificate850).bound⟩
theorem numericValid421 : certificate421.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound421 : certificate421.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch042.certificate848 H MomentCertificates.Batch021.valid421.1 GeometryCertificates.Batch042.valid848 GeometryCertificates.Batch042.sound848 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch042.certificate849 H MomentCertificates.Batch021.valid421.1 GeometryCertificates.Batch042.valid849 GeometryCertificates.Batch042.sound849 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound421 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound421 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch042.certificate850 H MomentCertificates.Batch021.valid421.1 GeometryCertificates.Batch042.valid850 GeometryCertificates.Batch042.sound850 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound6 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch042.certificate850).dm = (DegreeCertificates.Batch021.certificate421).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate421 GeometryCertificates.Batch042.certificate848 numericValid421
    MomentCertificates.Batch021.valid421 DegreeCertificates.Batch021.valid421 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate421,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate422 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate422,DegreeCertificates.Batch021.certificate422,(WitnessCertificates.Batch042.certificate851).beta,(WitnessCertificates.Batch042.certificate852).L,(some (WitnessCertificates.Batch042.certificate853).beta),(CutFailureCertificates.Budget042.certificate851).bound,(CutFailureCertificates.Budget042.certificate852).bound,(CutFailureCertificates.Budget042.certificate853).bound⟩
theorem numericValid422 : certificate422.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound422 : certificate422.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch042.certificate851 H MomentCertificates.Batch021.valid422.1 GeometryCertificates.Batch042.valid851 GeometryCertificates.Batch042.sound851 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch042.certificate852 H MomentCertificates.Batch021.valid422.1 GeometryCertificates.Batch042.valid852 GeometryCertificates.Batch042.sound852 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound422 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound422 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch042.certificate853 H MomentCertificates.Batch021.valid422.1 GeometryCertificates.Batch042.valid853 GeometryCertificates.Batch042.sound853 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound7 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch042.certificate853).dm = (DegreeCertificates.Batch021.certificate422).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate422 GeometryCertificates.Batch042.certificate851 numericValid422
    MomentCertificates.Batch021.valid422 DegreeCertificates.Batch021.valid422 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate422,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate423 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate423,DegreeCertificates.Batch021.certificate423,(WitnessCertificates.Batch042.certificate854).beta,(WitnessCertificates.Batch042.certificate855).L,(some (WitnessCertificates.Batch042.certificate856).beta),(CutFailureCertificates.Budget042.certificate854).bound,(CutFailureCertificates.Budget042.certificate855).bound,(CutFailureCertificates.Budget042.certificate856).bound⟩
theorem numericValid423 : certificate423.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound423 : certificate423.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch042.certificate854 H MomentCertificates.Batch021.valid423.1 GeometryCertificates.Batch042.valid854 GeometryCertificates.Batch042.sound854 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch042.certificate855 H MomentCertificates.Batch021.valid423.1 GeometryCertificates.Batch042.valid855 GeometryCertificates.Batch042.sound855 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound423 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound423 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch042.certificate856 H MomentCertificates.Batch021.valid423.1 GeometryCertificates.Batch042.valid856 GeometryCertificates.Batch042.sound856 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound8 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch042.certificate856).dm = (DegreeCertificates.Batch021.certificate423).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate423 GeometryCertificates.Batch042.certificate854 numericValid423
    MomentCertificates.Batch021.valid423 DegreeCertificates.Batch021.valid423 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate423,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate424 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate424,DegreeCertificates.Batch021.certificate424,(WitnessCertificates.Batch042.certificate857).beta,(WitnessCertificates.Batch042.certificate858).L,(some (WitnessCertificates.Batch042.certificate859).beta),(CutFailureCertificates.Budget042.certificate857).bound,(CutFailureCertificates.Budget042.certificate858).bound,(CutFailureCertificates.Budget042.certificate859).bound⟩
theorem numericValid424 : certificate424.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound424 : certificate424.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch042.certificate857 H MomentCertificates.Batch021.valid424.1 GeometryCertificates.Batch042.valid857 GeometryCertificates.Batch042.sound857 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch042.certificate858 H MomentCertificates.Batch021.valid424.1 GeometryCertificates.Batch042.valid858 GeometryCertificates.Batch042.sound858 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound424 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound424 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch042.certificate859 H MomentCertificates.Batch021.valid424.1 GeometryCertificates.Batch042.valid859 GeometryCertificates.Batch042.sound859 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound9 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch042.certificate859).dm = (DegreeCertificates.Batch021.certificate424).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate424 GeometryCertificates.Batch042.certificate857 numericValid424
    MomentCertificates.Batch021.valid424 DegreeCertificates.Batch021.valid424 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate424,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate425 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate425,DegreeCertificates.Batch021.certificate425,(WitnessCertificates.Batch043.certificate860).beta,(WitnessCertificates.Batch043.certificate861).L,(some (WitnessCertificates.Batch043.certificate862).beta),(CutFailureCertificates.Budget043.certificate860).bound,(CutFailureCertificates.Budget043.certificate861).bound,(CutFailureCertificates.Budget043.certificate862).bound⟩
theorem numericValid425 : certificate425.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound425 : certificate425.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch043.certificate860 H MomentCertificates.Batch021.valid425.1 GeometryCertificates.Batch043.valid860 GeometryCertificates.Batch043.sound860 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch043.certificate861 H MomentCertificates.Batch021.valid425.1 GeometryCertificates.Batch043.valid861 GeometryCertificates.Batch043.sound861 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound425 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound425 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch043.certificate862 H MomentCertificates.Batch021.valid425.1 GeometryCertificates.Batch043.valid862 GeometryCertificates.Batch043.sound862 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound10 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch043.certificate862).dm = (DegreeCertificates.Batch021.certificate425).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate425 GeometryCertificates.Batch043.certificate860 numericValid425
    MomentCertificates.Batch021.valid425 DegreeCertificates.Batch021.valid425 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate425,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate426 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate426,DegreeCertificates.Batch021.certificate426,(WitnessCertificates.Batch043.certificate863).beta,(WitnessCertificates.Batch043.certificate864).L,(some (WitnessCertificates.Batch043.certificate865).beta),(CutFailureCertificates.Budget043.certificate863).bound,(CutFailureCertificates.Budget043.certificate864).bound,(CutFailureCertificates.Budget043.certificate865).bound⟩
theorem numericValid426 : certificate426.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound426 : certificate426.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch043.certificate863 H MomentCertificates.Batch021.valid426.1 GeometryCertificates.Batch043.valid863 GeometryCertificates.Batch043.sound863 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch043.certificate864 H MomentCertificates.Batch021.valid426.1 GeometryCertificates.Batch043.valid864 GeometryCertificates.Batch043.sound864 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound426 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound426 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch043.certificate865 H MomentCertificates.Batch021.valid426.1 GeometryCertificates.Batch043.valid865 GeometryCertificates.Batch043.sound865 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound11 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch043.certificate865).dm = (DegreeCertificates.Batch021.certificate426).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate426 GeometryCertificates.Batch043.certificate863 numericValid426
    MomentCertificates.Batch021.valid426 DegreeCertificates.Batch021.valid426 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate426,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate427 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate427,DegreeCertificates.Batch021.certificate427,(WitnessCertificates.Batch043.certificate866).beta,(WitnessCertificates.Batch043.certificate867).L,(some (WitnessCertificates.Batch043.certificate868).beta),(CutFailureCertificates.Budget043.certificate866).bound,(CutFailureCertificates.Budget043.certificate867).bound,(CutFailureCertificates.Budget043.certificate868).bound⟩
theorem numericValid427 : certificate427.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound427 : certificate427.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch043.certificate866 H MomentCertificates.Batch021.valid427.1 GeometryCertificates.Batch043.valid866 GeometryCertificates.Batch043.sound866 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch043.certificate867 H MomentCertificates.Batch021.valid427.1 GeometryCertificates.Batch043.valid867 GeometryCertificates.Batch043.sound867 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound427 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound427 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch043.certificate868 H MomentCertificates.Batch021.valid427.1 GeometryCertificates.Batch043.valid868 GeometryCertificates.Batch043.sound868 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound12 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch043.certificate868).dm = (DegreeCertificates.Batch021.certificate427).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate427 GeometryCertificates.Batch043.certificate866 numericValid427
    MomentCertificates.Batch021.valid427 DegreeCertificates.Batch021.valid427 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate427,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate428 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate428,DegreeCertificates.Batch021.certificate428,(WitnessCertificates.Batch043.certificate869).beta,(WitnessCertificates.Batch043.certificate870).L,(some (WitnessCertificates.Batch043.certificate871).beta),(CutFailureCertificates.Budget043.certificate869).bound,(CutFailureCertificates.Budget043.certificate870).bound,(CutFailureCertificates.Budget043.certificate871).bound⟩
theorem numericValid428 : certificate428.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound428 : certificate428.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch043.certificate869 H MomentCertificates.Batch021.valid428.1 GeometryCertificates.Batch043.valid869 GeometryCertificates.Batch043.sound869 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch043.certificate870 H MomentCertificates.Batch021.valid428.1 GeometryCertificates.Batch043.valid870 GeometryCertificates.Batch043.sound870 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound428 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound428 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch043.certificate871 H MomentCertificates.Batch021.valid428.1 GeometryCertificates.Batch043.valid871 GeometryCertificates.Batch043.sound871 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound13 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch043.certificate871).dm = (DegreeCertificates.Batch021.certificate428).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate428 GeometryCertificates.Batch043.certificate869 numericValid428
    MomentCertificates.Batch021.valid428 DegreeCertificates.Batch021.valid428 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate428,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate429 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate429,DegreeCertificates.Batch021.certificate429,(WitnessCertificates.Batch043.certificate872).beta,(WitnessCertificates.Batch043.certificate873).L,(some (WitnessCertificates.Batch043.certificate874).beta),(CutFailureCertificates.Budget043.certificate872).bound,(CutFailureCertificates.Budget043.certificate873).bound,(CutFailureCertificates.Budget043.certificate874).bound⟩
theorem numericValid429 : certificate429.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound429 : certificate429.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch043.certificate872 H MomentCertificates.Batch021.valid429.1 GeometryCertificates.Batch043.valid872 GeometryCertificates.Batch043.sound872 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch043.certificate873 H MomentCertificates.Batch021.valid429.1 GeometryCertificates.Batch043.valid873 GeometryCertificates.Batch043.sound873 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound429 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound429 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch043.certificate874 H MomentCertificates.Batch021.valid429.1 GeometryCertificates.Batch043.valid874 GeometryCertificates.Batch043.sound874 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound14 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch043.certificate874).dm = (DegreeCertificates.Batch021.certificate429).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate429 GeometryCertificates.Batch043.certificate872 numericValid429
    MomentCertificates.Batch021.valid429 DegreeCertificates.Batch021.valid429 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate429,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate430 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate430,DegreeCertificates.Batch021.certificate430,(WitnessCertificates.Batch043.certificate875).beta,(WitnessCertificates.Batch043.certificate876).L,(some (WitnessCertificates.Batch043.certificate877).beta),(CutFailureCertificates.Budget043.certificate875).bound,(CutFailureCertificates.Budget043.certificate876).bound,(CutFailureCertificates.Budget043.certificate877).bound⟩
theorem numericValid430 : certificate430.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound430 : certificate430.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch043.certificate875 H MomentCertificates.Batch021.valid430.1 GeometryCertificates.Batch043.valid875 GeometryCertificates.Batch043.sound875 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch043.certificate876 H MomentCertificates.Batch021.valid430.1 GeometryCertificates.Batch043.valid876 GeometryCertificates.Batch043.sound876 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound430 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound430 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch043.certificate877 H MomentCertificates.Batch021.valid430.1 GeometryCertificates.Batch043.valid877 GeometryCertificates.Batch043.sound877 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound15 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch043.certificate877).dm = (DegreeCertificates.Batch021.certificate430).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate430 GeometryCertificates.Batch043.certificate875 numericValid430
    MomentCertificates.Batch021.valid430 DegreeCertificates.Batch021.valid430 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate430,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate431 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate431,DegreeCertificates.Batch021.certificate431,(WitnessCertificates.Batch043.certificate878).beta,(WitnessCertificates.Batch043.certificate879).L,(some (WitnessCertificates.Batch044.certificate880).beta),(CutFailureCertificates.Budget043.certificate878).bound,(CutFailureCertificates.Budget043.certificate879).bound,(CutFailureCertificates.Budget044.certificate880).bound⟩
theorem numericValid431 : certificate431.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound431 : certificate431.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch043.certificate878 H MomentCertificates.Batch021.valid431.1 GeometryCertificates.Batch043.valid878 GeometryCertificates.Batch043.sound878 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch043.certificate879 H MomentCertificates.Batch021.valid431.1 GeometryCertificates.Batch043.valid879 GeometryCertificates.Batch043.sound879 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound431 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound431 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch044.certificate880 H MomentCertificates.Batch021.valid431.1 GeometryCertificates.Batch044.valid880 GeometryCertificates.Batch044.sound880 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound16 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch044.certificate880).dm = (DegreeCertificates.Batch021.certificate431).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate431 GeometryCertificates.Batch043.certificate878 numericValid431
    MomentCertificates.Batch021.valid431 DegreeCertificates.Batch021.valid431 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate431,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate432 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate432,DegreeCertificates.Batch021.certificate432,(WitnessCertificates.Batch044.certificate881).beta,(WitnessCertificates.Batch044.certificate882).L,(some (WitnessCertificates.Batch044.certificate883).beta),(CutFailureCertificates.Budget044.certificate881).bound,(CutFailureCertificates.Budget044.certificate882).bound,(CutFailureCertificates.Budget044.certificate883).bound⟩
theorem numericValid432 : certificate432.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound432 : certificate432.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch044.certificate881 H MomentCertificates.Batch021.valid432.1 GeometryCertificates.Batch044.valid881 GeometryCertificates.Batch044.sound881 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch044.certificate882 H MomentCertificates.Batch021.valid432.1 GeometryCertificates.Batch044.valid882 GeometryCertificates.Batch044.sound882 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound432 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound432 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch044.certificate883 H MomentCertificates.Batch021.valid432.1 GeometryCertificates.Batch044.valid883 GeometryCertificates.Batch044.sound883 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound17 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch044.certificate883).dm = (DegreeCertificates.Batch021.certificate432).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate432 GeometryCertificates.Batch044.certificate881 numericValid432
    MomentCertificates.Batch021.valid432 DegreeCertificates.Batch021.valid432 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate432,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate433 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate433,DegreeCertificates.Batch021.certificate433,(WitnessCertificates.Batch044.certificate884).beta,(WitnessCertificates.Batch044.certificate885).L,(some (WitnessCertificates.Batch044.certificate886).beta),(CutFailureCertificates.Budget044.certificate884).bound,(CutFailureCertificates.Budget044.certificate885).bound,(CutFailureCertificates.Budget044.certificate886).bound⟩
theorem numericValid433 : certificate433.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound433 : certificate433.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch044.certificate884 H MomentCertificates.Batch021.valid433.1 GeometryCertificates.Batch044.valid884 GeometryCertificates.Batch044.sound884 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch044.certificate885 H MomentCertificates.Batch021.valid433.1 GeometryCertificates.Batch044.valid885 GeometryCertificates.Batch044.sound885 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound433 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound433 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch044.certificate886 H MomentCertificates.Batch021.valid433.1 GeometryCertificates.Batch044.valid886 GeometryCertificates.Batch044.sound886 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound18 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch044.certificate886).dm = (DegreeCertificates.Batch021.certificate433).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate433 GeometryCertificates.Batch044.certificate884 numericValid433
    MomentCertificates.Batch021.valid433 DegreeCertificates.Batch021.valid433 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate433,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate434 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate434,DegreeCertificates.Batch021.certificate434,(WitnessCertificates.Batch044.certificate887).beta,(WitnessCertificates.Batch044.certificate888).L,(some (WitnessCertificates.Batch044.certificate889).beta),(CutFailureCertificates.Budget044.certificate887).bound,(CutFailureCertificates.Budget044.certificate888).bound,(CutFailureCertificates.Budget044.certificate889).bound⟩
theorem numericValid434 : certificate434.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound434 : certificate434.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch044.certificate887 H MomentCertificates.Batch021.valid434.1 GeometryCertificates.Batch044.valid887 GeometryCertificates.Batch044.sound887 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch044.certificate888 H MomentCertificates.Batch021.valid434.1 GeometryCertificates.Batch044.valid888 GeometryCertificates.Batch044.sound888 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound434 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound434 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch044.certificate889 H MomentCertificates.Batch021.valid434.1 GeometryCertificates.Batch044.valid889 GeometryCertificates.Batch044.sound889 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch000.probabilityBound19 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch044.certificate889).dm = (DegreeCertificates.Batch021.certificate434).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate434 GeometryCertificates.Batch044.certificate887 numericValid434
    MomentCertificates.Batch021.valid434 DegreeCertificates.Batch021.valid434 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate434,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate435 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate435,DegreeCertificates.Batch021.certificate435,(WitnessCertificates.Batch044.certificate890).beta,(WitnessCertificates.Batch044.certificate891).L,(some (WitnessCertificates.Batch044.certificate892).beta),(CutFailureCertificates.Budget044.certificate890).bound,(CutFailureCertificates.Budget044.certificate891).bound,(CutFailureCertificates.Budget044.certificate892).bound⟩
theorem numericValid435 : certificate435.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound435 : certificate435.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch044.certificate890 H MomentCertificates.Batch021.valid435.1 GeometryCertificates.Batch044.valid890 GeometryCertificates.Batch044.sound890 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch044.certificate891 H MomentCertificates.Batch021.valid435.1 GeometryCertificates.Batch044.valid891 GeometryCertificates.Batch044.sound891 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound435 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound435 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch044.certificate892 H MomentCertificates.Batch021.valid435.1 GeometryCertificates.Batch044.valid892 GeometryCertificates.Batch044.sound892 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound20 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch044.certificate892).dm = (DegreeCertificates.Batch021.certificate435).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate435 GeometryCertificates.Batch044.certificate890 numericValid435
    MomentCertificates.Batch021.valid435 DegreeCertificates.Batch021.valid435 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate435,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate436 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate436,DegreeCertificates.Batch021.certificate436,(WitnessCertificates.Batch044.certificate893).beta,(WitnessCertificates.Batch044.certificate894).L,(some (WitnessCertificates.Batch044.certificate895).beta),(CutFailureCertificates.Budget044.certificate893).bound,(CutFailureCertificates.Budget044.certificate894).bound,(CutFailureCertificates.Budget044.certificate895).bound⟩
theorem numericValid436 : certificate436.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound436 : certificate436.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch044.certificate893 H MomentCertificates.Batch021.valid436.1 GeometryCertificates.Batch044.valid893 GeometryCertificates.Batch044.sound893 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch044.certificate894 H MomentCertificates.Batch021.valid436.1 GeometryCertificates.Batch044.valid894 GeometryCertificates.Batch044.sound894 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound436 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound436 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch044.certificate895 H MomentCertificates.Batch021.valid436.1 GeometryCertificates.Batch044.valid895 GeometryCertificates.Batch044.sound895 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound21 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch044.certificate895).dm = (DegreeCertificates.Batch021.certificate436).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate436 GeometryCertificates.Batch044.certificate893 numericValid436
    MomentCertificates.Batch021.valid436 DegreeCertificates.Batch021.valid436 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate436,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate437 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate437,DegreeCertificates.Batch021.certificate437,(WitnessCertificates.Batch044.certificate896).beta,(WitnessCertificates.Batch044.certificate897).L,(some (WitnessCertificates.Batch044.certificate898).beta),(CutFailureCertificates.Budget044.certificate896).bound,(CutFailureCertificates.Budget044.certificate897).bound,(CutFailureCertificates.Budget044.certificate898).bound⟩
theorem numericValid437 : certificate437.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound437 : certificate437.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch044.certificate896 H MomentCertificates.Batch021.valid437.1 GeometryCertificates.Batch044.valid896 GeometryCertificates.Batch044.sound896 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch044.certificate897 H MomentCertificates.Batch021.valid437.1 GeometryCertificates.Batch044.valid897 GeometryCertificates.Batch044.sound897 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound437 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound437 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch044.certificate898 H MomentCertificates.Batch021.valid437.1 GeometryCertificates.Batch044.valid898 GeometryCertificates.Batch044.sound898 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound22 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch044.certificate898).dm = (DegreeCertificates.Batch021.certificate437).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate437 GeometryCertificates.Batch044.certificate896 numericValid437
    MomentCertificates.Batch021.valid437 DegreeCertificates.Batch021.valid437 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate437,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate438 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate438,DegreeCertificates.Batch021.certificate438,(WitnessCertificates.Batch044.certificate899).beta,(WitnessCertificates.Batch045.certificate900).L,(some (WitnessCertificates.Batch045.certificate901).beta),(CutFailureCertificates.Budget044.certificate899).bound,(CutFailureCertificates.Budget045.certificate900).bound,(CutFailureCertificates.Budget045.certificate901).bound⟩
theorem numericValid438 : certificate438.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound438 : certificate438.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch044.certificate899 H MomentCertificates.Batch021.valid438.1 GeometryCertificates.Batch044.valid899 GeometryCertificates.Batch044.sound899 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch045.certificate900 H MomentCertificates.Batch021.valid438.1 GeometryCertificates.Batch045.valid900 GeometryCertificates.Batch045.sound900 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound438 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound438 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch045.certificate901 H MomentCertificates.Batch021.valid438.1 GeometryCertificates.Batch045.valid901 GeometryCertificates.Batch045.sound901 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound23 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch045.certificate901).dm = (DegreeCertificates.Batch021.certificate438).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate438 GeometryCertificates.Batch044.certificate899 numericValid438
    MomentCertificates.Batch021.valid438 DegreeCertificates.Batch021.valid438 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate438,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate439 : RatSamplerCase := ⟨MomentCertificates.Batch021.certificate439,DegreeCertificates.Batch021.certificate439,(WitnessCertificates.Batch045.certificate902).beta,(WitnessCertificates.Batch045.certificate903).L,(some (WitnessCertificates.Batch045.certificate904).beta),(CutFailureCertificates.Budget045.certificate902).bound,(CutFailureCertificates.Budget045.certificate903).bound,(CutFailureCertificates.Budget045.certificate904).bound⟩
theorem numericValid439 : certificate439.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound439 : certificate439.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch045.certificate902 H MomentCertificates.Batch021.valid439.1 GeometryCertificates.Batch045.valid902 GeometryCertificates.Batch045.sound902 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch045.certificate903 H MomentCertificates.Batch021.valid439.1 GeometryCertificates.Batch045.valid903 GeometryCertificates.Batch045.sound903 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch021.probabilityBound439 H st hI
  have hanchor := CertifiedAnchorFailures.Batch021.probabilityBound439 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch045.certificate904 H MomentCertificates.Batch021.valid439.1 GeometryCertificates.Batch045.valid904 GeometryCertificates.Batch045.sound904 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound24 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch045.certificate904).dm = (DegreeCertificates.Batch021.certificate439).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate439 GeometryCertificates.Batch045.certificate902 numericValid439
    MomentCertificates.Batch021.valid439 DegreeCertificates.Batch021.valid439 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate439,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate420,certificate421,certificate422,certificate423,certificate424,certificate425,certificate426,certificate427,certificate428,certificate429,certificate430,certificate431,certificate432,certificate433,certificate434,certificate435,certificate436,certificate437,certificate438,certificate439]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound420,List.forall_mem_cons.mpr ⟨sound421,List.forall_mem_cons.mpr ⟨sound422,List.forall_mem_cons.mpr ⟨sound423,List.forall_mem_cons.mpr ⟨sound424,List.forall_mem_cons.mpr ⟨sound425,List.forall_mem_cons.mpr ⟨sound426,List.forall_mem_cons.mpr ⟨sound427,List.forall_mem_cons.mpr ⟨sound428,List.forall_mem_cons.mpr ⟨sound429,List.forall_mem_cons.mpr ⟨sound430,List.forall_mem_cons.mpr ⟨sound431,List.forall_mem_cons.mpr ⟨sound432,List.forall_mem_cons.mpr ⟨sound433,List.forall_mem_cons.mpr ⟨sound434,List.forall_mem_cons.mpr ⟨sound435,List.forall_mem_cons.mpr ⟨sound436,List.forall_mem_cons.mpr ⟨sound437,List.forall_mem_cons.mpr ⟨sound438,List.forall_mem_cons.mpr ⟨sound439,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch021
