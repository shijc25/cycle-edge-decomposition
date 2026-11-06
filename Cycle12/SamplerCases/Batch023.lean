import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch023
import Cycle12.CertifiedGlobalFailures.Batch023
import Cycle12.CertifiedLocalFailures.Batch002
import Cycle12.CertifiedLocalFailures.Batch003
import Cycle12.CutFailureCertificates.Budget048
import Cycle12.CutFailureCertificates.Budget049
import Cycle12.CutFailureCertificates.Budget050
import Cycle12.CutFailureCertificates.Budget051
import Cycle12.DegreeCertificates.Batch023
import Cycle12.GeometryCertificates.Batch048
import Cycle12.GeometryCertificates.Batch049
import Cycle12.GeometryCertificates.Batch050
import Cycle12.GeometryCertificates.Batch051
import Cycle12.MomentCertificates.Batch023
import Cycle12.WitnessCertificates.Batch048
import Cycle12.WitnessCertificates.Batch049
import Cycle12.WitnessCertificates.Batch050
import Cycle12.WitnessCertificates.Batch051

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch023
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate460 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate460,DegreeCertificates.Batch023.certificate460,(WitnessCertificates.Batch048.certificate965).beta,(WitnessCertificates.Batch048.certificate966).L,(some (WitnessCertificates.Batch048.certificate967).beta),(CutFailureCertificates.Budget048.certificate965).bound,(CutFailureCertificates.Budget048.certificate966).bound,(CutFailureCertificates.Budget048.certificate967).bound⟩
theorem numericValid460 : certificate460.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound460 : certificate460.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch048.certificate965 H MomentCertificates.Batch023.valid460.1 GeometryCertificates.Batch048.valid965 GeometryCertificates.Batch048.sound965 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch048.certificate966 H MomentCertificates.Batch023.valid460.1 GeometryCertificates.Batch048.valid966 GeometryCertificates.Batch048.sound966 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound460 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound460 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch048.certificate967 H MomentCertificates.Batch023.valid460.1 GeometryCertificates.Batch048.valid967 GeometryCertificates.Batch048.sound967 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound45 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch048.certificate967).dm = (DegreeCertificates.Batch023.certificate460).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate460 GeometryCertificates.Batch048.certificate965 numericValid460
    MomentCertificates.Batch023.valid460 DegreeCertificates.Batch023.valid460 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate460,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate461 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate461,DegreeCertificates.Batch023.certificate461,(WitnessCertificates.Batch048.certificate968).beta,(WitnessCertificates.Batch048.certificate969).L,(some (WitnessCertificates.Batch048.certificate970).beta),(CutFailureCertificates.Budget048.certificate968).bound,(CutFailureCertificates.Budget048.certificate969).bound,(CutFailureCertificates.Budget048.certificate970).bound⟩
theorem numericValid461 : certificate461.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound461 : certificate461.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch048.certificate968 H MomentCertificates.Batch023.valid461.1 GeometryCertificates.Batch048.valid968 GeometryCertificates.Batch048.sound968 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch048.certificate969 H MomentCertificates.Batch023.valid461.1 GeometryCertificates.Batch048.valid969 GeometryCertificates.Batch048.sound969 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound461 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound461 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch048.certificate970 H MomentCertificates.Batch023.valid461.1 GeometryCertificates.Batch048.valid970 GeometryCertificates.Batch048.sound970 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound46 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch048.certificate970).dm = (DegreeCertificates.Batch023.certificate461).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate461 GeometryCertificates.Batch048.certificate968 numericValid461
    MomentCertificates.Batch023.valid461 DegreeCertificates.Batch023.valid461 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate461,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate462 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate462,DegreeCertificates.Batch023.certificate462,(WitnessCertificates.Batch048.certificate971).beta,(WitnessCertificates.Batch048.certificate972).L,(some (WitnessCertificates.Batch048.certificate973).beta),(CutFailureCertificates.Budget048.certificate971).bound,(CutFailureCertificates.Budget048.certificate972).bound,(CutFailureCertificates.Budget048.certificate973).bound⟩
theorem numericValid462 : certificate462.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound462 : certificate462.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch048.certificate971 H MomentCertificates.Batch023.valid462.1 GeometryCertificates.Batch048.valid971 GeometryCertificates.Batch048.sound971 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch048.certificate972 H MomentCertificates.Batch023.valid462.1 GeometryCertificates.Batch048.valid972 GeometryCertificates.Batch048.sound972 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound462 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound462 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch048.certificate973 H MomentCertificates.Batch023.valid462.1 GeometryCertificates.Batch048.valid973 GeometryCertificates.Batch048.sound973 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound47 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch048.certificate973).dm = (DegreeCertificates.Batch023.certificate462).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate462 GeometryCertificates.Batch048.certificate971 numericValid462
    MomentCertificates.Batch023.valid462 DegreeCertificates.Batch023.valid462 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate462,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate463 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate463,DegreeCertificates.Batch023.certificate463,(WitnessCertificates.Batch048.certificate974).beta,(WitnessCertificates.Batch048.certificate975).L,(some (WitnessCertificates.Batch048.certificate976).beta),(CutFailureCertificates.Budget048.certificate974).bound,(CutFailureCertificates.Budget048.certificate975).bound,(CutFailureCertificates.Budget048.certificate976).bound⟩
theorem numericValid463 : certificate463.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound463 : certificate463.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch048.certificate974 H MomentCertificates.Batch023.valid463.1 GeometryCertificates.Batch048.valid974 GeometryCertificates.Batch048.sound974 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch048.certificate975 H MomentCertificates.Batch023.valid463.1 GeometryCertificates.Batch048.valid975 GeometryCertificates.Batch048.sound975 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound463 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound463 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch048.certificate976 H MomentCertificates.Batch023.valid463.1 GeometryCertificates.Batch048.valid976 GeometryCertificates.Batch048.sound976 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound48 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch048.certificate976).dm = (DegreeCertificates.Batch023.certificate463).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate463 GeometryCertificates.Batch048.certificate974 numericValid463
    MomentCertificates.Batch023.valid463 DegreeCertificates.Batch023.valid463 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate463,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate464 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate464,DegreeCertificates.Batch023.certificate464,(WitnessCertificates.Batch048.certificate977).beta,(WitnessCertificates.Batch048.certificate978).L,(some (WitnessCertificates.Batch048.certificate979).beta),(CutFailureCertificates.Budget048.certificate977).bound,(CutFailureCertificates.Budget048.certificate978).bound,(CutFailureCertificates.Budget048.certificate979).bound⟩
theorem numericValid464 : certificate464.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound464 : certificate464.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch048.certificate977 H MomentCertificates.Batch023.valid464.1 GeometryCertificates.Batch048.valid977 GeometryCertificates.Batch048.sound977 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch048.certificate978 H MomentCertificates.Batch023.valid464.1 GeometryCertificates.Batch048.valid978 GeometryCertificates.Batch048.sound978 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound464 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound464 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch048.certificate979 H MomentCertificates.Batch023.valid464.1 GeometryCertificates.Batch048.valid979 GeometryCertificates.Batch048.sound979 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound49 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch048.certificate979).dm = (DegreeCertificates.Batch023.certificate464).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate464 GeometryCertificates.Batch048.certificate977 numericValid464
    MomentCertificates.Batch023.valid464 DegreeCertificates.Batch023.valid464 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate464,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate465 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate465,DegreeCertificates.Batch023.certificate465,(WitnessCertificates.Batch049.certificate980).beta,(WitnessCertificates.Batch049.certificate981).L,(some (WitnessCertificates.Batch049.certificate982).beta),(CutFailureCertificates.Budget049.certificate980).bound,(CutFailureCertificates.Budget049.certificate981).bound,(CutFailureCertificates.Budget049.certificate982).bound⟩
theorem numericValid465 : certificate465.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound465 : certificate465.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch049.certificate980 H MomentCertificates.Batch023.valid465.1 GeometryCertificates.Batch049.valid980 GeometryCertificates.Batch049.sound980 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch049.certificate981 H MomentCertificates.Batch023.valid465.1 GeometryCertificates.Batch049.valid981 GeometryCertificates.Batch049.sound981 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound465 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound465 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch049.certificate982 H MomentCertificates.Batch023.valid465.1 GeometryCertificates.Batch049.valid982 GeometryCertificates.Batch049.sound982 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound50 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch049.certificate982).dm = (DegreeCertificates.Batch023.certificate465).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate465 GeometryCertificates.Batch049.certificate980 numericValid465
    MomentCertificates.Batch023.valid465 DegreeCertificates.Batch023.valid465 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate465,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate466 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate466,DegreeCertificates.Batch023.certificate466,(WitnessCertificates.Batch049.certificate983).beta,(WitnessCertificates.Batch049.certificate984).L,(some (WitnessCertificates.Batch049.certificate985).beta),(CutFailureCertificates.Budget049.certificate983).bound,(CutFailureCertificates.Budget049.certificate984).bound,(CutFailureCertificates.Budget049.certificate985).bound⟩
theorem numericValid466 : certificate466.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound466 : certificate466.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch049.certificate983 H MomentCertificates.Batch023.valid466.1 GeometryCertificates.Batch049.valid983 GeometryCertificates.Batch049.sound983 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch049.certificate984 H MomentCertificates.Batch023.valid466.1 GeometryCertificates.Batch049.valid984 GeometryCertificates.Batch049.sound984 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound466 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound466 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch049.certificate985 H MomentCertificates.Batch023.valid466.1 GeometryCertificates.Batch049.valid985 GeometryCertificates.Batch049.sound985 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound51 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch049.certificate985).dm = (DegreeCertificates.Batch023.certificate466).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate466 GeometryCertificates.Batch049.certificate983 numericValid466
    MomentCertificates.Batch023.valid466 DegreeCertificates.Batch023.valid466 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate466,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate467 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate467,DegreeCertificates.Batch023.certificate467,(WitnessCertificates.Batch049.certificate986).beta,(WitnessCertificates.Batch049.certificate987).L,(some (WitnessCertificates.Batch049.certificate988).beta),(CutFailureCertificates.Budget049.certificate986).bound,(CutFailureCertificates.Budget049.certificate987).bound,(CutFailureCertificates.Budget049.certificate988).bound⟩
theorem numericValid467 : certificate467.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound467 : certificate467.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch049.certificate986 H MomentCertificates.Batch023.valid467.1 GeometryCertificates.Batch049.valid986 GeometryCertificates.Batch049.sound986 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch049.certificate987 H MomentCertificates.Batch023.valid467.1 GeometryCertificates.Batch049.valid987 GeometryCertificates.Batch049.sound987 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound467 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound467 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch049.certificate988 H MomentCertificates.Batch023.valid467.1 GeometryCertificates.Batch049.valid988 GeometryCertificates.Batch049.sound988 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound52 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch049.certificate988).dm = (DegreeCertificates.Batch023.certificate467).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate467 GeometryCertificates.Batch049.certificate986 numericValid467
    MomentCertificates.Batch023.valid467 DegreeCertificates.Batch023.valid467 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate467,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate468 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate468,DegreeCertificates.Batch023.certificate468,(WitnessCertificates.Batch049.certificate989).beta,(WitnessCertificates.Batch049.certificate990).L,(some (WitnessCertificates.Batch049.certificate991).beta),(CutFailureCertificates.Budget049.certificate989).bound,(CutFailureCertificates.Budget049.certificate990).bound,(CutFailureCertificates.Budget049.certificate991).bound⟩
theorem numericValid468 : certificate468.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound468 : certificate468.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch049.certificate989 H MomentCertificates.Batch023.valid468.1 GeometryCertificates.Batch049.valid989 GeometryCertificates.Batch049.sound989 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch049.certificate990 H MomentCertificates.Batch023.valid468.1 GeometryCertificates.Batch049.valid990 GeometryCertificates.Batch049.sound990 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound468 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound468 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch049.certificate991 H MomentCertificates.Batch023.valid468.1 GeometryCertificates.Batch049.valid991 GeometryCertificates.Batch049.sound991 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound53 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch049.certificate991).dm = (DegreeCertificates.Batch023.certificate468).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate468 GeometryCertificates.Batch049.certificate989 numericValid468
    MomentCertificates.Batch023.valid468 DegreeCertificates.Batch023.valid468 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate468,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate469 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate469,DegreeCertificates.Batch023.certificate469,(WitnessCertificates.Batch049.certificate992).beta,(WitnessCertificates.Batch049.certificate993).L,(some (WitnessCertificates.Batch049.certificate994).beta),(CutFailureCertificates.Budget049.certificate992).bound,(CutFailureCertificates.Budget049.certificate993).bound,(CutFailureCertificates.Budget049.certificate994).bound⟩
theorem numericValid469 : certificate469.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound469 : certificate469.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch049.certificate992 H MomentCertificates.Batch023.valid469.1 GeometryCertificates.Batch049.valid992 GeometryCertificates.Batch049.sound992 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch049.certificate993 H MomentCertificates.Batch023.valid469.1 GeometryCertificates.Batch049.valid993 GeometryCertificates.Batch049.sound993 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound469 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound469 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch049.certificate994 H MomentCertificates.Batch023.valid469.1 GeometryCertificates.Batch049.valid994 GeometryCertificates.Batch049.sound994 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound54 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch049.certificate994).dm = (DegreeCertificates.Batch023.certificate469).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate469 GeometryCertificates.Batch049.certificate992 numericValid469
    MomentCertificates.Batch023.valid469 DegreeCertificates.Batch023.valid469 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate469,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate470 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate470,DegreeCertificates.Batch023.certificate470,(WitnessCertificates.Batch049.certificate995).beta,(WitnessCertificates.Batch049.certificate996).L,(some (WitnessCertificates.Batch049.certificate997).beta),(CutFailureCertificates.Budget049.certificate995).bound,(CutFailureCertificates.Budget049.certificate996).bound,(CutFailureCertificates.Budget049.certificate997).bound⟩
theorem numericValid470 : certificate470.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound470 : certificate470.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch049.certificate995 H MomentCertificates.Batch023.valid470.1 GeometryCertificates.Batch049.valid995 GeometryCertificates.Batch049.sound995 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch049.certificate996 H MomentCertificates.Batch023.valid470.1 GeometryCertificates.Batch049.valid996 GeometryCertificates.Batch049.sound996 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound470 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound470 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch049.certificate997 H MomentCertificates.Batch023.valid470.1 GeometryCertificates.Batch049.valid997 GeometryCertificates.Batch049.sound997 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound55 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch049.certificate997).dm = (DegreeCertificates.Batch023.certificate470).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate470 GeometryCertificates.Batch049.certificate995 numericValid470
    MomentCertificates.Batch023.valid470 DegreeCertificates.Batch023.valid470 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate470,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate471 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate471,DegreeCertificates.Batch023.certificate471,(WitnessCertificates.Batch049.certificate998).beta,(WitnessCertificates.Batch049.certificate999).L,(some (WitnessCertificates.Batch050.certificate1000).beta),(CutFailureCertificates.Budget049.certificate998).bound,(CutFailureCertificates.Budget049.certificate999).bound,(CutFailureCertificates.Budget050.certificate1000).bound⟩
theorem numericValid471 : certificate471.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound471 : certificate471.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch049.certificate998 H MomentCertificates.Batch023.valid471.1 GeometryCertificates.Batch049.valid998 GeometryCertificates.Batch049.sound998 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch049.certificate999 H MomentCertificates.Batch023.valid471.1 GeometryCertificates.Batch049.valid999 GeometryCertificates.Batch049.sound999 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound471 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound471 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch050.certificate1000 H MomentCertificates.Batch023.valid471.1 GeometryCertificates.Batch050.valid1000 GeometryCertificates.Batch050.sound1000 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound56 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch050.certificate1000).dm = (DegreeCertificates.Batch023.certificate471).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate471 GeometryCertificates.Batch049.certificate998 numericValid471
    MomentCertificates.Batch023.valid471 DegreeCertificates.Batch023.valid471 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate471,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate472 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate472,DegreeCertificates.Batch023.certificate472,(WitnessCertificates.Batch050.certificate1001).beta,(WitnessCertificates.Batch050.certificate1002).L,(some (WitnessCertificates.Batch050.certificate1003).beta),(CutFailureCertificates.Budget050.certificate1001).bound,(CutFailureCertificates.Budget050.certificate1002).bound,(CutFailureCertificates.Budget050.certificate1003).bound⟩
theorem numericValid472 : certificate472.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound472 : certificate472.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch050.certificate1001 H MomentCertificates.Batch023.valid472.1 GeometryCertificates.Batch050.valid1001 GeometryCertificates.Batch050.sound1001 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch050.certificate1002 H MomentCertificates.Batch023.valid472.1 GeometryCertificates.Batch050.valid1002 GeometryCertificates.Batch050.sound1002 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound472 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound472 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch050.certificate1003 H MomentCertificates.Batch023.valid472.1 GeometryCertificates.Batch050.valid1003 GeometryCertificates.Batch050.sound1003 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound57 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch050.certificate1003).dm = (DegreeCertificates.Batch023.certificate472).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate472 GeometryCertificates.Batch050.certificate1001 numericValid472
    MomentCertificates.Batch023.valid472 DegreeCertificates.Batch023.valid472 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate472,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate473 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate473,DegreeCertificates.Batch023.certificate473,(WitnessCertificates.Batch050.certificate1004).beta,(WitnessCertificates.Batch050.certificate1005).L,(some (WitnessCertificates.Batch050.certificate1006).beta),(CutFailureCertificates.Budget050.certificate1004).bound,(CutFailureCertificates.Budget050.certificate1005).bound,(CutFailureCertificates.Budget050.certificate1006).bound⟩
theorem numericValid473 : certificate473.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound473 : certificate473.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch050.certificate1004 H MomentCertificates.Batch023.valid473.1 GeometryCertificates.Batch050.valid1004 GeometryCertificates.Batch050.sound1004 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch050.certificate1005 H MomentCertificates.Batch023.valid473.1 GeometryCertificates.Batch050.valid1005 GeometryCertificates.Batch050.sound1005 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound473 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound473 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch050.certificate1006 H MomentCertificates.Batch023.valid473.1 GeometryCertificates.Batch050.valid1006 GeometryCertificates.Batch050.sound1006 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound58 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch050.certificate1006).dm = (DegreeCertificates.Batch023.certificate473).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate473 GeometryCertificates.Batch050.certificate1004 numericValid473
    MomentCertificates.Batch023.valid473 DegreeCertificates.Batch023.valid473 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate473,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate474 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate474,DegreeCertificates.Batch023.certificate474,(WitnessCertificates.Batch050.certificate1007).beta,(WitnessCertificates.Batch050.certificate1008).L,(some (WitnessCertificates.Batch050.certificate1009).beta),(CutFailureCertificates.Budget050.certificate1007).bound,(CutFailureCertificates.Budget050.certificate1008).bound,(CutFailureCertificates.Budget050.certificate1009).bound⟩
theorem numericValid474 : certificate474.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound474 : certificate474.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch050.certificate1007 H MomentCertificates.Batch023.valid474.1 GeometryCertificates.Batch050.valid1007 GeometryCertificates.Batch050.sound1007 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch050.certificate1008 H MomentCertificates.Batch023.valid474.1 GeometryCertificates.Batch050.valid1008 GeometryCertificates.Batch050.sound1008 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound474 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound474 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch050.certificate1009 H MomentCertificates.Batch023.valid474.1 GeometryCertificates.Batch050.valid1009 GeometryCertificates.Batch050.sound1009 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound59 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch050.certificate1009).dm = (DegreeCertificates.Batch023.certificate474).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate474 GeometryCertificates.Batch050.certificate1007 numericValid474
    MomentCertificates.Batch023.valid474 DegreeCertificates.Batch023.valid474 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate474,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate475 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate475,DegreeCertificates.Batch023.certificate475,(WitnessCertificates.Batch050.certificate1010).beta,(WitnessCertificates.Batch050.certificate1011).L,(some (WitnessCertificates.Batch050.certificate1012).beta),(CutFailureCertificates.Budget050.certificate1010).bound,(CutFailureCertificates.Budget050.certificate1011).bound,(CutFailureCertificates.Budget050.certificate1012).bound⟩
theorem numericValid475 : certificate475.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound475 : certificate475.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch050.certificate1010 H MomentCertificates.Batch023.valid475.1 GeometryCertificates.Batch050.valid1010 GeometryCertificates.Batch050.sound1010 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch050.certificate1011 H MomentCertificates.Batch023.valid475.1 GeometryCertificates.Batch050.valid1011 GeometryCertificates.Batch050.sound1011 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound475 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound475 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch050.certificate1012 H MomentCertificates.Batch023.valid475.1 GeometryCertificates.Batch050.valid1012 GeometryCertificates.Batch050.sound1012 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound60 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch050.certificate1012).dm = (DegreeCertificates.Batch023.certificate475).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate475 GeometryCertificates.Batch050.certificate1010 numericValid475
    MomentCertificates.Batch023.valid475 DegreeCertificates.Batch023.valid475 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate475,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate476 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate476,DegreeCertificates.Batch023.certificate476,(WitnessCertificates.Batch050.certificate1013).beta,(WitnessCertificates.Batch050.certificate1014).L,(some (WitnessCertificates.Batch050.certificate1015).beta),(CutFailureCertificates.Budget050.certificate1013).bound,(CutFailureCertificates.Budget050.certificate1014).bound,(CutFailureCertificates.Budget050.certificate1015).bound⟩
theorem numericValid476 : certificate476.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound476 : certificate476.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch050.certificate1013 H MomentCertificates.Batch023.valid476.1 GeometryCertificates.Batch050.valid1013 GeometryCertificates.Batch050.sound1013 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch050.certificate1014 H MomentCertificates.Batch023.valid476.1 GeometryCertificates.Batch050.valid1014 GeometryCertificates.Batch050.sound1014 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound476 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound476 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch050.certificate1015 H MomentCertificates.Batch023.valid476.1 GeometryCertificates.Batch050.valid1015 GeometryCertificates.Batch050.sound1015 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound61 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch050.certificate1015).dm = (DegreeCertificates.Batch023.certificate476).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate476 GeometryCertificates.Batch050.certificate1013 numericValid476
    MomentCertificates.Batch023.valid476 DegreeCertificates.Batch023.valid476 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate476,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate477 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate477,DegreeCertificates.Batch023.certificate477,(WitnessCertificates.Batch050.certificate1016).beta,(WitnessCertificates.Batch050.certificate1017).L,(some (WitnessCertificates.Batch050.certificate1018).beta),(CutFailureCertificates.Budget050.certificate1016).bound,(CutFailureCertificates.Budget050.certificate1017).bound,(CutFailureCertificates.Budget050.certificate1018).bound⟩
theorem numericValid477 : certificate477.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound477 : certificate477.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch050.certificate1016 H MomentCertificates.Batch023.valid477.1 GeometryCertificates.Batch050.valid1016 GeometryCertificates.Batch050.sound1016 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch050.certificate1017 H MomentCertificates.Batch023.valid477.1 GeometryCertificates.Batch050.valid1017 GeometryCertificates.Batch050.sound1017 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound477 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound477 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch050.certificate1018 H MomentCertificates.Batch023.valid477.1 GeometryCertificates.Batch050.valid1018 GeometryCertificates.Batch050.sound1018 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound62 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch050.certificate1018).dm = (DegreeCertificates.Batch023.certificate477).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate477 GeometryCertificates.Batch050.certificate1016 numericValid477
    MomentCertificates.Batch023.valid477 DegreeCertificates.Batch023.valid477 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate477,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate478 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate478,DegreeCertificates.Batch023.certificate478,(WitnessCertificates.Batch050.certificate1019).beta,(WitnessCertificates.Batch051.certificate1020).L,(some (WitnessCertificates.Batch051.certificate1021).beta),(CutFailureCertificates.Budget050.certificate1019).bound,(CutFailureCertificates.Budget051.certificate1020).bound,(CutFailureCertificates.Budget051.certificate1021).bound⟩
theorem numericValid478 : certificate478.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound478 : certificate478.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch050.certificate1019 H MomentCertificates.Batch023.valid478.1 GeometryCertificates.Batch050.valid1019 GeometryCertificates.Batch050.sound1019 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch051.certificate1020 H MomentCertificates.Batch023.valid478.1 GeometryCertificates.Batch051.valid1020 GeometryCertificates.Batch051.sound1020 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound478 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound478 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch051.certificate1021 H MomentCertificates.Batch023.valid478.1 GeometryCertificates.Batch051.valid1021 GeometryCertificates.Batch051.sound1021 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound63 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch051.certificate1021).dm = (DegreeCertificates.Batch023.certificate478).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate478 GeometryCertificates.Batch050.certificate1019 numericValid478
    MomentCertificates.Batch023.valid478 DegreeCertificates.Batch023.valid478 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate478,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate479 : RatSamplerCase := ⟨MomentCertificates.Batch023.certificate479,DegreeCertificates.Batch023.certificate479,(WitnessCertificates.Batch051.certificate1022).beta,(WitnessCertificates.Batch051.certificate1023).L,(some (WitnessCertificates.Batch051.certificate1024).beta),(CutFailureCertificates.Budget051.certificate1022).bound,(CutFailureCertificates.Budget051.certificate1023).bound,(CutFailureCertificates.Budget051.certificate1024).bound⟩
theorem numericValid479 : certificate479.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound479 : certificate479.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch051.certificate1022 H MomentCertificates.Batch023.valid479.1 GeometryCertificates.Batch051.valid1022 GeometryCertificates.Batch051.sound1022 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch051.certificate1023 H MomentCertificates.Batch023.valid479.1 GeometryCertificates.Batch051.valid1023 GeometryCertificates.Batch051.sound1023 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch023.probabilityBound479 H st hI
  have hanchor := CertifiedAnchorFailures.Batch023.probabilityBound479 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch051.certificate1024 H MomentCertificates.Batch023.valid479.1 GeometryCertificates.Batch051.valid1024 GeometryCertificates.Batch051.sound1024 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch003.probabilityBound64 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch051.certificate1024).dm = (DegreeCertificates.Batch023.certificate479).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate479 GeometryCertificates.Batch051.certificate1022 numericValid479
    MomentCertificates.Batch023.valid479 DegreeCertificates.Batch023.valid479 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate479,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate460,certificate461,certificate462,certificate463,certificate464,certificate465,certificate466,certificate467,certificate468,certificate469,certificate470,certificate471,certificate472,certificate473,certificate474,certificate475,certificate476,certificate477,certificate478,certificate479]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound460,List.forall_mem_cons.mpr ⟨sound461,List.forall_mem_cons.mpr ⟨sound462,List.forall_mem_cons.mpr ⟨sound463,List.forall_mem_cons.mpr ⟨sound464,List.forall_mem_cons.mpr ⟨sound465,List.forall_mem_cons.mpr ⟨sound466,List.forall_mem_cons.mpr ⟨sound467,List.forall_mem_cons.mpr ⟨sound468,List.forall_mem_cons.mpr ⟨sound469,List.forall_mem_cons.mpr ⟨sound470,List.forall_mem_cons.mpr ⟨sound471,List.forall_mem_cons.mpr ⟨sound472,List.forall_mem_cons.mpr ⟨sound473,List.forall_mem_cons.mpr ⟨sound474,List.forall_mem_cons.mpr ⟨sound475,List.forall_mem_cons.mpr ⟨sound476,List.forall_mem_cons.mpr ⟨sound477,List.forall_mem_cons.mpr ⟨sound478,List.forall_mem_cons.mpr ⟨sound479,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch023
