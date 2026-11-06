import Cycle12.RationalSamplerCase
import Cycle12.CertifiedAnchorFailures.Batch022
import Cycle12.CertifiedGlobalFailures.Batch022
import Cycle12.CertifiedLocalFailures.Batch001
import Cycle12.CertifiedLocalFailures.Batch002
import Cycle12.CutFailureCertificates.Budget045
import Cycle12.CutFailureCertificates.Budget046
import Cycle12.CutFailureCertificates.Budget047
import Cycle12.CutFailureCertificates.Budget048
import Cycle12.DegreeCertificates.Batch022
import Cycle12.GeometryCertificates.Batch045
import Cycle12.GeometryCertificates.Batch046
import Cycle12.GeometryCertificates.Batch047
import Cycle12.GeometryCertificates.Batch048
import Cycle12.MomentCertificates.Batch022
import Cycle12.WitnessCertificates.Batch045
import Cycle12.WitnessCertificates.Batch046
import Cycle12.WitnessCertificates.Batch047
import Cycle12.WitnessCertificates.Batch048

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.SamplerCases.Batch022
open Finset SimpleGraph Cycle13 Real Cycle13.MixedSample

def certificate440 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate440,DegreeCertificates.Batch022.certificate440,(WitnessCertificates.Batch045.certificate905).beta,(WitnessCertificates.Batch045.certificate906).L,(some (WitnessCertificates.Batch045.certificate907).beta),(CutFailureCertificates.Budget045.certificate905).bound,(CutFailureCertificates.Budget045.certificate906).bound,(CutFailureCertificates.Budget045.certificate907).bound⟩
theorem numericValid440 : certificate440.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound440 : certificate440.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch045.certificate905 H MomentCertificates.Batch022.valid440.1 GeometryCertificates.Batch045.valid905 GeometryCertificates.Batch045.sound905 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch045.certificate906 H MomentCertificates.Batch022.valid440.1 GeometryCertificates.Batch045.valid906 GeometryCertificates.Batch045.sound906 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound440 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound440 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch045.certificate907 H MomentCertificates.Batch022.valid440.1 GeometryCertificates.Batch045.valid907 GeometryCertificates.Batch045.sound907 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound25 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch045.certificate907).dm = (DegreeCertificates.Batch022.certificate440).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate440 GeometryCertificates.Batch045.certificate905 numericValid440
    MomentCertificates.Batch022.valid440 DegreeCertificates.Batch022.valid440 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate440,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate441 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate441,DegreeCertificates.Batch022.certificate441,(WitnessCertificates.Batch045.certificate908).beta,(WitnessCertificates.Batch045.certificate909).L,(some (WitnessCertificates.Batch045.certificate910).beta),(CutFailureCertificates.Budget045.certificate908).bound,(CutFailureCertificates.Budget045.certificate909).bound,(CutFailureCertificates.Budget045.certificate910).bound⟩
theorem numericValid441 : certificate441.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound441 : certificate441.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch045.certificate908 H MomentCertificates.Batch022.valid441.1 GeometryCertificates.Batch045.valid908 GeometryCertificates.Batch045.sound908 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch045.certificate909 H MomentCertificates.Batch022.valid441.1 GeometryCertificates.Batch045.valid909 GeometryCertificates.Batch045.sound909 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound441 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound441 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch045.certificate910 H MomentCertificates.Batch022.valid441.1 GeometryCertificates.Batch045.valid910 GeometryCertificates.Batch045.sound910 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound26 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch045.certificate910).dm = (DegreeCertificates.Batch022.certificate441).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate441 GeometryCertificates.Batch045.certificate908 numericValid441
    MomentCertificates.Batch022.valid441 DegreeCertificates.Batch022.valid441 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate441,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate442 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate442,DegreeCertificates.Batch022.certificate442,(WitnessCertificates.Batch045.certificate911).beta,(WitnessCertificates.Batch045.certificate912).L,(some (WitnessCertificates.Batch045.certificate913).beta),(CutFailureCertificates.Budget045.certificate911).bound,(CutFailureCertificates.Budget045.certificate912).bound,(CutFailureCertificates.Budget045.certificate913).bound⟩
theorem numericValid442 : certificate442.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound442 : certificate442.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch045.certificate911 H MomentCertificates.Batch022.valid442.1 GeometryCertificates.Batch045.valid911 GeometryCertificates.Batch045.sound911 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch045.certificate912 H MomentCertificates.Batch022.valid442.1 GeometryCertificates.Batch045.valid912 GeometryCertificates.Batch045.sound912 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound442 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound442 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch045.certificate913 H MomentCertificates.Batch022.valid442.1 GeometryCertificates.Batch045.valid913 GeometryCertificates.Batch045.sound913 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound27 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch045.certificate913).dm = (DegreeCertificates.Batch022.certificate442).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate442 GeometryCertificates.Batch045.certificate911 numericValid442
    MomentCertificates.Batch022.valid442 DegreeCertificates.Batch022.valid442 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate442,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate443 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate443,DegreeCertificates.Batch022.certificate443,(WitnessCertificates.Batch045.certificate914).beta,(WitnessCertificates.Batch045.certificate915).L,(some (WitnessCertificates.Batch045.certificate916).beta),(CutFailureCertificates.Budget045.certificate914).bound,(CutFailureCertificates.Budget045.certificate915).bound,(CutFailureCertificates.Budget045.certificate916).bound⟩
theorem numericValid443 : certificate443.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound443 : certificate443.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch045.certificate914 H MomentCertificates.Batch022.valid443.1 GeometryCertificates.Batch045.valid914 GeometryCertificates.Batch045.sound914 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch045.certificate915 H MomentCertificates.Batch022.valid443.1 GeometryCertificates.Batch045.valid915 GeometryCertificates.Batch045.sound915 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound443 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound443 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch045.certificate916 H MomentCertificates.Batch022.valid443.1 GeometryCertificates.Batch045.valid916 GeometryCertificates.Batch045.sound916 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound28 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch045.certificate916).dm = (DegreeCertificates.Batch022.certificate443).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate443 GeometryCertificates.Batch045.certificate914 numericValid443
    MomentCertificates.Batch022.valid443 DegreeCertificates.Batch022.valid443 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate443,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate444 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate444,DegreeCertificates.Batch022.certificate444,(WitnessCertificates.Batch045.certificate917).beta,(WitnessCertificates.Batch045.certificate918).L,(some (WitnessCertificates.Batch045.certificate919).beta),(CutFailureCertificates.Budget045.certificate917).bound,(CutFailureCertificates.Budget045.certificate918).bound,(CutFailureCertificates.Budget045.certificate919).bound⟩
theorem numericValid444 : certificate444.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound444 : certificate444.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch045.certificate917 H MomentCertificates.Batch022.valid444.1 GeometryCertificates.Batch045.valid917 GeometryCertificates.Batch045.sound917 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch045.certificate918 H MomentCertificates.Batch022.valid444.1 GeometryCertificates.Batch045.valid918 GeometryCertificates.Batch045.sound918 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound444 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound444 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch045.certificate919 H MomentCertificates.Batch022.valid444.1 GeometryCertificates.Batch045.valid919 GeometryCertificates.Batch045.sound919 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound29 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch045.certificate919).dm = (DegreeCertificates.Batch022.certificate444).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate444 GeometryCertificates.Batch045.certificate917 numericValid444
    MomentCertificates.Batch022.valid444 DegreeCertificates.Batch022.valid444 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate444,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate445 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate445,DegreeCertificates.Batch022.certificate445,(WitnessCertificates.Batch046.certificate920).beta,(WitnessCertificates.Batch046.certificate921).L,(some (WitnessCertificates.Batch046.certificate922).beta),(CutFailureCertificates.Budget046.certificate920).bound,(CutFailureCertificates.Budget046.certificate921).bound,(CutFailureCertificates.Budget046.certificate922).bound⟩
theorem numericValid445 : certificate445.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound445 : certificate445.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch046.certificate920 H MomentCertificates.Batch022.valid445.1 GeometryCertificates.Batch046.valid920 GeometryCertificates.Batch046.sound920 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch046.certificate921 H MomentCertificates.Batch022.valid445.1 GeometryCertificates.Batch046.valid921 GeometryCertificates.Batch046.sound921 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound445 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound445 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch046.certificate922 H MomentCertificates.Batch022.valid445.1 GeometryCertificates.Batch046.valid922 GeometryCertificates.Batch046.sound922 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound30 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch046.certificate922).dm = (DegreeCertificates.Batch022.certificate445).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate445 GeometryCertificates.Batch046.certificate920 numericValid445
    MomentCertificates.Batch022.valid445 DegreeCertificates.Batch022.valid445 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate445,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate446 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate446,DegreeCertificates.Batch022.certificate446,(WitnessCertificates.Batch046.certificate923).beta,(WitnessCertificates.Batch046.certificate924).L,(some (WitnessCertificates.Batch046.certificate925).beta),(CutFailureCertificates.Budget046.certificate923).bound,(CutFailureCertificates.Budget046.certificate924).bound,(CutFailureCertificates.Budget046.certificate925).bound⟩
theorem numericValid446 : certificate446.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound446 : certificate446.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch046.certificate923 H MomentCertificates.Batch022.valid446.1 GeometryCertificates.Batch046.valid923 GeometryCertificates.Batch046.sound923 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch046.certificate924 H MomentCertificates.Batch022.valid446.1 GeometryCertificates.Batch046.valid924 GeometryCertificates.Batch046.sound924 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound446 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound446 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch046.certificate925 H MomentCertificates.Batch022.valid446.1 GeometryCertificates.Batch046.valid925 GeometryCertificates.Batch046.sound925 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound31 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch046.certificate925).dm = (DegreeCertificates.Batch022.certificate446).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate446 GeometryCertificates.Batch046.certificate923 numericValid446
    MomentCertificates.Batch022.valid446 DegreeCertificates.Batch022.valid446 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate446,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate447 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate447,DegreeCertificates.Batch022.certificate447,(WitnessCertificates.Batch046.certificate926).beta,(WitnessCertificates.Batch046.certificate927).L,(some (WitnessCertificates.Batch046.certificate928).beta),(CutFailureCertificates.Budget046.certificate926).bound,(CutFailureCertificates.Budget046.certificate927).bound,(CutFailureCertificates.Budget046.certificate928).bound⟩
theorem numericValid447 : certificate447.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound447 : certificate447.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch046.certificate926 H MomentCertificates.Batch022.valid447.1 GeometryCertificates.Batch046.valid926 GeometryCertificates.Batch046.sound926 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch046.certificate927 H MomentCertificates.Batch022.valid447.1 GeometryCertificates.Batch046.valid927 GeometryCertificates.Batch046.sound927 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound447 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound447 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch046.certificate928 H MomentCertificates.Batch022.valid447.1 GeometryCertificates.Batch046.valid928 GeometryCertificates.Batch046.sound928 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound32 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch046.certificate928).dm = (DegreeCertificates.Batch022.certificate447).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate447 GeometryCertificates.Batch046.certificate926 numericValid447
    MomentCertificates.Batch022.valid447 DegreeCertificates.Batch022.valid447 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate447,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate448 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate448,DegreeCertificates.Batch022.certificate448,(WitnessCertificates.Batch046.certificate929).beta,(WitnessCertificates.Batch046.certificate930).L,(some (WitnessCertificates.Batch046.certificate931).beta),(CutFailureCertificates.Budget046.certificate929).bound,(CutFailureCertificates.Budget046.certificate930).bound,(CutFailureCertificates.Budget046.certificate931).bound⟩
theorem numericValid448 : certificate448.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound448 : certificate448.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch046.certificate929 H MomentCertificates.Batch022.valid448.1 GeometryCertificates.Batch046.valid929 GeometryCertificates.Batch046.sound929 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch046.certificate930 H MomentCertificates.Batch022.valid448.1 GeometryCertificates.Batch046.valid930 GeometryCertificates.Batch046.sound930 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound448 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound448 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch046.certificate931 H MomentCertificates.Batch022.valid448.1 GeometryCertificates.Batch046.valid931 GeometryCertificates.Batch046.sound931 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound33 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch046.certificate931).dm = (DegreeCertificates.Batch022.certificate448).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate448 GeometryCertificates.Batch046.certificate929 numericValid448
    MomentCertificates.Batch022.valid448 DegreeCertificates.Batch022.valid448 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate448,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate449 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate449,DegreeCertificates.Batch022.certificate449,(WitnessCertificates.Batch046.certificate932).beta,(WitnessCertificates.Batch046.certificate933).L,(some (WitnessCertificates.Batch046.certificate934).beta),(CutFailureCertificates.Budget046.certificate932).bound,(CutFailureCertificates.Budget046.certificate933).bound,(CutFailureCertificates.Budget046.certificate934).bound⟩
theorem numericValid449 : certificate449.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound449 : certificate449.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch046.certificate932 H MomentCertificates.Batch022.valid449.1 GeometryCertificates.Batch046.valid932 GeometryCertificates.Batch046.sound932 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch046.certificate933 H MomentCertificates.Batch022.valid449.1 GeometryCertificates.Batch046.valid933 GeometryCertificates.Batch046.sound933 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound449 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound449 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch046.certificate934 H MomentCertificates.Batch022.valid449.1 GeometryCertificates.Batch046.valid934 GeometryCertificates.Batch046.sound934 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound34 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch046.certificate934).dm = (DegreeCertificates.Batch022.certificate449).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate449 GeometryCertificates.Batch046.certificate932 numericValid449
    MomentCertificates.Batch022.valid449 DegreeCertificates.Batch022.valid449 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate449,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate450 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate450,DegreeCertificates.Batch022.certificate450,(WitnessCertificates.Batch046.certificate935).beta,(WitnessCertificates.Batch046.certificate936).L,(some (WitnessCertificates.Batch046.certificate937).beta),(CutFailureCertificates.Budget046.certificate935).bound,(CutFailureCertificates.Budget046.certificate936).bound,(CutFailureCertificates.Budget046.certificate937).bound⟩
theorem numericValid450 : certificate450.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound450 : certificate450.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch046.certificate935 H MomentCertificates.Batch022.valid450.1 GeometryCertificates.Batch046.valid935 GeometryCertificates.Batch046.sound935 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch046.certificate936 H MomentCertificates.Batch022.valid450.1 GeometryCertificates.Batch046.valid936 GeometryCertificates.Batch046.sound936 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound450 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound450 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch046.certificate937 H MomentCertificates.Batch022.valid450.1 GeometryCertificates.Batch046.valid937 GeometryCertificates.Batch046.sound937 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound35 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch046.certificate937).dm = (DegreeCertificates.Batch022.certificate450).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate450 GeometryCertificates.Batch046.certificate935 numericValid450
    MomentCertificates.Batch022.valid450 DegreeCertificates.Batch022.valid450 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate450,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate451 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate451,DegreeCertificates.Batch022.certificate451,(WitnessCertificates.Batch046.certificate938).beta,(WitnessCertificates.Batch046.certificate939).L,(some (WitnessCertificates.Batch047.certificate940).beta),(CutFailureCertificates.Budget046.certificate938).bound,(CutFailureCertificates.Budget046.certificate939).bound,(CutFailureCertificates.Budget047.certificate940).bound⟩
theorem numericValid451 : certificate451.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound451 : certificate451.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch046.certificate938 H MomentCertificates.Batch022.valid451.1 GeometryCertificates.Batch046.valid938 GeometryCertificates.Batch046.sound938 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch046.certificate939 H MomentCertificates.Batch022.valid451.1 GeometryCertificates.Batch046.valid939 GeometryCertificates.Batch046.sound939 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound451 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound451 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch047.certificate940 H MomentCertificates.Batch022.valid451.1 GeometryCertificates.Batch047.valid940 GeometryCertificates.Batch047.sound940 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound36 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch047.certificate940).dm = (DegreeCertificates.Batch022.certificate451).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate451 GeometryCertificates.Batch046.certificate938 numericValid451
    MomentCertificates.Batch022.valid451 DegreeCertificates.Batch022.valid451 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate451,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate452 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate452,DegreeCertificates.Batch022.certificate452,(WitnessCertificates.Batch047.certificate941).beta,(WitnessCertificates.Batch047.certificate942).L,(some (WitnessCertificates.Batch047.certificate943).beta),(CutFailureCertificates.Budget047.certificate941).bound,(CutFailureCertificates.Budget047.certificate942).bound,(CutFailureCertificates.Budget047.certificate943).bound⟩
theorem numericValid452 : certificate452.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound452 : certificate452.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch047.certificate941 H MomentCertificates.Batch022.valid452.1 GeometryCertificates.Batch047.valid941 GeometryCertificates.Batch047.sound941 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch047.certificate942 H MomentCertificates.Batch022.valid452.1 GeometryCertificates.Batch047.valid942 GeometryCertificates.Batch047.sound942 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound452 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound452 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch047.certificate943 H MomentCertificates.Batch022.valid452.1 GeometryCertificates.Batch047.valid943 GeometryCertificates.Batch047.sound943 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound37 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch047.certificate943).dm = (DegreeCertificates.Batch022.certificate452).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate452 GeometryCertificates.Batch047.certificate941 numericValid452
    MomentCertificates.Batch022.valid452 DegreeCertificates.Batch022.valid452 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate452,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate453 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate453,DegreeCertificates.Batch022.certificate453,(WitnessCertificates.Batch047.certificate944).beta,(WitnessCertificates.Batch047.certificate945).L,(some (WitnessCertificates.Batch047.certificate946).beta),(CutFailureCertificates.Budget047.certificate944).bound,(CutFailureCertificates.Budget047.certificate945).bound,(CutFailureCertificates.Budget047.certificate946).bound⟩
theorem numericValid453 : certificate453.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound453 : certificate453.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch047.certificate944 H MomentCertificates.Batch022.valid453.1 GeometryCertificates.Batch047.valid944 GeometryCertificates.Batch047.sound944 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch047.certificate945 H MomentCertificates.Batch022.valid453.1 GeometryCertificates.Batch047.valid945 GeometryCertificates.Batch047.sound945 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound453 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound453 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch047.certificate946 H MomentCertificates.Batch022.valid453.1 GeometryCertificates.Batch047.valid946 GeometryCertificates.Batch047.sound946 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound38 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch047.certificate946).dm = (DegreeCertificates.Batch022.certificate453).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate453 GeometryCertificates.Batch047.certificate944 numericValid453
    MomentCertificates.Batch022.valid453 DegreeCertificates.Batch022.valid453 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate453,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate454 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate454,DegreeCertificates.Batch022.certificate454,(WitnessCertificates.Batch047.certificate947).beta,(WitnessCertificates.Batch047.certificate948).L,(some (WitnessCertificates.Batch047.certificate949).beta),(CutFailureCertificates.Budget047.certificate947).bound,(CutFailureCertificates.Budget047.certificate948).bound,(CutFailureCertificates.Budget047.certificate949).bound⟩
theorem numericValid454 : certificate454.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound454 : certificate454.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch047.certificate947 H MomentCertificates.Batch022.valid454.1 GeometryCertificates.Batch047.valid947 GeometryCertificates.Batch047.sound947 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch047.certificate948 H MomentCertificates.Batch022.valid454.1 GeometryCertificates.Batch047.valid948 GeometryCertificates.Batch047.sound948 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound454 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound454 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch047.certificate949 H MomentCertificates.Batch022.valid454.1 GeometryCertificates.Batch047.valid949 GeometryCertificates.Batch047.sound949 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch001.probabilityBound39 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch047.certificate949).dm = (DegreeCertificates.Batch022.certificate454).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate454 GeometryCertificates.Batch047.certificate947 numericValid454
    MomentCertificates.Batch022.valid454 DegreeCertificates.Batch022.valid454 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate454,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate455 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate455,DegreeCertificates.Batch022.certificate455,(WitnessCertificates.Batch047.certificate950).beta,(WitnessCertificates.Batch047.certificate951).L,(some (WitnessCertificates.Batch047.certificate952).beta),(CutFailureCertificates.Budget047.certificate950).bound,(CutFailureCertificates.Budget047.certificate951).bound,(CutFailureCertificates.Budget047.certificate952).bound⟩
theorem numericValid455 : certificate455.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound455 : certificate455.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch047.certificate950 H MomentCertificates.Batch022.valid455.1 GeometryCertificates.Batch047.valid950 GeometryCertificates.Batch047.sound950 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch047.certificate951 H MomentCertificates.Batch022.valid455.1 GeometryCertificates.Batch047.valid951 GeometryCertificates.Batch047.sound951 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound455 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound455 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch047.certificate952 H MomentCertificates.Batch022.valid455.1 GeometryCertificates.Batch047.valid952 GeometryCertificates.Batch047.sound952 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound40 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch047.certificate952).dm = (DegreeCertificates.Batch022.certificate455).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate455 GeometryCertificates.Batch047.certificate950 numericValid455
    MomentCertificates.Batch022.valid455 DegreeCertificates.Batch022.valid455 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate455,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate456 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate456,DegreeCertificates.Batch022.certificate456,(WitnessCertificates.Batch047.certificate953).beta,(WitnessCertificates.Batch047.certificate954).L,(some (WitnessCertificates.Batch047.certificate955).beta),(CutFailureCertificates.Budget047.certificate953).bound,(CutFailureCertificates.Budget047.certificate954).bound,(CutFailureCertificates.Budget047.certificate955).bound⟩
theorem numericValid456 : certificate456.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound456 : certificate456.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch047.certificate953 H MomentCertificates.Batch022.valid456.1 GeometryCertificates.Batch047.valid953 GeometryCertificates.Batch047.sound953 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch047.certificate954 H MomentCertificates.Batch022.valid456.1 GeometryCertificates.Batch047.valid954 GeometryCertificates.Batch047.sound954 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound456 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound456 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch047.certificate955 H MomentCertificates.Batch022.valid456.1 GeometryCertificates.Batch047.valid955 GeometryCertificates.Batch047.sound955 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound41 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch047.certificate955).dm = (DegreeCertificates.Batch022.certificate456).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate456 GeometryCertificates.Batch047.certificate953 numericValid456
    MomentCertificates.Batch022.valid456 DegreeCertificates.Batch022.valid456 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate456,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate457 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate457,DegreeCertificates.Batch022.certificate457,(WitnessCertificates.Batch047.certificate956).beta,(WitnessCertificates.Batch047.certificate957).L,(some (WitnessCertificates.Batch047.certificate958).beta),(CutFailureCertificates.Budget047.certificate956).bound,(CutFailureCertificates.Budget047.certificate957).bound,(CutFailureCertificates.Budget047.certificate958).bound⟩
theorem numericValid457 : certificate457.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound457 : certificate457.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch047.certificate956 H MomentCertificates.Batch022.valid457.1 GeometryCertificates.Batch047.valid956 GeometryCertificates.Batch047.sound956 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch047.certificate957 H MomentCertificates.Batch022.valid457.1 GeometryCertificates.Batch047.valid957 GeometryCertificates.Batch047.sound957 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound457 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound457 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch047.certificate958 H MomentCertificates.Batch022.valid457.1 GeometryCertificates.Batch047.valid958 GeometryCertificates.Batch047.sound958 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound42 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch047.certificate958).dm = (DegreeCertificates.Batch022.certificate457).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate457 GeometryCertificates.Batch047.certificate956 numericValid457
    MomentCertificates.Batch022.valid457 DegreeCertificates.Batch022.valid457 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate457,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate458 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate458,DegreeCertificates.Batch022.certificate458,(WitnessCertificates.Batch047.certificate959).beta,(WitnessCertificates.Batch048.certificate960).L,(some (WitnessCertificates.Batch048.certificate961).beta),(CutFailureCertificates.Budget047.certificate959).bound,(CutFailureCertificates.Budget048.certificate960).bound,(CutFailureCertificates.Budget048.certificate961).bound⟩
theorem numericValid458 : certificate458.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound458 : certificate458.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch047.certificate959 H MomentCertificates.Batch022.valid458.1 GeometryCertificates.Batch047.valid959 GeometryCertificates.Batch047.sound959 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch048.certificate960 H MomentCertificates.Batch022.valid458.1 GeometryCertificates.Batch048.valid960 GeometryCertificates.Batch048.sound960 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound458 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound458 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch048.certificate961 H MomentCertificates.Batch022.valid458.1 GeometryCertificates.Batch048.valid961 GeometryCertificates.Batch048.sound961 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound43 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch048.certificate961).dm = (DegreeCertificates.Batch022.certificate458).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate458 GeometryCertificates.Batch047.certificate959 numericValid458
    MomentCertificates.Batch022.valid458 DegreeCertificates.Batch022.valid458 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate458,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificate459 : RatSamplerCase := ⟨MomentCertificates.Batch022.certificate459,DegreeCertificates.Batch022.certificate459,(WitnessCertificates.Batch048.certificate962).beta,(WitnessCertificates.Batch048.certificate963).L,(some (WitnessCertificates.Batch048.certificate964).beta),(CutFailureCertificates.Budget048.certificate962).bound,(CutFailureCertificates.Budget048.certificate963).bound,(CutFailureCertificates.Budget048.certificate964).bound⟩
theorem numericValid459 : certificate459.NumericValid := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem sound459 : certificate459.Sound := by
  intro V _ _ H hm hxl hxh hs hdegree hI
  have hedge := twice_graph_edges_le_order_sq H
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  let st := cover_marked_graph_state GeometryCertificates.Batch048.certificate962 H MomentCertificates.Batch022.valid459.1 GeometryCertificates.Batch048.valid962 GeometryCertificates.Batch048.sound962 hn hm hxl hxh hs
  let stA := cover_marked_graph_state GeometryCertificates.Batch048.certificate963 H MomentCertificates.Batch022.valid459.1 GeometryCertificates.Batch048.valid963 GeometryCertificates.Batch048.sound963 hn hm hxl hxh hs
  have hcut := CertifiedGlobalFailures.Batch022.probabilityBound459 H st hI
  have hanchor := CertifiedAnchorFailures.Batch022.probabilityBound459 H stA hI
  have ha := cover_marked_states_same_sample st stA
  rw [← ha.1,← ha.2] at hanchor
  let stL := cover_marked_graph_state GeometryCertificates.Batch048.certificate964 H MomentCertificates.Batch022.valid459.1 GeometryCertificates.Batch048.valid964 GeometryCertificates.Batch048.sound964 hn hm hxl hxh hs
  have hextra := CertifiedLocalFailures.Batch002.probabilityBound44 H stL hI
  have hl := cover_marked_states_same_sample st stL
  rw [← hl.1,← hl.2] at hextra
  have hdm : (WitnessCertificates.Batch048.certificate964).dm = (DegreeCertificates.Batch022.certificate459).dm := by decide +kernel
  rw [hdm] at hextra
  have hgood := rat_sampler_case_good_from_cut_bounds certificate459 GeometryCertificates.Batch048.certificate962 numericValid459
    MomentCertificates.Batch022.valid459 DegreeCertificates.Batch022.valid459 rfl rfl H st hs hdegree hcut hanchor (by unfold RatSamplerCase.extraBad; simpa only [certificate459,Rat.cast_zero] using hextra)
  rw [cover_marked_state_z st,st.sample_floor] at hgood
  exact hgood

def certificates : List RatSamplerCase := [certificate440,certificate441,certificate442,certificate443,certificate444,certificate445,certificate446,certificate447,certificate448,certificate449,certificate450,certificate451,certificate452,certificate453,certificate454,certificate455,certificate456,certificate457,certificate458,certificate459]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound440,List.forall_mem_cons.mpr ⟨sound441,List.forall_mem_cons.mpr ⟨sound442,List.forall_mem_cons.mpr ⟨sound443,List.forall_mem_cons.mpr ⟨sound444,List.forall_mem_cons.mpr ⟨sound445,List.forall_mem_cons.mpr ⟨sound446,List.forall_mem_cons.mpr ⟨sound447,List.forall_mem_cons.mpr ⟨sound448,List.forall_mem_cons.mpr ⟨sound449,List.forall_mem_cons.mpr ⟨sound450,List.forall_mem_cons.mpr ⟨sound451,List.forall_mem_cons.mpr ⟨sound452,List.forall_mem_cons.mpr ⟨sound453,List.forall_mem_cons.mpr ⟨sound454,List.forall_mem_cons.mpr ⟨sound455,List.forall_mem_cons.mpr ⟨sound456,List.forall_mem_cons.mpr ⟨sound457,List.forall_mem_cons.mpr ⟨sound458,List.forall_mem_cons.mpr ⟨sound459,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.SamplerCases.Batch022
