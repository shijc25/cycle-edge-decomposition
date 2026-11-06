import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch002
import Cycle12.CountingCertificates.Batch003
import Cycle12.CutFailureCertificates.Budget002
import Cycle12.CutFailureCertificates.Budget003
import Cycle12.CutLabelCertificates.Entropy001
import Cycle12.CutLabelCertificates.Entropy002
import Cycle12.CutLabelCertificates.Minority001
import Cycle12.MergedCutGroups.Batch005
import Cycle12.MergedCutGroups.Batch006
import Cycle12.MergedCutGroups.Batch007
import Cycle12.MergedCutGroups.Batch008
import Cycle12.MergedCutGroups.Batch009
import Cycle12.PopulationCertificates.Batch002
import Cycle12.PopulationCertificates.Batch003
import Cycle12.WitnessCertificates.Batch002
import Cycle12.WitnessCertificates.Batch003

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch001
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches20 : (MergedCutGroups.Batch005.certificate60).GlobalMatches MergedCutGroups.Batch005.certificate61 CountingCertificates.Batch002.certificate40 CutLabelCertificates.Entropy001.certificate21 CutLabelCertificates.Minority001.certificate20 := by decide +kernel
theorem exponentialBound20 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch005.certificate60).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate40).dm (WitnessCertificates.Batch002.certificate40).beta) ≤ (2*exp (-((CountingCertificates.Batch002.certificate40).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch005.certificate60).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch005.certificate61).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch002.certificate40).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch005.certificate60 MergedCutGroups.Batch005.certificate61 CountingCertificates.Batch002.certificate40 CutLabelCertificates.Entropy001.certificate21 CutLabelCertificates.Minority001.certificate20 matches20 rfl rfl
    MergedCutGroups.Batch005.numericValid60 MergedCutGroups.Batch005.numericValid61 MergedCutGroups.Batch005.cellsSound60 MergedCutGroups.Batch005.cellsSound61
    MergedCutGroups.Batch005.cellsNumeric60 MergedCutGroups.Batch005.cellsNumeric61 MergedCutGroups.Batch005.populationMatches60 MergedCutGroups.Batch005.populationMatches61
    PopulationCertificates.Batch002.valid40 PopulationCertificates.Batch002.sound40 WitnessCertificates.Batch002.valid40 WitnessCertificates.Batch002.sound40 CountingCertificates.Batch002.valid40 CountingCertificates.Batch002.sound40
    CutLabelCertificates.Entropy001.valid21 CutLabelCertificates.Minority001.valid20 CutLabelCertificates.Minority001.sound20 H st hI
theorem probabilityBound20 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch005.certificate60).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate40).dm (WitnessCertificates.Batch002.certificate40).beta) ≤ ((CutFailureCertificates.Budget002.certificate40).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound40 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate40).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch005.certificate60).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch005.certificate61).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch002.certificate40).omega:ℝ) ≤ ((CutFailureCertificates.Budget002.certificate40).bound:ℝ) at hb
  exact (exponentialBound20 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches21 : (MergedCutGroups.Batch005.certificate63).GlobalMatches MergedCutGroups.Batch005.certificate64 CountingCertificates.Batch002.certificate42 CutLabelCertificates.Entropy001.certificate22 CutLabelCertificates.Minority001.certificate21 := by decide +kernel
theorem exponentialBound21 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch005.certificate63).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate42).dm (WitnessCertificates.Batch002.certificate42).beta) ≤ (2*exp (-((CountingCertificates.Batch002.certificate42).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch005.certificate63).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch005.certificate64).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch002.certificate42).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch005.certificate63 MergedCutGroups.Batch005.certificate64 CountingCertificates.Batch002.certificate42 CutLabelCertificates.Entropy001.certificate22 CutLabelCertificates.Minority001.certificate21 matches21 rfl rfl
    MergedCutGroups.Batch005.numericValid63 MergedCutGroups.Batch005.numericValid64 MergedCutGroups.Batch005.cellsSound63 MergedCutGroups.Batch005.cellsSound64
    MergedCutGroups.Batch005.cellsNumeric63 MergedCutGroups.Batch005.cellsNumeric64 MergedCutGroups.Batch005.populationMatches63 MergedCutGroups.Batch005.populationMatches64
    PopulationCertificates.Batch002.valid42 PopulationCertificates.Batch002.sound42 WitnessCertificates.Batch002.valid42 WitnessCertificates.Batch002.sound42 CountingCertificates.Batch002.valid42 CountingCertificates.Batch002.sound42
    CutLabelCertificates.Entropy001.valid22 CutLabelCertificates.Minority001.valid21 CutLabelCertificates.Minority001.sound21 H st hI
theorem probabilityBound21 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch005.certificate63).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate42).dm (WitnessCertificates.Batch002.certificate42).beta) ≤ ((CutFailureCertificates.Budget002.certificate42).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound42 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate42).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch005.certificate63).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch005.certificate64).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch002.certificate42).omega:ℝ) ≤ ((CutFailureCertificates.Budget002.certificate42).bound:ℝ) at hb
  exact (exponentialBound21 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches22 : (MergedCutGroups.Batch005.certificate66).GlobalMatches MergedCutGroups.Batch005.certificate67 CountingCertificates.Batch002.certificate44 CutLabelCertificates.Entropy001.certificate23 CutLabelCertificates.Minority001.certificate22 := by decide +kernel
theorem exponentialBound22 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch005.certificate66).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate44).dm (WitnessCertificates.Batch002.certificate44).beta) ≤ (2*exp (-((CountingCertificates.Batch002.certificate44).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch005.certificate66).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch005.certificate67).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch002.certificate44).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch005.certificate66 MergedCutGroups.Batch005.certificate67 CountingCertificates.Batch002.certificate44 CutLabelCertificates.Entropy001.certificate23 CutLabelCertificates.Minority001.certificate22 matches22 rfl rfl
    MergedCutGroups.Batch005.numericValid66 MergedCutGroups.Batch005.numericValid67 MergedCutGroups.Batch005.cellsSound66 MergedCutGroups.Batch005.cellsSound67
    MergedCutGroups.Batch005.cellsNumeric66 MergedCutGroups.Batch005.cellsNumeric67 MergedCutGroups.Batch005.populationMatches66 MergedCutGroups.Batch005.populationMatches67
    PopulationCertificates.Batch002.valid44 PopulationCertificates.Batch002.sound44 WitnessCertificates.Batch002.valid44 WitnessCertificates.Batch002.sound44 CountingCertificates.Batch002.valid44 CountingCertificates.Batch002.sound44
    CutLabelCertificates.Entropy001.valid23 CutLabelCertificates.Minority001.valid22 CutLabelCertificates.Minority001.sound22 H st hI
theorem probabilityBound22 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch005.certificate66).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate44).dm (WitnessCertificates.Batch002.certificate44).beta) ≤ ((CutFailureCertificates.Budget002.certificate44).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound44 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate44).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch005.certificate66).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch005.certificate67).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch002.certificate44).omega:ℝ) ≤ ((CutFailureCertificates.Budget002.certificate44).bound:ℝ) at hb
  exact (exponentialBound22 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches23 : (MergedCutGroups.Batch005.certificate69).GlobalMatches MergedCutGroups.Batch005.certificate70 CountingCertificates.Batch002.certificate46 CutLabelCertificates.Entropy001.certificate24 CutLabelCertificates.Minority001.certificate23 := by decide +kernel
theorem exponentialBound23 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch005.certificate69).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate46).dm (WitnessCertificates.Batch002.certificate46).beta) ≤ (2*exp (-((CountingCertificates.Batch002.certificate46).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch005.certificate69).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch005.certificate70).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch002.certificate46).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch005.certificate69 MergedCutGroups.Batch005.certificate70 CountingCertificates.Batch002.certificate46 CutLabelCertificates.Entropy001.certificate24 CutLabelCertificates.Minority001.certificate23 matches23 rfl rfl
    MergedCutGroups.Batch005.numericValid69 MergedCutGroups.Batch005.numericValid70 MergedCutGroups.Batch005.cellsSound69 MergedCutGroups.Batch005.cellsSound70
    MergedCutGroups.Batch005.cellsNumeric69 MergedCutGroups.Batch005.cellsNumeric70 MergedCutGroups.Batch005.populationMatches69 MergedCutGroups.Batch005.populationMatches70
    PopulationCertificates.Batch002.valid46 PopulationCertificates.Batch002.sound46 WitnessCertificates.Batch002.valid46 WitnessCertificates.Batch002.sound46 CountingCertificates.Batch002.valid46 CountingCertificates.Batch002.sound46
    CutLabelCertificates.Entropy001.valid24 CutLabelCertificates.Minority001.valid23 CutLabelCertificates.Minority001.sound23 H st hI
theorem probabilityBound23 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch005.certificate69).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate46).dm (WitnessCertificates.Batch002.certificate46).beta) ≤ ((CutFailureCertificates.Budget002.certificate46).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound46 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate46).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch005.certificate69).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch005.certificate70).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch002.certificate46).omega:ℝ) ≤ ((CutFailureCertificates.Budget002.certificate46).bound:ℝ) at hb
  exact (exponentialBound23 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches24 : (MergedCutGroups.Batch006.certificate72).GlobalMatches MergedCutGroups.Batch006.certificate73 CountingCertificates.Batch002.certificate48 CutLabelCertificates.Entropy001.certificate25 CutLabelCertificates.Minority001.certificate24 := by decide +kernel
theorem exponentialBound24 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch006.certificate72).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate48).dm (WitnessCertificates.Batch002.certificate48).beta) ≤ (2*exp (-((CountingCertificates.Batch002.certificate48).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch006.certificate72).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch006.certificate73).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch002.certificate48).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch006.certificate72 MergedCutGroups.Batch006.certificate73 CountingCertificates.Batch002.certificate48 CutLabelCertificates.Entropy001.certificate25 CutLabelCertificates.Minority001.certificate24 matches24 rfl rfl
    MergedCutGroups.Batch006.numericValid72 MergedCutGroups.Batch006.numericValid73 MergedCutGroups.Batch006.cellsSound72 MergedCutGroups.Batch006.cellsSound73
    MergedCutGroups.Batch006.cellsNumeric72 MergedCutGroups.Batch006.cellsNumeric73 MergedCutGroups.Batch006.populationMatches72 MergedCutGroups.Batch006.populationMatches73
    PopulationCertificates.Batch002.valid48 PopulationCertificates.Batch002.sound48 WitnessCertificates.Batch002.valid48 WitnessCertificates.Batch002.sound48 CountingCertificates.Batch002.valid48 CountingCertificates.Batch002.sound48
    CutLabelCertificates.Entropy001.valid25 CutLabelCertificates.Minority001.valid24 CutLabelCertificates.Minority001.sound24 H st hI
theorem probabilityBound24 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch006.certificate72).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate48).dm (WitnessCertificates.Batch002.certificate48).beta) ≤ ((CutFailureCertificates.Budget002.certificate48).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound48 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate48).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch006.certificate72).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch006.certificate73).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch002.certificate48).omega:ℝ) ≤ ((CutFailureCertificates.Budget002.certificate48).bound:ℝ) at hb
  exact (exponentialBound24 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches25 : (MergedCutGroups.Batch006.certificate75).GlobalMatches MergedCutGroups.Batch006.certificate76 CountingCertificates.Batch002.certificate50 CutLabelCertificates.Entropy001.certificate26 CutLabelCertificates.Minority001.certificate25 := by decide +kernel
theorem exponentialBound25 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch006.certificate75).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate50).dm (WitnessCertificates.Batch002.certificate50).beta) ≤ (2*exp (-((CountingCertificates.Batch002.certificate50).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch006.certificate75).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch006.certificate76).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch002.certificate50).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch006.certificate75 MergedCutGroups.Batch006.certificate76 CountingCertificates.Batch002.certificate50 CutLabelCertificates.Entropy001.certificate26 CutLabelCertificates.Minority001.certificate25 matches25 rfl rfl
    MergedCutGroups.Batch006.numericValid75 MergedCutGroups.Batch006.numericValid76 MergedCutGroups.Batch006.cellsSound75 MergedCutGroups.Batch006.cellsSound76
    MergedCutGroups.Batch006.cellsNumeric75 MergedCutGroups.Batch006.cellsNumeric76 MergedCutGroups.Batch006.populationMatches75 MergedCutGroups.Batch006.populationMatches76
    PopulationCertificates.Batch002.valid50 PopulationCertificates.Batch002.sound50 WitnessCertificates.Batch002.valid50 WitnessCertificates.Batch002.sound50 CountingCertificates.Batch002.valid50 CountingCertificates.Batch002.sound50
    CutLabelCertificates.Entropy001.valid26 CutLabelCertificates.Minority001.valid25 CutLabelCertificates.Minority001.sound25 H st hI
theorem probabilityBound25 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch006.certificate75).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate50).dm (WitnessCertificates.Batch002.certificate50).beta) ≤ ((CutFailureCertificates.Budget002.certificate50).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound50 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate50).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch006.certificate75).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch006.certificate76).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch002.certificate50).omega:ℝ) ≤ ((CutFailureCertificates.Budget002.certificate50).bound:ℝ) at hb
  exact (exponentialBound25 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches26 : (MergedCutGroups.Batch006.certificate78).GlobalMatches MergedCutGroups.Batch006.certificate79 CountingCertificates.Batch002.certificate52 CutLabelCertificates.Entropy001.certificate27 CutLabelCertificates.Minority001.certificate26 := by decide +kernel
theorem exponentialBound26 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch006.certificate78).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate52).dm (WitnessCertificates.Batch002.certificate52).beta) ≤ (2*exp (-((CountingCertificates.Batch002.certificate52).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch006.certificate78).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch006.certificate79).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch002.certificate52).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch006.certificate78 MergedCutGroups.Batch006.certificate79 CountingCertificates.Batch002.certificate52 CutLabelCertificates.Entropy001.certificate27 CutLabelCertificates.Minority001.certificate26 matches26 rfl rfl
    MergedCutGroups.Batch006.numericValid78 MergedCutGroups.Batch006.numericValid79 MergedCutGroups.Batch006.cellsSound78 MergedCutGroups.Batch006.cellsSound79
    MergedCutGroups.Batch006.cellsNumeric78 MergedCutGroups.Batch006.cellsNumeric79 MergedCutGroups.Batch006.populationMatches78 MergedCutGroups.Batch006.populationMatches79
    PopulationCertificates.Batch002.valid52 PopulationCertificates.Batch002.sound52 WitnessCertificates.Batch002.valid52 WitnessCertificates.Batch002.sound52 CountingCertificates.Batch002.valid52 CountingCertificates.Batch002.sound52
    CutLabelCertificates.Entropy001.valid27 CutLabelCertificates.Minority001.valid26 CutLabelCertificates.Minority001.sound26 H st hI
theorem probabilityBound26 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch006.certificate78).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate52).dm (WitnessCertificates.Batch002.certificate52).beta) ≤ ((CutFailureCertificates.Budget002.certificate52).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound52 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate52).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch006.certificate78).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch006.certificate79).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch002.certificate52).omega:ℝ) ≤ ((CutFailureCertificates.Budget002.certificate52).bound:ℝ) at hb
  exact (exponentialBound26 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches27 : (MergedCutGroups.Batch006.certificate81).GlobalMatches MergedCutGroups.Batch006.certificate82 CountingCertificates.Batch002.certificate54 CutLabelCertificates.Entropy001.certificate28 CutLabelCertificates.Minority001.certificate27 := by decide +kernel
theorem exponentialBound27 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch006.certificate81).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate54).dm (WitnessCertificates.Batch002.certificate54).beta) ≤ (2*exp (-((CountingCertificates.Batch002.certificate54).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch006.certificate81).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch006.certificate82).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch002.certificate54).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch006.certificate81 MergedCutGroups.Batch006.certificate82 CountingCertificates.Batch002.certificate54 CutLabelCertificates.Entropy001.certificate28 CutLabelCertificates.Minority001.certificate27 matches27 rfl rfl
    MergedCutGroups.Batch006.numericValid81 MergedCutGroups.Batch006.numericValid82 MergedCutGroups.Batch006.cellsSound81 MergedCutGroups.Batch006.cellsSound82
    MergedCutGroups.Batch006.cellsNumeric81 MergedCutGroups.Batch006.cellsNumeric82 MergedCutGroups.Batch006.populationMatches81 MergedCutGroups.Batch006.populationMatches82
    PopulationCertificates.Batch002.valid54 PopulationCertificates.Batch002.sound54 WitnessCertificates.Batch002.valid54 WitnessCertificates.Batch002.sound54 CountingCertificates.Batch002.valid54 CountingCertificates.Batch002.sound54
    CutLabelCertificates.Entropy001.valid28 CutLabelCertificates.Minority001.valid27 CutLabelCertificates.Minority001.sound27 H st hI
theorem probabilityBound27 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch006.certificate81).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate54).dm (WitnessCertificates.Batch002.certificate54).beta) ≤ ((CutFailureCertificates.Budget002.certificate54).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound54 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate54).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch006.certificate81).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch006.certificate82).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch002.certificate54).omega:ℝ) ≤ ((CutFailureCertificates.Budget002.certificate54).bound:ℝ) at hb
  exact (exponentialBound27 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches28 : (MergedCutGroups.Batch007.certificate84).GlobalMatches MergedCutGroups.Batch007.certificate85 CountingCertificates.Batch002.certificate56 CutLabelCertificates.Entropy001.certificate29 CutLabelCertificates.Minority001.certificate28 := by decide +kernel
theorem exponentialBound28 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch007.certificate84).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate56).dm (WitnessCertificates.Batch002.certificate56).beta) ≤ (2*exp (-((CountingCertificates.Batch002.certificate56).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch007.certificate84).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch007.certificate85).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch002.certificate56).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch007.certificate84 MergedCutGroups.Batch007.certificate85 CountingCertificates.Batch002.certificate56 CutLabelCertificates.Entropy001.certificate29 CutLabelCertificates.Minority001.certificate28 matches28 rfl rfl
    MergedCutGroups.Batch007.numericValid84 MergedCutGroups.Batch007.numericValid85 MergedCutGroups.Batch007.cellsSound84 MergedCutGroups.Batch007.cellsSound85
    MergedCutGroups.Batch007.cellsNumeric84 MergedCutGroups.Batch007.cellsNumeric85 MergedCutGroups.Batch007.populationMatches84 MergedCutGroups.Batch007.populationMatches85
    PopulationCertificates.Batch002.valid56 PopulationCertificates.Batch002.sound56 WitnessCertificates.Batch002.valid56 WitnessCertificates.Batch002.sound56 CountingCertificates.Batch002.valid56 CountingCertificates.Batch002.sound56
    CutLabelCertificates.Entropy001.valid29 CutLabelCertificates.Minority001.valid28 CutLabelCertificates.Minority001.sound28 H st hI
theorem probabilityBound28 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch007.certificate84).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate56).dm (WitnessCertificates.Batch002.certificate56).beta) ≤ ((CutFailureCertificates.Budget002.certificate56).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound56 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate56).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch007.certificate84).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch007.certificate85).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch002.certificate56).omega:ℝ) ≤ ((CutFailureCertificates.Budget002.certificate56).bound:ℝ) at hb
  exact (exponentialBound28 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches29 : (MergedCutGroups.Batch007.certificate87).GlobalMatches MergedCutGroups.Batch007.certificate88 CountingCertificates.Batch002.certificate58 CutLabelCertificates.Entropy001.certificate30 CutLabelCertificates.Minority001.certificate29 := by decide +kernel
theorem exponentialBound29 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch007.certificate87).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate58).dm (WitnessCertificates.Batch002.certificate58).beta) ≤ (2*exp (-((CountingCertificates.Batch002.certificate58).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch007.certificate87).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch007.certificate88).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch002.certificate58).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch007.certificate87 MergedCutGroups.Batch007.certificate88 CountingCertificates.Batch002.certificate58 CutLabelCertificates.Entropy001.certificate30 CutLabelCertificates.Minority001.certificate29 matches29 rfl rfl
    MergedCutGroups.Batch007.numericValid87 MergedCutGroups.Batch007.numericValid88 MergedCutGroups.Batch007.cellsSound87 MergedCutGroups.Batch007.cellsSound88
    MergedCutGroups.Batch007.cellsNumeric87 MergedCutGroups.Batch007.cellsNumeric88 MergedCutGroups.Batch007.populationMatches87 MergedCutGroups.Batch007.populationMatches88
    PopulationCertificates.Batch002.valid58 PopulationCertificates.Batch002.sound58 WitnessCertificates.Batch002.valid58 WitnessCertificates.Batch002.sound58 CountingCertificates.Batch002.valid58 CountingCertificates.Batch002.sound58
    CutLabelCertificates.Entropy001.valid30 CutLabelCertificates.Minority001.valid29 CutLabelCertificates.Minority001.sound29 H st hI
theorem probabilityBound29 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch007.certificate87).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch002.certificate58).dm (WitnessCertificates.Batch002.certificate58).beta) ≤ ((CutFailureCertificates.Budget002.certificate58).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound58 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate58).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch007.certificate87).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch007.certificate88).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch002.certificate58).omega:ℝ) ≤ ((CutFailureCertificates.Budget002.certificate58).bound:ℝ) at hb
  exact (exponentialBound29 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches30 : (MergedCutGroups.Batch007.certificate90).GlobalMatches MergedCutGroups.Batch007.certificate91 CountingCertificates.Batch003.certificate60 CutLabelCertificates.Entropy001.certificate31 CutLabelCertificates.Minority001.certificate30 := by decide +kernel
theorem exponentialBound30 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch007.certificate90).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate60).dm (WitnessCertificates.Batch003.certificate60).beta) ≤ (2*exp (-((CountingCertificates.Batch003.certificate60).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch007.certificate90).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch007.certificate91).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch003.certificate60).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch007.certificate90 MergedCutGroups.Batch007.certificate91 CountingCertificates.Batch003.certificate60 CutLabelCertificates.Entropy001.certificate31 CutLabelCertificates.Minority001.certificate30 matches30 rfl rfl
    MergedCutGroups.Batch007.numericValid90 MergedCutGroups.Batch007.numericValid91 MergedCutGroups.Batch007.cellsSound90 MergedCutGroups.Batch007.cellsSound91
    MergedCutGroups.Batch007.cellsNumeric90 MergedCutGroups.Batch007.cellsNumeric91 MergedCutGroups.Batch007.populationMatches90 MergedCutGroups.Batch007.populationMatches91
    PopulationCertificates.Batch003.valid60 PopulationCertificates.Batch003.sound60 WitnessCertificates.Batch003.valid60 WitnessCertificates.Batch003.sound60 CountingCertificates.Batch003.valid60 CountingCertificates.Batch003.sound60
    CutLabelCertificates.Entropy001.valid31 CutLabelCertificates.Minority001.valid30 CutLabelCertificates.Minority001.sound30 H st hI
theorem probabilityBound30 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch007.certificate90).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate60).dm (WitnessCertificates.Batch003.certificate60).beta) ≤ ((CutFailureCertificates.Budget003.certificate60).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound60 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate60).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch007.certificate90).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch007.certificate91).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch003.certificate60).omega:ℝ) ≤ ((CutFailureCertificates.Budget003.certificate60).bound:ℝ) at hb
  exact (exponentialBound30 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches31 : (MergedCutGroups.Batch007.certificate93).GlobalMatches MergedCutGroups.Batch007.certificate94 CountingCertificates.Batch003.certificate62 CutLabelCertificates.Entropy001.certificate32 CutLabelCertificates.Minority001.certificate31 := by decide +kernel
theorem exponentialBound31 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch007.certificate93).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate62).dm (WitnessCertificates.Batch003.certificate62).beta) ≤ (2*exp (-((CountingCertificates.Batch003.certificate62).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch007.certificate93).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch007.certificate94).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch003.certificate62).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch007.certificate93 MergedCutGroups.Batch007.certificate94 CountingCertificates.Batch003.certificate62 CutLabelCertificates.Entropy001.certificate32 CutLabelCertificates.Minority001.certificate31 matches31 rfl rfl
    MergedCutGroups.Batch007.numericValid93 MergedCutGroups.Batch007.numericValid94 MergedCutGroups.Batch007.cellsSound93 MergedCutGroups.Batch007.cellsSound94
    MergedCutGroups.Batch007.cellsNumeric93 MergedCutGroups.Batch007.cellsNumeric94 MergedCutGroups.Batch007.populationMatches93 MergedCutGroups.Batch007.populationMatches94
    PopulationCertificates.Batch003.valid62 PopulationCertificates.Batch003.sound62 WitnessCertificates.Batch003.valid62 WitnessCertificates.Batch003.sound62 CountingCertificates.Batch003.valid62 CountingCertificates.Batch003.sound62
    CutLabelCertificates.Entropy001.valid32 CutLabelCertificates.Minority001.valid31 CutLabelCertificates.Minority001.sound31 H st hI
theorem probabilityBound31 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch007.certificate93).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate62).dm (WitnessCertificates.Batch003.certificate62).beta) ≤ ((CutFailureCertificates.Budget003.certificate62).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound62 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate62).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch007.certificate93).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch007.certificate94).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch003.certificate62).omega:ℝ) ≤ ((CutFailureCertificates.Budget003.certificate62).bound:ℝ) at hb
  exact (exponentialBound31 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches32 : (MergedCutGroups.Batch008.certificate96).GlobalMatches MergedCutGroups.Batch008.certificate97 CountingCertificates.Batch003.certificate64 CutLabelCertificates.Entropy001.certificate33 CutLabelCertificates.Minority001.certificate32 := by decide +kernel
theorem exponentialBound32 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch008.certificate96).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate64).dm (WitnessCertificates.Batch003.certificate64).beta) ≤ (2*exp (-((CountingCertificates.Batch003.certificate64).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch008.certificate96).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch008.certificate97).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch003.certificate64).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch008.certificate96 MergedCutGroups.Batch008.certificate97 CountingCertificates.Batch003.certificate64 CutLabelCertificates.Entropy001.certificate33 CutLabelCertificates.Minority001.certificate32 matches32 rfl rfl
    MergedCutGroups.Batch008.numericValid96 MergedCutGroups.Batch008.numericValid97 MergedCutGroups.Batch008.cellsSound96 MergedCutGroups.Batch008.cellsSound97
    MergedCutGroups.Batch008.cellsNumeric96 MergedCutGroups.Batch008.cellsNumeric97 MergedCutGroups.Batch008.populationMatches96 MergedCutGroups.Batch008.populationMatches97
    PopulationCertificates.Batch003.valid64 PopulationCertificates.Batch003.sound64 WitnessCertificates.Batch003.valid64 WitnessCertificates.Batch003.sound64 CountingCertificates.Batch003.valid64 CountingCertificates.Batch003.sound64
    CutLabelCertificates.Entropy001.valid33 CutLabelCertificates.Minority001.valid32 CutLabelCertificates.Minority001.sound32 H st hI
theorem probabilityBound32 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch008.certificate96).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate64).dm (WitnessCertificates.Batch003.certificate64).beta) ≤ ((CutFailureCertificates.Budget003.certificate64).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound64 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate64).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch008.certificate96).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch008.certificate97).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch003.certificate64).omega:ℝ) ≤ ((CutFailureCertificates.Budget003.certificate64).bound:ℝ) at hb
  exact (exponentialBound32 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches33 : (MergedCutGroups.Batch008.certificate99).GlobalMatches MergedCutGroups.Batch008.certificate100 CountingCertificates.Batch003.certificate66 CutLabelCertificates.Entropy001.certificate34 CutLabelCertificates.Minority001.certificate33 := by decide +kernel
theorem exponentialBound33 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch008.certificate99).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate66).dm (WitnessCertificates.Batch003.certificate66).beta) ≤ (2*exp (-((CountingCertificates.Batch003.certificate66).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch008.certificate99).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch008.certificate100).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch003.certificate66).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch008.certificate99 MergedCutGroups.Batch008.certificate100 CountingCertificates.Batch003.certificate66 CutLabelCertificates.Entropy001.certificate34 CutLabelCertificates.Minority001.certificate33 matches33 rfl rfl
    MergedCutGroups.Batch008.numericValid99 MergedCutGroups.Batch008.numericValid100 MergedCutGroups.Batch008.cellsSound99 MergedCutGroups.Batch008.cellsSound100
    MergedCutGroups.Batch008.cellsNumeric99 MergedCutGroups.Batch008.cellsNumeric100 MergedCutGroups.Batch008.populationMatches99 MergedCutGroups.Batch008.populationMatches100
    PopulationCertificates.Batch003.valid66 PopulationCertificates.Batch003.sound66 WitnessCertificates.Batch003.valid66 WitnessCertificates.Batch003.sound66 CountingCertificates.Batch003.valid66 CountingCertificates.Batch003.sound66
    CutLabelCertificates.Entropy001.valid34 CutLabelCertificates.Minority001.valid33 CutLabelCertificates.Minority001.sound33 H st hI
theorem probabilityBound33 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch008.certificate99).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate66).dm (WitnessCertificates.Batch003.certificate66).beta) ≤ ((CutFailureCertificates.Budget003.certificate66).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound66 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate66).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch008.certificate99).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch008.certificate100).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch003.certificate66).omega:ℝ) ≤ ((CutFailureCertificates.Budget003.certificate66).bound:ℝ) at hb
  exact (exponentialBound33 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches34 : (MergedCutGroups.Batch008.certificate102).GlobalMatches MergedCutGroups.Batch008.certificate103 CountingCertificates.Batch003.certificate68 CutLabelCertificates.Entropy001.certificate35 CutLabelCertificates.Minority001.certificate34 := by decide +kernel
theorem exponentialBound34 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch008.certificate102).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate68).dm (WitnessCertificates.Batch003.certificate68).beta) ≤ (2*exp (-((CountingCertificates.Batch003.certificate68).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch008.certificate102).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch008.certificate103).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch003.certificate68).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch008.certificate102 MergedCutGroups.Batch008.certificate103 CountingCertificates.Batch003.certificate68 CutLabelCertificates.Entropy001.certificate35 CutLabelCertificates.Minority001.certificate34 matches34 rfl rfl
    MergedCutGroups.Batch008.numericValid102 MergedCutGroups.Batch008.numericValid103 MergedCutGroups.Batch008.cellsSound102 MergedCutGroups.Batch008.cellsSound103
    MergedCutGroups.Batch008.cellsNumeric102 MergedCutGroups.Batch008.cellsNumeric103 MergedCutGroups.Batch008.populationMatches102 MergedCutGroups.Batch008.populationMatches103
    PopulationCertificates.Batch003.valid68 PopulationCertificates.Batch003.sound68 WitnessCertificates.Batch003.valid68 WitnessCertificates.Batch003.sound68 CountingCertificates.Batch003.valid68 CountingCertificates.Batch003.sound68
    CutLabelCertificates.Entropy001.valid35 CutLabelCertificates.Minority001.valid34 CutLabelCertificates.Minority001.sound34 H st hI
theorem probabilityBound34 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch008.certificate102).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate68).dm (WitnessCertificates.Batch003.certificate68).beta) ≤ ((CutFailureCertificates.Budget003.certificate68).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound68 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate68).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch008.certificate102).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch008.certificate103).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch003.certificate68).omega:ℝ) ≤ ((CutFailureCertificates.Budget003.certificate68).bound:ℝ) at hb
  exact (exponentialBound34 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches35 : (MergedCutGroups.Batch008.certificate105).GlobalMatches MergedCutGroups.Batch008.certificate106 CountingCertificates.Batch003.certificate70 CutLabelCertificates.Entropy001.certificate36 CutLabelCertificates.Minority001.certificate35 := by decide +kernel
theorem exponentialBound35 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch008.certificate105).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate70).dm (WitnessCertificates.Batch003.certificate70).beta) ≤ (2*exp (-((CountingCertificates.Batch003.certificate70).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch008.certificate105).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch008.certificate106).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch003.certificate70).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch008.certificate105 MergedCutGroups.Batch008.certificate106 CountingCertificates.Batch003.certificate70 CutLabelCertificates.Entropy001.certificate36 CutLabelCertificates.Minority001.certificate35 matches35 rfl rfl
    MergedCutGroups.Batch008.numericValid105 MergedCutGroups.Batch008.numericValid106 MergedCutGroups.Batch008.cellsSound105 MergedCutGroups.Batch008.cellsSound106
    MergedCutGroups.Batch008.cellsNumeric105 MergedCutGroups.Batch008.cellsNumeric106 MergedCutGroups.Batch008.populationMatches105 MergedCutGroups.Batch008.populationMatches106
    PopulationCertificates.Batch003.valid70 PopulationCertificates.Batch003.sound70 WitnessCertificates.Batch003.valid70 WitnessCertificates.Batch003.sound70 CountingCertificates.Batch003.valid70 CountingCertificates.Batch003.sound70
    CutLabelCertificates.Entropy001.valid36 CutLabelCertificates.Minority001.valid35 CutLabelCertificates.Minority001.sound35 H st hI
theorem probabilityBound35 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch008.certificate105).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate70).dm (WitnessCertificates.Batch003.certificate70).beta) ≤ ((CutFailureCertificates.Budget003.certificate70).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound70 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate70).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch008.certificate105).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch008.certificate106).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch003.certificate70).omega:ℝ) ≤ ((CutFailureCertificates.Budget003.certificate70).bound:ℝ) at hb
  exact (exponentialBound35 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches36 : (MergedCutGroups.Batch009.certificate108).GlobalMatches MergedCutGroups.Batch009.certificate109 CountingCertificates.Batch003.certificate72 CutLabelCertificates.Entropy001.certificate37 CutLabelCertificates.Minority001.certificate36 := by decide +kernel
theorem exponentialBound36 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch009.certificate108).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate72).dm (WitnessCertificates.Batch003.certificate72).beta) ≤ (2*exp (-((CountingCertificates.Batch003.certificate72).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch009.certificate108).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch009.certificate109).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch003.certificate72).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch009.certificate108 MergedCutGroups.Batch009.certificate109 CountingCertificates.Batch003.certificate72 CutLabelCertificates.Entropy001.certificate37 CutLabelCertificates.Minority001.certificate36 matches36 rfl rfl
    MergedCutGroups.Batch009.numericValid108 MergedCutGroups.Batch009.numericValid109 MergedCutGroups.Batch009.cellsSound108 MergedCutGroups.Batch009.cellsSound109
    MergedCutGroups.Batch009.cellsNumeric108 MergedCutGroups.Batch009.cellsNumeric109 MergedCutGroups.Batch009.populationMatches108 MergedCutGroups.Batch009.populationMatches109
    PopulationCertificates.Batch003.valid72 PopulationCertificates.Batch003.sound72 WitnessCertificates.Batch003.valid72 WitnessCertificates.Batch003.sound72 CountingCertificates.Batch003.valid72 CountingCertificates.Batch003.sound72
    CutLabelCertificates.Entropy001.valid37 CutLabelCertificates.Minority001.valid36 CutLabelCertificates.Minority001.sound36 H st hI
theorem probabilityBound36 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch009.certificate108).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate72).dm (WitnessCertificates.Batch003.certificate72).beta) ≤ ((CutFailureCertificates.Budget003.certificate72).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound72 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate72).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch009.certificate108).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch009.certificate109).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch003.certificate72).omega:ℝ) ≤ ((CutFailureCertificates.Budget003.certificate72).bound:ℝ) at hb
  exact (exponentialBound36 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches37 : (MergedCutGroups.Batch009.certificate111).GlobalMatches MergedCutGroups.Batch009.certificate112 CountingCertificates.Batch003.certificate74 CutLabelCertificates.Entropy001.certificate38 CutLabelCertificates.Minority001.certificate37 := by decide +kernel
theorem exponentialBound37 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch009.certificate111).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate74).dm (WitnessCertificates.Batch003.certificate74).beta) ≤ (2*exp (-((CountingCertificates.Batch003.certificate74).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch009.certificate111).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch009.certificate112).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch003.certificate74).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch009.certificate111 MergedCutGroups.Batch009.certificate112 CountingCertificates.Batch003.certificate74 CutLabelCertificates.Entropy001.certificate38 CutLabelCertificates.Minority001.certificate37 matches37 rfl rfl
    MergedCutGroups.Batch009.numericValid111 MergedCutGroups.Batch009.numericValid112 MergedCutGroups.Batch009.cellsSound111 MergedCutGroups.Batch009.cellsSound112
    MergedCutGroups.Batch009.cellsNumeric111 MergedCutGroups.Batch009.cellsNumeric112 MergedCutGroups.Batch009.populationMatches111 MergedCutGroups.Batch009.populationMatches112
    PopulationCertificates.Batch003.valid74 PopulationCertificates.Batch003.sound74 WitnessCertificates.Batch003.valid74 WitnessCertificates.Batch003.sound74 CountingCertificates.Batch003.valid74 CountingCertificates.Batch003.sound74
    CutLabelCertificates.Entropy001.valid38 CutLabelCertificates.Minority001.valid37 CutLabelCertificates.Minority001.sound37 H st hI
theorem probabilityBound37 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch009.certificate111).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate74).dm (WitnessCertificates.Batch003.certificate74).beta) ≤ ((CutFailureCertificates.Budget003.certificate74).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound74 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate74).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch009.certificate111).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch009.certificate112).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch003.certificate74).omega:ℝ) ≤ ((CutFailureCertificates.Budget003.certificate74).bound:ℝ) at hb
  exact (exponentialBound37 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches38 : (MergedCutGroups.Batch009.certificate114).GlobalMatches MergedCutGroups.Batch009.certificate115 CountingCertificates.Batch003.certificate76 CutLabelCertificates.Entropy001.certificate39 CutLabelCertificates.Minority001.certificate38 := by decide +kernel
theorem exponentialBound38 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch009.certificate114).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate76).dm (WitnessCertificates.Batch003.certificate76).beta) ≤ (2*exp (-((CountingCertificates.Batch003.certificate76).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch009.certificate114).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch009.certificate115).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch003.certificate76).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch009.certificate114 MergedCutGroups.Batch009.certificate115 CountingCertificates.Batch003.certificate76 CutLabelCertificates.Entropy001.certificate39 CutLabelCertificates.Minority001.certificate38 matches38 rfl rfl
    MergedCutGroups.Batch009.numericValid114 MergedCutGroups.Batch009.numericValid115 MergedCutGroups.Batch009.cellsSound114 MergedCutGroups.Batch009.cellsSound115
    MergedCutGroups.Batch009.cellsNumeric114 MergedCutGroups.Batch009.cellsNumeric115 MergedCutGroups.Batch009.populationMatches114 MergedCutGroups.Batch009.populationMatches115
    PopulationCertificates.Batch003.valid76 PopulationCertificates.Batch003.sound76 WitnessCertificates.Batch003.valid76 WitnessCertificates.Batch003.sound76 CountingCertificates.Batch003.valid76 CountingCertificates.Batch003.sound76
    CutLabelCertificates.Entropy001.valid39 CutLabelCertificates.Minority001.valid38 CutLabelCertificates.Minority001.sound38 H st hI
theorem probabilityBound38 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch009.certificate114).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate76).dm (WitnessCertificates.Batch003.certificate76).beta) ≤ ((CutFailureCertificates.Budget003.certificate76).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound76 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate76).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch009.certificate114).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch009.certificate115).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch003.certificate76).omega:ℝ) ≤ ((CutFailureCertificates.Budget003.certificate76).bound:ℝ) at hb
  exact (exponentialBound38 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches39 : (MergedCutGroups.Batch009.certificate117).GlobalMatches MergedCutGroups.Batch009.certificate118 CountingCertificates.Batch003.certificate78 CutLabelCertificates.Entropy002.certificate40 CutLabelCertificates.Minority001.certificate39 := by decide +kernel
theorem exponentialBound39 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch009.certificate117).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate78).dm (WitnessCertificates.Batch003.certificate78).beta) ≤ (2*exp (-((CountingCertificates.Batch003.certificate78).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch009.certificate117).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch009.certificate118).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch003.certificate78).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch009.certificate117 MergedCutGroups.Batch009.certificate118 CountingCertificates.Batch003.certificate78 CutLabelCertificates.Entropy002.certificate40 CutLabelCertificates.Minority001.certificate39 matches39 rfl rfl
    MergedCutGroups.Batch009.numericValid117 MergedCutGroups.Batch009.numericValid118 MergedCutGroups.Batch009.cellsSound117 MergedCutGroups.Batch009.cellsSound118
    MergedCutGroups.Batch009.cellsNumeric117 MergedCutGroups.Batch009.cellsNumeric118 MergedCutGroups.Batch009.populationMatches117 MergedCutGroups.Batch009.populationMatches118
    PopulationCertificates.Batch003.valid78 PopulationCertificates.Batch003.sound78 WitnessCertificates.Batch003.valid78 WitnessCertificates.Batch003.sound78 CountingCertificates.Batch003.valid78 CountingCertificates.Batch003.sound78
    CutLabelCertificates.Entropy002.valid40 CutLabelCertificates.Minority001.valid39 CutLabelCertificates.Minority001.sound39 H st hI
theorem probabilityBound39 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch009.certificate117).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch003.certificate78).dm (WitnessCertificates.Batch003.certificate78).beta) ≤ ((CutFailureCertificates.Budget003.certificate78).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound78 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate78).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch009.certificate117).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch009.certificate118).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch003.certificate78).omega:ℝ) ≤ ((CutFailureCertificates.Budget003.certificate78).bound:ℝ) at hb
  exact (exponentialBound39 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch001
