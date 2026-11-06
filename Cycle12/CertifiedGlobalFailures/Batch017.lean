import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch034
import Cycle12.CountingCertificates.Batch035
import Cycle12.CutFailureCertificates.Budget034
import Cycle12.CutFailureCertificates.Budget035
import Cycle12.CutLabelCertificates.Entropy017
import Cycle12.CutLabelCertificates.Entropy018
import Cycle12.CutLabelCertificates.Minority017
import Cycle12.MergedCutGroups.Batch085
import Cycle12.MergedCutGroups.Batch086
import Cycle12.MergedCutGroups.Batch087
import Cycle12.MergedCutGroups.Batch088
import Cycle12.MergedCutGroups.Batch089
import Cycle12.PopulationCertificates.Batch034
import Cycle12.PopulationCertificates.Batch035
import Cycle12.WitnessCertificates.Batch034
import Cycle12.WitnessCertificates.Batch035

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch017
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches340 : (MergedCutGroups.Batch085.certificate1020).GlobalMatches MergedCutGroups.Batch085.certificate1021 CountingCertificates.Batch034.certificate680 CutLabelCertificates.Entropy017.certificate341 CutLabelCertificates.Minority017.certificate340 := by decide +kernel
theorem exponentialBound340 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch085.certificate1020).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate680).dm (WitnessCertificates.Batch034.certificate680).beta) ≤ (2*exp (-((CountingCertificates.Batch034.certificate680).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch085.certificate1020).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch085.certificate1021).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch034.certificate680).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch085.certificate1020 MergedCutGroups.Batch085.certificate1021 CountingCertificates.Batch034.certificate680 CutLabelCertificates.Entropy017.certificate341 CutLabelCertificates.Minority017.certificate340 matches340 rfl rfl
    MergedCutGroups.Batch085.numericValid1020 MergedCutGroups.Batch085.numericValid1021 MergedCutGroups.Batch085.cellsSound1020 MergedCutGroups.Batch085.cellsSound1021
    MergedCutGroups.Batch085.cellsNumeric1020 MergedCutGroups.Batch085.cellsNumeric1021 MergedCutGroups.Batch085.populationMatches1020 MergedCutGroups.Batch085.populationMatches1021
    PopulationCertificates.Batch034.valid680 PopulationCertificates.Batch034.sound680 WitnessCertificates.Batch034.valid680 WitnessCertificates.Batch034.sound680 CountingCertificates.Batch034.valid680 CountingCertificates.Batch034.sound680
    CutLabelCertificates.Entropy017.valid341 CutLabelCertificates.Minority017.valid340 CutLabelCertificates.Minority017.sound340 H st hI
theorem probabilityBound340 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch085.certificate1020).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate680).dm (WitnessCertificates.Batch034.certificate680).beta) ≤ ((CutFailureCertificates.Budget034.certificate680).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound680 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate680).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch085.certificate1020).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch085.certificate1021).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch034.certificate680).omega:ℝ) ≤ ((CutFailureCertificates.Budget034.certificate680).bound:ℝ) at hb
  exact (exponentialBound340 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches341 : (MergedCutGroups.Batch085.certificate1023).GlobalMatches MergedCutGroups.Batch085.certificate1024 CountingCertificates.Batch034.certificate682 CutLabelCertificates.Entropy017.certificate342 CutLabelCertificates.Minority017.certificate341 := by decide +kernel
theorem exponentialBound341 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch085.certificate1023).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate682).dm (WitnessCertificates.Batch034.certificate682).beta) ≤ (2*exp (-((CountingCertificates.Batch034.certificate682).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch085.certificate1023).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch085.certificate1024).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch034.certificate682).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch085.certificate1023 MergedCutGroups.Batch085.certificate1024 CountingCertificates.Batch034.certificate682 CutLabelCertificates.Entropy017.certificate342 CutLabelCertificates.Minority017.certificate341 matches341 rfl rfl
    MergedCutGroups.Batch085.numericValid1023 MergedCutGroups.Batch085.numericValid1024 MergedCutGroups.Batch085.cellsSound1023 MergedCutGroups.Batch085.cellsSound1024
    MergedCutGroups.Batch085.cellsNumeric1023 MergedCutGroups.Batch085.cellsNumeric1024 MergedCutGroups.Batch085.populationMatches1023 MergedCutGroups.Batch085.populationMatches1024
    PopulationCertificates.Batch034.valid682 PopulationCertificates.Batch034.sound682 WitnessCertificates.Batch034.valid682 WitnessCertificates.Batch034.sound682 CountingCertificates.Batch034.valid682 CountingCertificates.Batch034.sound682
    CutLabelCertificates.Entropy017.valid342 CutLabelCertificates.Minority017.valid341 CutLabelCertificates.Minority017.sound341 H st hI
theorem probabilityBound341 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch085.certificate1023).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate682).dm (WitnessCertificates.Batch034.certificate682).beta) ≤ ((CutFailureCertificates.Budget034.certificate682).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound682 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate682).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch085.certificate1023).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch085.certificate1024).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch034.certificate682).omega:ℝ) ≤ ((CutFailureCertificates.Budget034.certificate682).bound:ℝ) at hb
  exact (exponentialBound341 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches342 : (MergedCutGroups.Batch085.certificate1026).GlobalMatches MergedCutGroups.Batch085.certificate1027 CountingCertificates.Batch034.certificate684 CutLabelCertificates.Entropy017.certificate343 CutLabelCertificates.Minority017.certificate342 := by decide +kernel
theorem exponentialBound342 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch085.certificate1026).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate684).dm (WitnessCertificates.Batch034.certificate684).beta) ≤ (2*exp (-((CountingCertificates.Batch034.certificate684).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch085.certificate1026).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch085.certificate1027).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch034.certificate684).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch085.certificate1026 MergedCutGroups.Batch085.certificate1027 CountingCertificates.Batch034.certificate684 CutLabelCertificates.Entropy017.certificate343 CutLabelCertificates.Minority017.certificate342 matches342 rfl rfl
    MergedCutGroups.Batch085.numericValid1026 MergedCutGroups.Batch085.numericValid1027 MergedCutGroups.Batch085.cellsSound1026 MergedCutGroups.Batch085.cellsSound1027
    MergedCutGroups.Batch085.cellsNumeric1026 MergedCutGroups.Batch085.cellsNumeric1027 MergedCutGroups.Batch085.populationMatches1026 MergedCutGroups.Batch085.populationMatches1027
    PopulationCertificates.Batch034.valid684 PopulationCertificates.Batch034.sound684 WitnessCertificates.Batch034.valid684 WitnessCertificates.Batch034.sound684 CountingCertificates.Batch034.valid684 CountingCertificates.Batch034.sound684
    CutLabelCertificates.Entropy017.valid343 CutLabelCertificates.Minority017.valid342 CutLabelCertificates.Minority017.sound342 H st hI
theorem probabilityBound342 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch085.certificate1026).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate684).dm (WitnessCertificates.Batch034.certificate684).beta) ≤ ((CutFailureCertificates.Budget034.certificate684).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound684 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate684).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch085.certificate1026).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch085.certificate1027).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch034.certificate684).omega:ℝ) ≤ ((CutFailureCertificates.Budget034.certificate684).bound:ℝ) at hb
  exact (exponentialBound342 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches343 : (MergedCutGroups.Batch085.certificate1029).GlobalMatches MergedCutGroups.Batch085.certificate1030 CountingCertificates.Batch034.certificate686 CutLabelCertificates.Entropy017.certificate344 CutLabelCertificates.Minority017.certificate343 := by decide +kernel
theorem exponentialBound343 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch085.certificate1029).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate686).dm (WitnessCertificates.Batch034.certificate686).beta) ≤ (2*exp (-((CountingCertificates.Batch034.certificate686).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch085.certificate1029).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch085.certificate1030).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch034.certificate686).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch085.certificate1029 MergedCutGroups.Batch085.certificate1030 CountingCertificates.Batch034.certificate686 CutLabelCertificates.Entropy017.certificate344 CutLabelCertificates.Minority017.certificate343 matches343 rfl rfl
    MergedCutGroups.Batch085.numericValid1029 MergedCutGroups.Batch085.numericValid1030 MergedCutGroups.Batch085.cellsSound1029 MergedCutGroups.Batch085.cellsSound1030
    MergedCutGroups.Batch085.cellsNumeric1029 MergedCutGroups.Batch085.cellsNumeric1030 MergedCutGroups.Batch085.populationMatches1029 MergedCutGroups.Batch085.populationMatches1030
    PopulationCertificates.Batch034.valid686 PopulationCertificates.Batch034.sound686 WitnessCertificates.Batch034.valid686 WitnessCertificates.Batch034.sound686 CountingCertificates.Batch034.valid686 CountingCertificates.Batch034.sound686
    CutLabelCertificates.Entropy017.valid344 CutLabelCertificates.Minority017.valid343 CutLabelCertificates.Minority017.sound343 H st hI
theorem probabilityBound343 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch085.certificate1029).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate686).dm (WitnessCertificates.Batch034.certificate686).beta) ≤ ((CutFailureCertificates.Budget034.certificate686).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound686 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate686).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch085.certificate1029).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch085.certificate1030).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch034.certificate686).omega:ℝ) ≤ ((CutFailureCertificates.Budget034.certificate686).bound:ℝ) at hb
  exact (exponentialBound343 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches344 : (MergedCutGroups.Batch086.certificate1032).GlobalMatches MergedCutGroups.Batch086.certificate1033 CountingCertificates.Batch034.certificate688 CutLabelCertificates.Entropy017.certificate345 CutLabelCertificates.Minority017.certificate344 := by decide +kernel
theorem exponentialBound344 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch086.certificate1032).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate688).dm (WitnessCertificates.Batch034.certificate688).beta) ≤ (2*exp (-((CountingCertificates.Batch034.certificate688).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch086.certificate1032).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch086.certificate1033).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch034.certificate688).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch086.certificate1032 MergedCutGroups.Batch086.certificate1033 CountingCertificates.Batch034.certificate688 CutLabelCertificates.Entropy017.certificate345 CutLabelCertificates.Minority017.certificate344 matches344 rfl rfl
    MergedCutGroups.Batch086.numericValid1032 MergedCutGroups.Batch086.numericValid1033 MergedCutGroups.Batch086.cellsSound1032 MergedCutGroups.Batch086.cellsSound1033
    MergedCutGroups.Batch086.cellsNumeric1032 MergedCutGroups.Batch086.cellsNumeric1033 MergedCutGroups.Batch086.populationMatches1032 MergedCutGroups.Batch086.populationMatches1033
    PopulationCertificates.Batch034.valid688 PopulationCertificates.Batch034.sound688 WitnessCertificates.Batch034.valid688 WitnessCertificates.Batch034.sound688 CountingCertificates.Batch034.valid688 CountingCertificates.Batch034.sound688
    CutLabelCertificates.Entropy017.valid345 CutLabelCertificates.Minority017.valid344 CutLabelCertificates.Minority017.sound344 H st hI
theorem probabilityBound344 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch086.certificate1032).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate688).dm (WitnessCertificates.Batch034.certificate688).beta) ≤ ((CutFailureCertificates.Budget034.certificate688).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound688 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate688).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch086.certificate1032).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch086.certificate1033).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch034.certificate688).omega:ℝ) ≤ ((CutFailureCertificates.Budget034.certificate688).bound:ℝ) at hb
  exact (exponentialBound344 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches345 : (MergedCutGroups.Batch086.certificate1035).GlobalMatches MergedCutGroups.Batch086.certificate1036 CountingCertificates.Batch034.certificate690 CutLabelCertificates.Entropy017.certificate346 CutLabelCertificates.Minority017.certificate345 := by decide +kernel
theorem exponentialBound345 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch086.certificate1035).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate690).dm (WitnessCertificates.Batch034.certificate690).beta) ≤ (2*exp (-((CountingCertificates.Batch034.certificate690).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch086.certificate1035).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch086.certificate1036).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch034.certificate690).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch086.certificate1035 MergedCutGroups.Batch086.certificate1036 CountingCertificates.Batch034.certificate690 CutLabelCertificates.Entropy017.certificate346 CutLabelCertificates.Minority017.certificate345 matches345 rfl rfl
    MergedCutGroups.Batch086.numericValid1035 MergedCutGroups.Batch086.numericValid1036 MergedCutGroups.Batch086.cellsSound1035 MergedCutGroups.Batch086.cellsSound1036
    MergedCutGroups.Batch086.cellsNumeric1035 MergedCutGroups.Batch086.cellsNumeric1036 MergedCutGroups.Batch086.populationMatches1035 MergedCutGroups.Batch086.populationMatches1036
    PopulationCertificates.Batch034.valid690 PopulationCertificates.Batch034.sound690 WitnessCertificates.Batch034.valid690 WitnessCertificates.Batch034.sound690 CountingCertificates.Batch034.valid690 CountingCertificates.Batch034.sound690
    CutLabelCertificates.Entropy017.valid346 CutLabelCertificates.Minority017.valid345 CutLabelCertificates.Minority017.sound345 H st hI
theorem probabilityBound345 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch086.certificate1035).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate690).dm (WitnessCertificates.Batch034.certificate690).beta) ≤ ((CutFailureCertificates.Budget034.certificate690).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound690 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate690).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch086.certificate1035).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch086.certificate1036).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch034.certificate690).omega:ℝ) ≤ ((CutFailureCertificates.Budget034.certificate690).bound:ℝ) at hb
  exact (exponentialBound345 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches346 : (MergedCutGroups.Batch086.certificate1038).GlobalMatches MergedCutGroups.Batch086.certificate1039 CountingCertificates.Batch034.certificate692 CutLabelCertificates.Entropy017.certificate347 CutLabelCertificates.Minority017.certificate346 := by decide +kernel
theorem exponentialBound346 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch086.certificate1038).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate692).dm (WitnessCertificates.Batch034.certificate692).beta) ≤ (2*exp (-((CountingCertificates.Batch034.certificate692).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch086.certificate1038).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch086.certificate1039).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch034.certificate692).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch086.certificate1038 MergedCutGroups.Batch086.certificate1039 CountingCertificates.Batch034.certificate692 CutLabelCertificates.Entropy017.certificate347 CutLabelCertificates.Minority017.certificate346 matches346 rfl rfl
    MergedCutGroups.Batch086.numericValid1038 MergedCutGroups.Batch086.numericValid1039 MergedCutGroups.Batch086.cellsSound1038 MergedCutGroups.Batch086.cellsSound1039
    MergedCutGroups.Batch086.cellsNumeric1038 MergedCutGroups.Batch086.cellsNumeric1039 MergedCutGroups.Batch086.populationMatches1038 MergedCutGroups.Batch086.populationMatches1039
    PopulationCertificates.Batch034.valid692 PopulationCertificates.Batch034.sound692 WitnessCertificates.Batch034.valid692 WitnessCertificates.Batch034.sound692 CountingCertificates.Batch034.valid692 CountingCertificates.Batch034.sound692
    CutLabelCertificates.Entropy017.valid347 CutLabelCertificates.Minority017.valid346 CutLabelCertificates.Minority017.sound346 H st hI
theorem probabilityBound346 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch086.certificate1038).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate692).dm (WitnessCertificates.Batch034.certificate692).beta) ≤ ((CutFailureCertificates.Budget034.certificate692).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound692 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate692).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch086.certificate1038).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch086.certificate1039).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch034.certificate692).omega:ℝ) ≤ ((CutFailureCertificates.Budget034.certificate692).bound:ℝ) at hb
  exact (exponentialBound346 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches347 : (MergedCutGroups.Batch086.certificate1041).GlobalMatches MergedCutGroups.Batch086.certificate1042 CountingCertificates.Batch034.certificate694 CutLabelCertificates.Entropy017.certificate348 CutLabelCertificates.Minority017.certificate347 := by decide +kernel
theorem exponentialBound347 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch086.certificate1041).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate694).dm (WitnessCertificates.Batch034.certificate694).beta) ≤ (2*exp (-((CountingCertificates.Batch034.certificate694).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch086.certificate1041).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch086.certificate1042).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch034.certificate694).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch086.certificate1041 MergedCutGroups.Batch086.certificate1042 CountingCertificates.Batch034.certificate694 CutLabelCertificates.Entropy017.certificate348 CutLabelCertificates.Minority017.certificate347 matches347 rfl rfl
    MergedCutGroups.Batch086.numericValid1041 MergedCutGroups.Batch086.numericValid1042 MergedCutGroups.Batch086.cellsSound1041 MergedCutGroups.Batch086.cellsSound1042
    MergedCutGroups.Batch086.cellsNumeric1041 MergedCutGroups.Batch086.cellsNumeric1042 MergedCutGroups.Batch086.populationMatches1041 MergedCutGroups.Batch086.populationMatches1042
    PopulationCertificates.Batch034.valid694 PopulationCertificates.Batch034.sound694 WitnessCertificates.Batch034.valid694 WitnessCertificates.Batch034.sound694 CountingCertificates.Batch034.valid694 CountingCertificates.Batch034.sound694
    CutLabelCertificates.Entropy017.valid348 CutLabelCertificates.Minority017.valid347 CutLabelCertificates.Minority017.sound347 H st hI
theorem probabilityBound347 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch086.certificate1041).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate694).dm (WitnessCertificates.Batch034.certificate694).beta) ≤ ((CutFailureCertificates.Budget034.certificate694).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound694 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate694).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch086.certificate1041).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch086.certificate1042).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch034.certificate694).omega:ℝ) ≤ ((CutFailureCertificates.Budget034.certificate694).bound:ℝ) at hb
  exact (exponentialBound347 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches348 : (MergedCutGroups.Batch087.certificate1044).GlobalMatches MergedCutGroups.Batch087.certificate1045 CountingCertificates.Batch034.certificate696 CutLabelCertificates.Entropy017.certificate349 CutLabelCertificates.Minority017.certificate348 := by decide +kernel
theorem exponentialBound348 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch087.certificate1044).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate696).dm (WitnessCertificates.Batch034.certificate696).beta) ≤ (2*exp (-((CountingCertificates.Batch034.certificate696).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch087.certificate1044).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch087.certificate1045).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch034.certificate696).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch087.certificate1044 MergedCutGroups.Batch087.certificate1045 CountingCertificates.Batch034.certificate696 CutLabelCertificates.Entropy017.certificate349 CutLabelCertificates.Minority017.certificate348 matches348 rfl rfl
    MergedCutGroups.Batch087.numericValid1044 MergedCutGroups.Batch087.numericValid1045 MergedCutGroups.Batch087.cellsSound1044 MergedCutGroups.Batch087.cellsSound1045
    MergedCutGroups.Batch087.cellsNumeric1044 MergedCutGroups.Batch087.cellsNumeric1045 MergedCutGroups.Batch087.populationMatches1044 MergedCutGroups.Batch087.populationMatches1045
    PopulationCertificates.Batch034.valid696 PopulationCertificates.Batch034.sound696 WitnessCertificates.Batch034.valid696 WitnessCertificates.Batch034.sound696 CountingCertificates.Batch034.valid696 CountingCertificates.Batch034.sound696
    CutLabelCertificates.Entropy017.valid349 CutLabelCertificates.Minority017.valid348 CutLabelCertificates.Minority017.sound348 H st hI
theorem probabilityBound348 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch087.certificate1044).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate696).dm (WitnessCertificates.Batch034.certificate696).beta) ≤ ((CutFailureCertificates.Budget034.certificate696).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound696 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate696).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch087.certificate1044).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch087.certificate1045).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch034.certificate696).omega:ℝ) ≤ ((CutFailureCertificates.Budget034.certificate696).bound:ℝ) at hb
  exact (exponentialBound348 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches349 : (MergedCutGroups.Batch087.certificate1047).GlobalMatches MergedCutGroups.Batch087.certificate1048 CountingCertificates.Batch034.certificate698 CutLabelCertificates.Entropy017.certificate350 CutLabelCertificates.Minority017.certificate349 := by decide +kernel
theorem exponentialBound349 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch087.certificate1047).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate698).dm (WitnessCertificates.Batch034.certificate698).beta) ≤ (2*exp (-((CountingCertificates.Batch034.certificate698).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch087.certificate1047).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch087.certificate1048).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch034.certificate698).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch087.certificate1047 MergedCutGroups.Batch087.certificate1048 CountingCertificates.Batch034.certificate698 CutLabelCertificates.Entropy017.certificate350 CutLabelCertificates.Minority017.certificate349 matches349 rfl rfl
    MergedCutGroups.Batch087.numericValid1047 MergedCutGroups.Batch087.numericValid1048 MergedCutGroups.Batch087.cellsSound1047 MergedCutGroups.Batch087.cellsSound1048
    MergedCutGroups.Batch087.cellsNumeric1047 MergedCutGroups.Batch087.cellsNumeric1048 MergedCutGroups.Batch087.populationMatches1047 MergedCutGroups.Batch087.populationMatches1048
    PopulationCertificates.Batch034.valid698 PopulationCertificates.Batch034.sound698 WitnessCertificates.Batch034.valid698 WitnessCertificates.Batch034.sound698 CountingCertificates.Batch034.valid698 CountingCertificates.Batch034.sound698
    CutLabelCertificates.Entropy017.valid350 CutLabelCertificates.Minority017.valid349 CutLabelCertificates.Minority017.sound349 H st hI
theorem probabilityBound349 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch087.certificate1047).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch034.certificate698).dm (WitnessCertificates.Batch034.certificate698).beta) ≤ ((CutFailureCertificates.Budget034.certificate698).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound698 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate698).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch087.certificate1047).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch087.certificate1048).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch034.certificate698).omega:ℝ) ≤ ((CutFailureCertificates.Budget034.certificate698).bound:ℝ) at hb
  exact (exponentialBound349 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches350 : (MergedCutGroups.Batch087.certificate1050).GlobalMatches MergedCutGroups.Batch087.certificate1051 CountingCertificates.Batch035.certificate700 CutLabelCertificates.Entropy017.certificate351 CutLabelCertificates.Minority017.certificate350 := by decide +kernel
theorem exponentialBound350 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch087.certificate1050).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate700).dm (WitnessCertificates.Batch035.certificate700).beta) ≤ (2*exp (-((CountingCertificates.Batch035.certificate700).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch087.certificate1050).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch087.certificate1051).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch035.certificate700).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch087.certificate1050 MergedCutGroups.Batch087.certificate1051 CountingCertificates.Batch035.certificate700 CutLabelCertificates.Entropy017.certificate351 CutLabelCertificates.Minority017.certificate350 matches350 rfl rfl
    MergedCutGroups.Batch087.numericValid1050 MergedCutGroups.Batch087.numericValid1051 MergedCutGroups.Batch087.cellsSound1050 MergedCutGroups.Batch087.cellsSound1051
    MergedCutGroups.Batch087.cellsNumeric1050 MergedCutGroups.Batch087.cellsNumeric1051 MergedCutGroups.Batch087.populationMatches1050 MergedCutGroups.Batch087.populationMatches1051
    PopulationCertificates.Batch035.valid700 PopulationCertificates.Batch035.sound700 WitnessCertificates.Batch035.valid700 WitnessCertificates.Batch035.sound700 CountingCertificates.Batch035.valid700 CountingCertificates.Batch035.sound700
    CutLabelCertificates.Entropy017.valid351 CutLabelCertificates.Minority017.valid350 CutLabelCertificates.Minority017.sound350 H st hI
theorem probabilityBound350 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch087.certificate1050).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate700).dm (WitnessCertificates.Batch035.certificate700).beta) ≤ ((CutFailureCertificates.Budget035.certificate700).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound700 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate700).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch087.certificate1050).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch087.certificate1051).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch035.certificate700).omega:ℝ) ≤ ((CutFailureCertificates.Budget035.certificate700).bound:ℝ) at hb
  exact (exponentialBound350 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches351 : (MergedCutGroups.Batch087.certificate1053).GlobalMatches MergedCutGroups.Batch087.certificate1054 CountingCertificates.Batch035.certificate702 CutLabelCertificates.Entropy017.certificate352 CutLabelCertificates.Minority017.certificate351 := by decide +kernel
theorem exponentialBound351 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch087.certificate1053).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate702).dm (WitnessCertificates.Batch035.certificate702).beta) ≤ (2*exp (-((CountingCertificates.Batch035.certificate702).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch087.certificate1053).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch087.certificate1054).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch035.certificate702).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch087.certificate1053 MergedCutGroups.Batch087.certificate1054 CountingCertificates.Batch035.certificate702 CutLabelCertificates.Entropy017.certificate352 CutLabelCertificates.Minority017.certificate351 matches351 rfl rfl
    MergedCutGroups.Batch087.numericValid1053 MergedCutGroups.Batch087.numericValid1054 MergedCutGroups.Batch087.cellsSound1053 MergedCutGroups.Batch087.cellsSound1054
    MergedCutGroups.Batch087.cellsNumeric1053 MergedCutGroups.Batch087.cellsNumeric1054 MergedCutGroups.Batch087.populationMatches1053 MergedCutGroups.Batch087.populationMatches1054
    PopulationCertificates.Batch035.valid702 PopulationCertificates.Batch035.sound702 WitnessCertificates.Batch035.valid702 WitnessCertificates.Batch035.sound702 CountingCertificates.Batch035.valid702 CountingCertificates.Batch035.sound702
    CutLabelCertificates.Entropy017.valid352 CutLabelCertificates.Minority017.valid351 CutLabelCertificates.Minority017.sound351 H st hI
theorem probabilityBound351 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch087.certificate1053).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate702).dm (WitnessCertificates.Batch035.certificate702).beta) ≤ ((CutFailureCertificates.Budget035.certificate702).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound702 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate702).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch087.certificate1053).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch087.certificate1054).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch035.certificate702).omega:ℝ) ≤ ((CutFailureCertificates.Budget035.certificate702).bound:ℝ) at hb
  exact (exponentialBound351 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches352 : (MergedCutGroups.Batch088.certificate1056).GlobalMatches MergedCutGroups.Batch088.certificate1057 CountingCertificates.Batch035.certificate704 CutLabelCertificates.Entropy017.certificate353 CutLabelCertificates.Minority017.certificate352 := by decide +kernel
theorem exponentialBound352 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch088.certificate1056).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate704).dm (WitnessCertificates.Batch035.certificate704).beta) ≤ (2*exp (-((CountingCertificates.Batch035.certificate704).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch088.certificate1056).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch088.certificate1057).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch035.certificate704).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch088.certificate1056 MergedCutGroups.Batch088.certificate1057 CountingCertificates.Batch035.certificate704 CutLabelCertificates.Entropy017.certificate353 CutLabelCertificates.Minority017.certificate352 matches352 rfl rfl
    MergedCutGroups.Batch088.numericValid1056 MergedCutGroups.Batch088.numericValid1057 MergedCutGroups.Batch088.cellsSound1056 MergedCutGroups.Batch088.cellsSound1057
    MergedCutGroups.Batch088.cellsNumeric1056 MergedCutGroups.Batch088.cellsNumeric1057 MergedCutGroups.Batch088.populationMatches1056 MergedCutGroups.Batch088.populationMatches1057
    PopulationCertificates.Batch035.valid704 PopulationCertificates.Batch035.sound704 WitnessCertificates.Batch035.valid704 WitnessCertificates.Batch035.sound704 CountingCertificates.Batch035.valid704 CountingCertificates.Batch035.sound704
    CutLabelCertificates.Entropy017.valid353 CutLabelCertificates.Minority017.valid352 CutLabelCertificates.Minority017.sound352 H st hI
theorem probabilityBound352 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch088.certificate1056).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate704).dm (WitnessCertificates.Batch035.certificate704).beta) ≤ ((CutFailureCertificates.Budget035.certificate704).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound704 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate704).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch088.certificate1056).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch088.certificate1057).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch035.certificate704).omega:ℝ) ≤ ((CutFailureCertificates.Budget035.certificate704).bound:ℝ) at hb
  exact (exponentialBound352 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches353 : (MergedCutGroups.Batch088.certificate1059).GlobalMatches MergedCutGroups.Batch088.certificate1060 CountingCertificates.Batch035.certificate706 CutLabelCertificates.Entropy017.certificate354 CutLabelCertificates.Minority017.certificate353 := by decide +kernel
theorem exponentialBound353 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch088.certificate1059).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate706).dm (WitnessCertificates.Batch035.certificate706).beta) ≤ (2*exp (-((CountingCertificates.Batch035.certificate706).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch088.certificate1059).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch088.certificate1060).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch035.certificate706).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch088.certificate1059 MergedCutGroups.Batch088.certificate1060 CountingCertificates.Batch035.certificate706 CutLabelCertificates.Entropy017.certificate354 CutLabelCertificates.Minority017.certificate353 matches353 rfl rfl
    MergedCutGroups.Batch088.numericValid1059 MergedCutGroups.Batch088.numericValid1060 MergedCutGroups.Batch088.cellsSound1059 MergedCutGroups.Batch088.cellsSound1060
    MergedCutGroups.Batch088.cellsNumeric1059 MergedCutGroups.Batch088.cellsNumeric1060 MergedCutGroups.Batch088.populationMatches1059 MergedCutGroups.Batch088.populationMatches1060
    PopulationCertificates.Batch035.valid706 PopulationCertificates.Batch035.sound706 WitnessCertificates.Batch035.valid706 WitnessCertificates.Batch035.sound706 CountingCertificates.Batch035.valid706 CountingCertificates.Batch035.sound706
    CutLabelCertificates.Entropy017.valid354 CutLabelCertificates.Minority017.valid353 CutLabelCertificates.Minority017.sound353 H st hI
theorem probabilityBound353 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch088.certificate1059).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate706).dm (WitnessCertificates.Batch035.certificate706).beta) ≤ ((CutFailureCertificates.Budget035.certificate706).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound706 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate706).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch088.certificate1059).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch088.certificate1060).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch035.certificate706).omega:ℝ) ≤ ((CutFailureCertificates.Budget035.certificate706).bound:ℝ) at hb
  exact (exponentialBound353 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches354 : (MergedCutGroups.Batch088.certificate1062).GlobalMatches MergedCutGroups.Batch088.certificate1063 CountingCertificates.Batch035.certificate708 CutLabelCertificates.Entropy017.certificate355 CutLabelCertificates.Minority017.certificate354 := by decide +kernel
theorem exponentialBound354 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch088.certificate1062).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate708).dm (WitnessCertificates.Batch035.certificate708).beta) ≤ (2*exp (-((CountingCertificates.Batch035.certificate708).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch088.certificate1062).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch088.certificate1063).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch035.certificate708).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch088.certificate1062 MergedCutGroups.Batch088.certificate1063 CountingCertificates.Batch035.certificate708 CutLabelCertificates.Entropy017.certificate355 CutLabelCertificates.Minority017.certificate354 matches354 rfl rfl
    MergedCutGroups.Batch088.numericValid1062 MergedCutGroups.Batch088.numericValid1063 MergedCutGroups.Batch088.cellsSound1062 MergedCutGroups.Batch088.cellsSound1063
    MergedCutGroups.Batch088.cellsNumeric1062 MergedCutGroups.Batch088.cellsNumeric1063 MergedCutGroups.Batch088.populationMatches1062 MergedCutGroups.Batch088.populationMatches1063
    PopulationCertificates.Batch035.valid708 PopulationCertificates.Batch035.sound708 WitnessCertificates.Batch035.valid708 WitnessCertificates.Batch035.sound708 CountingCertificates.Batch035.valid708 CountingCertificates.Batch035.sound708
    CutLabelCertificates.Entropy017.valid355 CutLabelCertificates.Minority017.valid354 CutLabelCertificates.Minority017.sound354 H st hI
theorem probabilityBound354 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch088.certificate1062).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate708).dm (WitnessCertificates.Batch035.certificate708).beta) ≤ ((CutFailureCertificates.Budget035.certificate708).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound708 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate708).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch088.certificate1062).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch088.certificate1063).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch035.certificate708).omega:ℝ) ≤ ((CutFailureCertificates.Budget035.certificate708).bound:ℝ) at hb
  exact (exponentialBound354 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches355 : (MergedCutGroups.Batch088.certificate1065).GlobalMatches MergedCutGroups.Batch088.certificate1066 CountingCertificates.Batch035.certificate710 CutLabelCertificates.Entropy017.certificate356 CutLabelCertificates.Minority017.certificate355 := by decide +kernel
theorem exponentialBound355 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch088.certificate1065).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate710).dm (WitnessCertificates.Batch035.certificate710).beta) ≤ (2*exp (-((CountingCertificates.Batch035.certificate710).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch088.certificate1065).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch088.certificate1066).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch035.certificate710).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch088.certificate1065 MergedCutGroups.Batch088.certificate1066 CountingCertificates.Batch035.certificate710 CutLabelCertificates.Entropy017.certificate356 CutLabelCertificates.Minority017.certificate355 matches355 rfl rfl
    MergedCutGroups.Batch088.numericValid1065 MergedCutGroups.Batch088.numericValid1066 MergedCutGroups.Batch088.cellsSound1065 MergedCutGroups.Batch088.cellsSound1066
    MergedCutGroups.Batch088.cellsNumeric1065 MergedCutGroups.Batch088.cellsNumeric1066 MergedCutGroups.Batch088.populationMatches1065 MergedCutGroups.Batch088.populationMatches1066
    PopulationCertificates.Batch035.valid710 PopulationCertificates.Batch035.sound710 WitnessCertificates.Batch035.valid710 WitnessCertificates.Batch035.sound710 CountingCertificates.Batch035.valid710 CountingCertificates.Batch035.sound710
    CutLabelCertificates.Entropy017.valid356 CutLabelCertificates.Minority017.valid355 CutLabelCertificates.Minority017.sound355 H st hI
theorem probabilityBound355 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch088.certificate1065).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate710).dm (WitnessCertificates.Batch035.certificate710).beta) ≤ ((CutFailureCertificates.Budget035.certificate710).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound710 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate710).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch088.certificate1065).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch088.certificate1066).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch035.certificate710).omega:ℝ) ≤ ((CutFailureCertificates.Budget035.certificate710).bound:ℝ) at hb
  exact (exponentialBound355 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches356 : (MergedCutGroups.Batch089.certificate1068).GlobalMatches MergedCutGroups.Batch089.certificate1069 CountingCertificates.Batch035.certificate712 CutLabelCertificates.Entropy017.certificate357 CutLabelCertificates.Minority017.certificate356 := by decide +kernel
theorem exponentialBound356 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch089.certificate1068).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate712).dm (WitnessCertificates.Batch035.certificate712).beta) ≤ (2*exp (-((CountingCertificates.Batch035.certificate712).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch089.certificate1068).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch089.certificate1069).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch035.certificate712).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch089.certificate1068 MergedCutGroups.Batch089.certificate1069 CountingCertificates.Batch035.certificate712 CutLabelCertificates.Entropy017.certificate357 CutLabelCertificates.Minority017.certificate356 matches356 rfl rfl
    MergedCutGroups.Batch089.numericValid1068 MergedCutGroups.Batch089.numericValid1069 MergedCutGroups.Batch089.cellsSound1068 MergedCutGroups.Batch089.cellsSound1069
    MergedCutGroups.Batch089.cellsNumeric1068 MergedCutGroups.Batch089.cellsNumeric1069 MergedCutGroups.Batch089.populationMatches1068 MergedCutGroups.Batch089.populationMatches1069
    PopulationCertificates.Batch035.valid712 PopulationCertificates.Batch035.sound712 WitnessCertificates.Batch035.valid712 WitnessCertificates.Batch035.sound712 CountingCertificates.Batch035.valid712 CountingCertificates.Batch035.sound712
    CutLabelCertificates.Entropy017.valid357 CutLabelCertificates.Minority017.valid356 CutLabelCertificates.Minority017.sound356 H st hI
theorem probabilityBound356 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch089.certificate1068).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate712).dm (WitnessCertificates.Batch035.certificate712).beta) ≤ ((CutFailureCertificates.Budget035.certificate712).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound712 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate712).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch089.certificate1068).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch089.certificate1069).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch035.certificate712).omega:ℝ) ≤ ((CutFailureCertificates.Budget035.certificate712).bound:ℝ) at hb
  exact (exponentialBound356 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches357 : (MergedCutGroups.Batch089.certificate1071).GlobalMatches MergedCutGroups.Batch089.certificate1072 CountingCertificates.Batch035.certificate714 CutLabelCertificates.Entropy017.certificate358 CutLabelCertificates.Minority017.certificate357 := by decide +kernel
theorem exponentialBound357 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch089.certificate1071).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate714).dm (WitnessCertificates.Batch035.certificate714).beta) ≤ (2*exp (-((CountingCertificates.Batch035.certificate714).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch089.certificate1071).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch089.certificate1072).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch035.certificate714).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch089.certificate1071 MergedCutGroups.Batch089.certificate1072 CountingCertificates.Batch035.certificate714 CutLabelCertificates.Entropy017.certificate358 CutLabelCertificates.Minority017.certificate357 matches357 rfl rfl
    MergedCutGroups.Batch089.numericValid1071 MergedCutGroups.Batch089.numericValid1072 MergedCutGroups.Batch089.cellsSound1071 MergedCutGroups.Batch089.cellsSound1072
    MergedCutGroups.Batch089.cellsNumeric1071 MergedCutGroups.Batch089.cellsNumeric1072 MergedCutGroups.Batch089.populationMatches1071 MergedCutGroups.Batch089.populationMatches1072
    PopulationCertificates.Batch035.valid714 PopulationCertificates.Batch035.sound714 WitnessCertificates.Batch035.valid714 WitnessCertificates.Batch035.sound714 CountingCertificates.Batch035.valid714 CountingCertificates.Batch035.sound714
    CutLabelCertificates.Entropy017.valid358 CutLabelCertificates.Minority017.valid357 CutLabelCertificates.Minority017.sound357 H st hI
theorem probabilityBound357 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch089.certificate1071).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate714).dm (WitnessCertificates.Batch035.certificate714).beta) ≤ ((CutFailureCertificates.Budget035.certificate714).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound714 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate714).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch089.certificate1071).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch089.certificate1072).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch035.certificate714).omega:ℝ) ≤ ((CutFailureCertificates.Budget035.certificate714).bound:ℝ) at hb
  exact (exponentialBound357 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches358 : (MergedCutGroups.Batch089.certificate1074).GlobalMatches MergedCutGroups.Batch089.certificate1075 CountingCertificates.Batch035.certificate716 CutLabelCertificates.Entropy017.certificate359 CutLabelCertificates.Minority017.certificate358 := by decide +kernel
theorem exponentialBound358 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch089.certificate1074).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate716).dm (WitnessCertificates.Batch035.certificate716).beta) ≤ (2*exp (-((CountingCertificates.Batch035.certificate716).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch089.certificate1074).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch089.certificate1075).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch035.certificate716).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch089.certificate1074 MergedCutGroups.Batch089.certificate1075 CountingCertificates.Batch035.certificate716 CutLabelCertificates.Entropy017.certificate359 CutLabelCertificates.Minority017.certificate358 matches358 rfl rfl
    MergedCutGroups.Batch089.numericValid1074 MergedCutGroups.Batch089.numericValid1075 MergedCutGroups.Batch089.cellsSound1074 MergedCutGroups.Batch089.cellsSound1075
    MergedCutGroups.Batch089.cellsNumeric1074 MergedCutGroups.Batch089.cellsNumeric1075 MergedCutGroups.Batch089.populationMatches1074 MergedCutGroups.Batch089.populationMatches1075
    PopulationCertificates.Batch035.valid716 PopulationCertificates.Batch035.sound716 WitnessCertificates.Batch035.valid716 WitnessCertificates.Batch035.sound716 CountingCertificates.Batch035.valid716 CountingCertificates.Batch035.sound716
    CutLabelCertificates.Entropy017.valid359 CutLabelCertificates.Minority017.valid358 CutLabelCertificates.Minority017.sound358 H st hI
theorem probabilityBound358 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch089.certificate1074).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate716).dm (WitnessCertificates.Batch035.certificate716).beta) ≤ ((CutFailureCertificates.Budget035.certificate716).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound716 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate716).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch089.certificate1074).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch089.certificate1075).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch035.certificate716).omega:ℝ) ≤ ((CutFailureCertificates.Budget035.certificate716).bound:ℝ) at hb
  exact (exponentialBound358 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches359 : (MergedCutGroups.Batch089.certificate1077).GlobalMatches MergedCutGroups.Batch089.certificate1078 CountingCertificates.Batch035.certificate718 CutLabelCertificates.Entropy018.certificate360 CutLabelCertificates.Minority017.certificate359 := by decide +kernel
theorem exponentialBound359 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch089.certificate1077).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate718).dm (WitnessCertificates.Batch035.certificate718).beta) ≤ (2*exp (-((CountingCertificates.Batch035.certificate718).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch089.certificate1077).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch089.certificate1078).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch035.certificate718).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch089.certificate1077 MergedCutGroups.Batch089.certificate1078 CountingCertificates.Batch035.certificate718 CutLabelCertificates.Entropy018.certificate360 CutLabelCertificates.Minority017.certificate359 matches359 rfl rfl
    MergedCutGroups.Batch089.numericValid1077 MergedCutGroups.Batch089.numericValid1078 MergedCutGroups.Batch089.cellsSound1077 MergedCutGroups.Batch089.cellsSound1078
    MergedCutGroups.Batch089.cellsNumeric1077 MergedCutGroups.Batch089.cellsNumeric1078 MergedCutGroups.Batch089.populationMatches1077 MergedCutGroups.Batch089.populationMatches1078
    PopulationCertificates.Batch035.valid718 PopulationCertificates.Batch035.sound718 WitnessCertificates.Batch035.valid718 WitnessCertificates.Batch035.sound718 CountingCertificates.Batch035.valid718 CountingCertificates.Batch035.sound718
    CutLabelCertificates.Entropy018.valid360 CutLabelCertificates.Minority017.valid359 CutLabelCertificates.Minority017.sound359 H st hI
theorem probabilityBound359 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch089.certificate1077).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch035.certificate718).dm (WitnessCertificates.Batch035.certificate718).beta) ≤ ((CutFailureCertificates.Budget035.certificate718).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound718 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate718).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch089.certificate1077).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch089.certificate1078).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch035.certificate718).omega:ℝ) ≤ ((CutFailureCertificates.Budget035.certificate718).bound:ℝ) at hb
  exact (exponentialBound359 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch017
