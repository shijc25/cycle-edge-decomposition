import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch048
import Cycle12.CountingCertificates.Batch049
import Cycle12.CountingCertificates.Batch050
import Cycle12.CountingCertificates.Batch051
import Cycle12.CutFailureCertificates.Budget048
import Cycle12.CutFailureCertificates.Budget049
import Cycle12.CutFailureCertificates.Budget050
import Cycle12.CutFailureCertificates.Budget051
import Cycle12.CutLabelCertificates.Entropy031
import Cycle12.CutLabelCertificates.Entropy032
import Cycle12.CutLabelCertificates.Entropy033
import Cycle12.CutLabelCertificates.Entropy034
import Cycle12.CutLabelCertificates.Entropy035
import Cycle12.CutLabelCertificates.Entropy036
import Cycle12.CutLabelCertificates.Minority031
import Cycle12.CutLabelCertificates.Minority032
import Cycle12.CutLabelCertificates.Minority033
import Cycle12.CutLabelCertificates.Minority034
import Cycle12.CutLabelCertificates.Minority035
import Cycle12.CutLabelCertificates.Minority036
import Cycle12.MergedCutGroups.Batch118
import Cycle12.MergedCutGroups.Batch119
import Cycle12.MergedCutGroups.Batch120
import Cycle12.MergedCutGroups.Batch121
import Cycle12.MergedCutGroups.Batch122
import Cycle12.MergedCutGroups.Batch123
import Cycle12.MergedCutGroups.Batch124
import Cycle12.MergedCutGroups.Batch125
import Cycle12.PopulationCertificates.Batch048
import Cycle12.PopulationCertificates.Batch049
import Cycle12.PopulationCertificates.Batch050
import Cycle12.PopulationCertificates.Batch051
import Cycle12.WitnessCertificates.Batch048
import Cycle12.WitnessCertificates.Batch049
import Cycle12.WitnessCertificates.Batch050
import Cycle12.WitnessCertificates.Batch051

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch023
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches460 : (MergedCutGroups.Batch118.certificate1425).GlobalMatches MergedCutGroups.Batch118.certificate1426 CountingCertificates.Batch048.certificate965 CutLabelCertificates.Entropy031.certificate632 CutLabelCertificates.Minority031.certificate631 := by decide +kernel
theorem exponentialBound460 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch118.certificate1425).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate965).dm (WitnessCertificates.Batch048.certificate965).beta) ≤ (2*exp (-((CountingCertificates.Batch048.certificate965).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch118.certificate1425).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch118.certificate1426).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch048.certificate965).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch118.certificate1425 MergedCutGroups.Batch118.certificate1426 CountingCertificates.Batch048.certificate965 CutLabelCertificates.Entropy031.certificate632 CutLabelCertificates.Minority031.certificate631 matches460 rfl rfl
    MergedCutGroups.Batch118.numericValid1425 MergedCutGroups.Batch118.numericValid1426 MergedCutGroups.Batch118.cellsSound1425 MergedCutGroups.Batch118.cellsSound1426
    MergedCutGroups.Batch118.cellsNumeric1425 MergedCutGroups.Batch118.cellsNumeric1426 MergedCutGroups.Batch118.populationMatches1425 MergedCutGroups.Batch118.populationMatches1426
    PopulationCertificates.Batch048.valid965 PopulationCertificates.Batch048.sound965 WitnessCertificates.Batch048.valid965 WitnessCertificates.Batch048.sound965 CountingCertificates.Batch048.valid965 CountingCertificates.Batch048.sound965
    CutLabelCertificates.Entropy031.valid632 CutLabelCertificates.Minority031.valid631 CutLabelCertificates.Minority031.sound631 H st hI
theorem probabilityBound460 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch118.certificate1425).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate965).dm (WitnessCertificates.Batch048.certificate965).beta) ≤ ((CutFailureCertificates.Budget048.certificate965).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound965 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate965).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch118.certificate1425).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch118.certificate1426).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch048.certificate965).omega:ℝ) ≤ ((CutFailureCertificates.Budget048.certificate965).bound:ℝ) at hb
  exact (exponentialBound460 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches461 : (MergedCutGroups.Batch119.certificate1429).GlobalMatches MergedCutGroups.Batch119.certificate1430 CountingCertificates.Batch048.certificate968 CutLabelCertificates.Entropy031.certificate637 CutLabelCertificates.Minority031.certificate636 := by decide +kernel
theorem exponentialBound461 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch119.certificate1429).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate968).dm (WitnessCertificates.Batch048.certificate968).beta) ≤ (2*exp (-((CountingCertificates.Batch048.certificate968).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch119.certificate1429).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch119.certificate1430).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch048.certificate968).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch119.certificate1429 MergedCutGroups.Batch119.certificate1430 CountingCertificates.Batch048.certificate968 CutLabelCertificates.Entropy031.certificate637 CutLabelCertificates.Minority031.certificate636 matches461 rfl rfl
    MergedCutGroups.Batch119.numericValid1429 MergedCutGroups.Batch119.numericValid1430 MergedCutGroups.Batch119.cellsSound1429 MergedCutGroups.Batch119.cellsSound1430
    MergedCutGroups.Batch119.cellsNumeric1429 MergedCutGroups.Batch119.cellsNumeric1430 MergedCutGroups.Batch119.populationMatches1429 MergedCutGroups.Batch119.populationMatches1430
    PopulationCertificates.Batch048.valid968 PopulationCertificates.Batch048.sound968 WitnessCertificates.Batch048.valid968 WitnessCertificates.Batch048.sound968 CountingCertificates.Batch048.valid968 CountingCertificates.Batch048.sound968
    CutLabelCertificates.Entropy031.valid637 CutLabelCertificates.Minority031.valid636 CutLabelCertificates.Minority031.sound636 H st hI
theorem probabilityBound461 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch119.certificate1429).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate968).dm (WitnessCertificates.Batch048.certificate968).beta) ≤ ((CutFailureCertificates.Budget048.certificate968).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound968 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate968).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch119.certificate1429).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch119.certificate1430).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch048.certificate968).omega:ℝ) ≤ ((CutFailureCertificates.Budget048.certificate968).bound:ℝ) at hb
  exact (exponentialBound461 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches462 : (MergedCutGroups.Batch119.certificate1433).GlobalMatches MergedCutGroups.Batch119.certificate1434 CountingCertificates.Batch048.certificate971 CutLabelCertificates.Entropy032.certificate642 CutLabelCertificates.Minority032.certificate641 := by decide +kernel
theorem exponentialBound462 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch119.certificate1433).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate971).dm (WitnessCertificates.Batch048.certificate971).beta) ≤ (2*exp (-((CountingCertificates.Batch048.certificate971).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch119.certificate1433).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch119.certificate1434).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch048.certificate971).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch119.certificate1433 MergedCutGroups.Batch119.certificate1434 CountingCertificates.Batch048.certificate971 CutLabelCertificates.Entropy032.certificate642 CutLabelCertificates.Minority032.certificate641 matches462 rfl rfl
    MergedCutGroups.Batch119.numericValid1433 MergedCutGroups.Batch119.numericValid1434 MergedCutGroups.Batch119.cellsSound1433 MergedCutGroups.Batch119.cellsSound1434
    MergedCutGroups.Batch119.cellsNumeric1433 MergedCutGroups.Batch119.cellsNumeric1434 MergedCutGroups.Batch119.populationMatches1433 MergedCutGroups.Batch119.populationMatches1434
    PopulationCertificates.Batch048.valid971 PopulationCertificates.Batch048.sound971 WitnessCertificates.Batch048.valid971 WitnessCertificates.Batch048.sound971 CountingCertificates.Batch048.valid971 CountingCertificates.Batch048.sound971
    CutLabelCertificates.Entropy032.valid642 CutLabelCertificates.Minority032.valid641 CutLabelCertificates.Minority032.sound641 H st hI
theorem probabilityBound462 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch119.certificate1433).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate971).dm (WitnessCertificates.Batch048.certificate971).beta) ≤ ((CutFailureCertificates.Budget048.certificate971).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound971 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate971).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch119.certificate1433).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch119.certificate1434).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch048.certificate971).omega:ℝ) ≤ ((CutFailureCertificates.Budget048.certificate971).bound:ℝ) at hb
  exact (exponentialBound462 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches463 : (MergedCutGroups.Batch119.certificate1437).GlobalMatches MergedCutGroups.Batch119.certificate1438 CountingCertificates.Batch048.certificate974 CutLabelCertificates.Entropy032.certificate647 CutLabelCertificates.Minority032.certificate646 := by decide +kernel
theorem exponentialBound463 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch119.certificate1437).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate974).dm (WitnessCertificates.Batch048.certificate974).beta) ≤ (2*exp (-((CountingCertificates.Batch048.certificate974).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch119.certificate1437).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch119.certificate1438).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch048.certificate974).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch119.certificate1437 MergedCutGroups.Batch119.certificate1438 CountingCertificates.Batch048.certificate974 CutLabelCertificates.Entropy032.certificate647 CutLabelCertificates.Minority032.certificate646 matches463 rfl rfl
    MergedCutGroups.Batch119.numericValid1437 MergedCutGroups.Batch119.numericValid1438 MergedCutGroups.Batch119.cellsSound1437 MergedCutGroups.Batch119.cellsSound1438
    MergedCutGroups.Batch119.cellsNumeric1437 MergedCutGroups.Batch119.cellsNumeric1438 MergedCutGroups.Batch119.populationMatches1437 MergedCutGroups.Batch119.populationMatches1438
    PopulationCertificates.Batch048.valid974 PopulationCertificates.Batch048.sound974 WitnessCertificates.Batch048.valid974 WitnessCertificates.Batch048.sound974 CountingCertificates.Batch048.valid974 CountingCertificates.Batch048.sound974
    CutLabelCertificates.Entropy032.valid647 CutLabelCertificates.Minority032.valid646 CutLabelCertificates.Minority032.sound646 H st hI
theorem probabilityBound463 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch119.certificate1437).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate974).dm (WitnessCertificates.Batch048.certificate974).beta) ≤ ((CutFailureCertificates.Budget048.certificate974).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound974 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate974).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch119.certificate1437).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch119.certificate1438).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch048.certificate974).omega:ℝ) ≤ ((CutFailureCertificates.Budget048.certificate974).bound:ℝ) at hb
  exact (exponentialBound463 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches464 : (MergedCutGroups.Batch120.certificate1441).GlobalMatches MergedCutGroups.Batch120.certificate1442 CountingCertificates.Batch048.certificate977 CutLabelCertificates.Entropy032.certificate652 CutLabelCertificates.Minority032.certificate651 := by decide +kernel
theorem exponentialBound464 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch120.certificate1441).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate977).dm (WitnessCertificates.Batch048.certificate977).beta) ≤ (2*exp (-((CountingCertificates.Batch048.certificate977).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch120.certificate1441).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch120.certificate1442).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch048.certificate977).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch120.certificate1441 MergedCutGroups.Batch120.certificate1442 CountingCertificates.Batch048.certificate977 CutLabelCertificates.Entropy032.certificate652 CutLabelCertificates.Minority032.certificate651 matches464 rfl rfl
    MergedCutGroups.Batch120.numericValid1441 MergedCutGroups.Batch120.numericValid1442 MergedCutGroups.Batch120.cellsSound1441 MergedCutGroups.Batch120.cellsSound1442
    MergedCutGroups.Batch120.cellsNumeric1441 MergedCutGroups.Batch120.cellsNumeric1442 MergedCutGroups.Batch120.populationMatches1441 MergedCutGroups.Batch120.populationMatches1442
    PopulationCertificates.Batch048.valid977 PopulationCertificates.Batch048.sound977 WitnessCertificates.Batch048.valid977 WitnessCertificates.Batch048.sound977 CountingCertificates.Batch048.valid977 CountingCertificates.Batch048.sound977
    CutLabelCertificates.Entropy032.valid652 CutLabelCertificates.Minority032.valid651 CutLabelCertificates.Minority032.sound651 H st hI
theorem probabilityBound464 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch120.certificate1441).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate977).dm (WitnessCertificates.Batch048.certificate977).beta) ≤ ((CutFailureCertificates.Budget048.certificate977).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound977 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate977).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch120.certificate1441).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch120.certificate1442).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch048.certificate977).omega:ℝ) ≤ ((CutFailureCertificates.Budget048.certificate977).bound:ℝ) at hb
  exact (exponentialBound464 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches465 : (MergedCutGroups.Batch120.certificate1445).GlobalMatches MergedCutGroups.Batch120.certificate1446 CountingCertificates.Batch049.certificate980 CutLabelCertificates.Entropy032.certificate657 CutLabelCertificates.Minority032.certificate656 := by decide +kernel
theorem exponentialBound465 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch120.certificate1445).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate980).dm (WitnessCertificates.Batch049.certificate980).beta) ≤ (2*exp (-((CountingCertificates.Batch049.certificate980).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch120.certificate1445).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch120.certificate1446).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch049.certificate980).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch120.certificate1445 MergedCutGroups.Batch120.certificate1446 CountingCertificates.Batch049.certificate980 CutLabelCertificates.Entropy032.certificate657 CutLabelCertificates.Minority032.certificate656 matches465 rfl rfl
    MergedCutGroups.Batch120.numericValid1445 MergedCutGroups.Batch120.numericValid1446 MergedCutGroups.Batch120.cellsSound1445 MergedCutGroups.Batch120.cellsSound1446
    MergedCutGroups.Batch120.cellsNumeric1445 MergedCutGroups.Batch120.cellsNumeric1446 MergedCutGroups.Batch120.populationMatches1445 MergedCutGroups.Batch120.populationMatches1446
    PopulationCertificates.Batch049.valid980 PopulationCertificates.Batch049.sound980 WitnessCertificates.Batch049.valid980 WitnessCertificates.Batch049.sound980 CountingCertificates.Batch049.valid980 CountingCertificates.Batch049.sound980
    CutLabelCertificates.Entropy032.valid657 CutLabelCertificates.Minority032.valid656 CutLabelCertificates.Minority032.sound656 H st hI
theorem probabilityBound465 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch120.certificate1445).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate980).dm (WitnessCertificates.Batch049.certificate980).beta) ≤ ((CutFailureCertificates.Budget049.certificate980).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound980 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate980).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch120.certificate1445).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch120.certificate1446).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch049.certificate980).omega:ℝ) ≤ ((CutFailureCertificates.Budget049.certificate980).bound:ℝ) at hb
  exact (exponentialBound465 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches466 : (MergedCutGroups.Batch120.certificate1449).GlobalMatches MergedCutGroups.Batch120.certificate1450 CountingCertificates.Batch049.certificate983 CutLabelCertificates.Entropy033.certificate662 CutLabelCertificates.Minority033.certificate661 := by decide +kernel
theorem exponentialBound466 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch120.certificate1449).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate983).dm (WitnessCertificates.Batch049.certificate983).beta) ≤ (2*exp (-((CountingCertificates.Batch049.certificate983).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch120.certificate1449).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch120.certificate1450).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch049.certificate983).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch120.certificate1449 MergedCutGroups.Batch120.certificate1450 CountingCertificates.Batch049.certificate983 CutLabelCertificates.Entropy033.certificate662 CutLabelCertificates.Minority033.certificate661 matches466 rfl rfl
    MergedCutGroups.Batch120.numericValid1449 MergedCutGroups.Batch120.numericValid1450 MergedCutGroups.Batch120.cellsSound1449 MergedCutGroups.Batch120.cellsSound1450
    MergedCutGroups.Batch120.cellsNumeric1449 MergedCutGroups.Batch120.cellsNumeric1450 MergedCutGroups.Batch120.populationMatches1449 MergedCutGroups.Batch120.populationMatches1450
    PopulationCertificates.Batch049.valid983 PopulationCertificates.Batch049.sound983 WitnessCertificates.Batch049.valid983 WitnessCertificates.Batch049.sound983 CountingCertificates.Batch049.valid983 CountingCertificates.Batch049.sound983
    CutLabelCertificates.Entropy033.valid662 CutLabelCertificates.Minority033.valid661 CutLabelCertificates.Minority033.sound661 H st hI
theorem probabilityBound466 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch120.certificate1449).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate983).dm (WitnessCertificates.Batch049.certificate983).beta) ≤ ((CutFailureCertificates.Budget049.certificate983).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound983 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate983).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch120.certificate1449).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch120.certificate1450).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch049.certificate983).omega:ℝ) ≤ ((CutFailureCertificates.Budget049.certificate983).bound:ℝ) at hb
  exact (exponentialBound466 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches467 : (MergedCutGroups.Batch121.certificate1453).GlobalMatches MergedCutGroups.Batch121.certificate1454 CountingCertificates.Batch049.certificate986 CutLabelCertificates.Entropy033.certificate667 CutLabelCertificates.Minority033.certificate666 := by decide +kernel
theorem exponentialBound467 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch121.certificate1453).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate986).dm (WitnessCertificates.Batch049.certificate986).beta) ≤ (2*exp (-((CountingCertificates.Batch049.certificate986).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch121.certificate1453).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch121.certificate1454).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch049.certificate986).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch121.certificate1453 MergedCutGroups.Batch121.certificate1454 CountingCertificates.Batch049.certificate986 CutLabelCertificates.Entropy033.certificate667 CutLabelCertificates.Minority033.certificate666 matches467 rfl rfl
    MergedCutGroups.Batch121.numericValid1453 MergedCutGroups.Batch121.numericValid1454 MergedCutGroups.Batch121.cellsSound1453 MergedCutGroups.Batch121.cellsSound1454
    MergedCutGroups.Batch121.cellsNumeric1453 MergedCutGroups.Batch121.cellsNumeric1454 MergedCutGroups.Batch121.populationMatches1453 MergedCutGroups.Batch121.populationMatches1454
    PopulationCertificates.Batch049.valid986 PopulationCertificates.Batch049.sound986 WitnessCertificates.Batch049.valid986 WitnessCertificates.Batch049.sound986 CountingCertificates.Batch049.valid986 CountingCertificates.Batch049.sound986
    CutLabelCertificates.Entropy033.valid667 CutLabelCertificates.Minority033.valid666 CutLabelCertificates.Minority033.sound666 H st hI
theorem probabilityBound467 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch121.certificate1453).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate986).dm (WitnessCertificates.Batch049.certificate986).beta) ≤ ((CutFailureCertificates.Budget049.certificate986).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound986 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate986).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch121.certificate1453).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch121.certificate1454).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch049.certificate986).omega:ℝ) ≤ ((CutFailureCertificates.Budget049.certificate986).bound:ℝ) at hb
  exact (exponentialBound467 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches468 : (MergedCutGroups.Batch121.certificate1457).GlobalMatches MergedCutGroups.Batch121.certificate1458 CountingCertificates.Batch049.certificate989 CutLabelCertificates.Entropy033.certificate673 CutLabelCertificates.Minority033.certificate672 := by decide +kernel
theorem exponentialBound468 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch121.certificate1457).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate989).dm (WitnessCertificates.Batch049.certificate989).beta) ≤ (2*exp (-((CountingCertificates.Batch049.certificate989).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch121.certificate1457).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch121.certificate1458).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch049.certificate989).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch121.certificate1457 MergedCutGroups.Batch121.certificate1458 CountingCertificates.Batch049.certificate989 CutLabelCertificates.Entropy033.certificate673 CutLabelCertificates.Minority033.certificate672 matches468 rfl rfl
    MergedCutGroups.Batch121.numericValid1457 MergedCutGroups.Batch121.numericValid1458 MergedCutGroups.Batch121.cellsSound1457 MergedCutGroups.Batch121.cellsSound1458
    MergedCutGroups.Batch121.cellsNumeric1457 MergedCutGroups.Batch121.cellsNumeric1458 MergedCutGroups.Batch121.populationMatches1457 MergedCutGroups.Batch121.populationMatches1458
    PopulationCertificates.Batch049.valid989 PopulationCertificates.Batch049.sound989 WitnessCertificates.Batch049.valid989 WitnessCertificates.Batch049.sound989 CountingCertificates.Batch049.valid989 CountingCertificates.Batch049.sound989
    CutLabelCertificates.Entropy033.valid673 CutLabelCertificates.Minority033.valid672 CutLabelCertificates.Minority033.sound672 H st hI
theorem probabilityBound468 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch121.certificate1457).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate989).dm (WitnessCertificates.Batch049.certificate989).beta) ≤ ((CutFailureCertificates.Budget049.certificate989).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound989 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate989).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch121.certificate1457).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch121.certificate1458).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch049.certificate989).omega:ℝ) ≤ ((CutFailureCertificates.Budget049.certificate989).bound:ℝ) at hb
  exact (exponentialBound468 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches469 : (MergedCutGroups.Batch121.certificate1461).GlobalMatches MergedCutGroups.Batch121.certificate1462 CountingCertificates.Batch049.certificate992 CutLabelCertificates.Entropy033.certificate679 CutLabelCertificates.Minority033.certificate678 := by decide +kernel
theorem exponentialBound469 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch121.certificate1461).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate992).dm (WitnessCertificates.Batch049.certificate992).beta) ≤ (2*exp (-((CountingCertificates.Batch049.certificate992).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch121.certificate1461).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch121.certificate1462).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch049.certificate992).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch121.certificate1461 MergedCutGroups.Batch121.certificate1462 CountingCertificates.Batch049.certificate992 CutLabelCertificates.Entropy033.certificate679 CutLabelCertificates.Minority033.certificate678 matches469 rfl rfl
    MergedCutGroups.Batch121.numericValid1461 MergedCutGroups.Batch121.numericValid1462 MergedCutGroups.Batch121.cellsSound1461 MergedCutGroups.Batch121.cellsSound1462
    MergedCutGroups.Batch121.cellsNumeric1461 MergedCutGroups.Batch121.cellsNumeric1462 MergedCutGroups.Batch121.populationMatches1461 MergedCutGroups.Batch121.populationMatches1462
    PopulationCertificates.Batch049.valid992 PopulationCertificates.Batch049.sound992 WitnessCertificates.Batch049.valid992 WitnessCertificates.Batch049.sound992 CountingCertificates.Batch049.valid992 CountingCertificates.Batch049.sound992
    CutLabelCertificates.Entropy033.valid679 CutLabelCertificates.Minority033.valid678 CutLabelCertificates.Minority033.sound678 H st hI
theorem probabilityBound469 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch121.certificate1461).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate992).dm (WitnessCertificates.Batch049.certificate992).beta) ≤ ((CutFailureCertificates.Budget049.certificate992).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound992 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate992).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch121.certificate1461).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch121.certificate1462).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch049.certificate992).omega:ℝ) ≤ ((CutFailureCertificates.Budget049.certificate992).bound:ℝ) at hb
  exact (exponentialBound469 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches470 : (MergedCutGroups.Batch122.certificate1465).GlobalMatches MergedCutGroups.Batch122.certificate1466 CountingCertificates.Batch049.certificate995 CutLabelCertificates.Entropy034.certificate685 CutLabelCertificates.Minority034.certificate684 := by decide +kernel
theorem exponentialBound470 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch122.certificate1465).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate995).dm (WitnessCertificates.Batch049.certificate995).beta) ≤ (2*exp (-((CountingCertificates.Batch049.certificate995).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch122.certificate1465).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch122.certificate1466).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch049.certificate995).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch122.certificate1465 MergedCutGroups.Batch122.certificate1466 CountingCertificates.Batch049.certificate995 CutLabelCertificates.Entropy034.certificate685 CutLabelCertificates.Minority034.certificate684 matches470 rfl rfl
    MergedCutGroups.Batch122.numericValid1465 MergedCutGroups.Batch122.numericValid1466 MergedCutGroups.Batch122.cellsSound1465 MergedCutGroups.Batch122.cellsSound1466
    MergedCutGroups.Batch122.cellsNumeric1465 MergedCutGroups.Batch122.cellsNumeric1466 MergedCutGroups.Batch122.populationMatches1465 MergedCutGroups.Batch122.populationMatches1466
    PopulationCertificates.Batch049.valid995 PopulationCertificates.Batch049.sound995 WitnessCertificates.Batch049.valid995 WitnessCertificates.Batch049.sound995 CountingCertificates.Batch049.valid995 CountingCertificates.Batch049.sound995
    CutLabelCertificates.Entropy034.valid685 CutLabelCertificates.Minority034.valid684 CutLabelCertificates.Minority034.sound684 H st hI
theorem probabilityBound470 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch122.certificate1465).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate995).dm (WitnessCertificates.Batch049.certificate995).beta) ≤ ((CutFailureCertificates.Budget049.certificate995).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound995 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate995).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch122.certificate1465).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch122.certificate1466).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch049.certificate995).omega:ℝ) ≤ ((CutFailureCertificates.Budget049.certificate995).bound:ℝ) at hb
  exact (exponentialBound470 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches471 : (MergedCutGroups.Batch122.certificate1469).GlobalMatches MergedCutGroups.Batch122.certificate1470 CountingCertificates.Batch049.certificate998 CutLabelCertificates.Entropy034.certificate691 CutLabelCertificates.Minority034.certificate690 := by decide +kernel
theorem exponentialBound471 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch122.certificate1469).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate998).dm (WitnessCertificates.Batch049.certificate998).beta) ≤ (2*exp (-((CountingCertificates.Batch049.certificate998).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch122.certificate1469).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch122.certificate1470).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch049.certificate998).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch122.certificate1469 MergedCutGroups.Batch122.certificate1470 CountingCertificates.Batch049.certificate998 CutLabelCertificates.Entropy034.certificate691 CutLabelCertificates.Minority034.certificate690 matches471 rfl rfl
    MergedCutGroups.Batch122.numericValid1469 MergedCutGroups.Batch122.numericValid1470 MergedCutGroups.Batch122.cellsSound1469 MergedCutGroups.Batch122.cellsSound1470
    MergedCutGroups.Batch122.cellsNumeric1469 MergedCutGroups.Batch122.cellsNumeric1470 MergedCutGroups.Batch122.populationMatches1469 MergedCutGroups.Batch122.populationMatches1470
    PopulationCertificates.Batch049.valid998 PopulationCertificates.Batch049.sound998 WitnessCertificates.Batch049.valid998 WitnessCertificates.Batch049.sound998 CountingCertificates.Batch049.valid998 CountingCertificates.Batch049.sound998
    CutLabelCertificates.Entropy034.valid691 CutLabelCertificates.Minority034.valid690 CutLabelCertificates.Minority034.sound690 H st hI
theorem probabilityBound471 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch122.certificate1469).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate998).dm (WitnessCertificates.Batch049.certificate998).beta) ≤ ((CutFailureCertificates.Budget049.certificate998).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound998 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate998).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch122.certificate1469).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch122.certificate1470).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch049.certificate998).omega:ℝ) ≤ ((CutFailureCertificates.Budget049.certificate998).bound:ℝ) at hb
  exact (exponentialBound471 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches472 : (MergedCutGroups.Batch122.certificate1473).GlobalMatches MergedCutGroups.Batch122.certificate1474 CountingCertificates.Batch050.certificate1001 CutLabelCertificates.Entropy034.certificate697 CutLabelCertificates.Minority034.certificate696 := by decide +kernel
theorem exponentialBound472 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch122.certificate1473).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1001).dm (WitnessCertificates.Batch050.certificate1001).beta) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1001).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch122.certificate1473).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch122.certificate1474).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch050.certificate1001).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch122.certificate1473 MergedCutGroups.Batch122.certificate1474 CountingCertificates.Batch050.certificate1001 CutLabelCertificates.Entropy034.certificate697 CutLabelCertificates.Minority034.certificate696 matches472 rfl rfl
    MergedCutGroups.Batch122.numericValid1473 MergedCutGroups.Batch122.numericValid1474 MergedCutGroups.Batch122.cellsSound1473 MergedCutGroups.Batch122.cellsSound1474
    MergedCutGroups.Batch122.cellsNumeric1473 MergedCutGroups.Batch122.cellsNumeric1474 MergedCutGroups.Batch122.populationMatches1473 MergedCutGroups.Batch122.populationMatches1474
    PopulationCertificates.Batch050.valid1001 PopulationCertificates.Batch050.sound1001 WitnessCertificates.Batch050.valid1001 WitnessCertificates.Batch050.sound1001 CountingCertificates.Batch050.valid1001 CountingCertificates.Batch050.sound1001
    CutLabelCertificates.Entropy034.valid697 CutLabelCertificates.Minority034.valid696 CutLabelCertificates.Minority034.sound696 H st hI
theorem probabilityBound472 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch122.certificate1473).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1001).dm (WitnessCertificates.Batch050.certificate1001).beta) ≤ ((CutFailureCertificates.Budget050.certificate1001).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1001 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1001).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch122.certificate1473).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch122.certificate1474).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch050.certificate1001).omega:ℝ) ≤ ((CutFailureCertificates.Budget050.certificate1001).bound:ℝ) at hb
  exact (exponentialBound472 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches473 : (MergedCutGroups.Batch123.certificate1477).GlobalMatches MergedCutGroups.Batch123.certificate1478 CountingCertificates.Batch050.certificate1004 CutLabelCertificates.Entropy035.certificate703 CutLabelCertificates.Minority035.certificate702 := by decide +kernel
theorem exponentialBound473 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch123.certificate1477).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1004).dm (WitnessCertificates.Batch050.certificate1004).beta) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1004).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch123.certificate1477).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch123.certificate1478).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch050.certificate1004).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch123.certificate1477 MergedCutGroups.Batch123.certificate1478 CountingCertificates.Batch050.certificate1004 CutLabelCertificates.Entropy035.certificate703 CutLabelCertificates.Minority035.certificate702 matches473 rfl rfl
    MergedCutGroups.Batch123.numericValid1477 MergedCutGroups.Batch123.numericValid1478 MergedCutGroups.Batch123.cellsSound1477 MergedCutGroups.Batch123.cellsSound1478
    MergedCutGroups.Batch123.cellsNumeric1477 MergedCutGroups.Batch123.cellsNumeric1478 MergedCutGroups.Batch123.populationMatches1477 MergedCutGroups.Batch123.populationMatches1478
    PopulationCertificates.Batch050.valid1004 PopulationCertificates.Batch050.sound1004 WitnessCertificates.Batch050.valid1004 WitnessCertificates.Batch050.sound1004 CountingCertificates.Batch050.valid1004 CountingCertificates.Batch050.sound1004
    CutLabelCertificates.Entropy035.valid703 CutLabelCertificates.Minority035.valid702 CutLabelCertificates.Minority035.sound702 H st hI
theorem probabilityBound473 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch123.certificate1477).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1004).dm (WitnessCertificates.Batch050.certificate1004).beta) ≤ ((CutFailureCertificates.Budget050.certificate1004).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1004 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1004).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch123.certificate1477).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch123.certificate1478).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch050.certificate1004).omega:ℝ) ≤ ((CutFailureCertificates.Budget050.certificate1004).bound:ℝ) at hb
  exact (exponentialBound473 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches474 : (MergedCutGroups.Batch123.certificate1481).GlobalMatches MergedCutGroups.Batch123.certificate1482 CountingCertificates.Batch050.certificate1007 CutLabelCertificates.Entropy035.certificate709 CutLabelCertificates.Minority035.certificate708 := by decide +kernel
theorem exponentialBound474 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch123.certificate1481).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1007).dm (WitnessCertificates.Batch050.certificate1007).beta) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1007).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch123.certificate1481).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch123.certificate1482).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch050.certificate1007).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch123.certificate1481 MergedCutGroups.Batch123.certificate1482 CountingCertificates.Batch050.certificate1007 CutLabelCertificates.Entropy035.certificate709 CutLabelCertificates.Minority035.certificate708 matches474 rfl rfl
    MergedCutGroups.Batch123.numericValid1481 MergedCutGroups.Batch123.numericValid1482 MergedCutGroups.Batch123.cellsSound1481 MergedCutGroups.Batch123.cellsSound1482
    MergedCutGroups.Batch123.cellsNumeric1481 MergedCutGroups.Batch123.cellsNumeric1482 MergedCutGroups.Batch123.populationMatches1481 MergedCutGroups.Batch123.populationMatches1482
    PopulationCertificates.Batch050.valid1007 PopulationCertificates.Batch050.sound1007 WitnessCertificates.Batch050.valid1007 WitnessCertificates.Batch050.sound1007 CountingCertificates.Batch050.valid1007 CountingCertificates.Batch050.sound1007
    CutLabelCertificates.Entropy035.valid709 CutLabelCertificates.Minority035.valid708 CutLabelCertificates.Minority035.sound708 H st hI
theorem probabilityBound474 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch123.certificate1481).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1007).dm (WitnessCertificates.Batch050.certificate1007).beta) ≤ ((CutFailureCertificates.Budget050.certificate1007).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1007 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1007).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch123.certificate1481).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch123.certificate1482).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch050.certificate1007).omega:ℝ) ≤ ((CutFailureCertificates.Budget050.certificate1007).bound:ℝ) at hb
  exact (exponentialBound474 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches475 : (MergedCutGroups.Batch123.certificate1485).GlobalMatches MergedCutGroups.Batch123.certificate1486 CountingCertificates.Batch050.certificate1010 CutLabelCertificates.Entropy035.certificate715 CutLabelCertificates.Minority035.certificate714 := by decide +kernel
theorem exponentialBound475 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch123.certificate1485).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1010).dm (WitnessCertificates.Batch050.certificate1010).beta) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1010).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch123.certificate1485).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch123.certificate1486).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch050.certificate1010).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch123.certificate1485 MergedCutGroups.Batch123.certificate1486 CountingCertificates.Batch050.certificate1010 CutLabelCertificates.Entropy035.certificate715 CutLabelCertificates.Minority035.certificate714 matches475 rfl rfl
    MergedCutGroups.Batch123.numericValid1485 MergedCutGroups.Batch123.numericValid1486 MergedCutGroups.Batch123.cellsSound1485 MergedCutGroups.Batch123.cellsSound1486
    MergedCutGroups.Batch123.cellsNumeric1485 MergedCutGroups.Batch123.cellsNumeric1486 MergedCutGroups.Batch123.populationMatches1485 MergedCutGroups.Batch123.populationMatches1486
    PopulationCertificates.Batch050.valid1010 PopulationCertificates.Batch050.sound1010 WitnessCertificates.Batch050.valid1010 WitnessCertificates.Batch050.sound1010 CountingCertificates.Batch050.valid1010 CountingCertificates.Batch050.sound1010
    CutLabelCertificates.Entropy035.valid715 CutLabelCertificates.Minority035.valid714 CutLabelCertificates.Minority035.sound714 H st hI
theorem probabilityBound475 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch123.certificate1485).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1010).dm (WitnessCertificates.Batch050.certificate1010).beta) ≤ ((CutFailureCertificates.Budget050.certificate1010).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1010 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1010).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch123.certificate1485).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch123.certificate1486).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch050.certificate1010).omega:ℝ) ≤ ((CutFailureCertificates.Budget050.certificate1010).bound:ℝ) at hb
  exact (exponentialBound475 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches476 : (MergedCutGroups.Batch124.certificate1489).GlobalMatches MergedCutGroups.Batch124.certificate1490 CountingCertificates.Batch050.certificate1013 CutLabelCertificates.Entropy036.certificate721 CutLabelCertificates.Minority036.certificate720 := by decide +kernel
theorem exponentialBound476 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch124.certificate1489).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1013).dm (WitnessCertificates.Batch050.certificate1013).beta) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1013).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch124.certificate1489).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch124.certificate1490).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch050.certificate1013).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch124.certificate1489 MergedCutGroups.Batch124.certificate1490 CountingCertificates.Batch050.certificate1013 CutLabelCertificates.Entropy036.certificate721 CutLabelCertificates.Minority036.certificate720 matches476 rfl rfl
    MergedCutGroups.Batch124.numericValid1489 MergedCutGroups.Batch124.numericValid1490 MergedCutGroups.Batch124.cellsSound1489 MergedCutGroups.Batch124.cellsSound1490
    MergedCutGroups.Batch124.cellsNumeric1489 MergedCutGroups.Batch124.cellsNumeric1490 MergedCutGroups.Batch124.populationMatches1489 MergedCutGroups.Batch124.populationMatches1490
    PopulationCertificates.Batch050.valid1013 PopulationCertificates.Batch050.sound1013 WitnessCertificates.Batch050.valid1013 WitnessCertificates.Batch050.sound1013 CountingCertificates.Batch050.valid1013 CountingCertificates.Batch050.sound1013
    CutLabelCertificates.Entropy036.valid721 CutLabelCertificates.Minority036.valid720 CutLabelCertificates.Minority036.sound720 H st hI
theorem probabilityBound476 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch124.certificate1489).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1013).dm (WitnessCertificates.Batch050.certificate1013).beta) ≤ ((CutFailureCertificates.Budget050.certificate1013).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1013 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1013).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch124.certificate1489).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch124.certificate1490).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch050.certificate1013).omega:ℝ) ≤ ((CutFailureCertificates.Budget050.certificate1013).bound:ℝ) at hb
  exact (exponentialBound476 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches477 : (MergedCutGroups.Batch124.certificate1493).GlobalMatches MergedCutGroups.Batch124.certificate1494 CountingCertificates.Batch050.certificate1016 CutLabelCertificates.Entropy036.certificate727 CutLabelCertificates.Minority036.certificate726 := by decide +kernel
theorem exponentialBound477 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch124.certificate1493).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1016).dm (WitnessCertificates.Batch050.certificate1016).beta) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1016).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch124.certificate1493).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch124.certificate1494).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch050.certificate1016).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch124.certificate1493 MergedCutGroups.Batch124.certificate1494 CountingCertificates.Batch050.certificate1016 CutLabelCertificates.Entropy036.certificate727 CutLabelCertificates.Minority036.certificate726 matches477 rfl rfl
    MergedCutGroups.Batch124.numericValid1493 MergedCutGroups.Batch124.numericValid1494 MergedCutGroups.Batch124.cellsSound1493 MergedCutGroups.Batch124.cellsSound1494
    MergedCutGroups.Batch124.cellsNumeric1493 MergedCutGroups.Batch124.cellsNumeric1494 MergedCutGroups.Batch124.populationMatches1493 MergedCutGroups.Batch124.populationMatches1494
    PopulationCertificates.Batch050.valid1016 PopulationCertificates.Batch050.sound1016 WitnessCertificates.Batch050.valid1016 WitnessCertificates.Batch050.sound1016 CountingCertificates.Batch050.valid1016 CountingCertificates.Batch050.sound1016
    CutLabelCertificates.Entropy036.valid727 CutLabelCertificates.Minority036.valid726 CutLabelCertificates.Minority036.sound726 H st hI
theorem probabilityBound477 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch124.certificate1493).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1016).dm (WitnessCertificates.Batch050.certificate1016).beta) ≤ ((CutFailureCertificates.Budget050.certificate1016).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1016 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1016).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch124.certificate1493).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch124.certificate1494).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch050.certificate1016).omega:ℝ) ≤ ((CutFailureCertificates.Budget050.certificate1016).bound:ℝ) at hb
  exact (exponentialBound477 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches478 : (MergedCutGroups.Batch124.certificate1497).GlobalMatches MergedCutGroups.Batch124.certificate1498 CountingCertificates.Batch050.certificate1019 CutLabelCertificates.Entropy036.certificate733 CutLabelCertificates.Minority036.certificate732 := by decide +kernel
theorem exponentialBound478 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch124.certificate1497).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1019).dm (WitnessCertificates.Batch050.certificate1019).beta) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1019).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch124.certificate1497).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch124.certificate1498).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch050.certificate1019).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch124.certificate1497 MergedCutGroups.Batch124.certificate1498 CountingCertificates.Batch050.certificate1019 CutLabelCertificates.Entropy036.certificate733 CutLabelCertificates.Minority036.certificate732 matches478 rfl rfl
    MergedCutGroups.Batch124.numericValid1497 MergedCutGroups.Batch124.numericValid1498 MergedCutGroups.Batch124.cellsSound1497 MergedCutGroups.Batch124.cellsSound1498
    MergedCutGroups.Batch124.cellsNumeric1497 MergedCutGroups.Batch124.cellsNumeric1498 MergedCutGroups.Batch124.populationMatches1497 MergedCutGroups.Batch124.populationMatches1498
    PopulationCertificates.Batch050.valid1019 PopulationCertificates.Batch050.sound1019 WitnessCertificates.Batch050.valid1019 WitnessCertificates.Batch050.sound1019 CountingCertificates.Batch050.valid1019 CountingCertificates.Batch050.sound1019
    CutLabelCertificates.Entropy036.valid733 CutLabelCertificates.Minority036.valid732 CutLabelCertificates.Minority036.sound732 H st hI
theorem probabilityBound478 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch124.certificate1497).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1019).dm (WitnessCertificates.Batch050.certificate1019).beta) ≤ ((CutFailureCertificates.Budget050.certificate1019).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1019 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1019).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch124.certificate1497).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch124.certificate1498).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch050.certificate1019).omega:ℝ) ≤ ((CutFailureCertificates.Budget050.certificate1019).bound:ℝ) at hb
  exact (exponentialBound478 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches479 : (MergedCutGroups.Batch125.certificate1501).GlobalMatches MergedCutGroups.Batch125.certificate1502 CountingCertificates.Batch051.certificate1022 CutLabelCertificates.Entropy036.certificate739 CutLabelCertificates.Minority036.certificate738 := by decide +kernel
theorem exponentialBound479 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch125.certificate1501).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1022).dm (WitnessCertificates.Batch051.certificate1022).beta) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1022).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch125.certificate1501).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch125.certificate1502).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch051.certificate1022).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch125.certificate1501 MergedCutGroups.Batch125.certificate1502 CountingCertificates.Batch051.certificate1022 CutLabelCertificates.Entropy036.certificate739 CutLabelCertificates.Minority036.certificate738 matches479 rfl rfl
    MergedCutGroups.Batch125.numericValid1501 MergedCutGroups.Batch125.numericValid1502 MergedCutGroups.Batch125.cellsSound1501 MergedCutGroups.Batch125.cellsSound1502
    MergedCutGroups.Batch125.cellsNumeric1501 MergedCutGroups.Batch125.cellsNumeric1502 MergedCutGroups.Batch125.populationMatches1501 MergedCutGroups.Batch125.populationMatches1502
    PopulationCertificates.Batch051.valid1022 PopulationCertificates.Batch051.sound1022 WitnessCertificates.Batch051.valid1022 WitnessCertificates.Batch051.sound1022 CountingCertificates.Batch051.valid1022 CountingCertificates.Batch051.sound1022
    CutLabelCertificates.Entropy036.valid739 CutLabelCertificates.Minority036.valid738 CutLabelCertificates.Minority036.sound738 H st hI
theorem probabilityBound479 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch125.certificate1501).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1022).dm (WitnessCertificates.Batch051.certificate1022).beta) ≤ ((CutFailureCertificates.Budget051.certificate1022).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1022 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1022).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch125.certificate1501).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch125.certificate1502).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch051.certificate1022).omega:ℝ) ≤ ((CutFailureCertificates.Budget051.certificate1022).bound:ℝ) at hb
  exact (exponentialBound479 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch023
