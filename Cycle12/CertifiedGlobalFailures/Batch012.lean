import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch024
import Cycle12.CountingCertificates.Batch025
import Cycle12.CutFailureCertificates.Budget024
import Cycle12.CutFailureCertificates.Budget025
import Cycle12.CutLabelCertificates.Entropy012
import Cycle12.CutLabelCertificates.Entropy013
import Cycle12.CutLabelCertificates.Minority012
import Cycle12.MergedCutGroups.Batch060
import Cycle12.MergedCutGroups.Batch061
import Cycle12.MergedCutGroups.Batch062
import Cycle12.MergedCutGroups.Batch063
import Cycle12.MergedCutGroups.Batch064
import Cycle12.PopulationCertificates.Batch024
import Cycle12.PopulationCertificates.Batch025
import Cycle12.WitnessCertificates.Batch024
import Cycle12.WitnessCertificates.Batch025

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch012
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches240 : (MergedCutGroups.Batch060.certificate720).GlobalMatches MergedCutGroups.Batch060.certificate721 CountingCertificates.Batch024.certificate480 CutLabelCertificates.Entropy012.certificate241 CutLabelCertificates.Minority012.certificate240 := by decide +kernel
theorem exponentialBound240 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch060.certificate720).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate480).dm (WitnessCertificates.Batch024.certificate480).beta) ≤ (2*exp (-((CountingCertificates.Batch024.certificate480).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch060.certificate720).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch060.certificate721).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch024.certificate480).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch060.certificate720 MergedCutGroups.Batch060.certificate721 CountingCertificates.Batch024.certificate480 CutLabelCertificates.Entropy012.certificate241 CutLabelCertificates.Minority012.certificate240 matches240 rfl rfl
    MergedCutGroups.Batch060.numericValid720 MergedCutGroups.Batch060.numericValid721 MergedCutGroups.Batch060.cellsSound720 MergedCutGroups.Batch060.cellsSound721
    MergedCutGroups.Batch060.cellsNumeric720 MergedCutGroups.Batch060.cellsNumeric721 MergedCutGroups.Batch060.populationMatches720 MergedCutGroups.Batch060.populationMatches721
    PopulationCertificates.Batch024.valid480 PopulationCertificates.Batch024.sound480 WitnessCertificates.Batch024.valid480 WitnessCertificates.Batch024.sound480 CountingCertificates.Batch024.valid480 CountingCertificates.Batch024.sound480
    CutLabelCertificates.Entropy012.valid241 CutLabelCertificates.Minority012.valid240 CutLabelCertificates.Minority012.sound240 H st hI
theorem probabilityBound240 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch060.certificate720).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate480).dm (WitnessCertificates.Batch024.certificate480).beta) ≤ ((CutFailureCertificates.Budget024.certificate480).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound480 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate480).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch060.certificate720).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch060.certificate721).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch024.certificate480).omega:ℝ) ≤ ((CutFailureCertificates.Budget024.certificate480).bound:ℝ) at hb
  exact (exponentialBound240 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches241 : (MergedCutGroups.Batch060.certificate723).GlobalMatches MergedCutGroups.Batch060.certificate724 CountingCertificates.Batch024.certificate482 CutLabelCertificates.Entropy012.certificate242 CutLabelCertificates.Minority012.certificate241 := by decide +kernel
theorem exponentialBound241 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch060.certificate723).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate482).dm (WitnessCertificates.Batch024.certificate482).beta) ≤ (2*exp (-((CountingCertificates.Batch024.certificate482).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch060.certificate723).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch060.certificate724).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch024.certificate482).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch060.certificate723 MergedCutGroups.Batch060.certificate724 CountingCertificates.Batch024.certificate482 CutLabelCertificates.Entropy012.certificate242 CutLabelCertificates.Minority012.certificate241 matches241 rfl rfl
    MergedCutGroups.Batch060.numericValid723 MergedCutGroups.Batch060.numericValid724 MergedCutGroups.Batch060.cellsSound723 MergedCutGroups.Batch060.cellsSound724
    MergedCutGroups.Batch060.cellsNumeric723 MergedCutGroups.Batch060.cellsNumeric724 MergedCutGroups.Batch060.populationMatches723 MergedCutGroups.Batch060.populationMatches724
    PopulationCertificates.Batch024.valid482 PopulationCertificates.Batch024.sound482 WitnessCertificates.Batch024.valid482 WitnessCertificates.Batch024.sound482 CountingCertificates.Batch024.valid482 CountingCertificates.Batch024.sound482
    CutLabelCertificates.Entropy012.valid242 CutLabelCertificates.Minority012.valid241 CutLabelCertificates.Minority012.sound241 H st hI
theorem probabilityBound241 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch060.certificate723).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate482).dm (WitnessCertificates.Batch024.certificate482).beta) ≤ ((CutFailureCertificates.Budget024.certificate482).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound482 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate482).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch060.certificate723).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch060.certificate724).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch024.certificate482).omega:ℝ) ≤ ((CutFailureCertificates.Budget024.certificate482).bound:ℝ) at hb
  exact (exponentialBound241 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches242 : (MergedCutGroups.Batch060.certificate726).GlobalMatches MergedCutGroups.Batch060.certificate727 CountingCertificates.Batch024.certificate484 CutLabelCertificates.Entropy012.certificate243 CutLabelCertificates.Minority012.certificate242 := by decide +kernel
theorem exponentialBound242 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch060.certificate726).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate484).dm (WitnessCertificates.Batch024.certificate484).beta) ≤ (2*exp (-((CountingCertificates.Batch024.certificate484).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch060.certificate726).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch060.certificate727).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch024.certificate484).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch060.certificate726 MergedCutGroups.Batch060.certificate727 CountingCertificates.Batch024.certificate484 CutLabelCertificates.Entropy012.certificate243 CutLabelCertificates.Minority012.certificate242 matches242 rfl rfl
    MergedCutGroups.Batch060.numericValid726 MergedCutGroups.Batch060.numericValid727 MergedCutGroups.Batch060.cellsSound726 MergedCutGroups.Batch060.cellsSound727
    MergedCutGroups.Batch060.cellsNumeric726 MergedCutGroups.Batch060.cellsNumeric727 MergedCutGroups.Batch060.populationMatches726 MergedCutGroups.Batch060.populationMatches727
    PopulationCertificates.Batch024.valid484 PopulationCertificates.Batch024.sound484 WitnessCertificates.Batch024.valid484 WitnessCertificates.Batch024.sound484 CountingCertificates.Batch024.valid484 CountingCertificates.Batch024.sound484
    CutLabelCertificates.Entropy012.valid243 CutLabelCertificates.Minority012.valid242 CutLabelCertificates.Minority012.sound242 H st hI
theorem probabilityBound242 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch060.certificate726).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate484).dm (WitnessCertificates.Batch024.certificate484).beta) ≤ ((CutFailureCertificates.Budget024.certificate484).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound484 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate484).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch060.certificate726).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch060.certificate727).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch024.certificate484).omega:ℝ) ≤ ((CutFailureCertificates.Budget024.certificate484).bound:ℝ) at hb
  exact (exponentialBound242 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches243 : (MergedCutGroups.Batch060.certificate729).GlobalMatches MergedCutGroups.Batch060.certificate730 CountingCertificates.Batch024.certificate486 CutLabelCertificates.Entropy012.certificate244 CutLabelCertificates.Minority012.certificate243 := by decide +kernel
theorem exponentialBound243 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch060.certificate729).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate486).dm (WitnessCertificates.Batch024.certificate486).beta) ≤ (2*exp (-((CountingCertificates.Batch024.certificate486).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch060.certificate729).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch060.certificate730).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch024.certificate486).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch060.certificate729 MergedCutGroups.Batch060.certificate730 CountingCertificates.Batch024.certificate486 CutLabelCertificates.Entropy012.certificate244 CutLabelCertificates.Minority012.certificate243 matches243 rfl rfl
    MergedCutGroups.Batch060.numericValid729 MergedCutGroups.Batch060.numericValid730 MergedCutGroups.Batch060.cellsSound729 MergedCutGroups.Batch060.cellsSound730
    MergedCutGroups.Batch060.cellsNumeric729 MergedCutGroups.Batch060.cellsNumeric730 MergedCutGroups.Batch060.populationMatches729 MergedCutGroups.Batch060.populationMatches730
    PopulationCertificates.Batch024.valid486 PopulationCertificates.Batch024.sound486 WitnessCertificates.Batch024.valid486 WitnessCertificates.Batch024.sound486 CountingCertificates.Batch024.valid486 CountingCertificates.Batch024.sound486
    CutLabelCertificates.Entropy012.valid244 CutLabelCertificates.Minority012.valid243 CutLabelCertificates.Minority012.sound243 H st hI
theorem probabilityBound243 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch060.certificate729).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate486).dm (WitnessCertificates.Batch024.certificate486).beta) ≤ ((CutFailureCertificates.Budget024.certificate486).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound486 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate486).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch060.certificate729).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch060.certificate730).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch024.certificate486).omega:ℝ) ≤ ((CutFailureCertificates.Budget024.certificate486).bound:ℝ) at hb
  exact (exponentialBound243 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches244 : (MergedCutGroups.Batch061.certificate732).GlobalMatches MergedCutGroups.Batch061.certificate733 CountingCertificates.Batch024.certificate488 CutLabelCertificates.Entropy012.certificate245 CutLabelCertificates.Minority012.certificate244 := by decide +kernel
theorem exponentialBound244 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch061.certificate732).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate488).dm (WitnessCertificates.Batch024.certificate488).beta) ≤ (2*exp (-((CountingCertificates.Batch024.certificate488).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch061.certificate732).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch061.certificate733).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch024.certificate488).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch061.certificate732 MergedCutGroups.Batch061.certificate733 CountingCertificates.Batch024.certificate488 CutLabelCertificates.Entropy012.certificate245 CutLabelCertificates.Minority012.certificate244 matches244 rfl rfl
    MergedCutGroups.Batch061.numericValid732 MergedCutGroups.Batch061.numericValid733 MergedCutGroups.Batch061.cellsSound732 MergedCutGroups.Batch061.cellsSound733
    MergedCutGroups.Batch061.cellsNumeric732 MergedCutGroups.Batch061.cellsNumeric733 MergedCutGroups.Batch061.populationMatches732 MergedCutGroups.Batch061.populationMatches733
    PopulationCertificates.Batch024.valid488 PopulationCertificates.Batch024.sound488 WitnessCertificates.Batch024.valid488 WitnessCertificates.Batch024.sound488 CountingCertificates.Batch024.valid488 CountingCertificates.Batch024.sound488
    CutLabelCertificates.Entropy012.valid245 CutLabelCertificates.Minority012.valid244 CutLabelCertificates.Minority012.sound244 H st hI
theorem probabilityBound244 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch061.certificate732).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate488).dm (WitnessCertificates.Batch024.certificate488).beta) ≤ ((CutFailureCertificates.Budget024.certificate488).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound488 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate488).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch061.certificate732).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch061.certificate733).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch024.certificate488).omega:ℝ) ≤ ((CutFailureCertificates.Budget024.certificate488).bound:ℝ) at hb
  exact (exponentialBound244 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches245 : (MergedCutGroups.Batch061.certificate735).GlobalMatches MergedCutGroups.Batch061.certificate736 CountingCertificates.Batch024.certificate490 CutLabelCertificates.Entropy012.certificate246 CutLabelCertificates.Minority012.certificate245 := by decide +kernel
theorem exponentialBound245 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch061.certificate735).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate490).dm (WitnessCertificates.Batch024.certificate490).beta) ≤ (2*exp (-((CountingCertificates.Batch024.certificate490).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch061.certificate735).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch061.certificate736).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch024.certificate490).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch061.certificate735 MergedCutGroups.Batch061.certificate736 CountingCertificates.Batch024.certificate490 CutLabelCertificates.Entropy012.certificate246 CutLabelCertificates.Minority012.certificate245 matches245 rfl rfl
    MergedCutGroups.Batch061.numericValid735 MergedCutGroups.Batch061.numericValid736 MergedCutGroups.Batch061.cellsSound735 MergedCutGroups.Batch061.cellsSound736
    MergedCutGroups.Batch061.cellsNumeric735 MergedCutGroups.Batch061.cellsNumeric736 MergedCutGroups.Batch061.populationMatches735 MergedCutGroups.Batch061.populationMatches736
    PopulationCertificates.Batch024.valid490 PopulationCertificates.Batch024.sound490 WitnessCertificates.Batch024.valid490 WitnessCertificates.Batch024.sound490 CountingCertificates.Batch024.valid490 CountingCertificates.Batch024.sound490
    CutLabelCertificates.Entropy012.valid246 CutLabelCertificates.Minority012.valid245 CutLabelCertificates.Minority012.sound245 H st hI
theorem probabilityBound245 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch061.certificate735).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate490).dm (WitnessCertificates.Batch024.certificate490).beta) ≤ ((CutFailureCertificates.Budget024.certificate490).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound490 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate490).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch061.certificate735).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch061.certificate736).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch024.certificate490).omega:ℝ) ≤ ((CutFailureCertificates.Budget024.certificate490).bound:ℝ) at hb
  exact (exponentialBound245 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches246 : (MergedCutGroups.Batch061.certificate738).GlobalMatches MergedCutGroups.Batch061.certificate739 CountingCertificates.Batch024.certificate492 CutLabelCertificates.Entropy012.certificate247 CutLabelCertificates.Minority012.certificate246 := by decide +kernel
theorem exponentialBound246 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch061.certificate738).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate492).dm (WitnessCertificates.Batch024.certificate492).beta) ≤ (2*exp (-((CountingCertificates.Batch024.certificate492).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch061.certificate738).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch061.certificate739).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch024.certificate492).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch061.certificate738 MergedCutGroups.Batch061.certificate739 CountingCertificates.Batch024.certificate492 CutLabelCertificates.Entropy012.certificate247 CutLabelCertificates.Minority012.certificate246 matches246 rfl rfl
    MergedCutGroups.Batch061.numericValid738 MergedCutGroups.Batch061.numericValid739 MergedCutGroups.Batch061.cellsSound738 MergedCutGroups.Batch061.cellsSound739
    MergedCutGroups.Batch061.cellsNumeric738 MergedCutGroups.Batch061.cellsNumeric739 MergedCutGroups.Batch061.populationMatches738 MergedCutGroups.Batch061.populationMatches739
    PopulationCertificates.Batch024.valid492 PopulationCertificates.Batch024.sound492 WitnessCertificates.Batch024.valid492 WitnessCertificates.Batch024.sound492 CountingCertificates.Batch024.valid492 CountingCertificates.Batch024.sound492
    CutLabelCertificates.Entropy012.valid247 CutLabelCertificates.Minority012.valid246 CutLabelCertificates.Minority012.sound246 H st hI
theorem probabilityBound246 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch061.certificate738).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate492).dm (WitnessCertificates.Batch024.certificate492).beta) ≤ ((CutFailureCertificates.Budget024.certificate492).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound492 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate492).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch061.certificate738).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch061.certificate739).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch024.certificate492).omega:ℝ) ≤ ((CutFailureCertificates.Budget024.certificate492).bound:ℝ) at hb
  exact (exponentialBound246 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches247 : (MergedCutGroups.Batch061.certificate741).GlobalMatches MergedCutGroups.Batch061.certificate742 CountingCertificates.Batch024.certificate494 CutLabelCertificates.Entropy012.certificate248 CutLabelCertificates.Minority012.certificate247 := by decide +kernel
theorem exponentialBound247 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch061.certificate741).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate494).dm (WitnessCertificates.Batch024.certificate494).beta) ≤ (2*exp (-((CountingCertificates.Batch024.certificate494).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch061.certificate741).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch061.certificate742).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch024.certificate494).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch061.certificate741 MergedCutGroups.Batch061.certificate742 CountingCertificates.Batch024.certificate494 CutLabelCertificates.Entropy012.certificate248 CutLabelCertificates.Minority012.certificate247 matches247 rfl rfl
    MergedCutGroups.Batch061.numericValid741 MergedCutGroups.Batch061.numericValid742 MergedCutGroups.Batch061.cellsSound741 MergedCutGroups.Batch061.cellsSound742
    MergedCutGroups.Batch061.cellsNumeric741 MergedCutGroups.Batch061.cellsNumeric742 MergedCutGroups.Batch061.populationMatches741 MergedCutGroups.Batch061.populationMatches742
    PopulationCertificates.Batch024.valid494 PopulationCertificates.Batch024.sound494 WitnessCertificates.Batch024.valid494 WitnessCertificates.Batch024.sound494 CountingCertificates.Batch024.valid494 CountingCertificates.Batch024.sound494
    CutLabelCertificates.Entropy012.valid248 CutLabelCertificates.Minority012.valid247 CutLabelCertificates.Minority012.sound247 H st hI
theorem probabilityBound247 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch061.certificate741).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate494).dm (WitnessCertificates.Batch024.certificate494).beta) ≤ ((CutFailureCertificates.Budget024.certificate494).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound494 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate494).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch061.certificate741).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch061.certificate742).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch024.certificate494).omega:ℝ) ≤ ((CutFailureCertificates.Budget024.certificate494).bound:ℝ) at hb
  exact (exponentialBound247 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches248 : (MergedCutGroups.Batch062.certificate744).GlobalMatches MergedCutGroups.Batch062.certificate745 CountingCertificates.Batch024.certificate496 CutLabelCertificates.Entropy012.certificate249 CutLabelCertificates.Minority012.certificate248 := by decide +kernel
theorem exponentialBound248 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch062.certificate744).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate496).dm (WitnessCertificates.Batch024.certificate496).beta) ≤ (2*exp (-((CountingCertificates.Batch024.certificate496).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch062.certificate744).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch062.certificate745).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch024.certificate496).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch062.certificate744 MergedCutGroups.Batch062.certificate745 CountingCertificates.Batch024.certificate496 CutLabelCertificates.Entropy012.certificate249 CutLabelCertificates.Minority012.certificate248 matches248 rfl rfl
    MergedCutGroups.Batch062.numericValid744 MergedCutGroups.Batch062.numericValid745 MergedCutGroups.Batch062.cellsSound744 MergedCutGroups.Batch062.cellsSound745
    MergedCutGroups.Batch062.cellsNumeric744 MergedCutGroups.Batch062.cellsNumeric745 MergedCutGroups.Batch062.populationMatches744 MergedCutGroups.Batch062.populationMatches745
    PopulationCertificates.Batch024.valid496 PopulationCertificates.Batch024.sound496 WitnessCertificates.Batch024.valid496 WitnessCertificates.Batch024.sound496 CountingCertificates.Batch024.valid496 CountingCertificates.Batch024.sound496
    CutLabelCertificates.Entropy012.valid249 CutLabelCertificates.Minority012.valid248 CutLabelCertificates.Minority012.sound248 H st hI
theorem probabilityBound248 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch062.certificate744).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate496).dm (WitnessCertificates.Batch024.certificate496).beta) ≤ ((CutFailureCertificates.Budget024.certificate496).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound496 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate496).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch062.certificate744).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch062.certificate745).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch024.certificate496).omega:ℝ) ≤ ((CutFailureCertificates.Budget024.certificate496).bound:ℝ) at hb
  exact (exponentialBound248 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches249 : (MergedCutGroups.Batch062.certificate747).GlobalMatches MergedCutGroups.Batch062.certificate748 CountingCertificates.Batch024.certificate498 CutLabelCertificates.Entropy012.certificate250 CutLabelCertificates.Minority012.certificate249 := by decide +kernel
theorem exponentialBound249 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch062.certificate747).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate498).dm (WitnessCertificates.Batch024.certificate498).beta) ≤ (2*exp (-((CountingCertificates.Batch024.certificate498).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch062.certificate747).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch062.certificate748).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch024.certificate498).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch062.certificate747 MergedCutGroups.Batch062.certificate748 CountingCertificates.Batch024.certificate498 CutLabelCertificates.Entropy012.certificate250 CutLabelCertificates.Minority012.certificate249 matches249 rfl rfl
    MergedCutGroups.Batch062.numericValid747 MergedCutGroups.Batch062.numericValid748 MergedCutGroups.Batch062.cellsSound747 MergedCutGroups.Batch062.cellsSound748
    MergedCutGroups.Batch062.cellsNumeric747 MergedCutGroups.Batch062.cellsNumeric748 MergedCutGroups.Batch062.populationMatches747 MergedCutGroups.Batch062.populationMatches748
    PopulationCertificates.Batch024.valid498 PopulationCertificates.Batch024.sound498 WitnessCertificates.Batch024.valid498 WitnessCertificates.Batch024.sound498 CountingCertificates.Batch024.valid498 CountingCertificates.Batch024.sound498
    CutLabelCertificates.Entropy012.valid250 CutLabelCertificates.Minority012.valid249 CutLabelCertificates.Minority012.sound249 H st hI
theorem probabilityBound249 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch062.certificate747).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch024.certificate498).dm (WitnessCertificates.Batch024.certificate498).beta) ≤ ((CutFailureCertificates.Budget024.certificate498).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound498 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate498).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch062.certificate747).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch062.certificate748).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch024.certificate498).omega:ℝ) ≤ ((CutFailureCertificates.Budget024.certificate498).bound:ℝ) at hb
  exact (exponentialBound249 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches250 : (MergedCutGroups.Batch062.certificate750).GlobalMatches MergedCutGroups.Batch062.certificate751 CountingCertificates.Batch025.certificate500 CutLabelCertificates.Entropy012.certificate251 CutLabelCertificates.Minority012.certificate250 := by decide +kernel
theorem exponentialBound250 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch062.certificate750).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate500).dm (WitnessCertificates.Batch025.certificate500).beta) ≤ (2*exp (-((CountingCertificates.Batch025.certificate500).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch062.certificate750).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch062.certificate751).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch025.certificate500).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch062.certificate750 MergedCutGroups.Batch062.certificate751 CountingCertificates.Batch025.certificate500 CutLabelCertificates.Entropy012.certificate251 CutLabelCertificates.Minority012.certificate250 matches250 rfl rfl
    MergedCutGroups.Batch062.numericValid750 MergedCutGroups.Batch062.numericValid751 MergedCutGroups.Batch062.cellsSound750 MergedCutGroups.Batch062.cellsSound751
    MergedCutGroups.Batch062.cellsNumeric750 MergedCutGroups.Batch062.cellsNumeric751 MergedCutGroups.Batch062.populationMatches750 MergedCutGroups.Batch062.populationMatches751
    PopulationCertificates.Batch025.valid500 PopulationCertificates.Batch025.sound500 WitnessCertificates.Batch025.valid500 WitnessCertificates.Batch025.sound500 CountingCertificates.Batch025.valid500 CountingCertificates.Batch025.sound500
    CutLabelCertificates.Entropy012.valid251 CutLabelCertificates.Minority012.valid250 CutLabelCertificates.Minority012.sound250 H st hI
theorem probabilityBound250 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch062.certificate750).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate500).dm (WitnessCertificates.Batch025.certificate500).beta) ≤ ((CutFailureCertificates.Budget025.certificate500).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound500 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate500).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch062.certificate750).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch062.certificate751).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch025.certificate500).omega:ℝ) ≤ ((CutFailureCertificates.Budget025.certificate500).bound:ℝ) at hb
  exact (exponentialBound250 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches251 : (MergedCutGroups.Batch062.certificate753).GlobalMatches MergedCutGroups.Batch062.certificate754 CountingCertificates.Batch025.certificate502 CutLabelCertificates.Entropy012.certificate252 CutLabelCertificates.Minority012.certificate251 := by decide +kernel
theorem exponentialBound251 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch062.certificate753).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate502).dm (WitnessCertificates.Batch025.certificate502).beta) ≤ (2*exp (-((CountingCertificates.Batch025.certificate502).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch062.certificate753).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch062.certificate754).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch025.certificate502).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch062.certificate753 MergedCutGroups.Batch062.certificate754 CountingCertificates.Batch025.certificate502 CutLabelCertificates.Entropy012.certificate252 CutLabelCertificates.Minority012.certificate251 matches251 rfl rfl
    MergedCutGroups.Batch062.numericValid753 MergedCutGroups.Batch062.numericValid754 MergedCutGroups.Batch062.cellsSound753 MergedCutGroups.Batch062.cellsSound754
    MergedCutGroups.Batch062.cellsNumeric753 MergedCutGroups.Batch062.cellsNumeric754 MergedCutGroups.Batch062.populationMatches753 MergedCutGroups.Batch062.populationMatches754
    PopulationCertificates.Batch025.valid502 PopulationCertificates.Batch025.sound502 WitnessCertificates.Batch025.valid502 WitnessCertificates.Batch025.sound502 CountingCertificates.Batch025.valid502 CountingCertificates.Batch025.sound502
    CutLabelCertificates.Entropy012.valid252 CutLabelCertificates.Minority012.valid251 CutLabelCertificates.Minority012.sound251 H st hI
theorem probabilityBound251 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch062.certificate753).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate502).dm (WitnessCertificates.Batch025.certificate502).beta) ≤ ((CutFailureCertificates.Budget025.certificate502).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound502 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate502).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch062.certificate753).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch062.certificate754).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch025.certificate502).omega:ℝ) ≤ ((CutFailureCertificates.Budget025.certificate502).bound:ℝ) at hb
  exact (exponentialBound251 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches252 : (MergedCutGroups.Batch063.certificate756).GlobalMatches MergedCutGroups.Batch063.certificate757 CountingCertificates.Batch025.certificate504 CutLabelCertificates.Entropy012.certificate253 CutLabelCertificates.Minority012.certificate252 := by decide +kernel
theorem exponentialBound252 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch063.certificate756).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate504).dm (WitnessCertificates.Batch025.certificate504).beta) ≤ (2*exp (-((CountingCertificates.Batch025.certificate504).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch063.certificate756).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch063.certificate757).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch025.certificate504).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch063.certificate756 MergedCutGroups.Batch063.certificate757 CountingCertificates.Batch025.certificate504 CutLabelCertificates.Entropy012.certificate253 CutLabelCertificates.Minority012.certificate252 matches252 rfl rfl
    MergedCutGroups.Batch063.numericValid756 MergedCutGroups.Batch063.numericValid757 MergedCutGroups.Batch063.cellsSound756 MergedCutGroups.Batch063.cellsSound757
    MergedCutGroups.Batch063.cellsNumeric756 MergedCutGroups.Batch063.cellsNumeric757 MergedCutGroups.Batch063.populationMatches756 MergedCutGroups.Batch063.populationMatches757
    PopulationCertificates.Batch025.valid504 PopulationCertificates.Batch025.sound504 WitnessCertificates.Batch025.valid504 WitnessCertificates.Batch025.sound504 CountingCertificates.Batch025.valid504 CountingCertificates.Batch025.sound504
    CutLabelCertificates.Entropy012.valid253 CutLabelCertificates.Minority012.valid252 CutLabelCertificates.Minority012.sound252 H st hI
theorem probabilityBound252 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch063.certificate756).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate504).dm (WitnessCertificates.Batch025.certificate504).beta) ≤ ((CutFailureCertificates.Budget025.certificate504).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound504 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate504).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch063.certificate756).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch063.certificate757).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch025.certificate504).omega:ℝ) ≤ ((CutFailureCertificates.Budget025.certificate504).bound:ℝ) at hb
  exact (exponentialBound252 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches253 : (MergedCutGroups.Batch063.certificate759).GlobalMatches MergedCutGroups.Batch063.certificate760 CountingCertificates.Batch025.certificate506 CutLabelCertificates.Entropy012.certificate254 CutLabelCertificates.Minority012.certificate253 := by decide +kernel
theorem exponentialBound253 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch063.certificate759).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate506).dm (WitnessCertificates.Batch025.certificate506).beta) ≤ (2*exp (-((CountingCertificates.Batch025.certificate506).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch063.certificate759).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch063.certificate760).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch025.certificate506).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch063.certificate759 MergedCutGroups.Batch063.certificate760 CountingCertificates.Batch025.certificate506 CutLabelCertificates.Entropy012.certificate254 CutLabelCertificates.Minority012.certificate253 matches253 rfl rfl
    MergedCutGroups.Batch063.numericValid759 MergedCutGroups.Batch063.numericValid760 MergedCutGroups.Batch063.cellsSound759 MergedCutGroups.Batch063.cellsSound760
    MergedCutGroups.Batch063.cellsNumeric759 MergedCutGroups.Batch063.cellsNumeric760 MergedCutGroups.Batch063.populationMatches759 MergedCutGroups.Batch063.populationMatches760
    PopulationCertificates.Batch025.valid506 PopulationCertificates.Batch025.sound506 WitnessCertificates.Batch025.valid506 WitnessCertificates.Batch025.sound506 CountingCertificates.Batch025.valid506 CountingCertificates.Batch025.sound506
    CutLabelCertificates.Entropy012.valid254 CutLabelCertificates.Minority012.valid253 CutLabelCertificates.Minority012.sound253 H st hI
theorem probabilityBound253 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch063.certificate759).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate506).dm (WitnessCertificates.Batch025.certificate506).beta) ≤ ((CutFailureCertificates.Budget025.certificate506).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound506 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate506).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch063.certificate759).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch063.certificate760).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch025.certificate506).omega:ℝ) ≤ ((CutFailureCertificates.Budget025.certificate506).bound:ℝ) at hb
  exact (exponentialBound253 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches254 : (MergedCutGroups.Batch063.certificate762).GlobalMatches MergedCutGroups.Batch063.certificate763 CountingCertificates.Batch025.certificate508 CutLabelCertificates.Entropy012.certificate255 CutLabelCertificates.Minority012.certificate254 := by decide +kernel
theorem exponentialBound254 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch063.certificate762).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate508).dm (WitnessCertificates.Batch025.certificate508).beta) ≤ (2*exp (-((CountingCertificates.Batch025.certificate508).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch063.certificate762).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch063.certificate763).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch025.certificate508).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch063.certificate762 MergedCutGroups.Batch063.certificate763 CountingCertificates.Batch025.certificate508 CutLabelCertificates.Entropy012.certificate255 CutLabelCertificates.Minority012.certificate254 matches254 rfl rfl
    MergedCutGroups.Batch063.numericValid762 MergedCutGroups.Batch063.numericValid763 MergedCutGroups.Batch063.cellsSound762 MergedCutGroups.Batch063.cellsSound763
    MergedCutGroups.Batch063.cellsNumeric762 MergedCutGroups.Batch063.cellsNumeric763 MergedCutGroups.Batch063.populationMatches762 MergedCutGroups.Batch063.populationMatches763
    PopulationCertificates.Batch025.valid508 PopulationCertificates.Batch025.sound508 WitnessCertificates.Batch025.valid508 WitnessCertificates.Batch025.sound508 CountingCertificates.Batch025.valid508 CountingCertificates.Batch025.sound508
    CutLabelCertificates.Entropy012.valid255 CutLabelCertificates.Minority012.valid254 CutLabelCertificates.Minority012.sound254 H st hI
theorem probabilityBound254 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch063.certificate762).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate508).dm (WitnessCertificates.Batch025.certificate508).beta) ≤ ((CutFailureCertificates.Budget025.certificate508).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound508 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate508).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch063.certificate762).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch063.certificate763).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch025.certificate508).omega:ℝ) ≤ ((CutFailureCertificates.Budget025.certificate508).bound:ℝ) at hb
  exact (exponentialBound254 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches255 : (MergedCutGroups.Batch063.certificate765).GlobalMatches MergedCutGroups.Batch063.certificate766 CountingCertificates.Batch025.certificate510 CutLabelCertificates.Entropy012.certificate256 CutLabelCertificates.Minority012.certificate255 := by decide +kernel
theorem exponentialBound255 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch063.certificate765).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate510).dm (WitnessCertificates.Batch025.certificate510).beta) ≤ (2*exp (-((CountingCertificates.Batch025.certificate510).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch063.certificate765).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch063.certificate766).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch025.certificate510).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch063.certificate765 MergedCutGroups.Batch063.certificate766 CountingCertificates.Batch025.certificate510 CutLabelCertificates.Entropy012.certificate256 CutLabelCertificates.Minority012.certificate255 matches255 rfl rfl
    MergedCutGroups.Batch063.numericValid765 MergedCutGroups.Batch063.numericValid766 MergedCutGroups.Batch063.cellsSound765 MergedCutGroups.Batch063.cellsSound766
    MergedCutGroups.Batch063.cellsNumeric765 MergedCutGroups.Batch063.cellsNumeric766 MergedCutGroups.Batch063.populationMatches765 MergedCutGroups.Batch063.populationMatches766
    PopulationCertificates.Batch025.valid510 PopulationCertificates.Batch025.sound510 WitnessCertificates.Batch025.valid510 WitnessCertificates.Batch025.sound510 CountingCertificates.Batch025.valid510 CountingCertificates.Batch025.sound510
    CutLabelCertificates.Entropy012.valid256 CutLabelCertificates.Minority012.valid255 CutLabelCertificates.Minority012.sound255 H st hI
theorem probabilityBound255 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch063.certificate765).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate510).dm (WitnessCertificates.Batch025.certificate510).beta) ≤ ((CutFailureCertificates.Budget025.certificate510).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound510 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate510).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch063.certificate765).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch063.certificate766).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch025.certificate510).omega:ℝ) ≤ ((CutFailureCertificates.Budget025.certificate510).bound:ℝ) at hb
  exact (exponentialBound255 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches256 : (MergedCutGroups.Batch064.certificate768).GlobalMatches MergedCutGroups.Batch064.certificate769 CountingCertificates.Batch025.certificate512 CutLabelCertificates.Entropy012.certificate257 CutLabelCertificates.Minority012.certificate256 := by decide +kernel
theorem exponentialBound256 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch064.certificate768).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate512).dm (WitnessCertificates.Batch025.certificate512).beta) ≤ (2*exp (-((CountingCertificates.Batch025.certificate512).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch064.certificate768).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch064.certificate769).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch025.certificate512).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch064.certificate768 MergedCutGroups.Batch064.certificate769 CountingCertificates.Batch025.certificate512 CutLabelCertificates.Entropy012.certificate257 CutLabelCertificates.Minority012.certificate256 matches256 rfl rfl
    MergedCutGroups.Batch064.numericValid768 MergedCutGroups.Batch064.numericValid769 MergedCutGroups.Batch064.cellsSound768 MergedCutGroups.Batch064.cellsSound769
    MergedCutGroups.Batch064.cellsNumeric768 MergedCutGroups.Batch064.cellsNumeric769 MergedCutGroups.Batch064.populationMatches768 MergedCutGroups.Batch064.populationMatches769
    PopulationCertificates.Batch025.valid512 PopulationCertificates.Batch025.sound512 WitnessCertificates.Batch025.valid512 WitnessCertificates.Batch025.sound512 CountingCertificates.Batch025.valid512 CountingCertificates.Batch025.sound512
    CutLabelCertificates.Entropy012.valid257 CutLabelCertificates.Minority012.valid256 CutLabelCertificates.Minority012.sound256 H st hI
theorem probabilityBound256 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch064.certificate768).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate512).dm (WitnessCertificates.Batch025.certificate512).beta) ≤ ((CutFailureCertificates.Budget025.certificate512).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound512 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate512).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch064.certificate768).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch064.certificate769).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch025.certificate512).omega:ℝ) ≤ ((CutFailureCertificates.Budget025.certificate512).bound:ℝ) at hb
  exact (exponentialBound256 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches257 : (MergedCutGroups.Batch064.certificate771).GlobalMatches MergedCutGroups.Batch064.certificate772 CountingCertificates.Batch025.certificate514 CutLabelCertificates.Entropy012.certificate258 CutLabelCertificates.Minority012.certificate257 := by decide +kernel
theorem exponentialBound257 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch064.certificate771).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate514).dm (WitnessCertificates.Batch025.certificate514).beta) ≤ (2*exp (-((CountingCertificates.Batch025.certificate514).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch064.certificate771).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch064.certificate772).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch025.certificate514).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch064.certificate771 MergedCutGroups.Batch064.certificate772 CountingCertificates.Batch025.certificate514 CutLabelCertificates.Entropy012.certificate258 CutLabelCertificates.Minority012.certificate257 matches257 rfl rfl
    MergedCutGroups.Batch064.numericValid771 MergedCutGroups.Batch064.numericValid772 MergedCutGroups.Batch064.cellsSound771 MergedCutGroups.Batch064.cellsSound772
    MergedCutGroups.Batch064.cellsNumeric771 MergedCutGroups.Batch064.cellsNumeric772 MergedCutGroups.Batch064.populationMatches771 MergedCutGroups.Batch064.populationMatches772
    PopulationCertificates.Batch025.valid514 PopulationCertificates.Batch025.sound514 WitnessCertificates.Batch025.valid514 WitnessCertificates.Batch025.sound514 CountingCertificates.Batch025.valid514 CountingCertificates.Batch025.sound514
    CutLabelCertificates.Entropy012.valid258 CutLabelCertificates.Minority012.valid257 CutLabelCertificates.Minority012.sound257 H st hI
theorem probabilityBound257 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch064.certificate771).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate514).dm (WitnessCertificates.Batch025.certificate514).beta) ≤ ((CutFailureCertificates.Budget025.certificate514).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound514 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate514).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch064.certificate771).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch064.certificate772).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch025.certificate514).omega:ℝ) ≤ ((CutFailureCertificates.Budget025.certificate514).bound:ℝ) at hb
  exact (exponentialBound257 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches258 : (MergedCutGroups.Batch064.certificate774).GlobalMatches MergedCutGroups.Batch064.certificate775 CountingCertificates.Batch025.certificate516 CutLabelCertificates.Entropy012.certificate259 CutLabelCertificates.Minority012.certificate258 := by decide +kernel
theorem exponentialBound258 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch064.certificate774).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate516).dm (WitnessCertificates.Batch025.certificate516).beta) ≤ (2*exp (-((CountingCertificates.Batch025.certificate516).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch064.certificate774).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch064.certificate775).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch025.certificate516).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch064.certificate774 MergedCutGroups.Batch064.certificate775 CountingCertificates.Batch025.certificate516 CutLabelCertificates.Entropy012.certificate259 CutLabelCertificates.Minority012.certificate258 matches258 rfl rfl
    MergedCutGroups.Batch064.numericValid774 MergedCutGroups.Batch064.numericValid775 MergedCutGroups.Batch064.cellsSound774 MergedCutGroups.Batch064.cellsSound775
    MergedCutGroups.Batch064.cellsNumeric774 MergedCutGroups.Batch064.cellsNumeric775 MergedCutGroups.Batch064.populationMatches774 MergedCutGroups.Batch064.populationMatches775
    PopulationCertificates.Batch025.valid516 PopulationCertificates.Batch025.sound516 WitnessCertificates.Batch025.valid516 WitnessCertificates.Batch025.sound516 CountingCertificates.Batch025.valid516 CountingCertificates.Batch025.sound516
    CutLabelCertificates.Entropy012.valid259 CutLabelCertificates.Minority012.valid258 CutLabelCertificates.Minority012.sound258 H st hI
theorem probabilityBound258 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch064.certificate774).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate516).dm (WitnessCertificates.Batch025.certificate516).beta) ≤ ((CutFailureCertificates.Budget025.certificate516).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound516 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate516).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch064.certificate774).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch064.certificate775).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch025.certificate516).omega:ℝ) ≤ ((CutFailureCertificates.Budget025.certificate516).bound:ℝ) at hb
  exact (exponentialBound258 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches259 : (MergedCutGroups.Batch064.certificate777).GlobalMatches MergedCutGroups.Batch064.certificate778 CountingCertificates.Batch025.certificate518 CutLabelCertificates.Entropy013.certificate260 CutLabelCertificates.Minority012.certificate259 := by decide +kernel
theorem exponentialBound259 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch064.certificate777).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate518).dm (WitnessCertificates.Batch025.certificate518).beta) ≤ (2*exp (-((CountingCertificates.Batch025.certificate518).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch064.certificate777).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch064.certificate778).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch025.certificate518).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch064.certificate777 MergedCutGroups.Batch064.certificate778 CountingCertificates.Batch025.certificate518 CutLabelCertificates.Entropy013.certificate260 CutLabelCertificates.Minority012.certificate259 matches259 rfl rfl
    MergedCutGroups.Batch064.numericValid777 MergedCutGroups.Batch064.numericValid778 MergedCutGroups.Batch064.cellsSound777 MergedCutGroups.Batch064.cellsSound778
    MergedCutGroups.Batch064.cellsNumeric777 MergedCutGroups.Batch064.cellsNumeric778 MergedCutGroups.Batch064.populationMatches777 MergedCutGroups.Batch064.populationMatches778
    PopulationCertificates.Batch025.valid518 PopulationCertificates.Batch025.sound518 WitnessCertificates.Batch025.valid518 WitnessCertificates.Batch025.sound518 CountingCertificates.Batch025.valid518 CountingCertificates.Batch025.sound518
    CutLabelCertificates.Entropy013.valid260 CutLabelCertificates.Minority012.valid259 CutLabelCertificates.Minority012.sound259 H st hI
theorem probabilityBound259 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch064.certificate777).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch025.certificate518).dm (WitnessCertificates.Batch025.certificate518).beta) ≤ ((CutFailureCertificates.Budget025.certificate518).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound518 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate518).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch064.certificate777).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch064.certificate778).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch025.certificate518).omega:ℝ) ≤ ((CutFailureCertificates.Budget025.certificate518).bound:ℝ) at hb
  exact (exponentialBound259 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch012
