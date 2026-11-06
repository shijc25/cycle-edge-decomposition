import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch022
import Cycle12.CountingCertificates.Batch023
import Cycle12.CutFailureCertificates.Budget022
import Cycle12.CutFailureCertificates.Budget023
import Cycle12.CutLabelCertificates.Entropy011
import Cycle12.CutLabelCertificates.Entropy012
import Cycle12.CutLabelCertificates.Minority011
import Cycle12.MergedCutGroups.Batch055
import Cycle12.MergedCutGroups.Batch056
import Cycle12.MergedCutGroups.Batch057
import Cycle12.MergedCutGroups.Batch058
import Cycle12.MergedCutGroups.Batch059
import Cycle12.PopulationCertificates.Batch022
import Cycle12.PopulationCertificates.Batch023
import Cycle12.WitnessCertificates.Batch022
import Cycle12.WitnessCertificates.Batch023

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch011
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches220 : (MergedCutGroups.Batch055.certificate660).GlobalMatches MergedCutGroups.Batch055.certificate661 CountingCertificates.Batch022.certificate440 CutLabelCertificates.Entropy011.certificate221 CutLabelCertificates.Minority011.certificate220 := by decide +kernel
theorem exponentialBound220 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch055.certificate660).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate440).dm (WitnessCertificates.Batch022.certificate440).beta) ≤ (2*exp (-((CountingCertificates.Batch022.certificate440).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch055.certificate660).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch055.certificate661).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch022.certificate440).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch055.certificate660 MergedCutGroups.Batch055.certificate661 CountingCertificates.Batch022.certificate440 CutLabelCertificates.Entropy011.certificate221 CutLabelCertificates.Minority011.certificate220 matches220 rfl rfl
    MergedCutGroups.Batch055.numericValid660 MergedCutGroups.Batch055.numericValid661 MergedCutGroups.Batch055.cellsSound660 MergedCutGroups.Batch055.cellsSound661
    MergedCutGroups.Batch055.cellsNumeric660 MergedCutGroups.Batch055.cellsNumeric661 MergedCutGroups.Batch055.populationMatches660 MergedCutGroups.Batch055.populationMatches661
    PopulationCertificates.Batch022.valid440 PopulationCertificates.Batch022.sound440 WitnessCertificates.Batch022.valid440 WitnessCertificates.Batch022.sound440 CountingCertificates.Batch022.valid440 CountingCertificates.Batch022.sound440
    CutLabelCertificates.Entropy011.valid221 CutLabelCertificates.Minority011.valid220 CutLabelCertificates.Minority011.sound220 H st hI
theorem probabilityBound220 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch055.certificate660).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate440).dm (WitnessCertificates.Batch022.certificate440).beta) ≤ ((CutFailureCertificates.Budget022.certificate440).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound440 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate440).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch055.certificate660).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch055.certificate661).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch022.certificate440).omega:ℝ) ≤ ((CutFailureCertificates.Budget022.certificate440).bound:ℝ) at hb
  exact (exponentialBound220 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches221 : (MergedCutGroups.Batch055.certificate663).GlobalMatches MergedCutGroups.Batch055.certificate664 CountingCertificates.Batch022.certificate442 CutLabelCertificates.Entropy011.certificate222 CutLabelCertificates.Minority011.certificate221 := by decide +kernel
theorem exponentialBound221 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch055.certificate663).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate442).dm (WitnessCertificates.Batch022.certificate442).beta) ≤ (2*exp (-((CountingCertificates.Batch022.certificate442).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch055.certificate663).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch055.certificate664).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch022.certificate442).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch055.certificate663 MergedCutGroups.Batch055.certificate664 CountingCertificates.Batch022.certificate442 CutLabelCertificates.Entropy011.certificate222 CutLabelCertificates.Minority011.certificate221 matches221 rfl rfl
    MergedCutGroups.Batch055.numericValid663 MergedCutGroups.Batch055.numericValid664 MergedCutGroups.Batch055.cellsSound663 MergedCutGroups.Batch055.cellsSound664
    MergedCutGroups.Batch055.cellsNumeric663 MergedCutGroups.Batch055.cellsNumeric664 MergedCutGroups.Batch055.populationMatches663 MergedCutGroups.Batch055.populationMatches664
    PopulationCertificates.Batch022.valid442 PopulationCertificates.Batch022.sound442 WitnessCertificates.Batch022.valid442 WitnessCertificates.Batch022.sound442 CountingCertificates.Batch022.valid442 CountingCertificates.Batch022.sound442
    CutLabelCertificates.Entropy011.valid222 CutLabelCertificates.Minority011.valid221 CutLabelCertificates.Minority011.sound221 H st hI
theorem probabilityBound221 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch055.certificate663).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate442).dm (WitnessCertificates.Batch022.certificate442).beta) ≤ ((CutFailureCertificates.Budget022.certificate442).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound442 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate442).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch055.certificate663).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch055.certificate664).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch022.certificate442).omega:ℝ) ≤ ((CutFailureCertificates.Budget022.certificate442).bound:ℝ) at hb
  exact (exponentialBound221 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches222 : (MergedCutGroups.Batch055.certificate666).GlobalMatches MergedCutGroups.Batch055.certificate667 CountingCertificates.Batch022.certificate444 CutLabelCertificates.Entropy011.certificate223 CutLabelCertificates.Minority011.certificate222 := by decide +kernel
theorem exponentialBound222 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch055.certificate666).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate444).dm (WitnessCertificates.Batch022.certificate444).beta) ≤ (2*exp (-((CountingCertificates.Batch022.certificate444).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch055.certificate666).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch055.certificate667).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch022.certificate444).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch055.certificate666 MergedCutGroups.Batch055.certificate667 CountingCertificates.Batch022.certificate444 CutLabelCertificates.Entropy011.certificate223 CutLabelCertificates.Minority011.certificate222 matches222 rfl rfl
    MergedCutGroups.Batch055.numericValid666 MergedCutGroups.Batch055.numericValid667 MergedCutGroups.Batch055.cellsSound666 MergedCutGroups.Batch055.cellsSound667
    MergedCutGroups.Batch055.cellsNumeric666 MergedCutGroups.Batch055.cellsNumeric667 MergedCutGroups.Batch055.populationMatches666 MergedCutGroups.Batch055.populationMatches667
    PopulationCertificates.Batch022.valid444 PopulationCertificates.Batch022.sound444 WitnessCertificates.Batch022.valid444 WitnessCertificates.Batch022.sound444 CountingCertificates.Batch022.valid444 CountingCertificates.Batch022.sound444
    CutLabelCertificates.Entropy011.valid223 CutLabelCertificates.Minority011.valid222 CutLabelCertificates.Minority011.sound222 H st hI
theorem probabilityBound222 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch055.certificate666).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate444).dm (WitnessCertificates.Batch022.certificate444).beta) ≤ ((CutFailureCertificates.Budget022.certificate444).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound444 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate444).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch055.certificate666).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch055.certificate667).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch022.certificate444).omega:ℝ) ≤ ((CutFailureCertificates.Budget022.certificate444).bound:ℝ) at hb
  exact (exponentialBound222 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches223 : (MergedCutGroups.Batch055.certificate669).GlobalMatches MergedCutGroups.Batch055.certificate670 CountingCertificates.Batch022.certificate446 CutLabelCertificates.Entropy011.certificate224 CutLabelCertificates.Minority011.certificate223 := by decide +kernel
theorem exponentialBound223 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch055.certificate669).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate446).dm (WitnessCertificates.Batch022.certificate446).beta) ≤ (2*exp (-((CountingCertificates.Batch022.certificate446).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch055.certificate669).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch055.certificate670).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch022.certificate446).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch055.certificate669 MergedCutGroups.Batch055.certificate670 CountingCertificates.Batch022.certificate446 CutLabelCertificates.Entropy011.certificate224 CutLabelCertificates.Minority011.certificate223 matches223 rfl rfl
    MergedCutGroups.Batch055.numericValid669 MergedCutGroups.Batch055.numericValid670 MergedCutGroups.Batch055.cellsSound669 MergedCutGroups.Batch055.cellsSound670
    MergedCutGroups.Batch055.cellsNumeric669 MergedCutGroups.Batch055.cellsNumeric670 MergedCutGroups.Batch055.populationMatches669 MergedCutGroups.Batch055.populationMatches670
    PopulationCertificates.Batch022.valid446 PopulationCertificates.Batch022.sound446 WitnessCertificates.Batch022.valid446 WitnessCertificates.Batch022.sound446 CountingCertificates.Batch022.valid446 CountingCertificates.Batch022.sound446
    CutLabelCertificates.Entropy011.valid224 CutLabelCertificates.Minority011.valid223 CutLabelCertificates.Minority011.sound223 H st hI
theorem probabilityBound223 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch055.certificate669).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate446).dm (WitnessCertificates.Batch022.certificate446).beta) ≤ ((CutFailureCertificates.Budget022.certificate446).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound446 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate446).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch055.certificate669).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch055.certificate670).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch022.certificate446).omega:ℝ) ≤ ((CutFailureCertificates.Budget022.certificate446).bound:ℝ) at hb
  exact (exponentialBound223 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches224 : (MergedCutGroups.Batch056.certificate672).GlobalMatches MergedCutGroups.Batch056.certificate673 CountingCertificates.Batch022.certificate448 CutLabelCertificates.Entropy011.certificate225 CutLabelCertificates.Minority011.certificate224 := by decide +kernel
theorem exponentialBound224 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch056.certificate672).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate448).dm (WitnessCertificates.Batch022.certificate448).beta) ≤ (2*exp (-((CountingCertificates.Batch022.certificate448).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch056.certificate672).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch056.certificate673).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch022.certificate448).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch056.certificate672 MergedCutGroups.Batch056.certificate673 CountingCertificates.Batch022.certificate448 CutLabelCertificates.Entropy011.certificate225 CutLabelCertificates.Minority011.certificate224 matches224 rfl rfl
    MergedCutGroups.Batch056.numericValid672 MergedCutGroups.Batch056.numericValid673 MergedCutGroups.Batch056.cellsSound672 MergedCutGroups.Batch056.cellsSound673
    MergedCutGroups.Batch056.cellsNumeric672 MergedCutGroups.Batch056.cellsNumeric673 MergedCutGroups.Batch056.populationMatches672 MergedCutGroups.Batch056.populationMatches673
    PopulationCertificates.Batch022.valid448 PopulationCertificates.Batch022.sound448 WitnessCertificates.Batch022.valid448 WitnessCertificates.Batch022.sound448 CountingCertificates.Batch022.valid448 CountingCertificates.Batch022.sound448
    CutLabelCertificates.Entropy011.valid225 CutLabelCertificates.Minority011.valid224 CutLabelCertificates.Minority011.sound224 H st hI
theorem probabilityBound224 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch056.certificate672).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate448).dm (WitnessCertificates.Batch022.certificate448).beta) ≤ ((CutFailureCertificates.Budget022.certificate448).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound448 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate448).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch056.certificate672).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch056.certificate673).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch022.certificate448).omega:ℝ) ≤ ((CutFailureCertificates.Budget022.certificate448).bound:ℝ) at hb
  exact (exponentialBound224 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches225 : (MergedCutGroups.Batch056.certificate675).GlobalMatches MergedCutGroups.Batch056.certificate676 CountingCertificates.Batch022.certificate450 CutLabelCertificates.Entropy011.certificate226 CutLabelCertificates.Minority011.certificate225 := by decide +kernel
theorem exponentialBound225 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch056.certificate675).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate450).dm (WitnessCertificates.Batch022.certificate450).beta) ≤ (2*exp (-((CountingCertificates.Batch022.certificate450).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch056.certificate675).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch056.certificate676).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch022.certificate450).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch056.certificate675 MergedCutGroups.Batch056.certificate676 CountingCertificates.Batch022.certificate450 CutLabelCertificates.Entropy011.certificate226 CutLabelCertificates.Minority011.certificate225 matches225 rfl rfl
    MergedCutGroups.Batch056.numericValid675 MergedCutGroups.Batch056.numericValid676 MergedCutGroups.Batch056.cellsSound675 MergedCutGroups.Batch056.cellsSound676
    MergedCutGroups.Batch056.cellsNumeric675 MergedCutGroups.Batch056.cellsNumeric676 MergedCutGroups.Batch056.populationMatches675 MergedCutGroups.Batch056.populationMatches676
    PopulationCertificates.Batch022.valid450 PopulationCertificates.Batch022.sound450 WitnessCertificates.Batch022.valid450 WitnessCertificates.Batch022.sound450 CountingCertificates.Batch022.valid450 CountingCertificates.Batch022.sound450
    CutLabelCertificates.Entropy011.valid226 CutLabelCertificates.Minority011.valid225 CutLabelCertificates.Minority011.sound225 H st hI
theorem probabilityBound225 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch056.certificate675).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate450).dm (WitnessCertificates.Batch022.certificate450).beta) ≤ ((CutFailureCertificates.Budget022.certificate450).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound450 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate450).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch056.certificate675).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch056.certificate676).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch022.certificate450).omega:ℝ) ≤ ((CutFailureCertificates.Budget022.certificate450).bound:ℝ) at hb
  exact (exponentialBound225 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches226 : (MergedCutGroups.Batch056.certificate678).GlobalMatches MergedCutGroups.Batch056.certificate679 CountingCertificates.Batch022.certificate452 CutLabelCertificates.Entropy011.certificate227 CutLabelCertificates.Minority011.certificate226 := by decide +kernel
theorem exponentialBound226 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch056.certificate678).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate452).dm (WitnessCertificates.Batch022.certificate452).beta) ≤ (2*exp (-((CountingCertificates.Batch022.certificate452).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch056.certificate678).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch056.certificate679).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch022.certificate452).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch056.certificate678 MergedCutGroups.Batch056.certificate679 CountingCertificates.Batch022.certificate452 CutLabelCertificates.Entropy011.certificate227 CutLabelCertificates.Minority011.certificate226 matches226 rfl rfl
    MergedCutGroups.Batch056.numericValid678 MergedCutGroups.Batch056.numericValid679 MergedCutGroups.Batch056.cellsSound678 MergedCutGroups.Batch056.cellsSound679
    MergedCutGroups.Batch056.cellsNumeric678 MergedCutGroups.Batch056.cellsNumeric679 MergedCutGroups.Batch056.populationMatches678 MergedCutGroups.Batch056.populationMatches679
    PopulationCertificates.Batch022.valid452 PopulationCertificates.Batch022.sound452 WitnessCertificates.Batch022.valid452 WitnessCertificates.Batch022.sound452 CountingCertificates.Batch022.valid452 CountingCertificates.Batch022.sound452
    CutLabelCertificates.Entropy011.valid227 CutLabelCertificates.Minority011.valid226 CutLabelCertificates.Minority011.sound226 H st hI
theorem probabilityBound226 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch056.certificate678).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate452).dm (WitnessCertificates.Batch022.certificate452).beta) ≤ ((CutFailureCertificates.Budget022.certificate452).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound452 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate452).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch056.certificate678).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch056.certificate679).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch022.certificate452).omega:ℝ) ≤ ((CutFailureCertificates.Budget022.certificate452).bound:ℝ) at hb
  exact (exponentialBound226 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches227 : (MergedCutGroups.Batch056.certificate681).GlobalMatches MergedCutGroups.Batch056.certificate682 CountingCertificates.Batch022.certificate454 CutLabelCertificates.Entropy011.certificate228 CutLabelCertificates.Minority011.certificate227 := by decide +kernel
theorem exponentialBound227 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch056.certificate681).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate454).dm (WitnessCertificates.Batch022.certificate454).beta) ≤ (2*exp (-((CountingCertificates.Batch022.certificate454).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch056.certificate681).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch056.certificate682).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch022.certificate454).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch056.certificate681 MergedCutGroups.Batch056.certificate682 CountingCertificates.Batch022.certificate454 CutLabelCertificates.Entropy011.certificate228 CutLabelCertificates.Minority011.certificate227 matches227 rfl rfl
    MergedCutGroups.Batch056.numericValid681 MergedCutGroups.Batch056.numericValid682 MergedCutGroups.Batch056.cellsSound681 MergedCutGroups.Batch056.cellsSound682
    MergedCutGroups.Batch056.cellsNumeric681 MergedCutGroups.Batch056.cellsNumeric682 MergedCutGroups.Batch056.populationMatches681 MergedCutGroups.Batch056.populationMatches682
    PopulationCertificates.Batch022.valid454 PopulationCertificates.Batch022.sound454 WitnessCertificates.Batch022.valid454 WitnessCertificates.Batch022.sound454 CountingCertificates.Batch022.valid454 CountingCertificates.Batch022.sound454
    CutLabelCertificates.Entropy011.valid228 CutLabelCertificates.Minority011.valid227 CutLabelCertificates.Minority011.sound227 H st hI
theorem probabilityBound227 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch056.certificate681).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate454).dm (WitnessCertificates.Batch022.certificate454).beta) ≤ ((CutFailureCertificates.Budget022.certificate454).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound454 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate454).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch056.certificate681).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch056.certificate682).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch022.certificate454).omega:ℝ) ≤ ((CutFailureCertificates.Budget022.certificate454).bound:ℝ) at hb
  exact (exponentialBound227 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches228 : (MergedCutGroups.Batch057.certificate684).GlobalMatches MergedCutGroups.Batch057.certificate685 CountingCertificates.Batch022.certificate456 CutLabelCertificates.Entropy011.certificate229 CutLabelCertificates.Minority011.certificate228 := by decide +kernel
theorem exponentialBound228 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch057.certificate684).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate456).dm (WitnessCertificates.Batch022.certificate456).beta) ≤ (2*exp (-((CountingCertificates.Batch022.certificate456).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch057.certificate684).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch057.certificate685).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch022.certificate456).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch057.certificate684 MergedCutGroups.Batch057.certificate685 CountingCertificates.Batch022.certificate456 CutLabelCertificates.Entropy011.certificate229 CutLabelCertificates.Minority011.certificate228 matches228 rfl rfl
    MergedCutGroups.Batch057.numericValid684 MergedCutGroups.Batch057.numericValid685 MergedCutGroups.Batch057.cellsSound684 MergedCutGroups.Batch057.cellsSound685
    MergedCutGroups.Batch057.cellsNumeric684 MergedCutGroups.Batch057.cellsNumeric685 MergedCutGroups.Batch057.populationMatches684 MergedCutGroups.Batch057.populationMatches685
    PopulationCertificates.Batch022.valid456 PopulationCertificates.Batch022.sound456 WitnessCertificates.Batch022.valid456 WitnessCertificates.Batch022.sound456 CountingCertificates.Batch022.valid456 CountingCertificates.Batch022.sound456
    CutLabelCertificates.Entropy011.valid229 CutLabelCertificates.Minority011.valid228 CutLabelCertificates.Minority011.sound228 H st hI
theorem probabilityBound228 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch057.certificate684).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate456).dm (WitnessCertificates.Batch022.certificate456).beta) ≤ ((CutFailureCertificates.Budget022.certificate456).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound456 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate456).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch057.certificate684).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch057.certificate685).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch022.certificate456).omega:ℝ) ≤ ((CutFailureCertificates.Budget022.certificate456).bound:ℝ) at hb
  exact (exponentialBound228 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches229 : (MergedCutGroups.Batch057.certificate687).GlobalMatches MergedCutGroups.Batch057.certificate688 CountingCertificates.Batch022.certificate458 CutLabelCertificates.Entropy011.certificate230 CutLabelCertificates.Minority011.certificate229 := by decide +kernel
theorem exponentialBound229 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch057.certificate687).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate458).dm (WitnessCertificates.Batch022.certificate458).beta) ≤ (2*exp (-((CountingCertificates.Batch022.certificate458).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch057.certificate687).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch057.certificate688).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch022.certificate458).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch057.certificate687 MergedCutGroups.Batch057.certificate688 CountingCertificates.Batch022.certificate458 CutLabelCertificates.Entropy011.certificate230 CutLabelCertificates.Minority011.certificate229 matches229 rfl rfl
    MergedCutGroups.Batch057.numericValid687 MergedCutGroups.Batch057.numericValid688 MergedCutGroups.Batch057.cellsSound687 MergedCutGroups.Batch057.cellsSound688
    MergedCutGroups.Batch057.cellsNumeric687 MergedCutGroups.Batch057.cellsNumeric688 MergedCutGroups.Batch057.populationMatches687 MergedCutGroups.Batch057.populationMatches688
    PopulationCertificates.Batch022.valid458 PopulationCertificates.Batch022.sound458 WitnessCertificates.Batch022.valid458 WitnessCertificates.Batch022.sound458 CountingCertificates.Batch022.valid458 CountingCertificates.Batch022.sound458
    CutLabelCertificates.Entropy011.valid230 CutLabelCertificates.Minority011.valid229 CutLabelCertificates.Minority011.sound229 H st hI
theorem probabilityBound229 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch057.certificate687).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch022.certificate458).dm (WitnessCertificates.Batch022.certificate458).beta) ≤ ((CutFailureCertificates.Budget022.certificate458).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound458 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate458).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch057.certificate687).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch057.certificate688).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch022.certificate458).omega:ℝ) ≤ ((CutFailureCertificates.Budget022.certificate458).bound:ℝ) at hb
  exact (exponentialBound229 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches230 : (MergedCutGroups.Batch057.certificate690).GlobalMatches MergedCutGroups.Batch057.certificate691 CountingCertificates.Batch023.certificate460 CutLabelCertificates.Entropy011.certificate231 CutLabelCertificates.Minority011.certificate230 := by decide +kernel
theorem exponentialBound230 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch057.certificate690).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate460).dm (WitnessCertificates.Batch023.certificate460).beta) ≤ (2*exp (-((CountingCertificates.Batch023.certificate460).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch057.certificate690).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch057.certificate691).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch023.certificate460).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch057.certificate690 MergedCutGroups.Batch057.certificate691 CountingCertificates.Batch023.certificate460 CutLabelCertificates.Entropy011.certificate231 CutLabelCertificates.Minority011.certificate230 matches230 rfl rfl
    MergedCutGroups.Batch057.numericValid690 MergedCutGroups.Batch057.numericValid691 MergedCutGroups.Batch057.cellsSound690 MergedCutGroups.Batch057.cellsSound691
    MergedCutGroups.Batch057.cellsNumeric690 MergedCutGroups.Batch057.cellsNumeric691 MergedCutGroups.Batch057.populationMatches690 MergedCutGroups.Batch057.populationMatches691
    PopulationCertificates.Batch023.valid460 PopulationCertificates.Batch023.sound460 WitnessCertificates.Batch023.valid460 WitnessCertificates.Batch023.sound460 CountingCertificates.Batch023.valid460 CountingCertificates.Batch023.sound460
    CutLabelCertificates.Entropy011.valid231 CutLabelCertificates.Minority011.valid230 CutLabelCertificates.Minority011.sound230 H st hI
theorem probabilityBound230 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch057.certificate690).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate460).dm (WitnessCertificates.Batch023.certificate460).beta) ≤ ((CutFailureCertificates.Budget023.certificate460).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound460 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate460).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch057.certificate690).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch057.certificate691).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch023.certificate460).omega:ℝ) ≤ ((CutFailureCertificates.Budget023.certificate460).bound:ℝ) at hb
  exact (exponentialBound230 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches231 : (MergedCutGroups.Batch057.certificate693).GlobalMatches MergedCutGroups.Batch057.certificate694 CountingCertificates.Batch023.certificate462 CutLabelCertificates.Entropy011.certificate232 CutLabelCertificates.Minority011.certificate231 := by decide +kernel
theorem exponentialBound231 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch057.certificate693).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate462).dm (WitnessCertificates.Batch023.certificate462).beta) ≤ (2*exp (-((CountingCertificates.Batch023.certificate462).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch057.certificate693).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch057.certificate694).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch023.certificate462).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch057.certificate693 MergedCutGroups.Batch057.certificate694 CountingCertificates.Batch023.certificate462 CutLabelCertificates.Entropy011.certificate232 CutLabelCertificates.Minority011.certificate231 matches231 rfl rfl
    MergedCutGroups.Batch057.numericValid693 MergedCutGroups.Batch057.numericValid694 MergedCutGroups.Batch057.cellsSound693 MergedCutGroups.Batch057.cellsSound694
    MergedCutGroups.Batch057.cellsNumeric693 MergedCutGroups.Batch057.cellsNumeric694 MergedCutGroups.Batch057.populationMatches693 MergedCutGroups.Batch057.populationMatches694
    PopulationCertificates.Batch023.valid462 PopulationCertificates.Batch023.sound462 WitnessCertificates.Batch023.valid462 WitnessCertificates.Batch023.sound462 CountingCertificates.Batch023.valid462 CountingCertificates.Batch023.sound462
    CutLabelCertificates.Entropy011.valid232 CutLabelCertificates.Minority011.valid231 CutLabelCertificates.Minority011.sound231 H st hI
theorem probabilityBound231 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch057.certificate693).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate462).dm (WitnessCertificates.Batch023.certificate462).beta) ≤ ((CutFailureCertificates.Budget023.certificate462).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound462 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate462).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch057.certificate693).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch057.certificate694).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch023.certificate462).omega:ℝ) ≤ ((CutFailureCertificates.Budget023.certificate462).bound:ℝ) at hb
  exact (exponentialBound231 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches232 : (MergedCutGroups.Batch058.certificate696).GlobalMatches MergedCutGroups.Batch058.certificate697 CountingCertificates.Batch023.certificate464 CutLabelCertificates.Entropy011.certificate233 CutLabelCertificates.Minority011.certificate232 := by decide +kernel
theorem exponentialBound232 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch058.certificate696).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate464).dm (WitnessCertificates.Batch023.certificate464).beta) ≤ (2*exp (-((CountingCertificates.Batch023.certificate464).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch058.certificate696).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch058.certificate697).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch023.certificate464).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch058.certificate696 MergedCutGroups.Batch058.certificate697 CountingCertificates.Batch023.certificate464 CutLabelCertificates.Entropy011.certificate233 CutLabelCertificates.Minority011.certificate232 matches232 rfl rfl
    MergedCutGroups.Batch058.numericValid696 MergedCutGroups.Batch058.numericValid697 MergedCutGroups.Batch058.cellsSound696 MergedCutGroups.Batch058.cellsSound697
    MergedCutGroups.Batch058.cellsNumeric696 MergedCutGroups.Batch058.cellsNumeric697 MergedCutGroups.Batch058.populationMatches696 MergedCutGroups.Batch058.populationMatches697
    PopulationCertificates.Batch023.valid464 PopulationCertificates.Batch023.sound464 WitnessCertificates.Batch023.valid464 WitnessCertificates.Batch023.sound464 CountingCertificates.Batch023.valid464 CountingCertificates.Batch023.sound464
    CutLabelCertificates.Entropy011.valid233 CutLabelCertificates.Minority011.valid232 CutLabelCertificates.Minority011.sound232 H st hI
theorem probabilityBound232 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch058.certificate696).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate464).dm (WitnessCertificates.Batch023.certificate464).beta) ≤ ((CutFailureCertificates.Budget023.certificate464).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound464 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate464).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch058.certificate696).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch058.certificate697).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch023.certificate464).omega:ℝ) ≤ ((CutFailureCertificates.Budget023.certificate464).bound:ℝ) at hb
  exact (exponentialBound232 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches233 : (MergedCutGroups.Batch058.certificate699).GlobalMatches MergedCutGroups.Batch058.certificate700 CountingCertificates.Batch023.certificate466 CutLabelCertificates.Entropy011.certificate234 CutLabelCertificates.Minority011.certificate233 := by decide +kernel
theorem exponentialBound233 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch058.certificate699).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate466).dm (WitnessCertificates.Batch023.certificate466).beta) ≤ (2*exp (-((CountingCertificates.Batch023.certificate466).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch058.certificate699).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch058.certificate700).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch023.certificate466).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch058.certificate699 MergedCutGroups.Batch058.certificate700 CountingCertificates.Batch023.certificate466 CutLabelCertificates.Entropy011.certificate234 CutLabelCertificates.Minority011.certificate233 matches233 rfl rfl
    MergedCutGroups.Batch058.numericValid699 MergedCutGroups.Batch058.numericValid700 MergedCutGroups.Batch058.cellsSound699 MergedCutGroups.Batch058.cellsSound700
    MergedCutGroups.Batch058.cellsNumeric699 MergedCutGroups.Batch058.cellsNumeric700 MergedCutGroups.Batch058.populationMatches699 MergedCutGroups.Batch058.populationMatches700
    PopulationCertificates.Batch023.valid466 PopulationCertificates.Batch023.sound466 WitnessCertificates.Batch023.valid466 WitnessCertificates.Batch023.sound466 CountingCertificates.Batch023.valid466 CountingCertificates.Batch023.sound466
    CutLabelCertificates.Entropy011.valid234 CutLabelCertificates.Minority011.valid233 CutLabelCertificates.Minority011.sound233 H st hI
theorem probabilityBound233 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch058.certificate699).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate466).dm (WitnessCertificates.Batch023.certificate466).beta) ≤ ((CutFailureCertificates.Budget023.certificate466).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound466 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate466).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch058.certificate699).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch058.certificate700).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch023.certificate466).omega:ℝ) ≤ ((CutFailureCertificates.Budget023.certificate466).bound:ℝ) at hb
  exact (exponentialBound233 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches234 : (MergedCutGroups.Batch058.certificate702).GlobalMatches MergedCutGroups.Batch058.certificate703 CountingCertificates.Batch023.certificate468 CutLabelCertificates.Entropy011.certificate235 CutLabelCertificates.Minority011.certificate234 := by decide +kernel
theorem exponentialBound234 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch058.certificate702).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate468).dm (WitnessCertificates.Batch023.certificate468).beta) ≤ (2*exp (-((CountingCertificates.Batch023.certificate468).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch058.certificate702).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch058.certificate703).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch023.certificate468).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch058.certificate702 MergedCutGroups.Batch058.certificate703 CountingCertificates.Batch023.certificate468 CutLabelCertificates.Entropy011.certificate235 CutLabelCertificates.Minority011.certificate234 matches234 rfl rfl
    MergedCutGroups.Batch058.numericValid702 MergedCutGroups.Batch058.numericValid703 MergedCutGroups.Batch058.cellsSound702 MergedCutGroups.Batch058.cellsSound703
    MergedCutGroups.Batch058.cellsNumeric702 MergedCutGroups.Batch058.cellsNumeric703 MergedCutGroups.Batch058.populationMatches702 MergedCutGroups.Batch058.populationMatches703
    PopulationCertificates.Batch023.valid468 PopulationCertificates.Batch023.sound468 WitnessCertificates.Batch023.valid468 WitnessCertificates.Batch023.sound468 CountingCertificates.Batch023.valid468 CountingCertificates.Batch023.sound468
    CutLabelCertificates.Entropy011.valid235 CutLabelCertificates.Minority011.valid234 CutLabelCertificates.Minority011.sound234 H st hI
theorem probabilityBound234 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch058.certificate702).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate468).dm (WitnessCertificates.Batch023.certificate468).beta) ≤ ((CutFailureCertificates.Budget023.certificate468).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound468 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate468).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch058.certificate702).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch058.certificate703).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch023.certificate468).omega:ℝ) ≤ ((CutFailureCertificates.Budget023.certificate468).bound:ℝ) at hb
  exact (exponentialBound234 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches235 : (MergedCutGroups.Batch058.certificate705).GlobalMatches MergedCutGroups.Batch058.certificate706 CountingCertificates.Batch023.certificate470 CutLabelCertificates.Entropy011.certificate236 CutLabelCertificates.Minority011.certificate235 := by decide +kernel
theorem exponentialBound235 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch058.certificate705).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate470).dm (WitnessCertificates.Batch023.certificate470).beta) ≤ (2*exp (-((CountingCertificates.Batch023.certificate470).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch058.certificate705).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch058.certificate706).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch023.certificate470).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch058.certificate705 MergedCutGroups.Batch058.certificate706 CountingCertificates.Batch023.certificate470 CutLabelCertificates.Entropy011.certificate236 CutLabelCertificates.Minority011.certificate235 matches235 rfl rfl
    MergedCutGroups.Batch058.numericValid705 MergedCutGroups.Batch058.numericValid706 MergedCutGroups.Batch058.cellsSound705 MergedCutGroups.Batch058.cellsSound706
    MergedCutGroups.Batch058.cellsNumeric705 MergedCutGroups.Batch058.cellsNumeric706 MergedCutGroups.Batch058.populationMatches705 MergedCutGroups.Batch058.populationMatches706
    PopulationCertificates.Batch023.valid470 PopulationCertificates.Batch023.sound470 WitnessCertificates.Batch023.valid470 WitnessCertificates.Batch023.sound470 CountingCertificates.Batch023.valid470 CountingCertificates.Batch023.sound470
    CutLabelCertificates.Entropy011.valid236 CutLabelCertificates.Minority011.valid235 CutLabelCertificates.Minority011.sound235 H st hI
theorem probabilityBound235 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch058.certificate705).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate470).dm (WitnessCertificates.Batch023.certificate470).beta) ≤ ((CutFailureCertificates.Budget023.certificate470).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound470 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate470).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch058.certificate705).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch058.certificate706).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch023.certificate470).omega:ℝ) ≤ ((CutFailureCertificates.Budget023.certificate470).bound:ℝ) at hb
  exact (exponentialBound235 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches236 : (MergedCutGroups.Batch059.certificate708).GlobalMatches MergedCutGroups.Batch059.certificate709 CountingCertificates.Batch023.certificate472 CutLabelCertificates.Entropy011.certificate237 CutLabelCertificates.Minority011.certificate236 := by decide +kernel
theorem exponentialBound236 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch059.certificate708).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate472).dm (WitnessCertificates.Batch023.certificate472).beta) ≤ (2*exp (-((CountingCertificates.Batch023.certificate472).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch059.certificate708).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch059.certificate709).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch023.certificate472).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch059.certificate708 MergedCutGroups.Batch059.certificate709 CountingCertificates.Batch023.certificate472 CutLabelCertificates.Entropy011.certificate237 CutLabelCertificates.Minority011.certificate236 matches236 rfl rfl
    MergedCutGroups.Batch059.numericValid708 MergedCutGroups.Batch059.numericValid709 MergedCutGroups.Batch059.cellsSound708 MergedCutGroups.Batch059.cellsSound709
    MergedCutGroups.Batch059.cellsNumeric708 MergedCutGroups.Batch059.cellsNumeric709 MergedCutGroups.Batch059.populationMatches708 MergedCutGroups.Batch059.populationMatches709
    PopulationCertificates.Batch023.valid472 PopulationCertificates.Batch023.sound472 WitnessCertificates.Batch023.valid472 WitnessCertificates.Batch023.sound472 CountingCertificates.Batch023.valid472 CountingCertificates.Batch023.sound472
    CutLabelCertificates.Entropy011.valid237 CutLabelCertificates.Minority011.valid236 CutLabelCertificates.Minority011.sound236 H st hI
theorem probabilityBound236 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch059.certificate708).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate472).dm (WitnessCertificates.Batch023.certificate472).beta) ≤ ((CutFailureCertificates.Budget023.certificate472).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound472 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate472).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch059.certificate708).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch059.certificate709).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch023.certificate472).omega:ℝ) ≤ ((CutFailureCertificates.Budget023.certificate472).bound:ℝ) at hb
  exact (exponentialBound236 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches237 : (MergedCutGroups.Batch059.certificate711).GlobalMatches MergedCutGroups.Batch059.certificate712 CountingCertificates.Batch023.certificate474 CutLabelCertificates.Entropy011.certificate238 CutLabelCertificates.Minority011.certificate237 := by decide +kernel
theorem exponentialBound237 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch059.certificate711).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate474).dm (WitnessCertificates.Batch023.certificate474).beta) ≤ (2*exp (-((CountingCertificates.Batch023.certificate474).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch059.certificate711).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch059.certificate712).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch023.certificate474).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch059.certificate711 MergedCutGroups.Batch059.certificate712 CountingCertificates.Batch023.certificate474 CutLabelCertificates.Entropy011.certificate238 CutLabelCertificates.Minority011.certificate237 matches237 rfl rfl
    MergedCutGroups.Batch059.numericValid711 MergedCutGroups.Batch059.numericValid712 MergedCutGroups.Batch059.cellsSound711 MergedCutGroups.Batch059.cellsSound712
    MergedCutGroups.Batch059.cellsNumeric711 MergedCutGroups.Batch059.cellsNumeric712 MergedCutGroups.Batch059.populationMatches711 MergedCutGroups.Batch059.populationMatches712
    PopulationCertificates.Batch023.valid474 PopulationCertificates.Batch023.sound474 WitnessCertificates.Batch023.valid474 WitnessCertificates.Batch023.sound474 CountingCertificates.Batch023.valid474 CountingCertificates.Batch023.sound474
    CutLabelCertificates.Entropy011.valid238 CutLabelCertificates.Minority011.valid237 CutLabelCertificates.Minority011.sound237 H st hI
theorem probabilityBound237 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch059.certificate711).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate474).dm (WitnessCertificates.Batch023.certificate474).beta) ≤ ((CutFailureCertificates.Budget023.certificate474).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound474 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate474).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch059.certificate711).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch059.certificate712).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch023.certificate474).omega:ℝ) ≤ ((CutFailureCertificates.Budget023.certificate474).bound:ℝ) at hb
  exact (exponentialBound237 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches238 : (MergedCutGroups.Batch059.certificate714).GlobalMatches MergedCutGroups.Batch059.certificate715 CountingCertificates.Batch023.certificate476 CutLabelCertificates.Entropy011.certificate239 CutLabelCertificates.Minority011.certificate238 := by decide +kernel
theorem exponentialBound238 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch059.certificate714).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate476).dm (WitnessCertificates.Batch023.certificate476).beta) ≤ (2*exp (-((CountingCertificates.Batch023.certificate476).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch059.certificate714).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch059.certificate715).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch023.certificate476).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch059.certificate714 MergedCutGroups.Batch059.certificate715 CountingCertificates.Batch023.certificate476 CutLabelCertificates.Entropy011.certificate239 CutLabelCertificates.Minority011.certificate238 matches238 rfl rfl
    MergedCutGroups.Batch059.numericValid714 MergedCutGroups.Batch059.numericValid715 MergedCutGroups.Batch059.cellsSound714 MergedCutGroups.Batch059.cellsSound715
    MergedCutGroups.Batch059.cellsNumeric714 MergedCutGroups.Batch059.cellsNumeric715 MergedCutGroups.Batch059.populationMatches714 MergedCutGroups.Batch059.populationMatches715
    PopulationCertificates.Batch023.valid476 PopulationCertificates.Batch023.sound476 WitnessCertificates.Batch023.valid476 WitnessCertificates.Batch023.sound476 CountingCertificates.Batch023.valid476 CountingCertificates.Batch023.sound476
    CutLabelCertificates.Entropy011.valid239 CutLabelCertificates.Minority011.valid238 CutLabelCertificates.Minority011.sound238 H st hI
theorem probabilityBound238 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch059.certificate714).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate476).dm (WitnessCertificates.Batch023.certificate476).beta) ≤ ((CutFailureCertificates.Budget023.certificate476).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound476 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate476).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch059.certificate714).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch059.certificate715).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch023.certificate476).omega:ℝ) ≤ ((CutFailureCertificates.Budget023.certificate476).bound:ℝ) at hb
  exact (exponentialBound238 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches239 : (MergedCutGroups.Batch059.certificate717).GlobalMatches MergedCutGroups.Batch059.certificate718 CountingCertificates.Batch023.certificate478 CutLabelCertificates.Entropy012.certificate240 CutLabelCertificates.Minority011.certificate239 := by decide +kernel
theorem exponentialBound239 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch059.certificate717).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate478).dm (WitnessCertificates.Batch023.certificate478).beta) ≤ (2*exp (-((CountingCertificates.Batch023.certificate478).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch059.certificate717).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch059.certificate718).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch023.certificate478).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch059.certificate717 MergedCutGroups.Batch059.certificate718 CountingCertificates.Batch023.certificate478 CutLabelCertificates.Entropy012.certificate240 CutLabelCertificates.Minority011.certificate239 matches239 rfl rfl
    MergedCutGroups.Batch059.numericValid717 MergedCutGroups.Batch059.numericValid718 MergedCutGroups.Batch059.cellsSound717 MergedCutGroups.Batch059.cellsSound718
    MergedCutGroups.Batch059.cellsNumeric717 MergedCutGroups.Batch059.cellsNumeric718 MergedCutGroups.Batch059.populationMatches717 MergedCutGroups.Batch059.populationMatches718
    PopulationCertificates.Batch023.valid478 PopulationCertificates.Batch023.sound478 WitnessCertificates.Batch023.valid478 WitnessCertificates.Batch023.sound478 CountingCertificates.Batch023.valid478 CountingCertificates.Batch023.sound478
    CutLabelCertificates.Entropy012.valid240 CutLabelCertificates.Minority011.valid239 CutLabelCertificates.Minority011.sound239 H st hI
theorem probabilityBound239 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch059.certificate717).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch023.certificate478).dm (WitnessCertificates.Batch023.certificate478).beta) ≤ ((CutFailureCertificates.Budget023.certificate478).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound478 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate478).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch059.certificate717).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch059.certificate718).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch023.certificate478).omega:ℝ) ≤ ((CutFailureCertificates.Budget023.certificate478).bound:ℝ) at hb
  exact (exponentialBound239 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch011
