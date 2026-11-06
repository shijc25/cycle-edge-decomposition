import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch022
import Cycle12.CountingCertificates.Batch023
import Cycle12.CutFailureCertificates.Budget022
import Cycle12.CutFailureCertificates.Budget023
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

namespace Cycle12.CertifiedAnchorFailures.Batch011
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches220 : (MergedCutGroups.Batch055.certificate662).AnchorMatches CountingCertificates.Batch022.certificate441 := by decide +kernel
theorem exponentialBound220 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch055.certificate662).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate441).dm (WitnessCertificates.Batch022.certificate441).beta (WitnessCertificates.Batch022.certificate441).L) ≤ (2*exp (-((CountingCertificates.Batch022.certificate441).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch055.certificate662).exponent:ℝ)*st.R))/((WitnessCertificates.Batch022.certificate441).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch055.certificate662 CountingCertificates.Batch022.certificate441 matches220 MergedCutGroups.Batch055.numericValid662 MergedCutGroups.Batch055.cellsSound662 MergedCutGroups.Batch055.cellsNumeric662 MergedCutGroups.Batch055.populationMatches662
    PopulationCertificates.Batch022.valid441 PopulationCertificates.Batch022.sound441 WitnessCertificates.Batch022.valid441 WitnessCertificates.Batch022.sound441 CountingCertificates.Batch022.valid441 CountingCertificates.Batch022.sound441 H st hI
theorem probabilityBound220 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch055.certificate662).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate441).dm (WitnessCertificates.Batch022.certificate441).beta (WitnessCertificates.Batch022.certificate441).L) ≤ ((CutFailureCertificates.Budget022.certificate441).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound441 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate441).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch055.certificate662).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch022.certificate441).omega:ℝ)) ≤ ((CutFailureCertificates.Budget022.certificate441).bound:ℝ) at hb
  exact (exponentialBound220 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches221 : (MergedCutGroups.Batch055.certificate665).AnchorMatches CountingCertificates.Batch022.certificate443 := by decide +kernel
theorem exponentialBound221 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch055.certificate665).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate443).dm (WitnessCertificates.Batch022.certificate443).beta (WitnessCertificates.Batch022.certificate443).L) ≤ (2*exp (-((CountingCertificates.Batch022.certificate443).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch055.certificate665).exponent:ℝ)*st.R))/((WitnessCertificates.Batch022.certificate443).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch055.certificate665 CountingCertificates.Batch022.certificate443 matches221 MergedCutGroups.Batch055.numericValid665 MergedCutGroups.Batch055.cellsSound665 MergedCutGroups.Batch055.cellsNumeric665 MergedCutGroups.Batch055.populationMatches665
    PopulationCertificates.Batch022.valid443 PopulationCertificates.Batch022.sound443 WitnessCertificates.Batch022.valid443 WitnessCertificates.Batch022.sound443 CountingCertificates.Batch022.valid443 CountingCertificates.Batch022.sound443 H st hI
theorem probabilityBound221 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch055.certificate665).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate443).dm (WitnessCertificates.Batch022.certificate443).beta (WitnessCertificates.Batch022.certificate443).L) ≤ ((CutFailureCertificates.Budget022.certificate443).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound443 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate443).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch055.certificate665).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch022.certificate443).omega:ℝ)) ≤ ((CutFailureCertificates.Budget022.certificate443).bound:ℝ) at hb
  exact (exponentialBound221 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches222 : (MergedCutGroups.Batch055.certificate668).AnchorMatches CountingCertificates.Batch022.certificate445 := by decide +kernel
theorem exponentialBound222 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch055.certificate668).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate445).dm (WitnessCertificates.Batch022.certificate445).beta (WitnessCertificates.Batch022.certificate445).L) ≤ (2*exp (-((CountingCertificates.Batch022.certificate445).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch055.certificate668).exponent:ℝ)*st.R))/((WitnessCertificates.Batch022.certificate445).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch055.certificate668 CountingCertificates.Batch022.certificate445 matches222 MergedCutGroups.Batch055.numericValid668 MergedCutGroups.Batch055.cellsSound668 MergedCutGroups.Batch055.cellsNumeric668 MergedCutGroups.Batch055.populationMatches668
    PopulationCertificates.Batch022.valid445 PopulationCertificates.Batch022.sound445 WitnessCertificates.Batch022.valid445 WitnessCertificates.Batch022.sound445 CountingCertificates.Batch022.valid445 CountingCertificates.Batch022.sound445 H st hI
theorem probabilityBound222 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch055.certificate668).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate445).dm (WitnessCertificates.Batch022.certificate445).beta (WitnessCertificates.Batch022.certificate445).L) ≤ ((CutFailureCertificates.Budget022.certificate445).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound445 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate445).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch055.certificate668).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch022.certificate445).omega:ℝ)) ≤ ((CutFailureCertificates.Budget022.certificate445).bound:ℝ) at hb
  exact (exponentialBound222 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches223 : (MergedCutGroups.Batch055.certificate671).AnchorMatches CountingCertificates.Batch022.certificate447 := by decide +kernel
theorem exponentialBound223 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch055.certificate671).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate447).dm (WitnessCertificates.Batch022.certificate447).beta (WitnessCertificates.Batch022.certificate447).L) ≤ (2*exp (-((CountingCertificates.Batch022.certificate447).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch055.certificate671).exponent:ℝ)*st.R))/((WitnessCertificates.Batch022.certificate447).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch055.certificate671 CountingCertificates.Batch022.certificate447 matches223 MergedCutGroups.Batch055.numericValid671 MergedCutGroups.Batch055.cellsSound671 MergedCutGroups.Batch055.cellsNumeric671 MergedCutGroups.Batch055.populationMatches671
    PopulationCertificates.Batch022.valid447 PopulationCertificates.Batch022.sound447 WitnessCertificates.Batch022.valid447 WitnessCertificates.Batch022.sound447 CountingCertificates.Batch022.valid447 CountingCertificates.Batch022.sound447 H st hI
theorem probabilityBound223 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch055.certificate671).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate447).dm (WitnessCertificates.Batch022.certificate447).beta (WitnessCertificates.Batch022.certificate447).L) ≤ ((CutFailureCertificates.Budget022.certificate447).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound447 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate447).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch055.certificate671).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch022.certificate447).omega:ℝ)) ≤ ((CutFailureCertificates.Budget022.certificate447).bound:ℝ) at hb
  exact (exponentialBound223 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches224 : (MergedCutGroups.Batch056.certificate674).AnchorMatches CountingCertificates.Batch022.certificate449 := by decide +kernel
theorem exponentialBound224 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch056.certificate674).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate449).dm (WitnessCertificates.Batch022.certificate449).beta (WitnessCertificates.Batch022.certificate449).L) ≤ (2*exp (-((CountingCertificates.Batch022.certificate449).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch056.certificate674).exponent:ℝ)*st.R))/((WitnessCertificates.Batch022.certificate449).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch056.certificate674 CountingCertificates.Batch022.certificate449 matches224 MergedCutGroups.Batch056.numericValid674 MergedCutGroups.Batch056.cellsSound674 MergedCutGroups.Batch056.cellsNumeric674 MergedCutGroups.Batch056.populationMatches674
    PopulationCertificates.Batch022.valid449 PopulationCertificates.Batch022.sound449 WitnessCertificates.Batch022.valid449 WitnessCertificates.Batch022.sound449 CountingCertificates.Batch022.valid449 CountingCertificates.Batch022.sound449 H st hI
theorem probabilityBound224 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch056.certificate674).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate449).dm (WitnessCertificates.Batch022.certificate449).beta (WitnessCertificates.Batch022.certificate449).L) ≤ ((CutFailureCertificates.Budget022.certificate449).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound449 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate449).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch056.certificate674).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch022.certificate449).omega:ℝ)) ≤ ((CutFailureCertificates.Budget022.certificate449).bound:ℝ) at hb
  exact (exponentialBound224 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches225 : (MergedCutGroups.Batch056.certificate677).AnchorMatches CountingCertificates.Batch022.certificate451 := by decide +kernel
theorem exponentialBound225 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch056.certificate677).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate451).dm (WitnessCertificates.Batch022.certificate451).beta (WitnessCertificates.Batch022.certificate451).L) ≤ (2*exp (-((CountingCertificates.Batch022.certificate451).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch056.certificate677).exponent:ℝ)*st.R))/((WitnessCertificates.Batch022.certificate451).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch056.certificate677 CountingCertificates.Batch022.certificate451 matches225 MergedCutGroups.Batch056.numericValid677 MergedCutGroups.Batch056.cellsSound677 MergedCutGroups.Batch056.cellsNumeric677 MergedCutGroups.Batch056.populationMatches677
    PopulationCertificates.Batch022.valid451 PopulationCertificates.Batch022.sound451 WitnessCertificates.Batch022.valid451 WitnessCertificates.Batch022.sound451 CountingCertificates.Batch022.valid451 CountingCertificates.Batch022.sound451 H st hI
theorem probabilityBound225 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch056.certificate677).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate451).dm (WitnessCertificates.Batch022.certificate451).beta (WitnessCertificates.Batch022.certificate451).L) ≤ ((CutFailureCertificates.Budget022.certificate451).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound451 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate451).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch056.certificate677).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch022.certificate451).omega:ℝ)) ≤ ((CutFailureCertificates.Budget022.certificate451).bound:ℝ) at hb
  exact (exponentialBound225 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches226 : (MergedCutGroups.Batch056.certificate680).AnchorMatches CountingCertificates.Batch022.certificate453 := by decide +kernel
theorem exponentialBound226 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch056.certificate680).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate453).dm (WitnessCertificates.Batch022.certificate453).beta (WitnessCertificates.Batch022.certificate453).L) ≤ (2*exp (-((CountingCertificates.Batch022.certificate453).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch056.certificate680).exponent:ℝ)*st.R))/((WitnessCertificates.Batch022.certificate453).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch056.certificate680 CountingCertificates.Batch022.certificate453 matches226 MergedCutGroups.Batch056.numericValid680 MergedCutGroups.Batch056.cellsSound680 MergedCutGroups.Batch056.cellsNumeric680 MergedCutGroups.Batch056.populationMatches680
    PopulationCertificates.Batch022.valid453 PopulationCertificates.Batch022.sound453 WitnessCertificates.Batch022.valid453 WitnessCertificates.Batch022.sound453 CountingCertificates.Batch022.valid453 CountingCertificates.Batch022.sound453 H st hI
theorem probabilityBound226 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch056.certificate680).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate453).dm (WitnessCertificates.Batch022.certificate453).beta (WitnessCertificates.Batch022.certificate453).L) ≤ ((CutFailureCertificates.Budget022.certificate453).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound453 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate453).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch056.certificate680).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch022.certificate453).omega:ℝ)) ≤ ((CutFailureCertificates.Budget022.certificate453).bound:ℝ) at hb
  exact (exponentialBound226 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches227 : (MergedCutGroups.Batch056.certificate683).AnchorMatches CountingCertificates.Batch022.certificate455 := by decide +kernel
theorem exponentialBound227 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch056.certificate683).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate455).dm (WitnessCertificates.Batch022.certificate455).beta (WitnessCertificates.Batch022.certificate455).L) ≤ (2*exp (-((CountingCertificates.Batch022.certificate455).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch056.certificate683).exponent:ℝ)*st.R))/((WitnessCertificates.Batch022.certificate455).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch056.certificate683 CountingCertificates.Batch022.certificate455 matches227 MergedCutGroups.Batch056.numericValid683 MergedCutGroups.Batch056.cellsSound683 MergedCutGroups.Batch056.cellsNumeric683 MergedCutGroups.Batch056.populationMatches683
    PopulationCertificates.Batch022.valid455 PopulationCertificates.Batch022.sound455 WitnessCertificates.Batch022.valid455 WitnessCertificates.Batch022.sound455 CountingCertificates.Batch022.valid455 CountingCertificates.Batch022.sound455 H st hI
theorem probabilityBound227 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch056.certificate683).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate455).dm (WitnessCertificates.Batch022.certificate455).beta (WitnessCertificates.Batch022.certificate455).L) ≤ ((CutFailureCertificates.Budget022.certificate455).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound455 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate455).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch056.certificate683).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch022.certificate455).omega:ℝ)) ≤ ((CutFailureCertificates.Budget022.certificate455).bound:ℝ) at hb
  exact (exponentialBound227 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches228 : (MergedCutGroups.Batch057.certificate686).AnchorMatches CountingCertificates.Batch022.certificate457 := by decide +kernel
theorem exponentialBound228 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch057.certificate686).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate457).dm (WitnessCertificates.Batch022.certificate457).beta (WitnessCertificates.Batch022.certificate457).L) ≤ (2*exp (-((CountingCertificates.Batch022.certificate457).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch057.certificate686).exponent:ℝ)*st.R))/((WitnessCertificates.Batch022.certificate457).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch057.certificate686 CountingCertificates.Batch022.certificate457 matches228 MergedCutGroups.Batch057.numericValid686 MergedCutGroups.Batch057.cellsSound686 MergedCutGroups.Batch057.cellsNumeric686 MergedCutGroups.Batch057.populationMatches686
    PopulationCertificates.Batch022.valid457 PopulationCertificates.Batch022.sound457 WitnessCertificates.Batch022.valid457 WitnessCertificates.Batch022.sound457 CountingCertificates.Batch022.valid457 CountingCertificates.Batch022.sound457 H st hI
theorem probabilityBound228 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch057.certificate686).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate457).dm (WitnessCertificates.Batch022.certificate457).beta (WitnessCertificates.Batch022.certificate457).L) ≤ ((CutFailureCertificates.Budget022.certificate457).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound457 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate457).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch057.certificate686).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch022.certificate457).omega:ℝ)) ≤ ((CutFailureCertificates.Budget022.certificate457).bound:ℝ) at hb
  exact (exponentialBound228 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches229 : (MergedCutGroups.Batch057.certificate689).AnchorMatches CountingCertificates.Batch022.certificate459 := by decide +kernel
theorem exponentialBound229 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch057.certificate689).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate459).dm (WitnessCertificates.Batch022.certificate459).beta (WitnessCertificates.Batch022.certificate459).L) ≤ (2*exp (-((CountingCertificates.Batch022.certificate459).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch057.certificate689).exponent:ℝ)*st.R))/((WitnessCertificates.Batch022.certificate459).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch057.certificate689 CountingCertificates.Batch022.certificate459 matches229 MergedCutGroups.Batch057.numericValid689 MergedCutGroups.Batch057.cellsSound689 MergedCutGroups.Batch057.cellsNumeric689 MergedCutGroups.Batch057.populationMatches689
    PopulationCertificates.Batch022.valid459 PopulationCertificates.Batch022.sound459 WitnessCertificates.Batch022.valid459 WitnessCertificates.Batch022.sound459 CountingCertificates.Batch022.valid459 CountingCertificates.Batch022.sound459 H st hI
theorem probabilityBound229 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch057.certificate689).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch022.certificate459).dm (WitnessCertificates.Batch022.certificate459).beta (WitnessCertificates.Batch022.certificate459).L) ≤ ((CutFailureCertificates.Budget022.certificate459).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget022.sound459 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch022.certificate459).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch057.certificate689).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch022.certificate459).omega:ℝ)) ≤ ((CutFailureCertificates.Budget022.certificate459).bound:ℝ) at hb
  exact (exponentialBound229 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches230 : (MergedCutGroups.Batch057.certificate692).AnchorMatches CountingCertificates.Batch023.certificate461 := by decide +kernel
theorem exponentialBound230 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch057.certificate692).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate461).dm (WitnessCertificates.Batch023.certificate461).beta (WitnessCertificates.Batch023.certificate461).L) ≤ (2*exp (-((CountingCertificates.Batch023.certificate461).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch057.certificate692).exponent:ℝ)*st.R))/((WitnessCertificates.Batch023.certificate461).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch057.certificate692 CountingCertificates.Batch023.certificate461 matches230 MergedCutGroups.Batch057.numericValid692 MergedCutGroups.Batch057.cellsSound692 MergedCutGroups.Batch057.cellsNumeric692 MergedCutGroups.Batch057.populationMatches692
    PopulationCertificates.Batch023.valid461 PopulationCertificates.Batch023.sound461 WitnessCertificates.Batch023.valid461 WitnessCertificates.Batch023.sound461 CountingCertificates.Batch023.valid461 CountingCertificates.Batch023.sound461 H st hI
theorem probabilityBound230 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch057.certificate692).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate461).dm (WitnessCertificates.Batch023.certificate461).beta (WitnessCertificates.Batch023.certificate461).L) ≤ ((CutFailureCertificates.Budget023.certificate461).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound461 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate461).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch057.certificate692).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch023.certificate461).omega:ℝ)) ≤ ((CutFailureCertificates.Budget023.certificate461).bound:ℝ) at hb
  exact (exponentialBound230 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches231 : (MergedCutGroups.Batch057.certificate695).AnchorMatches CountingCertificates.Batch023.certificate463 := by decide +kernel
theorem exponentialBound231 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch057.certificate695).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate463).dm (WitnessCertificates.Batch023.certificate463).beta (WitnessCertificates.Batch023.certificate463).L) ≤ (2*exp (-((CountingCertificates.Batch023.certificate463).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch057.certificate695).exponent:ℝ)*st.R))/((WitnessCertificates.Batch023.certificate463).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch057.certificate695 CountingCertificates.Batch023.certificate463 matches231 MergedCutGroups.Batch057.numericValid695 MergedCutGroups.Batch057.cellsSound695 MergedCutGroups.Batch057.cellsNumeric695 MergedCutGroups.Batch057.populationMatches695
    PopulationCertificates.Batch023.valid463 PopulationCertificates.Batch023.sound463 WitnessCertificates.Batch023.valid463 WitnessCertificates.Batch023.sound463 CountingCertificates.Batch023.valid463 CountingCertificates.Batch023.sound463 H st hI
theorem probabilityBound231 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch057.certificate695).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate463).dm (WitnessCertificates.Batch023.certificate463).beta (WitnessCertificates.Batch023.certificate463).L) ≤ ((CutFailureCertificates.Budget023.certificate463).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound463 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate463).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch057.certificate695).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch023.certificate463).omega:ℝ)) ≤ ((CutFailureCertificates.Budget023.certificate463).bound:ℝ) at hb
  exact (exponentialBound231 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches232 : (MergedCutGroups.Batch058.certificate698).AnchorMatches CountingCertificates.Batch023.certificate465 := by decide +kernel
theorem exponentialBound232 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch058.certificate698).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate465).dm (WitnessCertificates.Batch023.certificate465).beta (WitnessCertificates.Batch023.certificate465).L) ≤ (2*exp (-((CountingCertificates.Batch023.certificate465).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch058.certificate698).exponent:ℝ)*st.R))/((WitnessCertificates.Batch023.certificate465).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch058.certificate698 CountingCertificates.Batch023.certificate465 matches232 MergedCutGroups.Batch058.numericValid698 MergedCutGroups.Batch058.cellsSound698 MergedCutGroups.Batch058.cellsNumeric698 MergedCutGroups.Batch058.populationMatches698
    PopulationCertificates.Batch023.valid465 PopulationCertificates.Batch023.sound465 WitnessCertificates.Batch023.valid465 WitnessCertificates.Batch023.sound465 CountingCertificates.Batch023.valid465 CountingCertificates.Batch023.sound465 H st hI
theorem probabilityBound232 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch058.certificate698).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate465).dm (WitnessCertificates.Batch023.certificate465).beta (WitnessCertificates.Batch023.certificate465).L) ≤ ((CutFailureCertificates.Budget023.certificate465).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound465 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate465).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch058.certificate698).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch023.certificate465).omega:ℝ)) ≤ ((CutFailureCertificates.Budget023.certificate465).bound:ℝ) at hb
  exact (exponentialBound232 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches233 : (MergedCutGroups.Batch058.certificate701).AnchorMatches CountingCertificates.Batch023.certificate467 := by decide +kernel
theorem exponentialBound233 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch058.certificate701).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate467).dm (WitnessCertificates.Batch023.certificate467).beta (WitnessCertificates.Batch023.certificate467).L) ≤ (2*exp (-((CountingCertificates.Batch023.certificate467).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch058.certificate701).exponent:ℝ)*st.R))/((WitnessCertificates.Batch023.certificate467).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch058.certificate701 CountingCertificates.Batch023.certificate467 matches233 MergedCutGroups.Batch058.numericValid701 MergedCutGroups.Batch058.cellsSound701 MergedCutGroups.Batch058.cellsNumeric701 MergedCutGroups.Batch058.populationMatches701
    PopulationCertificates.Batch023.valid467 PopulationCertificates.Batch023.sound467 WitnessCertificates.Batch023.valid467 WitnessCertificates.Batch023.sound467 CountingCertificates.Batch023.valid467 CountingCertificates.Batch023.sound467 H st hI
theorem probabilityBound233 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch058.certificate701).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate467).dm (WitnessCertificates.Batch023.certificate467).beta (WitnessCertificates.Batch023.certificate467).L) ≤ ((CutFailureCertificates.Budget023.certificate467).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound467 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate467).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch058.certificate701).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch023.certificate467).omega:ℝ)) ≤ ((CutFailureCertificates.Budget023.certificate467).bound:ℝ) at hb
  exact (exponentialBound233 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches234 : (MergedCutGroups.Batch058.certificate704).AnchorMatches CountingCertificates.Batch023.certificate469 := by decide +kernel
theorem exponentialBound234 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch058.certificate704).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate469).dm (WitnessCertificates.Batch023.certificate469).beta (WitnessCertificates.Batch023.certificate469).L) ≤ (2*exp (-((CountingCertificates.Batch023.certificate469).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch058.certificate704).exponent:ℝ)*st.R))/((WitnessCertificates.Batch023.certificate469).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch058.certificate704 CountingCertificates.Batch023.certificate469 matches234 MergedCutGroups.Batch058.numericValid704 MergedCutGroups.Batch058.cellsSound704 MergedCutGroups.Batch058.cellsNumeric704 MergedCutGroups.Batch058.populationMatches704
    PopulationCertificates.Batch023.valid469 PopulationCertificates.Batch023.sound469 WitnessCertificates.Batch023.valid469 WitnessCertificates.Batch023.sound469 CountingCertificates.Batch023.valid469 CountingCertificates.Batch023.sound469 H st hI
theorem probabilityBound234 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch058.certificate704).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate469).dm (WitnessCertificates.Batch023.certificate469).beta (WitnessCertificates.Batch023.certificate469).L) ≤ ((CutFailureCertificates.Budget023.certificate469).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound469 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate469).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch058.certificate704).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch023.certificate469).omega:ℝ)) ≤ ((CutFailureCertificates.Budget023.certificate469).bound:ℝ) at hb
  exact (exponentialBound234 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches235 : (MergedCutGroups.Batch058.certificate707).AnchorMatches CountingCertificates.Batch023.certificate471 := by decide +kernel
theorem exponentialBound235 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch058.certificate707).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate471).dm (WitnessCertificates.Batch023.certificate471).beta (WitnessCertificates.Batch023.certificate471).L) ≤ (2*exp (-((CountingCertificates.Batch023.certificate471).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch058.certificate707).exponent:ℝ)*st.R))/((WitnessCertificates.Batch023.certificate471).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch058.certificate707 CountingCertificates.Batch023.certificate471 matches235 MergedCutGroups.Batch058.numericValid707 MergedCutGroups.Batch058.cellsSound707 MergedCutGroups.Batch058.cellsNumeric707 MergedCutGroups.Batch058.populationMatches707
    PopulationCertificates.Batch023.valid471 PopulationCertificates.Batch023.sound471 WitnessCertificates.Batch023.valid471 WitnessCertificates.Batch023.sound471 CountingCertificates.Batch023.valid471 CountingCertificates.Batch023.sound471 H st hI
theorem probabilityBound235 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch058.certificate707).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate471).dm (WitnessCertificates.Batch023.certificate471).beta (WitnessCertificates.Batch023.certificate471).L) ≤ ((CutFailureCertificates.Budget023.certificate471).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound471 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate471).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch058.certificate707).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch023.certificate471).omega:ℝ)) ≤ ((CutFailureCertificates.Budget023.certificate471).bound:ℝ) at hb
  exact (exponentialBound235 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches236 : (MergedCutGroups.Batch059.certificate710).AnchorMatches CountingCertificates.Batch023.certificate473 := by decide +kernel
theorem exponentialBound236 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch059.certificate710).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate473).dm (WitnessCertificates.Batch023.certificate473).beta (WitnessCertificates.Batch023.certificate473).L) ≤ (2*exp (-((CountingCertificates.Batch023.certificate473).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch059.certificate710).exponent:ℝ)*st.R))/((WitnessCertificates.Batch023.certificate473).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch059.certificate710 CountingCertificates.Batch023.certificate473 matches236 MergedCutGroups.Batch059.numericValid710 MergedCutGroups.Batch059.cellsSound710 MergedCutGroups.Batch059.cellsNumeric710 MergedCutGroups.Batch059.populationMatches710
    PopulationCertificates.Batch023.valid473 PopulationCertificates.Batch023.sound473 WitnessCertificates.Batch023.valid473 WitnessCertificates.Batch023.sound473 CountingCertificates.Batch023.valid473 CountingCertificates.Batch023.sound473 H st hI
theorem probabilityBound236 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch059.certificate710).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate473).dm (WitnessCertificates.Batch023.certificate473).beta (WitnessCertificates.Batch023.certificate473).L) ≤ ((CutFailureCertificates.Budget023.certificate473).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound473 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate473).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch059.certificate710).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch023.certificate473).omega:ℝ)) ≤ ((CutFailureCertificates.Budget023.certificate473).bound:ℝ) at hb
  exact (exponentialBound236 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches237 : (MergedCutGroups.Batch059.certificate713).AnchorMatches CountingCertificates.Batch023.certificate475 := by decide +kernel
theorem exponentialBound237 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch059.certificate713).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate475).dm (WitnessCertificates.Batch023.certificate475).beta (WitnessCertificates.Batch023.certificate475).L) ≤ (2*exp (-((CountingCertificates.Batch023.certificate475).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch059.certificate713).exponent:ℝ)*st.R))/((WitnessCertificates.Batch023.certificate475).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch059.certificate713 CountingCertificates.Batch023.certificate475 matches237 MergedCutGroups.Batch059.numericValid713 MergedCutGroups.Batch059.cellsSound713 MergedCutGroups.Batch059.cellsNumeric713 MergedCutGroups.Batch059.populationMatches713
    PopulationCertificates.Batch023.valid475 PopulationCertificates.Batch023.sound475 WitnessCertificates.Batch023.valid475 WitnessCertificates.Batch023.sound475 CountingCertificates.Batch023.valid475 CountingCertificates.Batch023.sound475 H st hI
theorem probabilityBound237 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch059.certificate713).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate475).dm (WitnessCertificates.Batch023.certificate475).beta (WitnessCertificates.Batch023.certificate475).L) ≤ ((CutFailureCertificates.Budget023.certificate475).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound475 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate475).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch059.certificate713).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch023.certificate475).omega:ℝ)) ≤ ((CutFailureCertificates.Budget023.certificate475).bound:ℝ) at hb
  exact (exponentialBound237 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches238 : (MergedCutGroups.Batch059.certificate716).AnchorMatches CountingCertificates.Batch023.certificate477 := by decide +kernel
theorem exponentialBound238 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch059.certificate716).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate477).dm (WitnessCertificates.Batch023.certificate477).beta (WitnessCertificates.Batch023.certificate477).L) ≤ (2*exp (-((CountingCertificates.Batch023.certificate477).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch059.certificate716).exponent:ℝ)*st.R))/((WitnessCertificates.Batch023.certificate477).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch059.certificate716 CountingCertificates.Batch023.certificate477 matches238 MergedCutGroups.Batch059.numericValid716 MergedCutGroups.Batch059.cellsSound716 MergedCutGroups.Batch059.cellsNumeric716 MergedCutGroups.Batch059.populationMatches716
    PopulationCertificates.Batch023.valid477 PopulationCertificates.Batch023.sound477 WitnessCertificates.Batch023.valid477 WitnessCertificates.Batch023.sound477 CountingCertificates.Batch023.valid477 CountingCertificates.Batch023.sound477 H st hI
theorem probabilityBound238 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch059.certificate716).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate477).dm (WitnessCertificates.Batch023.certificate477).beta (WitnessCertificates.Batch023.certificate477).L) ≤ ((CutFailureCertificates.Budget023.certificate477).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound477 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate477).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch059.certificate716).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch023.certificate477).omega:ℝ)) ≤ ((CutFailureCertificates.Budget023.certificate477).bound:ℝ) at hb
  exact (exponentialBound238 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches239 : (MergedCutGroups.Batch059.certificate719).AnchorMatches CountingCertificates.Batch023.certificate479 := by decide +kernel
theorem exponentialBound239 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch059.certificate719).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate479).dm (WitnessCertificates.Batch023.certificate479).beta (WitnessCertificates.Batch023.certificate479).L) ≤ (2*exp (-((CountingCertificates.Batch023.certificate479).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch059.certificate719).exponent:ℝ)*st.R))/((WitnessCertificates.Batch023.certificate479).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch059.certificate719 CountingCertificates.Batch023.certificate479 matches239 MergedCutGroups.Batch059.numericValid719 MergedCutGroups.Batch059.cellsSound719 MergedCutGroups.Batch059.cellsNumeric719 MergedCutGroups.Batch059.populationMatches719
    PopulationCertificates.Batch023.valid479 PopulationCertificates.Batch023.sound479 WitnessCertificates.Batch023.valid479 WitnessCertificates.Batch023.sound479 CountingCertificates.Batch023.valid479 CountingCertificates.Batch023.sound479 H st hI
theorem probabilityBound239 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch059.certificate719).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch023.certificate479).dm (WitnessCertificates.Batch023.certificate479).beta (WitnessCertificates.Batch023.certificate479).L) ≤ ((CutFailureCertificates.Budget023.certificate479).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget023.sound479 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch023.certificate479).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch059.certificate719).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch023.certificate479).omega:ℝ)) ≤ ((CutFailureCertificates.Budget023.certificate479).bound:ℝ) at hb
  exact (exponentialBound239 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch011
