import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch024
import Cycle12.CountingCertificates.Batch025
import Cycle12.CutFailureCertificates.Budget024
import Cycle12.CutFailureCertificates.Budget025
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

namespace Cycle12.CertifiedAnchorFailures.Batch012
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches240 : (MergedCutGroups.Batch060.certificate722).AnchorMatches CountingCertificates.Batch024.certificate481 := by decide +kernel
theorem exponentialBound240 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch060.certificate722).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate481).dm (WitnessCertificates.Batch024.certificate481).beta (WitnessCertificates.Batch024.certificate481).L) ≤ (2*exp (-((CountingCertificates.Batch024.certificate481).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch060.certificate722).exponent:ℝ)*st.R))/((WitnessCertificates.Batch024.certificate481).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch060.certificate722 CountingCertificates.Batch024.certificate481 matches240 MergedCutGroups.Batch060.numericValid722 MergedCutGroups.Batch060.cellsSound722 MergedCutGroups.Batch060.cellsNumeric722 MergedCutGroups.Batch060.populationMatches722
    PopulationCertificates.Batch024.valid481 PopulationCertificates.Batch024.sound481 WitnessCertificates.Batch024.valid481 WitnessCertificates.Batch024.sound481 CountingCertificates.Batch024.valid481 CountingCertificates.Batch024.sound481 H st hI
theorem probabilityBound240 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch060.certificate722).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate481).dm (WitnessCertificates.Batch024.certificate481).beta (WitnessCertificates.Batch024.certificate481).L) ≤ ((CutFailureCertificates.Budget024.certificate481).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound481 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate481).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch060.certificate722).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch024.certificate481).omega:ℝ)) ≤ ((CutFailureCertificates.Budget024.certificate481).bound:ℝ) at hb
  exact (exponentialBound240 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches241 : (MergedCutGroups.Batch060.certificate725).AnchorMatches CountingCertificates.Batch024.certificate483 := by decide +kernel
theorem exponentialBound241 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch060.certificate725).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate483).dm (WitnessCertificates.Batch024.certificate483).beta (WitnessCertificates.Batch024.certificate483).L) ≤ (2*exp (-((CountingCertificates.Batch024.certificate483).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch060.certificate725).exponent:ℝ)*st.R))/((WitnessCertificates.Batch024.certificate483).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch060.certificate725 CountingCertificates.Batch024.certificate483 matches241 MergedCutGroups.Batch060.numericValid725 MergedCutGroups.Batch060.cellsSound725 MergedCutGroups.Batch060.cellsNumeric725 MergedCutGroups.Batch060.populationMatches725
    PopulationCertificates.Batch024.valid483 PopulationCertificates.Batch024.sound483 WitnessCertificates.Batch024.valid483 WitnessCertificates.Batch024.sound483 CountingCertificates.Batch024.valid483 CountingCertificates.Batch024.sound483 H st hI
theorem probabilityBound241 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch060.certificate725).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate483).dm (WitnessCertificates.Batch024.certificate483).beta (WitnessCertificates.Batch024.certificate483).L) ≤ ((CutFailureCertificates.Budget024.certificate483).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound483 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate483).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch060.certificate725).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch024.certificate483).omega:ℝ)) ≤ ((CutFailureCertificates.Budget024.certificate483).bound:ℝ) at hb
  exact (exponentialBound241 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches242 : (MergedCutGroups.Batch060.certificate728).AnchorMatches CountingCertificates.Batch024.certificate485 := by decide +kernel
theorem exponentialBound242 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch060.certificate728).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate485).dm (WitnessCertificates.Batch024.certificate485).beta (WitnessCertificates.Batch024.certificate485).L) ≤ (2*exp (-((CountingCertificates.Batch024.certificate485).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch060.certificate728).exponent:ℝ)*st.R))/((WitnessCertificates.Batch024.certificate485).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch060.certificate728 CountingCertificates.Batch024.certificate485 matches242 MergedCutGroups.Batch060.numericValid728 MergedCutGroups.Batch060.cellsSound728 MergedCutGroups.Batch060.cellsNumeric728 MergedCutGroups.Batch060.populationMatches728
    PopulationCertificates.Batch024.valid485 PopulationCertificates.Batch024.sound485 WitnessCertificates.Batch024.valid485 WitnessCertificates.Batch024.sound485 CountingCertificates.Batch024.valid485 CountingCertificates.Batch024.sound485 H st hI
theorem probabilityBound242 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch060.certificate728).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate485).dm (WitnessCertificates.Batch024.certificate485).beta (WitnessCertificates.Batch024.certificate485).L) ≤ ((CutFailureCertificates.Budget024.certificate485).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound485 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate485).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch060.certificate728).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch024.certificate485).omega:ℝ)) ≤ ((CutFailureCertificates.Budget024.certificate485).bound:ℝ) at hb
  exact (exponentialBound242 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches243 : (MergedCutGroups.Batch060.certificate731).AnchorMatches CountingCertificates.Batch024.certificate487 := by decide +kernel
theorem exponentialBound243 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch060.certificate731).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate487).dm (WitnessCertificates.Batch024.certificate487).beta (WitnessCertificates.Batch024.certificate487).L) ≤ (2*exp (-((CountingCertificates.Batch024.certificate487).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch060.certificate731).exponent:ℝ)*st.R))/((WitnessCertificates.Batch024.certificate487).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch060.certificate731 CountingCertificates.Batch024.certificate487 matches243 MergedCutGroups.Batch060.numericValid731 MergedCutGroups.Batch060.cellsSound731 MergedCutGroups.Batch060.cellsNumeric731 MergedCutGroups.Batch060.populationMatches731
    PopulationCertificates.Batch024.valid487 PopulationCertificates.Batch024.sound487 WitnessCertificates.Batch024.valid487 WitnessCertificates.Batch024.sound487 CountingCertificates.Batch024.valid487 CountingCertificates.Batch024.sound487 H st hI
theorem probabilityBound243 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch060.certificate731).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate487).dm (WitnessCertificates.Batch024.certificate487).beta (WitnessCertificates.Batch024.certificate487).L) ≤ ((CutFailureCertificates.Budget024.certificate487).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound487 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate487).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch060.certificate731).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch024.certificate487).omega:ℝ)) ≤ ((CutFailureCertificates.Budget024.certificate487).bound:ℝ) at hb
  exact (exponentialBound243 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches244 : (MergedCutGroups.Batch061.certificate734).AnchorMatches CountingCertificates.Batch024.certificate489 := by decide +kernel
theorem exponentialBound244 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch061.certificate734).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate489).dm (WitnessCertificates.Batch024.certificate489).beta (WitnessCertificates.Batch024.certificate489).L) ≤ (2*exp (-((CountingCertificates.Batch024.certificate489).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch061.certificate734).exponent:ℝ)*st.R))/((WitnessCertificates.Batch024.certificate489).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch061.certificate734 CountingCertificates.Batch024.certificate489 matches244 MergedCutGroups.Batch061.numericValid734 MergedCutGroups.Batch061.cellsSound734 MergedCutGroups.Batch061.cellsNumeric734 MergedCutGroups.Batch061.populationMatches734
    PopulationCertificates.Batch024.valid489 PopulationCertificates.Batch024.sound489 WitnessCertificates.Batch024.valid489 WitnessCertificates.Batch024.sound489 CountingCertificates.Batch024.valid489 CountingCertificates.Batch024.sound489 H st hI
theorem probabilityBound244 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch061.certificate734).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate489).dm (WitnessCertificates.Batch024.certificate489).beta (WitnessCertificates.Batch024.certificate489).L) ≤ ((CutFailureCertificates.Budget024.certificate489).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound489 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate489).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch061.certificate734).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch024.certificate489).omega:ℝ)) ≤ ((CutFailureCertificates.Budget024.certificate489).bound:ℝ) at hb
  exact (exponentialBound244 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches245 : (MergedCutGroups.Batch061.certificate737).AnchorMatches CountingCertificates.Batch024.certificate491 := by decide +kernel
theorem exponentialBound245 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch061.certificate737).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate491).dm (WitnessCertificates.Batch024.certificate491).beta (WitnessCertificates.Batch024.certificate491).L) ≤ (2*exp (-((CountingCertificates.Batch024.certificate491).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch061.certificate737).exponent:ℝ)*st.R))/((WitnessCertificates.Batch024.certificate491).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch061.certificate737 CountingCertificates.Batch024.certificate491 matches245 MergedCutGroups.Batch061.numericValid737 MergedCutGroups.Batch061.cellsSound737 MergedCutGroups.Batch061.cellsNumeric737 MergedCutGroups.Batch061.populationMatches737
    PopulationCertificates.Batch024.valid491 PopulationCertificates.Batch024.sound491 WitnessCertificates.Batch024.valid491 WitnessCertificates.Batch024.sound491 CountingCertificates.Batch024.valid491 CountingCertificates.Batch024.sound491 H st hI
theorem probabilityBound245 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch061.certificate737).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate491).dm (WitnessCertificates.Batch024.certificate491).beta (WitnessCertificates.Batch024.certificate491).L) ≤ ((CutFailureCertificates.Budget024.certificate491).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound491 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate491).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch061.certificate737).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch024.certificate491).omega:ℝ)) ≤ ((CutFailureCertificates.Budget024.certificate491).bound:ℝ) at hb
  exact (exponentialBound245 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches246 : (MergedCutGroups.Batch061.certificate740).AnchorMatches CountingCertificates.Batch024.certificate493 := by decide +kernel
theorem exponentialBound246 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch061.certificate740).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate493).dm (WitnessCertificates.Batch024.certificate493).beta (WitnessCertificates.Batch024.certificate493).L) ≤ (2*exp (-((CountingCertificates.Batch024.certificate493).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch061.certificate740).exponent:ℝ)*st.R))/((WitnessCertificates.Batch024.certificate493).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch061.certificate740 CountingCertificates.Batch024.certificate493 matches246 MergedCutGroups.Batch061.numericValid740 MergedCutGroups.Batch061.cellsSound740 MergedCutGroups.Batch061.cellsNumeric740 MergedCutGroups.Batch061.populationMatches740
    PopulationCertificates.Batch024.valid493 PopulationCertificates.Batch024.sound493 WitnessCertificates.Batch024.valid493 WitnessCertificates.Batch024.sound493 CountingCertificates.Batch024.valid493 CountingCertificates.Batch024.sound493 H st hI
theorem probabilityBound246 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch061.certificate740).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate493).dm (WitnessCertificates.Batch024.certificate493).beta (WitnessCertificates.Batch024.certificate493).L) ≤ ((CutFailureCertificates.Budget024.certificate493).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound493 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate493).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch061.certificate740).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch024.certificate493).omega:ℝ)) ≤ ((CutFailureCertificates.Budget024.certificate493).bound:ℝ) at hb
  exact (exponentialBound246 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches247 : (MergedCutGroups.Batch061.certificate743).AnchorMatches CountingCertificates.Batch024.certificate495 := by decide +kernel
theorem exponentialBound247 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch061.certificate743).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate495).dm (WitnessCertificates.Batch024.certificate495).beta (WitnessCertificates.Batch024.certificate495).L) ≤ (2*exp (-((CountingCertificates.Batch024.certificate495).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch061.certificate743).exponent:ℝ)*st.R))/((WitnessCertificates.Batch024.certificate495).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch061.certificate743 CountingCertificates.Batch024.certificate495 matches247 MergedCutGroups.Batch061.numericValid743 MergedCutGroups.Batch061.cellsSound743 MergedCutGroups.Batch061.cellsNumeric743 MergedCutGroups.Batch061.populationMatches743
    PopulationCertificates.Batch024.valid495 PopulationCertificates.Batch024.sound495 WitnessCertificates.Batch024.valid495 WitnessCertificates.Batch024.sound495 CountingCertificates.Batch024.valid495 CountingCertificates.Batch024.sound495 H st hI
theorem probabilityBound247 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch061.certificate743).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate495).dm (WitnessCertificates.Batch024.certificate495).beta (WitnessCertificates.Batch024.certificate495).L) ≤ ((CutFailureCertificates.Budget024.certificate495).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound495 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate495).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch061.certificate743).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch024.certificate495).omega:ℝ)) ≤ ((CutFailureCertificates.Budget024.certificate495).bound:ℝ) at hb
  exact (exponentialBound247 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches248 : (MergedCutGroups.Batch062.certificate746).AnchorMatches CountingCertificates.Batch024.certificate497 := by decide +kernel
theorem exponentialBound248 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch062.certificate746).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate497).dm (WitnessCertificates.Batch024.certificate497).beta (WitnessCertificates.Batch024.certificate497).L) ≤ (2*exp (-((CountingCertificates.Batch024.certificate497).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch062.certificate746).exponent:ℝ)*st.R))/((WitnessCertificates.Batch024.certificate497).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch062.certificate746 CountingCertificates.Batch024.certificate497 matches248 MergedCutGroups.Batch062.numericValid746 MergedCutGroups.Batch062.cellsSound746 MergedCutGroups.Batch062.cellsNumeric746 MergedCutGroups.Batch062.populationMatches746
    PopulationCertificates.Batch024.valid497 PopulationCertificates.Batch024.sound497 WitnessCertificates.Batch024.valid497 WitnessCertificates.Batch024.sound497 CountingCertificates.Batch024.valid497 CountingCertificates.Batch024.sound497 H st hI
theorem probabilityBound248 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch062.certificate746).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate497).dm (WitnessCertificates.Batch024.certificate497).beta (WitnessCertificates.Batch024.certificate497).L) ≤ ((CutFailureCertificates.Budget024.certificate497).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound497 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate497).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch062.certificate746).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch024.certificate497).omega:ℝ)) ≤ ((CutFailureCertificates.Budget024.certificate497).bound:ℝ) at hb
  exact (exponentialBound248 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches249 : (MergedCutGroups.Batch062.certificate749).AnchorMatches CountingCertificates.Batch024.certificate499 := by decide +kernel
theorem exponentialBound249 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch062.certificate749).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate499).dm (WitnessCertificates.Batch024.certificate499).beta (WitnessCertificates.Batch024.certificate499).L) ≤ (2*exp (-((CountingCertificates.Batch024.certificate499).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch062.certificate749).exponent:ℝ)*st.R))/((WitnessCertificates.Batch024.certificate499).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch062.certificate749 CountingCertificates.Batch024.certificate499 matches249 MergedCutGroups.Batch062.numericValid749 MergedCutGroups.Batch062.cellsSound749 MergedCutGroups.Batch062.cellsNumeric749 MergedCutGroups.Batch062.populationMatches749
    PopulationCertificates.Batch024.valid499 PopulationCertificates.Batch024.sound499 WitnessCertificates.Batch024.valid499 WitnessCertificates.Batch024.sound499 CountingCertificates.Batch024.valid499 CountingCertificates.Batch024.sound499 H st hI
theorem probabilityBound249 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch062.certificate749).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch024.certificate499).dm (WitnessCertificates.Batch024.certificate499).beta (WitnessCertificates.Batch024.certificate499).L) ≤ ((CutFailureCertificates.Budget024.certificate499).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget024.sound499 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch024.certificate499).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch062.certificate749).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch024.certificate499).omega:ℝ)) ≤ ((CutFailureCertificates.Budget024.certificate499).bound:ℝ) at hb
  exact (exponentialBound249 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches250 : (MergedCutGroups.Batch062.certificate752).AnchorMatches CountingCertificates.Batch025.certificate501 := by decide +kernel
theorem exponentialBound250 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch062.certificate752).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate501).dm (WitnessCertificates.Batch025.certificate501).beta (WitnessCertificates.Batch025.certificate501).L) ≤ (2*exp (-((CountingCertificates.Batch025.certificate501).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch062.certificate752).exponent:ℝ)*st.R))/((WitnessCertificates.Batch025.certificate501).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch062.certificate752 CountingCertificates.Batch025.certificate501 matches250 MergedCutGroups.Batch062.numericValid752 MergedCutGroups.Batch062.cellsSound752 MergedCutGroups.Batch062.cellsNumeric752 MergedCutGroups.Batch062.populationMatches752
    PopulationCertificates.Batch025.valid501 PopulationCertificates.Batch025.sound501 WitnessCertificates.Batch025.valid501 WitnessCertificates.Batch025.sound501 CountingCertificates.Batch025.valid501 CountingCertificates.Batch025.sound501 H st hI
theorem probabilityBound250 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch062.certificate752).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate501).dm (WitnessCertificates.Batch025.certificate501).beta (WitnessCertificates.Batch025.certificate501).L) ≤ ((CutFailureCertificates.Budget025.certificate501).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound501 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate501).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch062.certificate752).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch025.certificate501).omega:ℝ)) ≤ ((CutFailureCertificates.Budget025.certificate501).bound:ℝ) at hb
  exact (exponentialBound250 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches251 : (MergedCutGroups.Batch062.certificate755).AnchorMatches CountingCertificates.Batch025.certificate503 := by decide +kernel
theorem exponentialBound251 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch062.certificate755).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate503).dm (WitnessCertificates.Batch025.certificate503).beta (WitnessCertificates.Batch025.certificate503).L) ≤ (2*exp (-((CountingCertificates.Batch025.certificate503).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch062.certificate755).exponent:ℝ)*st.R))/((WitnessCertificates.Batch025.certificate503).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch062.certificate755 CountingCertificates.Batch025.certificate503 matches251 MergedCutGroups.Batch062.numericValid755 MergedCutGroups.Batch062.cellsSound755 MergedCutGroups.Batch062.cellsNumeric755 MergedCutGroups.Batch062.populationMatches755
    PopulationCertificates.Batch025.valid503 PopulationCertificates.Batch025.sound503 WitnessCertificates.Batch025.valid503 WitnessCertificates.Batch025.sound503 CountingCertificates.Batch025.valid503 CountingCertificates.Batch025.sound503 H st hI
theorem probabilityBound251 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch062.certificate755).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate503).dm (WitnessCertificates.Batch025.certificate503).beta (WitnessCertificates.Batch025.certificate503).L) ≤ ((CutFailureCertificates.Budget025.certificate503).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound503 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate503).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch062.certificate755).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch025.certificate503).omega:ℝ)) ≤ ((CutFailureCertificates.Budget025.certificate503).bound:ℝ) at hb
  exact (exponentialBound251 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches252 : (MergedCutGroups.Batch063.certificate758).AnchorMatches CountingCertificates.Batch025.certificate505 := by decide +kernel
theorem exponentialBound252 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch063.certificate758).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate505).dm (WitnessCertificates.Batch025.certificate505).beta (WitnessCertificates.Batch025.certificate505).L) ≤ (2*exp (-((CountingCertificates.Batch025.certificate505).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch063.certificate758).exponent:ℝ)*st.R))/((WitnessCertificates.Batch025.certificate505).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch063.certificate758 CountingCertificates.Batch025.certificate505 matches252 MergedCutGroups.Batch063.numericValid758 MergedCutGroups.Batch063.cellsSound758 MergedCutGroups.Batch063.cellsNumeric758 MergedCutGroups.Batch063.populationMatches758
    PopulationCertificates.Batch025.valid505 PopulationCertificates.Batch025.sound505 WitnessCertificates.Batch025.valid505 WitnessCertificates.Batch025.sound505 CountingCertificates.Batch025.valid505 CountingCertificates.Batch025.sound505 H st hI
theorem probabilityBound252 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch063.certificate758).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate505).dm (WitnessCertificates.Batch025.certificate505).beta (WitnessCertificates.Batch025.certificate505).L) ≤ ((CutFailureCertificates.Budget025.certificate505).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound505 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate505).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch063.certificate758).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch025.certificate505).omega:ℝ)) ≤ ((CutFailureCertificates.Budget025.certificate505).bound:ℝ) at hb
  exact (exponentialBound252 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches253 : (MergedCutGroups.Batch063.certificate761).AnchorMatches CountingCertificates.Batch025.certificate507 := by decide +kernel
theorem exponentialBound253 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch063.certificate761).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate507).dm (WitnessCertificates.Batch025.certificate507).beta (WitnessCertificates.Batch025.certificate507).L) ≤ (2*exp (-((CountingCertificates.Batch025.certificate507).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch063.certificate761).exponent:ℝ)*st.R))/((WitnessCertificates.Batch025.certificate507).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch063.certificate761 CountingCertificates.Batch025.certificate507 matches253 MergedCutGroups.Batch063.numericValid761 MergedCutGroups.Batch063.cellsSound761 MergedCutGroups.Batch063.cellsNumeric761 MergedCutGroups.Batch063.populationMatches761
    PopulationCertificates.Batch025.valid507 PopulationCertificates.Batch025.sound507 WitnessCertificates.Batch025.valid507 WitnessCertificates.Batch025.sound507 CountingCertificates.Batch025.valid507 CountingCertificates.Batch025.sound507 H st hI
theorem probabilityBound253 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch063.certificate761).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate507).dm (WitnessCertificates.Batch025.certificate507).beta (WitnessCertificates.Batch025.certificate507).L) ≤ ((CutFailureCertificates.Budget025.certificate507).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound507 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate507).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch063.certificate761).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch025.certificate507).omega:ℝ)) ≤ ((CutFailureCertificates.Budget025.certificate507).bound:ℝ) at hb
  exact (exponentialBound253 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches254 : (MergedCutGroups.Batch063.certificate764).AnchorMatches CountingCertificates.Batch025.certificate509 := by decide +kernel
theorem exponentialBound254 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch063.certificate764).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate509).dm (WitnessCertificates.Batch025.certificate509).beta (WitnessCertificates.Batch025.certificate509).L) ≤ (2*exp (-((CountingCertificates.Batch025.certificate509).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch063.certificate764).exponent:ℝ)*st.R))/((WitnessCertificates.Batch025.certificate509).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch063.certificate764 CountingCertificates.Batch025.certificate509 matches254 MergedCutGroups.Batch063.numericValid764 MergedCutGroups.Batch063.cellsSound764 MergedCutGroups.Batch063.cellsNumeric764 MergedCutGroups.Batch063.populationMatches764
    PopulationCertificates.Batch025.valid509 PopulationCertificates.Batch025.sound509 WitnessCertificates.Batch025.valid509 WitnessCertificates.Batch025.sound509 CountingCertificates.Batch025.valid509 CountingCertificates.Batch025.sound509 H st hI
theorem probabilityBound254 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch063.certificate764).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate509).dm (WitnessCertificates.Batch025.certificate509).beta (WitnessCertificates.Batch025.certificate509).L) ≤ ((CutFailureCertificates.Budget025.certificate509).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound509 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate509).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch063.certificate764).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch025.certificate509).omega:ℝ)) ≤ ((CutFailureCertificates.Budget025.certificate509).bound:ℝ) at hb
  exact (exponentialBound254 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches255 : (MergedCutGroups.Batch063.certificate767).AnchorMatches CountingCertificates.Batch025.certificate511 := by decide +kernel
theorem exponentialBound255 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch063.certificate767).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate511).dm (WitnessCertificates.Batch025.certificate511).beta (WitnessCertificates.Batch025.certificate511).L) ≤ (2*exp (-((CountingCertificates.Batch025.certificate511).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch063.certificate767).exponent:ℝ)*st.R))/((WitnessCertificates.Batch025.certificate511).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch063.certificate767 CountingCertificates.Batch025.certificate511 matches255 MergedCutGroups.Batch063.numericValid767 MergedCutGroups.Batch063.cellsSound767 MergedCutGroups.Batch063.cellsNumeric767 MergedCutGroups.Batch063.populationMatches767
    PopulationCertificates.Batch025.valid511 PopulationCertificates.Batch025.sound511 WitnessCertificates.Batch025.valid511 WitnessCertificates.Batch025.sound511 CountingCertificates.Batch025.valid511 CountingCertificates.Batch025.sound511 H st hI
theorem probabilityBound255 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch063.certificate767).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate511).dm (WitnessCertificates.Batch025.certificate511).beta (WitnessCertificates.Batch025.certificate511).L) ≤ ((CutFailureCertificates.Budget025.certificate511).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound511 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate511).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch063.certificate767).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch025.certificate511).omega:ℝ)) ≤ ((CutFailureCertificates.Budget025.certificate511).bound:ℝ) at hb
  exact (exponentialBound255 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches256 : (MergedCutGroups.Batch064.certificate770).AnchorMatches CountingCertificates.Batch025.certificate513 := by decide +kernel
theorem exponentialBound256 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch064.certificate770).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate513).dm (WitnessCertificates.Batch025.certificate513).beta (WitnessCertificates.Batch025.certificate513).L) ≤ (2*exp (-((CountingCertificates.Batch025.certificate513).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch064.certificate770).exponent:ℝ)*st.R))/((WitnessCertificates.Batch025.certificate513).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch064.certificate770 CountingCertificates.Batch025.certificate513 matches256 MergedCutGroups.Batch064.numericValid770 MergedCutGroups.Batch064.cellsSound770 MergedCutGroups.Batch064.cellsNumeric770 MergedCutGroups.Batch064.populationMatches770
    PopulationCertificates.Batch025.valid513 PopulationCertificates.Batch025.sound513 WitnessCertificates.Batch025.valid513 WitnessCertificates.Batch025.sound513 CountingCertificates.Batch025.valid513 CountingCertificates.Batch025.sound513 H st hI
theorem probabilityBound256 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch064.certificate770).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate513).dm (WitnessCertificates.Batch025.certificate513).beta (WitnessCertificates.Batch025.certificate513).L) ≤ ((CutFailureCertificates.Budget025.certificate513).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound513 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate513).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch064.certificate770).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch025.certificate513).omega:ℝ)) ≤ ((CutFailureCertificates.Budget025.certificate513).bound:ℝ) at hb
  exact (exponentialBound256 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches257 : (MergedCutGroups.Batch064.certificate773).AnchorMatches CountingCertificates.Batch025.certificate515 := by decide +kernel
theorem exponentialBound257 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch064.certificate773).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate515).dm (WitnessCertificates.Batch025.certificate515).beta (WitnessCertificates.Batch025.certificate515).L) ≤ (2*exp (-((CountingCertificates.Batch025.certificate515).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch064.certificate773).exponent:ℝ)*st.R))/((WitnessCertificates.Batch025.certificate515).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch064.certificate773 CountingCertificates.Batch025.certificate515 matches257 MergedCutGroups.Batch064.numericValid773 MergedCutGroups.Batch064.cellsSound773 MergedCutGroups.Batch064.cellsNumeric773 MergedCutGroups.Batch064.populationMatches773
    PopulationCertificates.Batch025.valid515 PopulationCertificates.Batch025.sound515 WitnessCertificates.Batch025.valid515 WitnessCertificates.Batch025.sound515 CountingCertificates.Batch025.valid515 CountingCertificates.Batch025.sound515 H st hI
theorem probabilityBound257 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch064.certificate773).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate515).dm (WitnessCertificates.Batch025.certificate515).beta (WitnessCertificates.Batch025.certificate515).L) ≤ ((CutFailureCertificates.Budget025.certificate515).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound515 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate515).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch064.certificate773).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch025.certificate515).omega:ℝ)) ≤ ((CutFailureCertificates.Budget025.certificate515).bound:ℝ) at hb
  exact (exponentialBound257 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches258 : (MergedCutGroups.Batch064.certificate776).AnchorMatches CountingCertificates.Batch025.certificate517 := by decide +kernel
theorem exponentialBound258 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch064.certificate776).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate517).dm (WitnessCertificates.Batch025.certificate517).beta (WitnessCertificates.Batch025.certificate517).L) ≤ (2*exp (-((CountingCertificates.Batch025.certificate517).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch064.certificate776).exponent:ℝ)*st.R))/((WitnessCertificates.Batch025.certificate517).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch064.certificate776 CountingCertificates.Batch025.certificate517 matches258 MergedCutGroups.Batch064.numericValid776 MergedCutGroups.Batch064.cellsSound776 MergedCutGroups.Batch064.cellsNumeric776 MergedCutGroups.Batch064.populationMatches776
    PopulationCertificates.Batch025.valid517 PopulationCertificates.Batch025.sound517 WitnessCertificates.Batch025.valid517 WitnessCertificates.Batch025.sound517 CountingCertificates.Batch025.valid517 CountingCertificates.Batch025.sound517 H st hI
theorem probabilityBound258 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch064.certificate776).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate517).dm (WitnessCertificates.Batch025.certificate517).beta (WitnessCertificates.Batch025.certificate517).L) ≤ ((CutFailureCertificates.Budget025.certificate517).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound517 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate517).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch064.certificate776).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch025.certificate517).omega:ℝ)) ≤ ((CutFailureCertificates.Budget025.certificate517).bound:ℝ) at hb
  exact (exponentialBound258 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches259 : (MergedCutGroups.Batch064.certificate779).AnchorMatches CountingCertificates.Batch025.certificate519 := by decide +kernel
theorem exponentialBound259 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch064.certificate779).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate519).dm (WitnessCertificates.Batch025.certificate519).beta (WitnessCertificates.Batch025.certificate519).L) ≤ (2*exp (-((CountingCertificates.Batch025.certificate519).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch064.certificate779).exponent:ℝ)*st.R))/((WitnessCertificates.Batch025.certificate519).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch064.certificate779 CountingCertificates.Batch025.certificate519 matches259 MergedCutGroups.Batch064.numericValid779 MergedCutGroups.Batch064.cellsSound779 MergedCutGroups.Batch064.cellsNumeric779 MergedCutGroups.Batch064.populationMatches779
    PopulationCertificates.Batch025.valid519 PopulationCertificates.Batch025.sound519 WitnessCertificates.Batch025.valid519 WitnessCertificates.Batch025.sound519 CountingCertificates.Batch025.valid519 CountingCertificates.Batch025.sound519 H st hI
theorem probabilityBound259 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch064.certificate779).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch025.certificate519).dm (WitnessCertificates.Batch025.certificate519).beta (WitnessCertificates.Batch025.certificate519).L) ≤ ((CutFailureCertificates.Budget025.certificate519).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget025.sound519 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch025.certificate519).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch064.certificate779).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch025.certificate519).omega:ℝ)) ≤ ((CutFailureCertificates.Budget025.certificate519).bound:ℝ) at hb
  exact (exponentialBound259 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch012
