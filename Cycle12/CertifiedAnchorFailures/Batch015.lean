import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch030
import Cycle12.CountingCertificates.Batch031
import Cycle12.CutFailureCertificates.Budget030
import Cycle12.CutFailureCertificates.Budget031
import Cycle12.MergedCutGroups.Batch075
import Cycle12.MergedCutGroups.Batch076
import Cycle12.MergedCutGroups.Batch077
import Cycle12.MergedCutGroups.Batch078
import Cycle12.MergedCutGroups.Batch079
import Cycle12.PopulationCertificates.Batch030
import Cycle12.PopulationCertificates.Batch031
import Cycle12.WitnessCertificates.Batch030
import Cycle12.WitnessCertificates.Batch031

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedAnchorFailures.Batch015
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches300 : (MergedCutGroups.Batch075.certificate902).AnchorMatches CountingCertificates.Batch030.certificate601 := by decide +kernel
theorem exponentialBound300 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch075.certificate902).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate601).dm (WitnessCertificates.Batch030.certificate601).beta (WitnessCertificates.Batch030.certificate601).L) ≤ (2*exp (-((CountingCertificates.Batch030.certificate601).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch075.certificate902).exponent:ℝ)*st.R))/((WitnessCertificates.Batch030.certificate601).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch075.certificate902 CountingCertificates.Batch030.certificate601 matches300 MergedCutGroups.Batch075.numericValid902 MergedCutGroups.Batch075.cellsSound902 MergedCutGroups.Batch075.cellsNumeric902 MergedCutGroups.Batch075.populationMatches902
    PopulationCertificates.Batch030.valid601 PopulationCertificates.Batch030.sound601 WitnessCertificates.Batch030.valid601 WitnessCertificates.Batch030.sound601 CountingCertificates.Batch030.valid601 CountingCertificates.Batch030.sound601 H st hI
theorem probabilityBound300 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch075.certificate902).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate601).dm (WitnessCertificates.Batch030.certificate601).beta (WitnessCertificates.Batch030.certificate601).L) ≤ ((CutFailureCertificates.Budget030.certificate601).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound601 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate601).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch075.certificate902).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch030.certificate601).omega:ℝ)) ≤ ((CutFailureCertificates.Budget030.certificate601).bound:ℝ) at hb
  exact (exponentialBound300 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches301 : (MergedCutGroups.Batch075.certificate905).AnchorMatches CountingCertificates.Batch030.certificate603 := by decide +kernel
theorem exponentialBound301 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch075.certificate905).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate603).dm (WitnessCertificates.Batch030.certificate603).beta (WitnessCertificates.Batch030.certificate603).L) ≤ (2*exp (-((CountingCertificates.Batch030.certificate603).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch075.certificate905).exponent:ℝ)*st.R))/((WitnessCertificates.Batch030.certificate603).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch075.certificate905 CountingCertificates.Batch030.certificate603 matches301 MergedCutGroups.Batch075.numericValid905 MergedCutGroups.Batch075.cellsSound905 MergedCutGroups.Batch075.cellsNumeric905 MergedCutGroups.Batch075.populationMatches905
    PopulationCertificates.Batch030.valid603 PopulationCertificates.Batch030.sound603 WitnessCertificates.Batch030.valid603 WitnessCertificates.Batch030.sound603 CountingCertificates.Batch030.valid603 CountingCertificates.Batch030.sound603 H st hI
theorem probabilityBound301 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch075.certificate905).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate603).dm (WitnessCertificates.Batch030.certificate603).beta (WitnessCertificates.Batch030.certificate603).L) ≤ ((CutFailureCertificates.Budget030.certificate603).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound603 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate603).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch075.certificate905).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch030.certificate603).omega:ℝ)) ≤ ((CutFailureCertificates.Budget030.certificate603).bound:ℝ) at hb
  exact (exponentialBound301 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches302 : (MergedCutGroups.Batch075.certificate908).AnchorMatches CountingCertificates.Batch030.certificate605 := by decide +kernel
theorem exponentialBound302 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch075.certificate908).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate605).dm (WitnessCertificates.Batch030.certificate605).beta (WitnessCertificates.Batch030.certificate605).L) ≤ (2*exp (-((CountingCertificates.Batch030.certificate605).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch075.certificate908).exponent:ℝ)*st.R))/((WitnessCertificates.Batch030.certificate605).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch075.certificate908 CountingCertificates.Batch030.certificate605 matches302 MergedCutGroups.Batch075.numericValid908 MergedCutGroups.Batch075.cellsSound908 MergedCutGroups.Batch075.cellsNumeric908 MergedCutGroups.Batch075.populationMatches908
    PopulationCertificates.Batch030.valid605 PopulationCertificates.Batch030.sound605 WitnessCertificates.Batch030.valid605 WitnessCertificates.Batch030.sound605 CountingCertificates.Batch030.valid605 CountingCertificates.Batch030.sound605 H st hI
theorem probabilityBound302 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch075.certificate908).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate605).dm (WitnessCertificates.Batch030.certificate605).beta (WitnessCertificates.Batch030.certificate605).L) ≤ ((CutFailureCertificates.Budget030.certificate605).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound605 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate605).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch075.certificate908).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch030.certificate605).omega:ℝ)) ≤ ((CutFailureCertificates.Budget030.certificate605).bound:ℝ) at hb
  exact (exponentialBound302 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches303 : (MergedCutGroups.Batch075.certificate911).AnchorMatches CountingCertificates.Batch030.certificate607 := by decide +kernel
theorem exponentialBound303 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch075.certificate911).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate607).dm (WitnessCertificates.Batch030.certificate607).beta (WitnessCertificates.Batch030.certificate607).L) ≤ (2*exp (-((CountingCertificates.Batch030.certificate607).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch075.certificate911).exponent:ℝ)*st.R))/((WitnessCertificates.Batch030.certificate607).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch075.certificate911 CountingCertificates.Batch030.certificate607 matches303 MergedCutGroups.Batch075.numericValid911 MergedCutGroups.Batch075.cellsSound911 MergedCutGroups.Batch075.cellsNumeric911 MergedCutGroups.Batch075.populationMatches911
    PopulationCertificates.Batch030.valid607 PopulationCertificates.Batch030.sound607 WitnessCertificates.Batch030.valid607 WitnessCertificates.Batch030.sound607 CountingCertificates.Batch030.valid607 CountingCertificates.Batch030.sound607 H st hI
theorem probabilityBound303 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch075.certificate911).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate607).dm (WitnessCertificates.Batch030.certificate607).beta (WitnessCertificates.Batch030.certificate607).L) ≤ ((CutFailureCertificates.Budget030.certificate607).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound607 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate607).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch075.certificate911).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch030.certificate607).omega:ℝ)) ≤ ((CutFailureCertificates.Budget030.certificate607).bound:ℝ) at hb
  exact (exponentialBound303 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches304 : (MergedCutGroups.Batch076.certificate914).AnchorMatches CountingCertificates.Batch030.certificate609 := by decide +kernel
theorem exponentialBound304 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch076.certificate914).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate609).dm (WitnessCertificates.Batch030.certificate609).beta (WitnessCertificates.Batch030.certificate609).L) ≤ (2*exp (-((CountingCertificates.Batch030.certificate609).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch076.certificate914).exponent:ℝ)*st.R))/((WitnessCertificates.Batch030.certificate609).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch076.certificate914 CountingCertificates.Batch030.certificate609 matches304 MergedCutGroups.Batch076.numericValid914 MergedCutGroups.Batch076.cellsSound914 MergedCutGroups.Batch076.cellsNumeric914 MergedCutGroups.Batch076.populationMatches914
    PopulationCertificates.Batch030.valid609 PopulationCertificates.Batch030.sound609 WitnessCertificates.Batch030.valid609 WitnessCertificates.Batch030.sound609 CountingCertificates.Batch030.valid609 CountingCertificates.Batch030.sound609 H st hI
theorem probabilityBound304 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch076.certificate914).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate609).dm (WitnessCertificates.Batch030.certificate609).beta (WitnessCertificates.Batch030.certificate609).L) ≤ ((CutFailureCertificates.Budget030.certificate609).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound609 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate609).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch076.certificate914).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch030.certificate609).omega:ℝ)) ≤ ((CutFailureCertificates.Budget030.certificate609).bound:ℝ) at hb
  exact (exponentialBound304 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches305 : (MergedCutGroups.Batch076.certificate917).AnchorMatches CountingCertificates.Batch030.certificate611 := by decide +kernel
theorem exponentialBound305 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch076.certificate917).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate611).dm (WitnessCertificates.Batch030.certificate611).beta (WitnessCertificates.Batch030.certificate611).L) ≤ (2*exp (-((CountingCertificates.Batch030.certificate611).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch076.certificate917).exponent:ℝ)*st.R))/((WitnessCertificates.Batch030.certificate611).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch076.certificate917 CountingCertificates.Batch030.certificate611 matches305 MergedCutGroups.Batch076.numericValid917 MergedCutGroups.Batch076.cellsSound917 MergedCutGroups.Batch076.cellsNumeric917 MergedCutGroups.Batch076.populationMatches917
    PopulationCertificates.Batch030.valid611 PopulationCertificates.Batch030.sound611 WitnessCertificates.Batch030.valid611 WitnessCertificates.Batch030.sound611 CountingCertificates.Batch030.valid611 CountingCertificates.Batch030.sound611 H st hI
theorem probabilityBound305 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch076.certificate917).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate611).dm (WitnessCertificates.Batch030.certificate611).beta (WitnessCertificates.Batch030.certificate611).L) ≤ ((CutFailureCertificates.Budget030.certificate611).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound611 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate611).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch076.certificate917).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch030.certificate611).omega:ℝ)) ≤ ((CutFailureCertificates.Budget030.certificate611).bound:ℝ) at hb
  exact (exponentialBound305 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches306 : (MergedCutGroups.Batch076.certificate920).AnchorMatches CountingCertificates.Batch030.certificate613 := by decide +kernel
theorem exponentialBound306 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch076.certificate920).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate613).dm (WitnessCertificates.Batch030.certificate613).beta (WitnessCertificates.Batch030.certificate613).L) ≤ (2*exp (-((CountingCertificates.Batch030.certificate613).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch076.certificate920).exponent:ℝ)*st.R))/((WitnessCertificates.Batch030.certificate613).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch076.certificate920 CountingCertificates.Batch030.certificate613 matches306 MergedCutGroups.Batch076.numericValid920 MergedCutGroups.Batch076.cellsSound920 MergedCutGroups.Batch076.cellsNumeric920 MergedCutGroups.Batch076.populationMatches920
    PopulationCertificates.Batch030.valid613 PopulationCertificates.Batch030.sound613 WitnessCertificates.Batch030.valid613 WitnessCertificates.Batch030.sound613 CountingCertificates.Batch030.valid613 CountingCertificates.Batch030.sound613 H st hI
theorem probabilityBound306 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch076.certificate920).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate613).dm (WitnessCertificates.Batch030.certificate613).beta (WitnessCertificates.Batch030.certificate613).L) ≤ ((CutFailureCertificates.Budget030.certificate613).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound613 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate613).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch076.certificate920).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch030.certificate613).omega:ℝ)) ≤ ((CutFailureCertificates.Budget030.certificate613).bound:ℝ) at hb
  exact (exponentialBound306 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches307 : (MergedCutGroups.Batch076.certificate923).AnchorMatches CountingCertificates.Batch030.certificate615 := by decide +kernel
theorem exponentialBound307 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch076.certificate923).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate615).dm (WitnessCertificates.Batch030.certificate615).beta (WitnessCertificates.Batch030.certificate615).L) ≤ (2*exp (-((CountingCertificates.Batch030.certificate615).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch076.certificate923).exponent:ℝ)*st.R))/((WitnessCertificates.Batch030.certificate615).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch076.certificate923 CountingCertificates.Batch030.certificate615 matches307 MergedCutGroups.Batch076.numericValid923 MergedCutGroups.Batch076.cellsSound923 MergedCutGroups.Batch076.cellsNumeric923 MergedCutGroups.Batch076.populationMatches923
    PopulationCertificates.Batch030.valid615 PopulationCertificates.Batch030.sound615 WitnessCertificates.Batch030.valid615 WitnessCertificates.Batch030.sound615 CountingCertificates.Batch030.valid615 CountingCertificates.Batch030.sound615 H st hI
theorem probabilityBound307 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch076.certificate923).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate615).dm (WitnessCertificates.Batch030.certificate615).beta (WitnessCertificates.Batch030.certificate615).L) ≤ ((CutFailureCertificates.Budget030.certificate615).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound615 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate615).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch076.certificate923).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch030.certificate615).omega:ℝ)) ≤ ((CutFailureCertificates.Budget030.certificate615).bound:ℝ) at hb
  exact (exponentialBound307 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches308 : (MergedCutGroups.Batch077.certificate926).AnchorMatches CountingCertificates.Batch030.certificate617 := by decide +kernel
theorem exponentialBound308 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch077.certificate926).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate617).dm (WitnessCertificates.Batch030.certificate617).beta (WitnessCertificates.Batch030.certificate617).L) ≤ (2*exp (-((CountingCertificates.Batch030.certificate617).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch077.certificate926).exponent:ℝ)*st.R))/((WitnessCertificates.Batch030.certificate617).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch077.certificate926 CountingCertificates.Batch030.certificate617 matches308 MergedCutGroups.Batch077.numericValid926 MergedCutGroups.Batch077.cellsSound926 MergedCutGroups.Batch077.cellsNumeric926 MergedCutGroups.Batch077.populationMatches926
    PopulationCertificates.Batch030.valid617 PopulationCertificates.Batch030.sound617 WitnessCertificates.Batch030.valid617 WitnessCertificates.Batch030.sound617 CountingCertificates.Batch030.valid617 CountingCertificates.Batch030.sound617 H st hI
theorem probabilityBound308 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch077.certificate926).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate617).dm (WitnessCertificates.Batch030.certificate617).beta (WitnessCertificates.Batch030.certificate617).L) ≤ ((CutFailureCertificates.Budget030.certificate617).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound617 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate617).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch077.certificate926).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch030.certificate617).omega:ℝ)) ≤ ((CutFailureCertificates.Budget030.certificate617).bound:ℝ) at hb
  exact (exponentialBound308 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches309 : (MergedCutGroups.Batch077.certificate929).AnchorMatches CountingCertificates.Batch030.certificate619 := by decide +kernel
theorem exponentialBound309 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch077.certificate929).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate619).dm (WitnessCertificates.Batch030.certificate619).beta (WitnessCertificates.Batch030.certificate619).L) ≤ (2*exp (-((CountingCertificates.Batch030.certificate619).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch077.certificate929).exponent:ℝ)*st.R))/((WitnessCertificates.Batch030.certificate619).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch077.certificate929 CountingCertificates.Batch030.certificate619 matches309 MergedCutGroups.Batch077.numericValid929 MergedCutGroups.Batch077.cellsSound929 MergedCutGroups.Batch077.cellsNumeric929 MergedCutGroups.Batch077.populationMatches929
    PopulationCertificates.Batch030.valid619 PopulationCertificates.Batch030.sound619 WitnessCertificates.Batch030.valid619 WitnessCertificates.Batch030.sound619 CountingCertificates.Batch030.valid619 CountingCertificates.Batch030.sound619 H st hI
theorem probabilityBound309 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch077.certificate929).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch030.certificate619).dm (WitnessCertificates.Batch030.certificate619).beta (WitnessCertificates.Batch030.certificate619).L) ≤ ((CutFailureCertificates.Budget030.certificate619).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget030.sound619 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch030.certificate619).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch077.certificate929).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch030.certificate619).omega:ℝ)) ≤ ((CutFailureCertificates.Budget030.certificate619).bound:ℝ) at hb
  exact (exponentialBound309 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches310 : (MergedCutGroups.Batch077.certificate932).AnchorMatches CountingCertificates.Batch031.certificate621 := by decide +kernel
theorem exponentialBound310 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch077.certificate932).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate621).dm (WitnessCertificates.Batch031.certificate621).beta (WitnessCertificates.Batch031.certificate621).L) ≤ (2*exp (-((CountingCertificates.Batch031.certificate621).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch077.certificate932).exponent:ℝ)*st.R))/((WitnessCertificates.Batch031.certificate621).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch077.certificate932 CountingCertificates.Batch031.certificate621 matches310 MergedCutGroups.Batch077.numericValid932 MergedCutGroups.Batch077.cellsSound932 MergedCutGroups.Batch077.cellsNumeric932 MergedCutGroups.Batch077.populationMatches932
    PopulationCertificates.Batch031.valid621 PopulationCertificates.Batch031.sound621 WitnessCertificates.Batch031.valid621 WitnessCertificates.Batch031.sound621 CountingCertificates.Batch031.valid621 CountingCertificates.Batch031.sound621 H st hI
theorem probabilityBound310 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch077.certificate932).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate621).dm (WitnessCertificates.Batch031.certificate621).beta (WitnessCertificates.Batch031.certificate621).L) ≤ ((CutFailureCertificates.Budget031.certificate621).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound621 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate621).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch077.certificate932).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch031.certificate621).omega:ℝ)) ≤ ((CutFailureCertificates.Budget031.certificate621).bound:ℝ) at hb
  exact (exponentialBound310 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches311 : (MergedCutGroups.Batch077.certificate935).AnchorMatches CountingCertificates.Batch031.certificate623 := by decide +kernel
theorem exponentialBound311 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch077.certificate935).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate623).dm (WitnessCertificates.Batch031.certificate623).beta (WitnessCertificates.Batch031.certificate623).L) ≤ (2*exp (-((CountingCertificates.Batch031.certificate623).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch077.certificate935).exponent:ℝ)*st.R))/((WitnessCertificates.Batch031.certificate623).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch077.certificate935 CountingCertificates.Batch031.certificate623 matches311 MergedCutGroups.Batch077.numericValid935 MergedCutGroups.Batch077.cellsSound935 MergedCutGroups.Batch077.cellsNumeric935 MergedCutGroups.Batch077.populationMatches935
    PopulationCertificates.Batch031.valid623 PopulationCertificates.Batch031.sound623 WitnessCertificates.Batch031.valid623 WitnessCertificates.Batch031.sound623 CountingCertificates.Batch031.valid623 CountingCertificates.Batch031.sound623 H st hI
theorem probabilityBound311 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch077.certificate935).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate623).dm (WitnessCertificates.Batch031.certificate623).beta (WitnessCertificates.Batch031.certificate623).L) ≤ ((CutFailureCertificates.Budget031.certificate623).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound623 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate623).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch077.certificate935).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch031.certificate623).omega:ℝ)) ≤ ((CutFailureCertificates.Budget031.certificate623).bound:ℝ) at hb
  exact (exponentialBound311 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches312 : (MergedCutGroups.Batch078.certificate938).AnchorMatches CountingCertificates.Batch031.certificate625 := by decide +kernel
theorem exponentialBound312 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch078.certificate938).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate625).dm (WitnessCertificates.Batch031.certificate625).beta (WitnessCertificates.Batch031.certificate625).L) ≤ (2*exp (-((CountingCertificates.Batch031.certificate625).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch078.certificate938).exponent:ℝ)*st.R))/((WitnessCertificates.Batch031.certificate625).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch078.certificate938 CountingCertificates.Batch031.certificate625 matches312 MergedCutGroups.Batch078.numericValid938 MergedCutGroups.Batch078.cellsSound938 MergedCutGroups.Batch078.cellsNumeric938 MergedCutGroups.Batch078.populationMatches938
    PopulationCertificates.Batch031.valid625 PopulationCertificates.Batch031.sound625 WitnessCertificates.Batch031.valid625 WitnessCertificates.Batch031.sound625 CountingCertificates.Batch031.valid625 CountingCertificates.Batch031.sound625 H st hI
theorem probabilityBound312 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch078.certificate938).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate625).dm (WitnessCertificates.Batch031.certificate625).beta (WitnessCertificates.Batch031.certificate625).L) ≤ ((CutFailureCertificates.Budget031.certificate625).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound625 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate625).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch078.certificate938).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch031.certificate625).omega:ℝ)) ≤ ((CutFailureCertificates.Budget031.certificate625).bound:ℝ) at hb
  exact (exponentialBound312 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches313 : (MergedCutGroups.Batch078.certificate941).AnchorMatches CountingCertificates.Batch031.certificate627 := by decide +kernel
theorem exponentialBound313 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch078.certificate941).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate627).dm (WitnessCertificates.Batch031.certificate627).beta (WitnessCertificates.Batch031.certificate627).L) ≤ (2*exp (-((CountingCertificates.Batch031.certificate627).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch078.certificate941).exponent:ℝ)*st.R))/((WitnessCertificates.Batch031.certificate627).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch078.certificate941 CountingCertificates.Batch031.certificate627 matches313 MergedCutGroups.Batch078.numericValid941 MergedCutGroups.Batch078.cellsSound941 MergedCutGroups.Batch078.cellsNumeric941 MergedCutGroups.Batch078.populationMatches941
    PopulationCertificates.Batch031.valid627 PopulationCertificates.Batch031.sound627 WitnessCertificates.Batch031.valid627 WitnessCertificates.Batch031.sound627 CountingCertificates.Batch031.valid627 CountingCertificates.Batch031.sound627 H st hI
theorem probabilityBound313 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch078.certificate941).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate627).dm (WitnessCertificates.Batch031.certificate627).beta (WitnessCertificates.Batch031.certificate627).L) ≤ ((CutFailureCertificates.Budget031.certificate627).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound627 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate627).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch078.certificate941).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch031.certificate627).omega:ℝ)) ≤ ((CutFailureCertificates.Budget031.certificate627).bound:ℝ) at hb
  exact (exponentialBound313 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches314 : (MergedCutGroups.Batch078.certificate944).AnchorMatches CountingCertificates.Batch031.certificate629 := by decide +kernel
theorem exponentialBound314 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch078.certificate944).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate629).dm (WitnessCertificates.Batch031.certificate629).beta (WitnessCertificates.Batch031.certificate629).L) ≤ (2*exp (-((CountingCertificates.Batch031.certificate629).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch078.certificate944).exponent:ℝ)*st.R))/((WitnessCertificates.Batch031.certificate629).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch078.certificate944 CountingCertificates.Batch031.certificate629 matches314 MergedCutGroups.Batch078.numericValid944 MergedCutGroups.Batch078.cellsSound944 MergedCutGroups.Batch078.cellsNumeric944 MergedCutGroups.Batch078.populationMatches944
    PopulationCertificates.Batch031.valid629 PopulationCertificates.Batch031.sound629 WitnessCertificates.Batch031.valid629 WitnessCertificates.Batch031.sound629 CountingCertificates.Batch031.valid629 CountingCertificates.Batch031.sound629 H st hI
theorem probabilityBound314 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch078.certificate944).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate629).dm (WitnessCertificates.Batch031.certificate629).beta (WitnessCertificates.Batch031.certificate629).L) ≤ ((CutFailureCertificates.Budget031.certificate629).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound629 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate629).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch078.certificate944).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch031.certificate629).omega:ℝ)) ≤ ((CutFailureCertificates.Budget031.certificate629).bound:ℝ) at hb
  exact (exponentialBound314 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches315 : (MergedCutGroups.Batch078.certificate947).AnchorMatches CountingCertificates.Batch031.certificate631 := by decide +kernel
theorem exponentialBound315 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch078.certificate947).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate631).dm (WitnessCertificates.Batch031.certificate631).beta (WitnessCertificates.Batch031.certificate631).L) ≤ (2*exp (-((CountingCertificates.Batch031.certificate631).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch078.certificate947).exponent:ℝ)*st.R))/((WitnessCertificates.Batch031.certificate631).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch078.certificate947 CountingCertificates.Batch031.certificate631 matches315 MergedCutGroups.Batch078.numericValid947 MergedCutGroups.Batch078.cellsSound947 MergedCutGroups.Batch078.cellsNumeric947 MergedCutGroups.Batch078.populationMatches947
    PopulationCertificates.Batch031.valid631 PopulationCertificates.Batch031.sound631 WitnessCertificates.Batch031.valid631 WitnessCertificates.Batch031.sound631 CountingCertificates.Batch031.valid631 CountingCertificates.Batch031.sound631 H st hI
theorem probabilityBound315 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch078.certificate947).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate631).dm (WitnessCertificates.Batch031.certificate631).beta (WitnessCertificates.Batch031.certificate631).L) ≤ ((CutFailureCertificates.Budget031.certificate631).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound631 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate631).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch078.certificate947).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch031.certificate631).omega:ℝ)) ≤ ((CutFailureCertificates.Budget031.certificate631).bound:ℝ) at hb
  exact (exponentialBound315 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches316 : (MergedCutGroups.Batch079.certificate950).AnchorMatches CountingCertificates.Batch031.certificate633 := by decide +kernel
theorem exponentialBound316 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch079.certificate950).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate633).dm (WitnessCertificates.Batch031.certificate633).beta (WitnessCertificates.Batch031.certificate633).L) ≤ (2*exp (-((CountingCertificates.Batch031.certificate633).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch079.certificate950).exponent:ℝ)*st.R))/((WitnessCertificates.Batch031.certificate633).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch079.certificate950 CountingCertificates.Batch031.certificate633 matches316 MergedCutGroups.Batch079.numericValid950 MergedCutGroups.Batch079.cellsSound950 MergedCutGroups.Batch079.cellsNumeric950 MergedCutGroups.Batch079.populationMatches950
    PopulationCertificates.Batch031.valid633 PopulationCertificates.Batch031.sound633 WitnessCertificates.Batch031.valid633 WitnessCertificates.Batch031.sound633 CountingCertificates.Batch031.valid633 CountingCertificates.Batch031.sound633 H st hI
theorem probabilityBound316 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch079.certificate950).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate633).dm (WitnessCertificates.Batch031.certificate633).beta (WitnessCertificates.Batch031.certificate633).L) ≤ ((CutFailureCertificates.Budget031.certificate633).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound633 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate633).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch079.certificate950).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch031.certificate633).omega:ℝ)) ≤ ((CutFailureCertificates.Budget031.certificate633).bound:ℝ) at hb
  exact (exponentialBound316 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches317 : (MergedCutGroups.Batch079.certificate953).AnchorMatches CountingCertificates.Batch031.certificate635 := by decide +kernel
theorem exponentialBound317 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch079.certificate953).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate635).dm (WitnessCertificates.Batch031.certificate635).beta (WitnessCertificates.Batch031.certificate635).L) ≤ (2*exp (-((CountingCertificates.Batch031.certificate635).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch079.certificate953).exponent:ℝ)*st.R))/((WitnessCertificates.Batch031.certificate635).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch079.certificate953 CountingCertificates.Batch031.certificate635 matches317 MergedCutGroups.Batch079.numericValid953 MergedCutGroups.Batch079.cellsSound953 MergedCutGroups.Batch079.cellsNumeric953 MergedCutGroups.Batch079.populationMatches953
    PopulationCertificates.Batch031.valid635 PopulationCertificates.Batch031.sound635 WitnessCertificates.Batch031.valid635 WitnessCertificates.Batch031.sound635 CountingCertificates.Batch031.valid635 CountingCertificates.Batch031.sound635 H st hI
theorem probabilityBound317 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch079.certificate953).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate635).dm (WitnessCertificates.Batch031.certificate635).beta (WitnessCertificates.Batch031.certificate635).L) ≤ ((CutFailureCertificates.Budget031.certificate635).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound635 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate635).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch079.certificate953).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch031.certificate635).omega:ℝ)) ≤ ((CutFailureCertificates.Budget031.certificate635).bound:ℝ) at hb
  exact (exponentialBound317 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches318 : (MergedCutGroups.Batch079.certificate956).AnchorMatches CountingCertificates.Batch031.certificate637 := by decide +kernel
theorem exponentialBound318 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch079.certificate956).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate637).dm (WitnessCertificates.Batch031.certificate637).beta (WitnessCertificates.Batch031.certificate637).L) ≤ (2*exp (-((CountingCertificates.Batch031.certificate637).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch079.certificate956).exponent:ℝ)*st.R))/((WitnessCertificates.Batch031.certificate637).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch079.certificate956 CountingCertificates.Batch031.certificate637 matches318 MergedCutGroups.Batch079.numericValid956 MergedCutGroups.Batch079.cellsSound956 MergedCutGroups.Batch079.cellsNumeric956 MergedCutGroups.Batch079.populationMatches956
    PopulationCertificates.Batch031.valid637 PopulationCertificates.Batch031.sound637 WitnessCertificates.Batch031.valid637 WitnessCertificates.Batch031.sound637 CountingCertificates.Batch031.valid637 CountingCertificates.Batch031.sound637 H st hI
theorem probabilityBound318 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch079.certificate956).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate637).dm (WitnessCertificates.Batch031.certificate637).beta (WitnessCertificates.Batch031.certificate637).L) ≤ ((CutFailureCertificates.Budget031.certificate637).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound637 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate637).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch079.certificate956).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch031.certificate637).omega:ℝ)) ≤ ((CutFailureCertificates.Budget031.certificate637).bound:ℝ) at hb
  exact (exponentialBound318 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches319 : (MergedCutGroups.Batch079.certificate959).AnchorMatches CountingCertificates.Batch031.certificate639 := by decide +kernel
theorem exponentialBound319 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch079.certificate959).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate639).dm (WitnessCertificates.Batch031.certificate639).beta (WitnessCertificates.Batch031.certificate639).L) ≤ (2*exp (-((CountingCertificates.Batch031.certificate639).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch079.certificate959).exponent:ℝ)*st.R))/((WitnessCertificates.Batch031.certificate639).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch079.certificate959 CountingCertificates.Batch031.certificate639 matches319 MergedCutGroups.Batch079.numericValid959 MergedCutGroups.Batch079.cellsSound959 MergedCutGroups.Batch079.cellsNumeric959 MergedCutGroups.Batch079.populationMatches959
    PopulationCertificates.Batch031.valid639 PopulationCertificates.Batch031.sound639 WitnessCertificates.Batch031.valid639 WitnessCertificates.Batch031.sound639 CountingCertificates.Batch031.valid639 CountingCertificates.Batch031.sound639 H st hI
theorem probabilityBound319 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch079.certificate959).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch031.certificate639).dm (WitnessCertificates.Batch031.certificate639).beta (WitnessCertificates.Batch031.certificate639).L) ≤ ((CutFailureCertificates.Budget031.certificate639).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget031.sound639 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch031.certificate639).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch079.certificate959).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch031.certificate639).omega:ℝ)) ≤ ((CutFailureCertificates.Budget031.certificate639).bound:ℝ) at hb
  exact (exponentialBound319 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch015
