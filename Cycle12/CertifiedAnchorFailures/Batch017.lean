import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch034
import Cycle12.CountingCertificates.Batch035
import Cycle12.CutFailureCertificates.Budget034
import Cycle12.CutFailureCertificates.Budget035
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

namespace Cycle12.CertifiedAnchorFailures.Batch017
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches340 : (MergedCutGroups.Batch085.certificate1022).AnchorMatches CountingCertificates.Batch034.certificate681 := by decide +kernel
theorem exponentialBound340 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch085.certificate1022).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate681).dm (WitnessCertificates.Batch034.certificate681).beta (WitnessCertificates.Batch034.certificate681).L) ≤ (2*exp (-((CountingCertificates.Batch034.certificate681).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch085.certificate1022).exponent:ℝ)*st.R))/((WitnessCertificates.Batch034.certificate681).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch085.certificate1022 CountingCertificates.Batch034.certificate681 matches340 MergedCutGroups.Batch085.numericValid1022 MergedCutGroups.Batch085.cellsSound1022 MergedCutGroups.Batch085.cellsNumeric1022 MergedCutGroups.Batch085.populationMatches1022
    PopulationCertificates.Batch034.valid681 PopulationCertificates.Batch034.sound681 WitnessCertificates.Batch034.valid681 WitnessCertificates.Batch034.sound681 CountingCertificates.Batch034.valid681 CountingCertificates.Batch034.sound681 H st hI
theorem probabilityBound340 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch085.certificate1022).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate681).dm (WitnessCertificates.Batch034.certificate681).beta (WitnessCertificates.Batch034.certificate681).L) ≤ ((CutFailureCertificates.Budget034.certificate681).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound681 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate681).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch085.certificate1022).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch034.certificate681).omega:ℝ)) ≤ ((CutFailureCertificates.Budget034.certificate681).bound:ℝ) at hb
  exact (exponentialBound340 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches341 : (MergedCutGroups.Batch085.certificate1025).AnchorMatches CountingCertificates.Batch034.certificate683 := by decide +kernel
theorem exponentialBound341 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch085.certificate1025).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate683).dm (WitnessCertificates.Batch034.certificate683).beta (WitnessCertificates.Batch034.certificate683).L) ≤ (2*exp (-((CountingCertificates.Batch034.certificate683).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch085.certificate1025).exponent:ℝ)*st.R))/((WitnessCertificates.Batch034.certificate683).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch085.certificate1025 CountingCertificates.Batch034.certificate683 matches341 MergedCutGroups.Batch085.numericValid1025 MergedCutGroups.Batch085.cellsSound1025 MergedCutGroups.Batch085.cellsNumeric1025 MergedCutGroups.Batch085.populationMatches1025
    PopulationCertificates.Batch034.valid683 PopulationCertificates.Batch034.sound683 WitnessCertificates.Batch034.valid683 WitnessCertificates.Batch034.sound683 CountingCertificates.Batch034.valid683 CountingCertificates.Batch034.sound683 H st hI
theorem probabilityBound341 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch085.certificate1025).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate683).dm (WitnessCertificates.Batch034.certificate683).beta (WitnessCertificates.Batch034.certificate683).L) ≤ ((CutFailureCertificates.Budget034.certificate683).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound683 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate683).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch085.certificate1025).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch034.certificate683).omega:ℝ)) ≤ ((CutFailureCertificates.Budget034.certificate683).bound:ℝ) at hb
  exact (exponentialBound341 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches342 : (MergedCutGroups.Batch085.certificate1028).AnchorMatches CountingCertificates.Batch034.certificate685 := by decide +kernel
theorem exponentialBound342 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch085.certificate1028).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate685).dm (WitnessCertificates.Batch034.certificate685).beta (WitnessCertificates.Batch034.certificate685).L) ≤ (2*exp (-((CountingCertificates.Batch034.certificate685).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch085.certificate1028).exponent:ℝ)*st.R))/((WitnessCertificates.Batch034.certificate685).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch085.certificate1028 CountingCertificates.Batch034.certificate685 matches342 MergedCutGroups.Batch085.numericValid1028 MergedCutGroups.Batch085.cellsSound1028 MergedCutGroups.Batch085.cellsNumeric1028 MergedCutGroups.Batch085.populationMatches1028
    PopulationCertificates.Batch034.valid685 PopulationCertificates.Batch034.sound685 WitnessCertificates.Batch034.valid685 WitnessCertificates.Batch034.sound685 CountingCertificates.Batch034.valid685 CountingCertificates.Batch034.sound685 H st hI
theorem probabilityBound342 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch085.certificate1028).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate685).dm (WitnessCertificates.Batch034.certificate685).beta (WitnessCertificates.Batch034.certificate685).L) ≤ ((CutFailureCertificates.Budget034.certificate685).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound685 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate685).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch085.certificate1028).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch034.certificate685).omega:ℝ)) ≤ ((CutFailureCertificates.Budget034.certificate685).bound:ℝ) at hb
  exact (exponentialBound342 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches343 : (MergedCutGroups.Batch085.certificate1031).AnchorMatches CountingCertificates.Batch034.certificate687 := by decide +kernel
theorem exponentialBound343 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch085.certificate1031).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate687).dm (WitnessCertificates.Batch034.certificate687).beta (WitnessCertificates.Batch034.certificate687).L) ≤ (2*exp (-((CountingCertificates.Batch034.certificate687).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch085.certificate1031).exponent:ℝ)*st.R))/((WitnessCertificates.Batch034.certificate687).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch085.certificate1031 CountingCertificates.Batch034.certificate687 matches343 MergedCutGroups.Batch085.numericValid1031 MergedCutGroups.Batch085.cellsSound1031 MergedCutGroups.Batch085.cellsNumeric1031 MergedCutGroups.Batch085.populationMatches1031
    PopulationCertificates.Batch034.valid687 PopulationCertificates.Batch034.sound687 WitnessCertificates.Batch034.valid687 WitnessCertificates.Batch034.sound687 CountingCertificates.Batch034.valid687 CountingCertificates.Batch034.sound687 H st hI
theorem probabilityBound343 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch085.certificate1031).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate687).dm (WitnessCertificates.Batch034.certificate687).beta (WitnessCertificates.Batch034.certificate687).L) ≤ ((CutFailureCertificates.Budget034.certificate687).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound687 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate687).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch085.certificate1031).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch034.certificate687).omega:ℝ)) ≤ ((CutFailureCertificates.Budget034.certificate687).bound:ℝ) at hb
  exact (exponentialBound343 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches344 : (MergedCutGroups.Batch086.certificate1034).AnchorMatches CountingCertificates.Batch034.certificate689 := by decide +kernel
theorem exponentialBound344 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch086.certificate1034).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate689).dm (WitnessCertificates.Batch034.certificate689).beta (WitnessCertificates.Batch034.certificate689).L) ≤ (2*exp (-((CountingCertificates.Batch034.certificate689).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch086.certificate1034).exponent:ℝ)*st.R))/((WitnessCertificates.Batch034.certificate689).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch086.certificate1034 CountingCertificates.Batch034.certificate689 matches344 MergedCutGroups.Batch086.numericValid1034 MergedCutGroups.Batch086.cellsSound1034 MergedCutGroups.Batch086.cellsNumeric1034 MergedCutGroups.Batch086.populationMatches1034
    PopulationCertificates.Batch034.valid689 PopulationCertificates.Batch034.sound689 WitnessCertificates.Batch034.valid689 WitnessCertificates.Batch034.sound689 CountingCertificates.Batch034.valid689 CountingCertificates.Batch034.sound689 H st hI
theorem probabilityBound344 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch086.certificate1034).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate689).dm (WitnessCertificates.Batch034.certificate689).beta (WitnessCertificates.Batch034.certificate689).L) ≤ ((CutFailureCertificates.Budget034.certificate689).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound689 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate689).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch086.certificate1034).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch034.certificate689).omega:ℝ)) ≤ ((CutFailureCertificates.Budget034.certificate689).bound:ℝ) at hb
  exact (exponentialBound344 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches345 : (MergedCutGroups.Batch086.certificate1037).AnchorMatches CountingCertificates.Batch034.certificate691 := by decide +kernel
theorem exponentialBound345 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch086.certificate1037).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate691).dm (WitnessCertificates.Batch034.certificate691).beta (WitnessCertificates.Batch034.certificate691).L) ≤ (2*exp (-((CountingCertificates.Batch034.certificate691).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch086.certificate1037).exponent:ℝ)*st.R))/((WitnessCertificates.Batch034.certificate691).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch086.certificate1037 CountingCertificates.Batch034.certificate691 matches345 MergedCutGroups.Batch086.numericValid1037 MergedCutGroups.Batch086.cellsSound1037 MergedCutGroups.Batch086.cellsNumeric1037 MergedCutGroups.Batch086.populationMatches1037
    PopulationCertificates.Batch034.valid691 PopulationCertificates.Batch034.sound691 WitnessCertificates.Batch034.valid691 WitnessCertificates.Batch034.sound691 CountingCertificates.Batch034.valid691 CountingCertificates.Batch034.sound691 H st hI
theorem probabilityBound345 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch086.certificate1037).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate691).dm (WitnessCertificates.Batch034.certificate691).beta (WitnessCertificates.Batch034.certificate691).L) ≤ ((CutFailureCertificates.Budget034.certificate691).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound691 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate691).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch086.certificate1037).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch034.certificate691).omega:ℝ)) ≤ ((CutFailureCertificates.Budget034.certificate691).bound:ℝ) at hb
  exact (exponentialBound345 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches346 : (MergedCutGroups.Batch086.certificate1040).AnchorMatches CountingCertificates.Batch034.certificate693 := by decide +kernel
theorem exponentialBound346 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch086.certificate1040).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate693).dm (WitnessCertificates.Batch034.certificate693).beta (WitnessCertificates.Batch034.certificate693).L) ≤ (2*exp (-((CountingCertificates.Batch034.certificate693).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch086.certificate1040).exponent:ℝ)*st.R))/((WitnessCertificates.Batch034.certificate693).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch086.certificate1040 CountingCertificates.Batch034.certificate693 matches346 MergedCutGroups.Batch086.numericValid1040 MergedCutGroups.Batch086.cellsSound1040 MergedCutGroups.Batch086.cellsNumeric1040 MergedCutGroups.Batch086.populationMatches1040
    PopulationCertificates.Batch034.valid693 PopulationCertificates.Batch034.sound693 WitnessCertificates.Batch034.valid693 WitnessCertificates.Batch034.sound693 CountingCertificates.Batch034.valid693 CountingCertificates.Batch034.sound693 H st hI
theorem probabilityBound346 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch086.certificate1040).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate693).dm (WitnessCertificates.Batch034.certificate693).beta (WitnessCertificates.Batch034.certificate693).L) ≤ ((CutFailureCertificates.Budget034.certificate693).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound693 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate693).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch086.certificate1040).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch034.certificate693).omega:ℝ)) ≤ ((CutFailureCertificates.Budget034.certificate693).bound:ℝ) at hb
  exact (exponentialBound346 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches347 : (MergedCutGroups.Batch086.certificate1043).AnchorMatches CountingCertificates.Batch034.certificate695 := by decide +kernel
theorem exponentialBound347 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch086.certificate1043).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate695).dm (WitnessCertificates.Batch034.certificate695).beta (WitnessCertificates.Batch034.certificate695).L) ≤ (2*exp (-((CountingCertificates.Batch034.certificate695).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch086.certificate1043).exponent:ℝ)*st.R))/((WitnessCertificates.Batch034.certificate695).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch086.certificate1043 CountingCertificates.Batch034.certificate695 matches347 MergedCutGroups.Batch086.numericValid1043 MergedCutGroups.Batch086.cellsSound1043 MergedCutGroups.Batch086.cellsNumeric1043 MergedCutGroups.Batch086.populationMatches1043
    PopulationCertificates.Batch034.valid695 PopulationCertificates.Batch034.sound695 WitnessCertificates.Batch034.valid695 WitnessCertificates.Batch034.sound695 CountingCertificates.Batch034.valid695 CountingCertificates.Batch034.sound695 H st hI
theorem probabilityBound347 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch086.certificate1043).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate695).dm (WitnessCertificates.Batch034.certificate695).beta (WitnessCertificates.Batch034.certificate695).L) ≤ ((CutFailureCertificates.Budget034.certificate695).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound695 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate695).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch086.certificate1043).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch034.certificate695).omega:ℝ)) ≤ ((CutFailureCertificates.Budget034.certificate695).bound:ℝ) at hb
  exact (exponentialBound347 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches348 : (MergedCutGroups.Batch087.certificate1046).AnchorMatches CountingCertificates.Batch034.certificate697 := by decide +kernel
theorem exponentialBound348 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch087.certificate1046).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate697).dm (WitnessCertificates.Batch034.certificate697).beta (WitnessCertificates.Batch034.certificate697).L) ≤ (2*exp (-((CountingCertificates.Batch034.certificate697).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch087.certificate1046).exponent:ℝ)*st.R))/((WitnessCertificates.Batch034.certificate697).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch087.certificate1046 CountingCertificates.Batch034.certificate697 matches348 MergedCutGroups.Batch087.numericValid1046 MergedCutGroups.Batch087.cellsSound1046 MergedCutGroups.Batch087.cellsNumeric1046 MergedCutGroups.Batch087.populationMatches1046
    PopulationCertificates.Batch034.valid697 PopulationCertificates.Batch034.sound697 WitnessCertificates.Batch034.valid697 WitnessCertificates.Batch034.sound697 CountingCertificates.Batch034.valid697 CountingCertificates.Batch034.sound697 H st hI
theorem probabilityBound348 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch087.certificate1046).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate697).dm (WitnessCertificates.Batch034.certificate697).beta (WitnessCertificates.Batch034.certificate697).L) ≤ ((CutFailureCertificates.Budget034.certificate697).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound697 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate697).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch087.certificate1046).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch034.certificate697).omega:ℝ)) ≤ ((CutFailureCertificates.Budget034.certificate697).bound:ℝ) at hb
  exact (exponentialBound348 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches349 : (MergedCutGroups.Batch087.certificate1049).AnchorMatches CountingCertificates.Batch034.certificate699 := by decide +kernel
theorem exponentialBound349 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch087.certificate1049).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate699).dm (WitnessCertificates.Batch034.certificate699).beta (WitnessCertificates.Batch034.certificate699).L) ≤ (2*exp (-((CountingCertificates.Batch034.certificate699).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch087.certificate1049).exponent:ℝ)*st.R))/((WitnessCertificates.Batch034.certificate699).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch087.certificate1049 CountingCertificates.Batch034.certificate699 matches349 MergedCutGroups.Batch087.numericValid1049 MergedCutGroups.Batch087.cellsSound1049 MergedCutGroups.Batch087.cellsNumeric1049 MergedCutGroups.Batch087.populationMatches1049
    PopulationCertificates.Batch034.valid699 PopulationCertificates.Batch034.sound699 WitnessCertificates.Batch034.valid699 WitnessCertificates.Batch034.sound699 CountingCertificates.Batch034.valid699 CountingCertificates.Batch034.sound699 H st hI
theorem probabilityBound349 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch087.certificate1049).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch034.certificate699).dm (WitnessCertificates.Batch034.certificate699).beta (WitnessCertificates.Batch034.certificate699).L) ≤ ((CutFailureCertificates.Budget034.certificate699).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget034.sound699 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch034.certificate699).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch087.certificate1049).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch034.certificate699).omega:ℝ)) ≤ ((CutFailureCertificates.Budget034.certificate699).bound:ℝ) at hb
  exact (exponentialBound349 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches350 : (MergedCutGroups.Batch087.certificate1052).AnchorMatches CountingCertificates.Batch035.certificate701 := by decide +kernel
theorem exponentialBound350 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch087.certificate1052).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate701).dm (WitnessCertificates.Batch035.certificate701).beta (WitnessCertificates.Batch035.certificate701).L) ≤ (2*exp (-((CountingCertificates.Batch035.certificate701).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch087.certificate1052).exponent:ℝ)*st.R))/((WitnessCertificates.Batch035.certificate701).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch087.certificate1052 CountingCertificates.Batch035.certificate701 matches350 MergedCutGroups.Batch087.numericValid1052 MergedCutGroups.Batch087.cellsSound1052 MergedCutGroups.Batch087.cellsNumeric1052 MergedCutGroups.Batch087.populationMatches1052
    PopulationCertificates.Batch035.valid701 PopulationCertificates.Batch035.sound701 WitnessCertificates.Batch035.valid701 WitnessCertificates.Batch035.sound701 CountingCertificates.Batch035.valid701 CountingCertificates.Batch035.sound701 H st hI
theorem probabilityBound350 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch087.certificate1052).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate701).dm (WitnessCertificates.Batch035.certificate701).beta (WitnessCertificates.Batch035.certificate701).L) ≤ ((CutFailureCertificates.Budget035.certificate701).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound701 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate701).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch087.certificate1052).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch035.certificate701).omega:ℝ)) ≤ ((CutFailureCertificates.Budget035.certificate701).bound:ℝ) at hb
  exact (exponentialBound350 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches351 : (MergedCutGroups.Batch087.certificate1055).AnchorMatches CountingCertificates.Batch035.certificate703 := by decide +kernel
theorem exponentialBound351 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch087.certificate1055).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate703).dm (WitnessCertificates.Batch035.certificate703).beta (WitnessCertificates.Batch035.certificate703).L) ≤ (2*exp (-((CountingCertificates.Batch035.certificate703).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch087.certificate1055).exponent:ℝ)*st.R))/((WitnessCertificates.Batch035.certificate703).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch087.certificate1055 CountingCertificates.Batch035.certificate703 matches351 MergedCutGroups.Batch087.numericValid1055 MergedCutGroups.Batch087.cellsSound1055 MergedCutGroups.Batch087.cellsNumeric1055 MergedCutGroups.Batch087.populationMatches1055
    PopulationCertificates.Batch035.valid703 PopulationCertificates.Batch035.sound703 WitnessCertificates.Batch035.valid703 WitnessCertificates.Batch035.sound703 CountingCertificates.Batch035.valid703 CountingCertificates.Batch035.sound703 H st hI
theorem probabilityBound351 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch087.certificate1055).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate703).dm (WitnessCertificates.Batch035.certificate703).beta (WitnessCertificates.Batch035.certificate703).L) ≤ ((CutFailureCertificates.Budget035.certificate703).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound703 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate703).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch087.certificate1055).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch035.certificate703).omega:ℝ)) ≤ ((CutFailureCertificates.Budget035.certificate703).bound:ℝ) at hb
  exact (exponentialBound351 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches352 : (MergedCutGroups.Batch088.certificate1058).AnchorMatches CountingCertificates.Batch035.certificate705 := by decide +kernel
theorem exponentialBound352 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch088.certificate1058).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate705).dm (WitnessCertificates.Batch035.certificate705).beta (WitnessCertificates.Batch035.certificate705).L) ≤ (2*exp (-((CountingCertificates.Batch035.certificate705).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch088.certificate1058).exponent:ℝ)*st.R))/((WitnessCertificates.Batch035.certificate705).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch088.certificate1058 CountingCertificates.Batch035.certificate705 matches352 MergedCutGroups.Batch088.numericValid1058 MergedCutGroups.Batch088.cellsSound1058 MergedCutGroups.Batch088.cellsNumeric1058 MergedCutGroups.Batch088.populationMatches1058
    PopulationCertificates.Batch035.valid705 PopulationCertificates.Batch035.sound705 WitnessCertificates.Batch035.valid705 WitnessCertificates.Batch035.sound705 CountingCertificates.Batch035.valid705 CountingCertificates.Batch035.sound705 H st hI
theorem probabilityBound352 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch088.certificate1058).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate705).dm (WitnessCertificates.Batch035.certificate705).beta (WitnessCertificates.Batch035.certificate705).L) ≤ ((CutFailureCertificates.Budget035.certificate705).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound705 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate705).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch088.certificate1058).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch035.certificate705).omega:ℝ)) ≤ ((CutFailureCertificates.Budget035.certificate705).bound:ℝ) at hb
  exact (exponentialBound352 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches353 : (MergedCutGroups.Batch088.certificate1061).AnchorMatches CountingCertificates.Batch035.certificate707 := by decide +kernel
theorem exponentialBound353 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch088.certificate1061).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate707).dm (WitnessCertificates.Batch035.certificate707).beta (WitnessCertificates.Batch035.certificate707).L) ≤ (2*exp (-((CountingCertificates.Batch035.certificate707).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch088.certificate1061).exponent:ℝ)*st.R))/((WitnessCertificates.Batch035.certificate707).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch088.certificate1061 CountingCertificates.Batch035.certificate707 matches353 MergedCutGroups.Batch088.numericValid1061 MergedCutGroups.Batch088.cellsSound1061 MergedCutGroups.Batch088.cellsNumeric1061 MergedCutGroups.Batch088.populationMatches1061
    PopulationCertificates.Batch035.valid707 PopulationCertificates.Batch035.sound707 WitnessCertificates.Batch035.valid707 WitnessCertificates.Batch035.sound707 CountingCertificates.Batch035.valid707 CountingCertificates.Batch035.sound707 H st hI
theorem probabilityBound353 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch088.certificate1061).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate707).dm (WitnessCertificates.Batch035.certificate707).beta (WitnessCertificates.Batch035.certificate707).L) ≤ ((CutFailureCertificates.Budget035.certificate707).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound707 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate707).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch088.certificate1061).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch035.certificate707).omega:ℝ)) ≤ ((CutFailureCertificates.Budget035.certificate707).bound:ℝ) at hb
  exact (exponentialBound353 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches354 : (MergedCutGroups.Batch088.certificate1064).AnchorMatches CountingCertificates.Batch035.certificate709 := by decide +kernel
theorem exponentialBound354 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch088.certificate1064).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate709).dm (WitnessCertificates.Batch035.certificate709).beta (WitnessCertificates.Batch035.certificate709).L) ≤ (2*exp (-((CountingCertificates.Batch035.certificate709).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch088.certificate1064).exponent:ℝ)*st.R))/((WitnessCertificates.Batch035.certificate709).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch088.certificate1064 CountingCertificates.Batch035.certificate709 matches354 MergedCutGroups.Batch088.numericValid1064 MergedCutGroups.Batch088.cellsSound1064 MergedCutGroups.Batch088.cellsNumeric1064 MergedCutGroups.Batch088.populationMatches1064
    PopulationCertificates.Batch035.valid709 PopulationCertificates.Batch035.sound709 WitnessCertificates.Batch035.valid709 WitnessCertificates.Batch035.sound709 CountingCertificates.Batch035.valid709 CountingCertificates.Batch035.sound709 H st hI
theorem probabilityBound354 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch088.certificate1064).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate709).dm (WitnessCertificates.Batch035.certificate709).beta (WitnessCertificates.Batch035.certificate709).L) ≤ ((CutFailureCertificates.Budget035.certificate709).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound709 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate709).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch088.certificate1064).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch035.certificate709).omega:ℝ)) ≤ ((CutFailureCertificates.Budget035.certificate709).bound:ℝ) at hb
  exact (exponentialBound354 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches355 : (MergedCutGroups.Batch088.certificate1067).AnchorMatches CountingCertificates.Batch035.certificate711 := by decide +kernel
theorem exponentialBound355 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch088.certificate1067).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate711).dm (WitnessCertificates.Batch035.certificate711).beta (WitnessCertificates.Batch035.certificate711).L) ≤ (2*exp (-((CountingCertificates.Batch035.certificate711).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch088.certificate1067).exponent:ℝ)*st.R))/((WitnessCertificates.Batch035.certificate711).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch088.certificate1067 CountingCertificates.Batch035.certificate711 matches355 MergedCutGroups.Batch088.numericValid1067 MergedCutGroups.Batch088.cellsSound1067 MergedCutGroups.Batch088.cellsNumeric1067 MergedCutGroups.Batch088.populationMatches1067
    PopulationCertificates.Batch035.valid711 PopulationCertificates.Batch035.sound711 WitnessCertificates.Batch035.valid711 WitnessCertificates.Batch035.sound711 CountingCertificates.Batch035.valid711 CountingCertificates.Batch035.sound711 H st hI
theorem probabilityBound355 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch088.certificate1067).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate711).dm (WitnessCertificates.Batch035.certificate711).beta (WitnessCertificates.Batch035.certificate711).L) ≤ ((CutFailureCertificates.Budget035.certificate711).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound711 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate711).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch088.certificate1067).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch035.certificate711).omega:ℝ)) ≤ ((CutFailureCertificates.Budget035.certificate711).bound:ℝ) at hb
  exact (exponentialBound355 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches356 : (MergedCutGroups.Batch089.certificate1070).AnchorMatches CountingCertificates.Batch035.certificate713 := by decide +kernel
theorem exponentialBound356 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch089.certificate1070).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate713).dm (WitnessCertificates.Batch035.certificate713).beta (WitnessCertificates.Batch035.certificate713).L) ≤ (2*exp (-((CountingCertificates.Batch035.certificate713).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch089.certificate1070).exponent:ℝ)*st.R))/((WitnessCertificates.Batch035.certificate713).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch089.certificate1070 CountingCertificates.Batch035.certificate713 matches356 MergedCutGroups.Batch089.numericValid1070 MergedCutGroups.Batch089.cellsSound1070 MergedCutGroups.Batch089.cellsNumeric1070 MergedCutGroups.Batch089.populationMatches1070
    PopulationCertificates.Batch035.valid713 PopulationCertificates.Batch035.sound713 WitnessCertificates.Batch035.valid713 WitnessCertificates.Batch035.sound713 CountingCertificates.Batch035.valid713 CountingCertificates.Batch035.sound713 H st hI
theorem probabilityBound356 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch089.certificate1070).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate713).dm (WitnessCertificates.Batch035.certificate713).beta (WitnessCertificates.Batch035.certificate713).L) ≤ ((CutFailureCertificates.Budget035.certificate713).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound713 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate713).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch089.certificate1070).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch035.certificate713).omega:ℝ)) ≤ ((CutFailureCertificates.Budget035.certificate713).bound:ℝ) at hb
  exact (exponentialBound356 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches357 : (MergedCutGroups.Batch089.certificate1073).AnchorMatches CountingCertificates.Batch035.certificate715 := by decide +kernel
theorem exponentialBound357 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch089.certificate1073).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate715).dm (WitnessCertificates.Batch035.certificate715).beta (WitnessCertificates.Batch035.certificate715).L) ≤ (2*exp (-((CountingCertificates.Batch035.certificate715).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch089.certificate1073).exponent:ℝ)*st.R))/((WitnessCertificates.Batch035.certificate715).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch089.certificate1073 CountingCertificates.Batch035.certificate715 matches357 MergedCutGroups.Batch089.numericValid1073 MergedCutGroups.Batch089.cellsSound1073 MergedCutGroups.Batch089.cellsNumeric1073 MergedCutGroups.Batch089.populationMatches1073
    PopulationCertificates.Batch035.valid715 PopulationCertificates.Batch035.sound715 WitnessCertificates.Batch035.valid715 WitnessCertificates.Batch035.sound715 CountingCertificates.Batch035.valid715 CountingCertificates.Batch035.sound715 H st hI
theorem probabilityBound357 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch089.certificate1073).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate715).dm (WitnessCertificates.Batch035.certificate715).beta (WitnessCertificates.Batch035.certificate715).L) ≤ ((CutFailureCertificates.Budget035.certificate715).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound715 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate715).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch089.certificate1073).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch035.certificate715).omega:ℝ)) ≤ ((CutFailureCertificates.Budget035.certificate715).bound:ℝ) at hb
  exact (exponentialBound357 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches358 : (MergedCutGroups.Batch089.certificate1076).AnchorMatches CountingCertificates.Batch035.certificate717 := by decide +kernel
theorem exponentialBound358 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch089.certificate1076).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate717).dm (WitnessCertificates.Batch035.certificate717).beta (WitnessCertificates.Batch035.certificate717).L) ≤ (2*exp (-((CountingCertificates.Batch035.certificate717).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch089.certificate1076).exponent:ℝ)*st.R))/((WitnessCertificates.Batch035.certificate717).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch089.certificate1076 CountingCertificates.Batch035.certificate717 matches358 MergedCutGroups.Batch089.numericValid1076 MergedCutGroups.Batch089.cellsSound1076 MergedCutGroups.Batch089.cellsNumeric1076 MergedCutGroups.Batch089.populationMatches1076
    PopulationCertificates.Batch035.valid717 PopulationCertificates.Batch035.sound717 WitnessCertificates.Batch035.valid717 WitnessCertificates.Batch035.sound717 CountingCertificates.Batch035.valid717 CountingCertificates.Batch035.sound717 H st hI
theorem probabilityBound358 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch089.certificate1076).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate717).dm (WitnessCertificates.Batch035.certificate717).beta (WitnessCertificates.Batch035.certificate717).L) ≤ ((CutFailureCertificates.Budget035.certificate717).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound717 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate717).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch089.certificate1076).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch035.certificate717).omega:ℝ)) ≤ ((CutFailureCertificates.Budget035.certificate717).bound:ℝ) at hb
  exact (exponentialBound358 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches359 : (MergedCutGroups.Batch089.certificate1079).AnchorMatches CountingCertificates.Batch035.certificate719 := by decide +kernel
theorem exponentialBound359 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch089.certificate1079).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate719).dm (WitnessCertificates.Batch035.certificate719).beta (WitnessCertificates.Batch035.certificate719).L) ≤ (2*exp (-((CountingCertificates.Batch035.certificate719).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch089.certificate1079).exponent:ℝ)*st.R))/((WitnessCertificates.Batch035.certificate719).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch089.certificate1079 CountingCertificates.Batch035.certificate719 matches359 MergedCutGroups.Batch089.numericValid1079 MergedCutGroups.Batch089.cellsSound1079 MergedCutGroups.Batch089.cellsNumeric1079 MergedCutGroups.Batch089.populationMatches1079
    PopulationCertificates.Batch035.valid719 PopulationCertificates.Batch035.sound719 WitnessCertificates.Batch035.valid719 WitnessCertificates.Batch035.sound719 CountingCertificates.Batch035.valid719 CountingCertificates.Batch035.sound719 H st hI
theorem probabilityBound359 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch089.certificate1079).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch035.certificate719).dm (WitnessCertificates.Batch035.certificate719).beta (WitnessCertificates.Batch035.certificate719).L) ≤ ((CutFailureCertificates.Budget035.certificate719).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget035.sound719 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch035.certificate719).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch089.certificate1079).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch035.certificate719).omega:ℝ)) ≤ ((CutFailureCertificates.Budget035.certificate719).bound:ℝ) at hb
  exact (exponentialBound359 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch017
