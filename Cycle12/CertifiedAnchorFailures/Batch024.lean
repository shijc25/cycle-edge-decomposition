import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch051
import Cycle12.CountingCertificates.Batch052
import Cycle12.CountingCertificates.Batch053
import Cycle12.CutFailureCertificates.Budget051
import Cycle12.CutFailureCertificates.Budget052
import Cycle12.CutFailureCertificates.Budget053
import Cycle12.MergedCutGroups.Batch125
import Cycle12.MergedCutGroups.Batch126
import Cycle12.MergedCutGroups.Batch127
import Cycle12.MergedCutGroups.Batch128
import Cycle12.MergedCutGroups.Batch129
import Cycle12.PopulationCertificates.Batch051
import Cycle12.PopulationCertificates.Batch052
import Cycle12.PopulationCertificates.Batch053
import Cycle12.WitnessCertificates.Batch051
import Cycle12.WitnessCertificates.Batch052
import Cycle12.WitnessCertificates.Batch053

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedAnchorFailures.Batch024
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches480 : (MergedCutGroups.Batch125.certificate1507).AnchorMatches CountingCertificates.Batch051.certificate1026 := by decide +kernel
theorem exponentialBound480 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch125.certificate1507).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch051.certificate1026).dm (WitnessCertificates.Batch051.certificate1026).beta (WitnessCertificates.Batch051.certificate1026).L) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1026).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch125.certificate1507).exponent:ℝ)*st.R))/((WitnessCertificates.Batch051.certificate1026).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch125.certificate1507 CountingCertificates.Batch051.certificate1026 matches480 MergedCutGroups.Batch125.numericValid1507 MergedCutGroups.Batch125.cellsSound1507 MergedCutGroups.Batch125.cellsNumeric1507 MergedCutGroups.Batch125.populationMatches1507
    PopulationCertificates.Batch051.valid1026 PopulationCertificates.Batch051.sound1026 WitnessCertificates.Batch051.valid1026 WitnessCertificates.Batch051.sound1026 CountingCertificates.Batch051.valid1026 CountingCertificates.Batch051.sound1026 H st hI
theorem probabilityBound480 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch125.certificate1507).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch051.certificate1026).dm (WitnessCertificates.Batch051.certificate1026).beta (WitnessCertificates.Batch051.certificate1026).L) ≤ ((CutFailureCertificates.Budget051.certificate1026).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1026 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1026).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch125.certificate1507).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch051.certificate1026).omega:ℝ)) ≤ ((CutFailureCertificates.Budget051.certificate1026).bound:ℝ) at hb
  exact (exponentialBound480 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches481 : (MergedCutGroups.Batch125.certificate1511).AnchorMatches CountingCertificates.Batch051.certificate1029 := by decide +kernel
theorem exponentialBound481 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch125.certificate1511).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch051.certificate1029).dm (WitnessCertificates.Batch051.certificate1029).beta (WitnessCertificates.Batch051.certificate1029).L) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1029).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch125.certificate1511).exponent:ℝ)*st.R))/((WitnessCertificates.Batch051.certificate1029).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch125.certificate1511 CountingCertificates.Batch051.certificate1029 matches481 MergedCutGroups.Batch125.numericValid1511 MergedCutGroups.Batch125.cellsSound1511 MergedCutGroups.Batch125.cellsNumeric1511 MergedCutGroups.Batch125.populationMatches1511
    PopulationCertificates.Batch051.valid1029 PopulationCertificates.Batch051.sound1029 WitnessCertificates.Batch051.valid1029 WitnessCertificates.Batch051.sound1029 CountingCertificates.Batch051.valid1029 CountingCertificates.Batch051.sound1029 H st hI
theorem probabilityBound481 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch125.certificate1511).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch051.certificate1029).dm (WitnessCertificates.Batch051.certificate1029).beta (WitnessCertificates.Batch051.certificate1029).L) ≤ ((CutFailureCertificates.Budget051.certificate1029).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1029 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1029).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch125.certificate1511).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch051.certificate1029).omega:ℝ)) ≤ ((CutFailureCertificates.Budget051.certificate1029).bound:ℝ) at hb
  exact (exponentialBound481 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches482 : (MergedCutGroups.Batch126.certificate1515).AnchorMatches CountingCertificates.Batch051.certificate1032 := by decide +kernel
theorem exponentialBound482 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch126.certificate1515).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch051.certificate1032).dm (WitnessCertificates.Batch051.certificate1032).beta (WitnessCertificates.Batch051.certificate1032).L) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1032).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch126.certificate1515).exponent:ℝ)*st.R))/((WitnessCertificates.Batch051.certificate1032).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch126.certificate1515 CountingCertificates.Batch051.certificate1032 matches482 MergedCutGroups.Batch126.numericValid1515 MergedCutGroups.Batch126.cellsSound1515 MergedCutGroups.Batch126.cellsNumeric1515 MergedCutGroups.Batch126.populationMatches1515
    PopulationCertificates.Batch051.valid1032 PopulationCertificates.Batch051.sound1032 WitnessCertificates.Batch051.valid1032 WitnessCertificates.Batch051.sound1032 CountingCertificates.Batch051.valid1032 CountingCertificates.Batch051.sound1032 H st hI
theorem probabilityBound482 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch126.certificate1515).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch051.certificate1032).dm (WitnessCertificates.Batch051.certificate1032).beta (WitnessCertificates.Batch051.certificate1032).L) ≤ ((CutFailureCertificates.Budget051.certificate1032).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1032 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1032).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch126.certificate1515).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch051.certificate1032).omega:ℝ)) ≤ ((CutFailureCertificates.Budget051.certificate1032).bound:ℝ) at hb
  exact (exponentialBound482 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches483 : (MergedCutGroups.Batch126.certificate1519).AnchorMatches CountingCertificates.Batch051.certificate1035 := by decide +kernel
theorem exponentialBound483 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch126.certificate1519).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch051.certificate1035).dm (WitnessCertificates.Batch051.certificate1035).beta (WitnessCertificates.Batch051.certificate1035).L) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1035).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch126.certificate1519).exponent:ℝ)*st.R))/((WitnessCertificates.Batch051.certificate1035).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch126.certificate1519 CountingCertificates.Batch051.certificate1035 matches483 MergedCutGroups.Batch126.numericValid1519 MergedCutGroups.Batch126.cellsSound1519 MergedCutGroups.Batch126.cellsNumeric1519 MergedCutGroups.Batch126.populationMatches1519
    PopulationCertificates.Batch051.valid1035 PopulationCertificates.Batch051.sound1035 WitnessCertificates.Batch051.valid1035 WitnessCertificates.Batch051.sound1035 CountingCertificates.Batch051.valid1035 CountingCertificates.Batch051.sound1035 H st hI
theorem probabilityBound483 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch126.certificate1519).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch051.certificate1035).dm (WitnessCertificates.Batch051.certificate1035).beta (WitnessCertificates.Batch051.certificate1035).L) ≤ ((CutFailureCertificates.Budget051.certificate1035).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1035 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1035).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch126.certificate1519).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch051.certificate1035).omega:ℝ)) ≤ ((CutFailureCertificates.Budget051.certificate1035).bound:ℝ) at hb
  exact (exponentialBound483 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches484 : (MergedCutGroups.Batch126.certificate1523).AnchorMatches CountingCertificates.Batch051.certificate1038 := by decide +kernel
theorem exponentialBound484 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch126.certificate1523).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch051.certificate1038).dm (WitnessCertificates.Batch051.certificate1038).beta (WitnessCertificates.Batch051.certificate1038).L) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1038).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch126.certificate1523).exponent:ℝ)*st.R))/((WitnessCertificates.Batch051.certificate1038).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch126.certificate1523 CountingCertificates.Batch051.certificate1038 matches484 MergedCutGroups.Batch126.numericValid1523 MergedCutGroups.Batch126.cellsSound1523 MergedCutGroups.Batch126.cellsNumeric1523 MergedCutGroups.Batch126.populationMatches1523
    PopulationCertificates.Batch051.valid1038 PopulationCertificates.Batch051.sound1038 WitnessCertificates.Batch051.valid1038 WitnessCertificates.Batch051.sound1038 CountingCertificates.Batch051.valid1038 CountingCertificates.Batch051.sound1038 H st hI
theorem probabilityBound484 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch126.certificate1523).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch051.certificate1038).dm (WitnessCertificates.Batch051.certificate1038).beta (WitnessCertificates.Batch051.certificate1038).L) ≤ ((CutFailureCertificates.Budget051.certificate1038).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1038 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1038).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch126.certificate1523).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch051.certificate1038).omega:ℝ)) ≤ ((CutFailureCertificates.Budget051.certificate1038).bound:ℝ) at hb
  exact (exponentialBound484 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches485 : (MergedCutGroups.Batch127.certificate1527).AnchorMatches CountingCertificates.Batch052.certificate1041 := by decide +kernel
theorem exponentialBound485 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch127.certificate1527).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch052.certificate1041).dm (WitnessCertificates.Batch052.certificate1041).beta (WitnessCertificates.Batch052.certificate1041).L) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1041).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch127.certificate1527).exponent:ℝ)*st.R))/((WitnessCertificates.Batch052.certificate1041).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch127.certificate1527 CountingCertificates.Batch052.certificate1041 matches485 MergedCutGroups.Batch127.numericValid1527 MergedCutGroups.Batch127.cellsSound1527 MergedCutGroups.Batch127.cellsNumeric1527 MergedCutGroups.Batch127.populationMatches1527
    PopulationCertificates.Batch052.valid1041 PopulationCertificates.Batch052.sound1041 WitnessCertificates.Batch052.valid1041 WitnessCertificates.Batch052.sound1041 CountingCertificates.Batch052.valid1041 CountingCertificates.Batch052.sound1041 H st hI
theorem probabilityBound485 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch127.certificate1527).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch052.certificate1041).dm (WitnessCertificates.Batch052.certificate1041).beta (WitnessCertificates.Batch052.certificate1041).L) ≤ ((CutFailureCertificates.Budget052.certificate1041).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1041 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1041).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch127.certificate1527).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch052.certificate1041).omega:ℝ)) ≤ ((CutFailureCertificates.Budget052.certificate1041).bound:ℝ) at hb
  exact (exponentialBound485 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches486 : (MergedCutGroups.Batch127.certificate1531).AnchorMatches CountingCertificates.Batch052.certificate1044 := by decide +kernel
theorem exponentialBound486 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch127.certificate1531).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch052.certificate1044).dm (WitnessCertificates.Batch052.certificate1044).beta (WitnessCertificates.Batch052.certificate1044).L) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1044).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch127.certificate1531).exponent:ℝ)*st.R))/((WitnessCertificates.Batch052.certificate1044).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch127.certificate1531 CountingCertificates.Batch052.certificate1044 matches486 MergedCutGroups.Batch127.numericValid1531 MergedCutGroups.Batch127.cellsSound1531 MergedCutGroups.Batch127.cellsNumeric1531 MergedCutGroups.Batch127.populationMatches1531
    PopulationCertificates.Batch052.valid1044 PopulationCertificates.Batch052.sound1044 WitnessCertificates.Batch052.valid1044 WitnessCertificates.Batch052.sound1044 CountingCertificates.Batch052.valid1044 CountingCertificates.Batch052.sound1044 H st hI
theorem probabilityBound486 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch127.certificate1531).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch052.certificate1044).dm (WitnessCertificates.Batch052.certificate1044).beta (WitnessCertificates.Batch052.certificate1044).L) ≤ ((CutFailureCertificates.Budget052.certificate1044).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1044 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1044).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch127.certificate1531).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch052.certificate1044).omega:ℝ)) ≤ ((CutFailureCertificates.Budget052.certificate1044).bound:ℝ) at hb
  exact (exponentialBound486 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches487 : (MergedCutGroups.Batch127.certificate1535).AnchorMatches CountingCertificates.Batch052.certificate1047 := by decide +kernel
theorem exponentialBound487 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch127.certificate1535).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch052.certificate1047).dm (WitnessCertificates.Batch052.certificate1047).beta (WitnessCertificates.Batch052.certificate1047).L) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1047).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch127.certificate1535).exponent:ℝ)*st.R))/((WitnessCertificates.Batch052.certificate1047).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch127.certificate1535 CountingCertificates.Batch052.certificate1047 matches487 MergedCutGroups.Batch127.numericValid1535 MergedCutGroups.Batch127.cellsSound1535 MergedCutGroups.Batch127.cellsNumeric1535 MergedCutGroups.Batch127.populationMatches1535
    PopulationCertificates.Batch052.valid1047 PopulationCertificates.Batch052.sound1047 WitnessCertificates.Batch052.valid1047 WitnessCertificates.Batch052.sound1047 CountingCertificates.Batch052.valid1047 CountingCertificates.Batch052.sound1047 H st hI
theorem probabilityBound487 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch127.certificate1535).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch052.certificate1047).dm (WitnessCertificates.Batch052.certificate1047).beta (WitnessCertificates.Batch052.certificate1047).L) ≤ ((CutFailureCertificates.Budget052.certificate1047).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1047 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1047).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch127.certificate1535).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch052.certificate1047).omega:ℝ)) ≤ ((CutFailureCertificates.Budget052.certificate1047).bound:ℝ) at hb
  exact (exponentialBound487 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches488 : (MergedCutGroups.Batch128.certificate1539).AnchorMatches CountingCertificates.Batch052.certificate1050 := by decide +kernel
theorem exponentialBound488 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch128.certificate1539).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch052.certificate1050).dm (WitnessCertificates.Batch052.certificate1050).beta (WitnessCertificates.Batch052.certificate1050).L) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1050).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch128.certificate1539).exponent:ℝ)*st.R))/((WitnessCertificates.Batch052.certificate1050).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch128.certificate1539 CountingCertificates.Batch052.certificate1050 matches488 MergedCutGroups.Batch128.numericValid1539 MergedCutGroups.Batch128.cellsSound1539 MergedCutGroups.Batch128.cellsNumeric1539 MergedCutGroups.Batch128.populationMatches1539
    PopulationCertificates.Batch052.valid1050 PopulationCertificates.Batch052.sound1050 WitnessCertificates.Batch052.valid1050 WitnessCertificates.Batch052.sound1050 CountingCertificates.Batch052.valid1050 CountingCertificates.Batch052.sound1050 H st hI
theorem probabilityBound488 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch128.certificate1539).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch052.certificate1050).dm (WitnessCertificates.Batch052.certificate1050).beta (WitnessCertificates.Batch052.certificate1050).L) ≤ ((CutFailureCertificates.Budget052.certificate1050).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1050 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1050).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch128.certificate1539).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch052.certificate1050).omega:ℝ)) ≤ ((CutFailureCertificates.Budget052.certificate1050).bound:ℝ) at hb
  exact (exponentialBound488 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches489 : (MergedCutGroups.Batch128.certificate1543).AnchorMatches CountingCertificates.Batch052.certificate1053 := by decide +kernel
theorem exponentialBound489 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch128.certificate1543).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch052.certificate1053).dm (WitnessCertificates.Batch052.certificate1053).beta (WitnessCertificates.Batch052.certificate1053).L) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1053).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch128.certificate1543).exponent:ℝ)*st.R))/((WitnessCertificates.Batch052.certificate1053).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch128.certificate1543 CountingCertificates.Batch052.certificate1053 matches489 MergedCutGroups.Batch128.numericValid1543 MergedCutGroups.Batch128.cellsSound1543 MergedCutGroups.Batch128.cellsNumeric1543 MergedCutGroups.Batch128.populationMatches1543
    PopulationCertificates.Batch052.valid1053 PopulationCertificates.Batch052.sound1053 WitnessCertificates.Batch052.valid1053 WitnessCertificates.Batch052.sound1053 CountingCertificates.Batch052.valid1053 CountingCertificates.Batch052.sound1053 H st hI
theorem probabilityBound489 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch128.certificate1543).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch052.certificate1053).dm (WitnessCertificates.Batch052.certificate1053).beta (WitnessCertificates.Batch052.certificate1053).L) ≤ ((CutFailureCertificates.Budget052.certificate1053).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1053 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1053).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch128.certificate1543).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch052.certificate1053).omega:ℝ)) ≤ ((CutFailureCertificates.Budget052.certificate1053).bound:ℝ) at hb
  exact (exponentialBound489 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches490 : (MergedCutGroups.Batch128.certificate1547).AnchorMatches CountingCertificates.Batch052.certificate1056 := by decide +kernel
theorem exponentialBound490 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch128.certificate1547).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch052.certificate1056).dm (WitnessCertificates.Batch052.certificate1056).beta (WitnessCertificates.Batch052.certificate1056).L) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1056).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch128.certificate1547).exponent:ℝ)*st.R))/((WitnessCertificates.Batch052.certificate1056).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch128.certificate1547 CountingCertificates.Batch052.certificate1056 matches490 MergedCutGroups.Batch128.numericValid1547 MergedCutGroups.Batch128.cellsSound1547 MergedCutGroups.Batch128.cellsNumeric1547 MergedCutGroups.Batch128.populationMatches1547
    PopulationCertificates.Batch052.valid1056 PopulationCertificates.Batch052.sound1056 WitnessCertificates.Batch052.valid1056 WitnessCertificates.Batch052.sound1056 CountingCertificates.Batch052.valid1056 CountingCertificates.Batch052.sound1056 H st hI
theorem probabilityBound490 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch128.certificate1547).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch052.certificate1056).dm (WitnessCertificates.Batch052.certificate1056).beta (WitnessCertificates.Batch052.certificate1056).L) ≤ ((CutFailureCertificates.Budget052.certificate1056).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1056 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1056).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch128.certificate1547).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch052.certificate1056).omega:ℝ)) ≤ ((CutFailureCertificates.Budget052.certificate1056).bound:ℝ) at hb
  exact (exponentialBound490 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches491 : (MergedCutGroups.Batch129.certificate1551).AnchorMatches CountingCertificates.Batch052.certificate1059 := by decide +kernel
theorem exponentialBound491 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch129.certificate1551).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch052.certificate1059).dm (WitnessCertificates.Batch052.certificate1059).beta (WitnessCertificates.Batch052.certificate1059).L) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1059).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch129.certificate1551).exponent:ℝ)*st.R))/((WitnessCertificates.Batch052.certificate1059).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch129.certificate1551 CountingCertificates.Batch052.certificate1059 matches491 MergedCutGroups.Batch129.numericValid1551 MergedCutGroups.Batch129.cellsSound1551 MergedCutGroups.Batch129.cellsNumeric1551 MergedCutGroups.Batch129.populationMatches1551
    PopulationCertificates.Batch052.valid1059 PopulationCertificates.Batch052.sound1059 WitnessCertificates.Batch052.valid1059 WitnessCertificates.Batch052.sound1059 CountingCertificates.Batch052.valid1059 CountingCertificates.Batch052.sound1059 H st hI
theorem probabilityBound491 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch129.certificate1551).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch052.certificate1059).dm (WitnessCertificates.Batch052.certificate1059).beta (WitnessCertificates.Batch052.certificate1059).L) ≤ ((CutFailureCertificates.Budget052.certificate1059).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1059 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1059).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch129.certificate1551).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch052.certificate1059).omega:ℝ)) ≤ ((CutFailureCertificates.Budget052.certificate1059).bound:ℝ) at hb
  exact (exponentialBound491 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches492 : (MergedCutGroups.Batch129.certificate1555).AnchorMatches CountingCertificates.Batch053.certificate1062 := by decide +kernel
theorem exponentialBound492 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch129.certificate1555).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch053.certificate1062).dm (WitnessCertificates.Batch053.certificate1062).beta (WitnessCertificates.Batch053.certificate1062).L) ≤ (2*exp (-((CountingCertificates.Batch053.certificate1062).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch129.certificate1555).exponent:ℝ)*st.R))/((WitnessCertificates.Batch053.certificate1062).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch129.certificate1555 CountingCertificates.Batch053.certificate1062 matches492 MergedCutGroups.Batch129.numericValid1555 MergedCutGroups.Batch129.cellsSound1555 MergedCutGroups.Batch129.cellsNumeric1555 MergedCutGroups.Batch129.populationMatches1555
    PopulationCertificates.Batch053.valid1062 PopulationCertificates.Batch053.sound1062 WitnessCertificates.Batch053.valid1062 WitnessCertificates.Batch053.sound1062 CountingCertificates.Batch053.valid1062 CountingCertificates.Batch053.sound1062 H st hI
theorem probabilityBound492 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch129.certificate1555).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch053.certificate1062).dm (WitnessCertificates.Batch053.certificate1062).beta (WitnessCertificates.Batch053.certificate1062).L) ≤ ((CutFailureCertificates.Budget053.certificate1062).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget053.sound1062 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch053.certificate1062).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch129.certificate1555).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch053.certificate1062).omega:ℝ)) ≤ ((CutFailureCertificates.Budget053.certificate1062).bound:ℝ) at hb
  exact (exponentialBound492 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches493 : (MergedCutGroups.Batch129.certificate1559).AnchorMatches CountingCertificates.Batch053.certificate1065 := by decide +kernel
theorem exponentialBound493 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch129.certificate1559).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch053.certificate1065).dm (WitnessCertificates.Batch053.certificate1065).beta (WitnessCertificates.Batch053.certificate1065).L) ≤ (2*exp (-((CountingCertificates.Batch053.certificate1065).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch129.certificate1559).exponent:ℝ)*st.R))/((WitnessCertificates.Batch053.certificate1065).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch129.certificate1559 CountingCertificates.Batch053.certificate1065 matches493 MergedCutGroups.Batch129.numericValid1559 MergedCutGroups.Batch129.cellsSound1559 MergedCutGroups.Batch129.cellsNumeric1559 MergedCutGroups.Batch129.populationMatches1559
    PopulationCertificates.Batch053.valid1065 PopulationCertificates.Batch053.sound1065 WitnessCertificates.Batch053.valid1065 WitnessCertificates.Batch053.sound1065 CountingCertificates.Batch053.valid1065 CountingCertificates.Batch053.sound1065 H st hI
theorem probabilityBound493 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch129.certificate1559).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch053.certificate1065).dm (WitnessCertificates.Batch053.certificate1065).beta (WitnessCertificates.Batch053.certificate1065).L) ≤ ((CutFailureCertificates.Budget053.certificate1065).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget053.sound1065 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch053.certificate1065).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch129.certificate1559).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch053.certificate1065).omega:ℝ)) ≤ ((CutFailureCertificates.Budget053.certificate1065).bound:ℝ) at hb
  exact (exponentialBound493 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch024
