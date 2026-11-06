import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch048
import Cycle12.CountingCertificates.Batch049
import Cycle12.CountingCertificates.Batch050
import Cycle12.CountingCertificates.Batch051
import Cycle12.CutFailureCertificates.Budget048
import Cycle12.CutFailureCertificates.Budget049
import Cycle12.CutFailureCertificates.Budget050
import Cycle12.CutFailureCertificates.Budget051
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

namespace Cycle12.CertifiedAnchorFailures.Batch023
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches460 : (MergedCutGroups.Batch118.certificate1427).AnchorMatches CountingCertificates.Batch048.certificate966 := by decide +kernel
theorem exponentialBound460 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch118.certificate1427).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch048.certificate966).dm (WitnessCertificates.Batch048.certificate966).beta (WitnessCertificates.Batch048.certificate966).L) ≤ (2*exp (-((CountingCertificates.Batch048.certificate966).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch118.certificate1427).exponent:ℝ)*st.R))/((WitnessCertificates.Batch048.certificate966).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch118.certificate1427 CountingCertificates.Batch048.certificate966 matches460 MergedCutGroups.Batch118.numericValid1427 MergedCutGroups.Batch118.cellsSound1427 MergedCutGroups.Batch118.cellsNumeric1427 MergedCutGroups.Batch118.populationMatches1427
    PopulationCertificates.Batch048.valid966 PopulationCertificates.Batch048.sound966 WitnessCertificates.Batch048.valid966 WitnessCertificates.Batch048.sound966 CountingCertificates.Batch048.valid966 CountingCertificates.Batch048.sound966 H st hI
theorem probabilityBound460 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch118.certificate1427).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch048.certificate966).dm (WitnessCertificates.Batch048.certificate966).beta (WitnessCertificates.Batch048.certificate966).L) ≤ ((CutFailureCertificates.Budget048.certificate966).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound966 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate966).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch118.certificate1427).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch048.certificate966).omega:ℝ)) ≤ ((CutFailureCertificates.Budget048.certificate966).bound:ℝ) at hb
  exact (exponentialBound460 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches461 : (MergedCutGroups.Batch119.certificate1431).AnchorMatches CountingCertificates.Batch048.certificate969 := by decide +kernel
theorem exponentialBound461 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch119.certificate1431).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch048.certificate969).dm (WitnessCertificates.Batch048.certificate969).beta (WitnessCertificates.Batch048.certificate969).L) ≤ (2*exp (-((CountingCertificates.Batch048.certificate969).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch119.certificate1431).exponent:ℝ)*st.R))/((WitnessCertificates.Batch048.certificate969).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch119.certificate1431 CountingCertificates.Batch048.certificate969 matches461 MergedCutGroups.Batch119.numericValid1431 MergedCutGroups.Batch119.cellsSound1431 MergedCutGroups.Batch119.cellsNumeric1431 MergedCutGroups.Batch119.populationMatches1431
    PopulationCertificates.Batch048.valid969 PopulationCertificates.Batch048.sound969 WitnessCertificates.Batch048.valid969 WitnessCertificates.Batch048.sound969 CountingCertificates.Batch048.valid969 CountingCertificates.Batch048.sound969 H st hI
theorem probabilityBound461 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch119.certificate1431).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch048.certificate969).dm (WitnessCertificates.Batch048.certificate969).beta (WitnessCertificates.Batch048.certificate969).L) ≤ ((CutFailureCertificates.Budget048.certificate969).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound969 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate969).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch119.certificate1431).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch048.certificate969).omega:ℝ)) ≤ ((CutFailureCertificates.Budget048.certificate969).bound:ℝ) at hb
  exact (exponentialBound461 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches462 : (MergedCutGroups.Batch119.certificate1435).AnchorMatches CountingCertificates.Batch048.certificate972 := by decide +kernel
theorem exponentialBound462 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch119.certificate1435).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch048.certificate972).dm (WitnessCertificates.Batch048.certificate972).beta (WitnessCertificates.Batch048.certificate972).L) ≤ (2*exp (-((CountingCertificates.Batch048.certificate972).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch119.certificate1435).exponent:ℝ)*st.R))/((WitnessCertificates.Batch048.certificate972).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch119.certificate1435 CountingCertificates.Batch048.certificate972 matches462 MergedCutGroups.Batch119.numericValid1435 MergedCutGroups.Batch119.cellsSound1435 MergedCutGroups.Batch119.cellsNumeric1435 MergedCutGroups.Batch119.populationMatches1435
    PopulationCertificates.Batch048.valid972 PopulationCertificates.Batch048.sound972 WitnessCertificates.Batch048.valid972 WitnessCertificates.Batch048.sound972 CountingCertificates.Batch048.valid972 CountingCertificates.Batch048.sound972 H st hI
theorem probabilityBound462 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch119.certificate1435).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch048.certificate972).dm (WitnessCertificates.Batch048.certificate972).beta (WitnessCertificates.Batch048.certificate972).L) ≤ ((CutFailureCertificates.Budget048.certificate972).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound972 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate972).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch119.certificate1435).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch048.certificate972).omega:ℝ)) ≤ ((CutFailureCertificates.Budget048.certificate972).bound:ℝ) at hb
  exact (exponentialBound462 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches463 : (MergedCutGroups.Batch119.certificate1439).AnchorMatches CountingCertificates.Batch048.certificate975 := by decide +kernel
theorem exponentialBound463 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch119.certificate1439).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch048.certificate975).dm (WitnessCertificates.Batch048.certificate975).beta (WitnessCertificates.Batch048.certificate975).L) ≤ (2*exp (-((CountingCertificates.Batch048.certificate975).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch119.certificate1439).exponent:ℝ)*st.R))/((WitnessCertificates.Batch048.certificate975).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch119.certificate1439 CountingCertificates.Batch048.certificate975 matches463 MergedCutGroups.Batch119.numericValid1439 MergedCutGroups.Batch119.cellsSound1439 MergedCutGroups.Batch119.cellsNumeric1439 MergedCutGroups.Batch119.populationMatches1439
    PopulationCertificates.Batch048.valid975 PopulationCertificates.Batch048.sound975 WitnessCertificates.Batch048.valid975 WitnessCertificates.Batch048.sound975 CountingCertificates.Batch048.valid975 CountingCertificates.Batch048.sound975 H st hI
theorem probabilityBound463 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch119.certificate1439).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch048.certificate975).dm (WitnessCertificates.Batch048.certificate975).beta (WitnessCertificates.Batch048.certificate975).L) ≤ ((CutFailureCertificates.Budget048.certificate975).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound975 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate975).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch119.certificate1439).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch048.certificate975).omega:ℝ)) ≤ ((CutFailureCertificates.Budget048.certificate975).bound:ℝ) at hb
  exact (exponentialBound463 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches464 : (MergedCutGroups.Batch120.certificate1443).AnchorMatches CountingCertificates.Batch048.certificate978 := by decide +kernel
theorem exponentialBound464 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch120.certificate1443).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch048.certificate978).dm (WitnessCertificates.Batch048.certificate978).beta (WitnessCertificates.Batch048.certificate978).L) ≤ (2*exp (-((CountingCertificates.Batch048.certificate978).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch120.certificate1443).exponent:ℝ)*st.R))/((WitnessCertificates.Batch048.certificate978).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch120.certificate1443 CountingCertificates.Batch048.certificate978 matches464 MergedCutGroups.Batch120.numericValid1443 MergedCutGroups.Batch120.cellsSound1443 MergedCutGroups.Batch120.cellsNumeric1443 MergedCutGroups.Batch120.populationMatches1443
    PopulationCertificates.Batch048.valid978 PopulationCertificates.Batch048.sound978 WitnessCertificates.Batch048.valid978 WitnessCertificates.Batch048.sound978 CountingCertificates.Batch048.valid978 CountingCertificates.Batch048.sound978 H st hI
theorem probabilityBound464 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch120.certificate1443).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch048.certificate978).dm (WitnessCertificates.Batch048.certificate978).beta (WitnessCertificates.Batch048.certificate978).L) ≤ ((CutFailureCertificates.Budget048.certificate978).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound978 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate978).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch120.certificate1443).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch048.certificate978).omega:ℝ)) ≤ ((CutFailureCertificates.Budget048.certificate978).bound:ℝ) at hb
  exact (exponentialBound464 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches465 : (MergedCutGroups.Batch120.certificate1447).AnchorMatches CountingCertificates.Batch049.certificate981 := by decide +kernel
theorem exponentialBound465 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch120.certificate1447).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch049.certificate981).dm (WitnessCertificates.Batch049.certificate981).beta (WitnessCertificates.Batch049.certificate981).L) ≤ (2*exp (-((CountingCertificates.Batch049.certificate981).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch120.certificate1447).exponent:ℝ)*st.R))/((WitnessCertificates.Batch049.certificate981).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch120.certificate1447 CountingCertificates.Batch049.certificate981 matches465 MergedCutGroups.Batch120.numericValid1447 MergedCutGroups.Batch120.cellsSound1447 MergedCutGroups.Batch120.cellsNumeric1447 MergedCutGroups.Batch120.populationMatches1447
    PopulationCertificates.Batch049.valid981 PopulationCertificates.Batch049.sound981 WitnessCertificates.Batch049.valid981 WitnessCertificates.Batch049.sound981 CountingCertificates.Batch049.valid981 CountingCertificates.Batch049.sound981 H st hI
theorem probabilityBound465 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch120.certificate1447).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch049.certificate981).dm (WitnessCertificates.Batch049.certificate981).beta (WitnessCertificates.Batch049.certificate981).L) ≤ ((CutFailureCertificates.Budget049.certificate981).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound981 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate981).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch120.certificate1447).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch049.certificate981).omega:ℝ)) ≤ ((CutFailureCertificates.Budget049.certificate981).bound:ℝ) at hb
  exact (exponentialBound465 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches466 : (MergedCutGroups.Batch120.certificate1451).AnchorMatches CountingCertificates.Batch049.certificate984 := by decide +kernel
theorem exponentialBound466 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch120.certificate1451).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch049.certificate984).dm (WitnessCertificates.Batch049.certificate984).beta (WitnessCertificates.Batch049.certificate984).L) ≤ (2*exp (-((CountingCertificates.Batch049.certificate984).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch120.certificate1451).exponent:ℝ)*st.R))/((WitnessCertificates.Batch049.certificate984).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch120.certificate1451 CountingCertificates.Batch049.certificate984 matches466 MergedCutGroups.Batch120.numericValid1451 MergedCutGroups.Batch120.cellsSound1451 MergedCutGroups.Batch120.cellsNumeric1451 MergedCutGroups.Batch120.populationMatches1451
    PopulationCertificates.Batch049.valid984 PopulationCertificates.Batch049.sound984 WitnessCertificates.Batch049.valid984 WitnessCertificates.Batch049.sound984 CountingCertificates.Batch049.valid984 CountingCertificates.Batch049.sound984 H st hI
theorem probabilityBound466 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch120.certificate1451).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch049.certificate984).dm (WitnessCertificates.Batch049.certificate984).beta (WitnessCertificates.Batch049.certificate984).L) ≤ ((CutFailureCertificates.Budget049.certificate984).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound984 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate984).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch120.certificate1451).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch049.certificate984).omega:ℝ)) ≤ ((CutFailureCertificates.Budget049.certificate984).bound:ℝ) at hb
  exact (exponentialBound466 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches467 : (MergedCutGroups.Batch121.certificate1455).AnchorMatches CountingCertificates.Batch049.certificate987 := by decide +kernel
theorem exponentialBound467 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch121.certificate1455).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch049.certificate987).dm (WitnessCertificates.Batch049.certificate987).beta (WitnessCertificates.Batch049.certificate987).L) ≤ (2*exp (-((CountingCertificates.Batch049.certificate987).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch121.certificate1455).exponent:ℝ)*st.R))/((WitnessCertificates.Batch049.certificate987).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch121.certificate1455 CountingCertificates.Batch049.certificate987 matches467 MergedCutGroups.Batch121.numericValid1455 MergedCutGroups.Batch121.cellsSound1455 MergedCutGroups.Batch121.cellsNumeric1455 MergedCutGroups.Batch121.populationMatches1455
    PopulationCertificates.Batch049.valid987 PopulationCertificates.Batch049.sound987 WitnessCertificates.Batch049.valid987 WitnessCertificates.Batch049.sound987 CountingCertificates.Batch049.valid987 CountingCertificates.Batch049.sound987 H st hI
theorem probabilityBound467 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch121.certificate1455).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch049.certificate987).dm (WitnessCertificates.Batch049.certificate987).beta (WitnessCertificates.Batch049.certificate987).L) ≤ ((CutFailureCertificates.Budget049.certificate987).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound987 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate987).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch121.certificate1455).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch049.certificate987).omega:ℝ)) ≤ ((CutFailureCertificates.Budget049.certificate987).bound:ℝ) at hb
  exact (exponentialBound467 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches468 : (MergedCutGroups.Batch121.certificate1459).AnchorMatches CountingCertificates.Batch049.certificate990 := by decide +kernel
theorem exponentialBound468 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch121.certificate1459).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch049.certificate990).dm (WitnessCertificates.Batch049.certificate990).beta (WitnessCertificates.Batch049.certificate990).L) ≤ (2*exp (-((CountingCertificates.Batch049.certificate990).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch121.certificate1459).exponent:ℝ)*st.R))/((WitnessCertificates.Batch049.certificate990).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch121.certificate1459 CountingCertificates.Batch049.certificate990 matches468 MergedCutGroups.Batch121.numericValid1459 MergedCutGroups.Batch121.cellsSound1459 MergedCutGroups.Batch121.cellsNumeric1459 MergedCutGroups.Batch121.populationMatches1459
    PopulationCertificates.Batch049.valid990 PopulationCertificates.Batch049.sound990 WitnessCertificates.Batch049.valid990 WitnessCertificates.Batch049.sound990 CountingCertificates.Batch049.valid990 CountingCertificates.Batch049.sound990 H st hI
theorem probabilityBound468 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch121.certificate1459).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch049.certificate990).dm (WitnessCertificates.Batch049.certificate990).beta (WitnessCertificates.Batch049.certificate990).L) ≤ ((CutFailureCertificates.Budget049.certificate990).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound990 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate990).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch121.certificate1459).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch049.certificate990).omega:ℝ)) ≤ ((CutFailureCertificates.Budget049.certificate990).bound:ℝ) at hb
  exact (exponentialBound468 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches469 : (MergedCutGroups.Batch121.certificate1463).AnchorMatches CountingCertificates.Batch049.certificate993 := by decide +kernel
theorem exponentialBound469 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch121.certificate1463).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch049.certificate993).dm (WitnessCertificates.Batch049.certificate993).beta (WitnessCertificates.Batch049.certificate993).L) ≤ (2*exp (-((CountingCertificates.Batch049.certificate993).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch121.certificate1463).exponent:ℝ)*st.R))/((WitnessCertificates.Batch049.certificate993).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch121.certificate1463 CountingCertificates.Batch049.certificate993 matches469 MergedCutGroups.Batch121.numericValid1463 MergedCutGroups.Batch121.cellsSound1463 MergedCutGroups.Batch121.cellsNumeric1463 MergedCutGroups.Batch121.populationMatches1463
    PopulationCertificates.Batch049.valid993 PopulationCertificates.Batch049.sound993 WitnessCertificates.Batch049.valid993 WitnessCertificates.Batch049.sound993 CountingCertificates.Batch049.valid993 CountingCertificates.Batch049.sound993 H st hI
theorem probabilityBound469 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch121.certificate1463).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch049.certificate993).dm (WitnessCertificates.Batch049.certificate993).beta (WitnessCertificates.Batch049.certificate993).L) ≤ ((CutFailureCertificates.Budget049.certificate993).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound993 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate993).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch121.certificate1463).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch049.certificate993).omega:ℝ)) ≤ ((CutFailureCertificates.Budget049.certificate993).bound:ℝ) at hb
  exact (exponentialBound469 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches470 : (MergedCutGroups.Batch122.certificate1467).AnchorMatches CountingCertificates.Batch049.certificate996 := by decide +kernel
theorem exponentialBound470 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch122.certificate1467).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch049.certificate996).dm (WitnessCertificates.Batch049.certificate996).beta (WitnessCertificates.Batch049.certificate996).L) ≤ (2*exp (-((CountingCertificates.Batch049.certificate996).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch122.certificate1467).exponent:ℝ)*st.R))/((WitnessCertificates.Batch049.certificate996).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch122.certificate1467 CountingCertificates.Batch049.certificate996 matches470 MergedCutGroups.Batch122.numericValid1467 MergedCutGroups.Batch122.cellsSound1467 MergedCutGroups.Batch122.cellsNumeric1467 MergedCutGroups.Batch122.populationMatches1467
    PopulationCertificates.Batch049.valid996 PopulationCertificates.Batch049.sound996 WitnessCertificates.Batch049.valid996 WitnessCertificates.Batch049.sound996 CountingCertificates.Batch049.valid996 CountingCertificates.Batch049.sound996 H st hI
theorem probabilityBound470 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch122.certificate1467).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch049.certificate996).dm (WitnessCertificates.Batch049.certificate996).beta (WitnessCertificates.Batch049.certificate996).L) ≤ ((CutFailureCertificates.Budget049.certificate996).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound996 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate996).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch122.certificate1467).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch049.certificate996).omega:ℝ)) ≤ ((CutFailureCertificates.Budget049.certificate996).bound:ℝ) at hb
  exact (exponentialBound470 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches471 : (MergedCutGroups.Batch122.certificate1471).AnchorMatches CountingCertificates.Batch049.certificate999 := by decide +kernel
theorem exponentialBound471 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch122.certificate1471).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch049.certificate999).dm (WitnessCertificates.Batch049.certificate999).beta (WitnessCertificates.Batch049.certificate999).L) ≤ (2*exp (-((CountingCertificates.Batch049.certificate999).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch122.certificate1471).exponent:ℝ)*st.R))/((WitnessCertificates.Batch049.certificate999).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch122.certificate1471 CountingCertificates.Batch049.certificate999 matches471 MergedCutGroups.Batch122.numericValid1471 MergedCutGroups.Batch122.cellsSound1471 MergedCutGroups.Batch122.cellsNumeric1471 MergedCutGroups.Batch122.populationMatches1471
    PopulationCertificates.Batch049.valid999 PopulationCertificates.Batch049.sound999 WitnessCertificates.Batch049.valid999 WitnessCertificates.Batch049.sound999 CountingCertificates.Batch049.valid999 CountingCertificates.Batch049.sound999 H st hI
theorem probabilityBound471 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch122.certificate1471).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch049.certificate999).dm (WitnessCertificates.Batch049.certificate999).beta (WitnessCertificates.Batch049.certificate999).L) ≤ ((CutFailureCertificates.Budget049.certificate999).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound999 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate999).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch122.certificate1471).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch049.certificate999).omega:ℝ)) ≤ ((CutFailureCertificates.Budget049.certificate999).bound:ℝ) at hb
  exact (exponentialBound471 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches472 : (MergedCutGroups.Batch122.certificate1475).AnchorMatches CountingCertificates.Batch050.certificate1002 := by decide +kernel
theorem exponentialBound472 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch122.certificate1475).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch050.certificate1002).dm (WitnessCertificates.Batch050.certificate1002).beta (WitnessCertificates.Batch050.certificate1002).L) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1002).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch122.certificate1475).exponent:ℝ)*st.R))/((WitnessCertificates.Batch050.certificate1002).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch122.certificate1475 CountingCertificates.Batch050.certificate1002 matches472 MergedCutGroups.Batch122.numericValid1475 MergedCutGroups.Batch122.cellsSound1475 MergedCutGroups.Batch122.cellsNumeric1475 MergedCutGroups.Batch122.populationMatches1475
    PopulationCertificates.Batch050.valid1002 PopulationCertificates.Batch050.sound1002 WitnessCertificates.Batch050.valid1002 WitnessCertificates.Batch050.sound1002 CountingCertificates.Batch050.valid1002 CountingCertificates.Batch050.sound1002 H st hI
theorem probabilityBound472 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch122.certificate1475).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch050.certificate1002).dm (WitnessCertificates.Batch050.certificate1002).beta (WitnessCertificates.Batch050.certificate1002).L) ≤ ((CutFailureCertificates.Budget050.certificate1002).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1002 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1002).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch122.certificate1475).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch050.certificate1002).omega:ℝ)) ≤ ((CutFailureCertificates.Budget050.certificate1002).bound:ℝ) at hb
  exact (exponentialBound472 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches473 : (MergedCutGroups.Batch123.certificate1479).AnchorMatches CountingCertificates.Batch050.certificate1005 := by decide +kernel
theorem exponentialBound473 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch123.certificate1479).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch050.certificate1005).dm (WitnessCertificates.Batch050.certificate1005).beta (WitnessCertificates.Batch050.certificate1005).L) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1005).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch123.certificate1479).exponent:ℝ)*st.R))/((WitnessCertificates.Batch050.certificate1005).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch123.certificate1479 CountingCertificates.Batch050.certificate1005 matches473 MergedCutGroups.Batch123.numericValid1479 MergedCutGroups.Batch123.cellsSound1479 MergedCutGroups.Batch123.cellsNumeric1479 MergedCutGroups.Batch123.populationMatches1479
    PopulationCertificates.Batch050.valid1005 PopulationCertificates.Batch050.sound1005 WitnessCertificates.Batch050.valid1005 WitnessCertificates.Batch050.sound1005 CountingCertificates.Batch050.valid1005 CountingCertificates.Batch050.sound1005 H st hI
theorem probabilityBound473 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch123.certificate1479).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch050.certificate1005).dm (WitnessCertificates.Batch050.certificate1005).beta (WitnessCertificates.Batch050.certificate1005).L) ≤ ((CutFailureCertificates.Budget050.certificate1005).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1005 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1005).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch123.certificate1479).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch050.certificate1005).omega:ℝ)) ≤ ((CutFailureCertificates.Budget050.certificate1005).bound:ℝ) at hb
  exact (exponentialBound473 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches474 : (MergedCutGroups.Batch123.certificate1483).AnchorMatches CountingCertificates.Batch050.certificate1008 := by decide +kernel
theorem exponentialBound474 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch123.certificate1483).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch050.certificate1008).dm (WitnessCertificates.Batch050.certificate1008).beta (WitnessCertificates.Batch050.certificate1008).L) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1008).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch123.certificate1483).exponent:ℝ)*st.R))/((WitnessCertificates.Batch050.certificate1008).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch123.certificate1483 CountingCertificates.Batch050.certificate1008 matches474 MergedCutGroups.Batch123.numericValid1483 MergedCutGroups.Batch123.cellsSound1483 MergedCutGroups.Batch123.cellsNumeric1483 MergedCutGroups.Batch123.populationMatches1483
    PopulationCertificates.Batch050.valid1008 PopulationCertificates.Batch050.sound1008 WitnessCertificates.Batch050.valid1008 WitnessCertificates.Batch050.sound1008 CountingCertificates.Batch050.valid1008 CountingCertificates.Batch050.sound1008 H st hI
theorem probabilityBound474 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch123.certificate1483).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch050.certificate1008).dm (WitnessCertificates.Batch050.certificate1008).beta (WitnessCertificates.Batch050.certificate1008).L) ≤ ((CutFailureCertificates.Budget050.certificate1008).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1008 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1008).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch123.certificate1483).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch050.certificate1008).omega:ℝ)) ≤ ((CutFailureCertificates.Budget050.certificate1008).bound:ℝ) at hb
  exact (exponentialBound474 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches475 : (MergedCutGroups.Batch123.certificate1487).AnchorMatches CountingCertificates.Batch050.certificate1011 := by decide +kernel
theorem exponentialBound475 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch123.certificate1487).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch050.certificate1011).dm (WitnessCertificates.Batch050.certificate1011).beta (WitnessCertificates.Batch050.certificate1011).L) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1011).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch123.certificate1487).exponent:ℝ)*st.R))/((WitnessCertificates.Batch050.certificate1011).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch123.certificate1487 CountingCertificates.Batch050.certificate1011 matches475 MergedCutGroups.Batch123.numericValid1487 MergedCutGroups.Batch123.cellsSound1487 MergedCutGroups.Batch123.cellsNumeric1487 MergedCutGroups.Batch123.populationMatches1487
    PopulationCertificates.Batch050.valid1011 PopulationCertificates.Batch050.sound1011 WitnessCertificates.Batch050.valid1011 WitnessCertificates.Batch050.sound1011 CountingCertificates.Batch050.valid1011 CountingCertificates.Batch050.sound1011 H st hI
theorem probabilityBound475 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch123.certificate1487).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch050.certificate1011).dm (WitnessCertificates.Batch050.certificate1011).beta (WitnessCertificates.Batch050.certificate1011).L) ≤ ((CutFailureCertificates.Budget050.certificate1011).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1011 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1011).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch123.certificate1487).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch050.certificate1011).omega:ℝ)) ≤ ((CutFailureCertificates.Budget050.certificate1011).bound:ℝ) at hb
  exact (exponentialBound475 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches476 : (MergedCutGroups.Batch124.certificate1491).AnchorMatches CountingCertificates.Batch050.certificate1014 := by decide +kernel
theorem exponentialBound476 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch124.certificate1491).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch050.certificate1014).dm (WitnessCertificates.Batch050.certificate1014).beta (WitnessCertificates.Batch050.certificate1014).L) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1014).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch124.certificate1491).exponent:ℝ)*st.R))/((WitnessCertificates.Batch050.certificate1014).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch124.certificate1491 CountingCertificates.Batch050.certificate1014 matches476 MergedCutGroups.Batch124.numericValid1491 MergedCutGroups.Batch124.cellsSound1491 MergedCutGroups.Batch124.cellsNumeric1491 MergedCutGroups.Batch124.populationMatches1491
    PopulationCertificates.Batch050.valid1014 PopulationCertificates.Batch050.sound1014 WitnessCertificates.Batch050.valid1014 WitnessCertificates.Batch050.sound1014 CountingCertificates.Batch050.valid1014 CountingCertificates.Batch050.sound1014 H st hI
theorem probabilityBound476 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch124.certificate1491).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch050.certificate1014).dm (WitnessCertificates.Batch050.certificate1014).beta (WitnessCertificates.Batch050.certificate1014).L) ≤ ((CutFailureCertificates.Budget050.certificate1014).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1014 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1014).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch124.certificate1491).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch050.certificate1014).omega:ℝ)) ≤ ((CutFailureCertificates.Budget050.certificate1014).bound:ℝ) at hb
  exact (exponentialBound476 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches477 : (MergedCutGroups.Batch124.certificate1495).AnchorMatches CountingCertificates.Batch050.certificate1017 := by decide +kernel
theorem exponentialBound477 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch124.certificate1495).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch050.certificate1017).dm (WitnessCertificates.Batch050.certificate1017).beta (WitnessCertificates.Batch050.certificate1017).L) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1017).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch124.certificate1495).exponent:ℝ)*st.R))/((WitnessCertificates.Batch050.certificate1017).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch124.certificate1495 CountingCertificates.Batch050.certificate1017 matches477 MergedCutGroups.Batch124.numericValid1495 MergedCutGroups.Batch124.cellsSound1495 MergedCutGroups.Batch124.cellsNumeric1495 MergedCutGroups.Batch124.populationMatches1495
    PopulationCertificates.Batch050.valid1017 PopulationCertificates.Batch050.sound1017 WitnessCertificates.Batch050.valid1017 WitnessCertificates.Batch050.sound1017 CountingCertificates.Batch050.valid1017 CountingCertificates.Batch050.sound1017 H st hI
theorem probabilityBound477 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch124.certificate1495).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch050.certificate1017).dm (WitnessCertificates.Batch050.certificate1017).beta (WitnessCertificates.Batch050.certificate1017).L) ≤ ((CutFailureCertificates.Budget050.certificate1017).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1017 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1017).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch124.certificate1495).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch050.certificate1017).omega:ℝ)) ≤ ((CutFailureCertificates.Budget050.certificate1017).bound:ℝ) at hb
  exact (exponentialBound477 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches478 : (MergedCutGroups.Batch124.certificate1499).AnchorMatches CountingCertificates.Batch051.certificate1020 := by decide +kernel
theorem exponentialBound478 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch124.certificate1499).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch051.certificate1020).dm (WitnessCertificates.Batch051.certificate1020).beta (WitnessCertificates.Batch051.certificate1020).L) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1020).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch124.certificate1499).exponent:ℝ)*st.R))/((WitnessCertificates.Batch051.certificate1020).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch124.certificate1499 CountingCertificates.Batch051.certificate1020 matches478 MergedCutGroups.Batch124.numericValid1499 MergedCutGroups.Batch124.cellsSound1499 MergedCutGroups.Batch124.cellsNumeric1499 MergedCutGroups.Batch124.populationMatches1499
    PopulationCertificates.Batch051.valid1020 PopulationCertificates.Batch051.sound1020 WitnessCertificates.Batch051.valid1020 WitnessCertificates.Batch051.sound1020 CountingCertificates.Batch051.valid1020 CountingCertificates.Batch051.sound1020 H st hI
theorem probabilityBound478 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch124.certificate1499).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch051.certificate1020).dm (WitnessCertificates.Batch051.certificate1020).beta (WitnessCertificates.Batch051.certificate1020).L) ≤ ((CutFailureCertificates.Budget051.certificate1020).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1020 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1020).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch124.certificate1499).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch051.certificate1020).omega:ℝ)) ≤ ((CutFailureCertificates.Budget051.certificate1020).bound:ℝ) at hb
  exact (exponentialBound478 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches479 : (MergedCutGroups.Batch125.certificate1503).AnchorMatches CountingCertificates.Batch051.certificate1023 := by decide +kernel
theorem exponentialBound479 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch125.certificate1503).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch051.certificate1023).dm (WitnessCertificates.Batch051.certificate1023).beta (WitnessCertificates.Batch051.certificate1023).L) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1023).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch125.certificate1503).exponent:ℝ)*st.R))/((WitnessCertificates.Batch051.certificate1023).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch125.certificate1503 CountingCertificates.Batch051.certificate1023 matches479 MergedCutGroups.Batch125.numericValid1503 MergedCutGroups.Batch125.cellsSound1503 MergedCutGroups.Batch125.cellsNumeric1503 MergedCutGroups.Batch125.populationMatches1503
    PopulationCertificates.Batch051.valid1023 PopulationCertificates.Batch051.sound1023 WitnessCertificates.Batch051.valid1023 WitnessCertificates.Batch051.sound1023 CountingCertificates.Batch051.valid1023 CountingCertificates.Batch051.sound1023 H st hI
theorem probabilityBound479 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch125.certificate1503).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch051.certificate1023).dm (WitnessCertificates.Batch051.certificate1023).beta (WitnessCertificates.Batch051.certificate1023).L) ≤ ((CutFailureCertificates.Budget051.certificate1023).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1023 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1023).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch125.certificate1503).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch051.certificate1023).omega:ℝ)) ≤ ((CutFailureCertificates.Budget051.certificate1023).bound:ℝ) at hb
  exact (exponentialBound479 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch023
