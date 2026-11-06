import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch018
import Cycle12.CountingCertificates.Batch019
import Cycle12.CutFailureCertificates.Budget018
import Cycle12.CutFailureCertificates.Budget019
import Cycle12.MergedCutGroups.Batch045
import Cycle12.MergedCutGroups.Batch046
import Cycle12.MergedCutGroups.Batch047
import Cycle12.MergedCutGroups.Batch048
import Cycle12.MergedCutGroups.Batch049
import Cycle12.PopulationCertificates.Batch018
import Cycle12.PopulationCertificates.Batch019
import Cycle12.WitnessCertificates.Batch018
import Cycle12.WitnessCertificates.Batch019

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedAnchorFailures.Batch009
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches180 : (MergedCutGroups.Batch045.certificate542).AnchorMatches CountingCertificates.Batch018.certificate361 := by decide +kernel
theorem exponentialBound180 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch045.certificate542).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate361).dm (WitnessCertificates.Batch018.certificate361).beta (WitnessCertificates.Batch018.certificate361).L) ≤ (2*exp (-((CountingCertificates.Batch018.certificate361).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch045.certificate542).exponent:ℝ)*st.R))/((WitnessCertificates.Batch018.certificate361).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch045.certificate542 CountingCertificates.Batch018.certificate361 matches180 MergedCutGroups.Batch045.numericValid542 MergedCutGroups.Batch045.cellsSound542 MergedCutGroups.Batch045.cellsNumeric542 MergedCutGroups.Batch045.populationMatches542
    PopulationCertificates.Batch018.valid361 PopulationCertificates.Batch018.sound361 WitnessCertificates.Batch018.valid361 WitnessCertificates.Batch018.sound361 CountingCertificates.Batch018.valid361 CountingCertificates.Batch018.sound361 H st hI
theorem probabilityBound180 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch045.certificate542).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate361).dm (WitnessCertificates.Batch018.certificate361).beta (WitnessCertificates.Batch018.certificate361).L) ≤ ((CutFailureCertificates.Budget018.certificate361).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound361 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate361).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch045.certificate542).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch018.certificate361).omega:ℝ)) ≤ ((CutFailureCertificates.Budget018.certificate361).bound:ℝ) at hb
  exact (exponentialBound180 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches181 : (MergedCutGroups.Batch045.certificate545).AnchorMatches CountingCertificates.Batch018.certificate363 := by decide +kernel
theorem exponentialBound181 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch045.certificate545).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate363).dm (WitnessCertificates.Batch018.certificate363).beta (WitnessCertificates.Batch018.certificate363).L) ≤ (2*exp (-((CountingCertificates.Batch018.certificate363).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch045.certificate545).exponent:ℝ)*st.R))/((WitnessCertificates.Batch018.certificate363).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch045.certificate545 CountingCertificates.Batch018.certificate363 matches181 MergedCutGroups.Batch045.numericValid545 MergedCutGroups.Batch045.cellsSound545 MergedCutGroups.Batch045.cellsNumeric545 MergedCutGroups.Batch045.populationMatches545
    PopulationCertificates.Batch018.valid363 PopulationCertificates.Batch018.sound363 WitnessCertificates.Batch018.valid363 WitnessCertificates.Batch018.sound363 CountingCertificates.Batch018.valid363 CountingCertificates.Batch018.sound363 H st hI
theorem probabilityBound181 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch045.certificate545).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate363).dm (WitnessCertificates.Batch018.certificate363).beta (WitnessCertificates.Batch018.certificate363).L) ≤ ((CutFailureCertificates.Budget018.certificate363).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound363 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate363).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch045.certificate545).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch018.certificate363).omega:ℝ)) ≤ ((CutFailureCertificates.Budget018.certificate363).bound:ℝ) at hb
  exact (exponentialBound181 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches182 : (MergedCutGroups.Batch045.certificate548).AnchorMatches CountingCertificates.Batch018.certificate365 := by decide +kernel
theorem exponentialBound182 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch045.certificate548).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate365).dm (WitnessCertificates.Batch018.certificate365).beta (WitnessCertificates.Batch018.certificate365).L) ≤ (2*exp (-((CountingCertificates.Batch018.certificate365).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch045.certificate548).exponent:ℝ)*st.R))/((WitnessCertificates.Batch018.certificate365).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch045.certificate548 CountingCertificates.Batch018.certificate365 matches182 MergedCutGroups.Batch045.numericValid548 MergedCutGroups.Batch045.cellsSound548 MergedCutGroups.Batch045.cellsNumeric548 MergedCutGroups.Batch045.populationMatches548
    PopulationCertificates.Batch018.valid365 PopulationCertificates.Batch018.sound365 WitnessCertificates.Batch018.valid365 WitnessCertificates.Batch018.sound365 CountingCertificates.Batch018.valid365 CountingCertificates.Batch018.sound365 H st hI
theorem probabilityBound182 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch045.certificate548).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate365).dm (WitnessCertificates.Batch018.certificate365).beta (WitnessCertificates.Batch018.certificate365).L) ≤ ((CutFailureCertificates.Budget018.certificate365).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound365 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate365).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch045.certificate548).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch018.certificate365).omega:ℝ)) ≤ ((CutFailureCertificates.Budget018.certificate365).bound:ℝ) at hb
  exact (exponentialBound182 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches183 : (MergedCutGroups.Batch045.certificate551).AnchorMatches CountingCertificates.Batch018.certificate367 := by decide +kernel
theorem exponentialBound183 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch045.certificate551).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate367).dm (WitnessCertificates.Batch018.certificate367).beta (WitnessCertificates.Batch018.certificate367).L) ≤ (2*exp (-((CountingCertificates.Batch018.certificate367).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch045.certificate551).exponent:ℝ)*st.R))/((WitnessCertificates.Batch018.certificate367).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch045.certificate551 CountingCertificates.Batch018.certificate367 matches183 MergedCutGroups.Batch045.numericValid551 MergedCutGroups.Batch045.cellsSound551 MergedCutGroups.Batch045.cellsNumeric551 MergedCutGroups.Batch045.populationMatches551
    PopulationCertificates.Batch018.valid367 PopulationCertificates.Batch018.sound367 WitnessCertificates.Batch018.valid367 WitnessCertificates.Batch018.sound367 CountingCertificates.Batch018.valid367 CountingCertificates.Batch018.sound367 H st hI
theorem probabilityBound183 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch045.certificate551).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate367).dm (WitnessCertificates.Batch018.certificate367).beta (WitnessCertificates.Batch018.certificate367).L) ≤ ((CutFailureCertificates.Budget018.certificate367).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound367 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate367).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch045.certificate551).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch018.certificate367).omega:ℝ)) ≤ ((CutFailureCertificates.Budget018.certificate367).bound:ℝ) at hb
  exact (exponentialBound183 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches184 : (MergedCutGroups.Batch046.certificate554).AnchorMatches CountingCertificates.Batch018.certificate369 := by decide +kernel
theorem exponentialBound184 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch046.certificate554).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate369).dm (WitnessCertificates.Batch018.certificate369).beta (WitnessCertificates.Batch018.certificate369).L) ≤ (2*exp (-((CountingCertificates.Batch018.certificate369).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch046.certificate554).exponent:ℝ)*st.R))/((WitnessCertificates.Batch018.certificate369).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch046.certificate554 CountingCertificates.Batch018.certificate369 matches184 MergedCutGroups.Batch046.numericValid554 MergedCutGroups.Batch046.cellsSound554 MergedCutGroups.Batch046.cellsNumeric554 MergedCutGroups.Batch046.populationMatches554
    PopulationCertificates.Batch018.valid369 PopulationCertificates.Batch018.sound369 WitnessCertificates.Batch018.valid369 WitnessCertificates.Batch018.sound369 CountingCertificates.Batch018.valid369 CountingCertificates.Batch018.sound369 H st hI
theorem probabilityBound184 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch046.certificate554).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate369).dm (WitnessCertificates.Batch018.certificate369).beta (WitnessCertificates.Batch018.certificate369).L) ≤ ((CutFailureCertificates.Budget018.certificate369).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound369 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate369).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch046.certificate554).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch018.certificate369).omega:ℝ)) ≤ ((CutFailureCertificates.Budget018.certificate369).bound:ℝ) at hb
  exact (exponentialBound184 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches185 : (MergedCutGroups.Batch046.certificate557).AnchorMatches CountingCertificates.Batch018.certificate371 := by decide +kernel
theorem exponentialBound185 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch046.certificate557).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate371).dm (WitnessCertificates.Batch018.certificate371).beta (WitnessCertificates.Batch018.certificate371).L) ≤ (2*exp (-((CountingCertificates.Batch018.certificate371).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch046.certificate557).exponent:ℝ)*st.R))/((WitnessCertificates.Batch018.certificate371).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch046.certificate557 CountingCertificates.Batch018.certificate371 matches185 MergedCutGroups.Batch046.numericValid557 MergedCutGroups.Batch046.cellsSound557 MergedCutGroups.Batch046.cellsNumeric557 MergedCutGroups.Batch046.populationMatches557
    PopulationCertificates.Batch018.valid371 PopulationCertificates.Batch018.sound371 WitnessCertificates.Batch018.valid371 WitnessCertificates.Batch018.sound371 CountingCertificates.Batch018.valid371 CountingCertificates.Batch018.sound371 H st hI
theorem probabilityBound185 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch046.certificate557).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate371).dm (WitnessCertificates.Batch018.certificate371).beta (WitnessCertificates.Batch018.certificate371).L) ≤ ((CutFailureCertificates.Budget018.certificate371).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound371 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate371).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch046.certificate557).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch018.certificate371).omega:ℝ)) ≤ ((CutFailureCertificates.Budget018.certificate371).bound:ℝ) at hb
  exact (exponentialBound185 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches186 : (MergedCutGroups.Batch046.certificate560).AnchorMatches CountingCertificates.Batch018.certificate373 := by decide +kernel
theorem exponentialBound186 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch046.certificate560).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate373).dm (WitnessCertificates.Batch018.certificate373).beta (WitnessCertificates.Batch018.certificate373).L) ≤ (2*exp (-((CountingCertificates.Batch018.certificate373).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch046.certificate560).exponent:ℝ)*st.R))/((WitnessCertificates.Batch018.certificate373).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch046.certificate560 CountingCertificates.Batch018.certificate373 matches186 MergedCutGroups.Batch046.numericValid560 MergedCutGroups.Batch046.cellsSound560 MergedCutGroups.Batch046.cellsNumeric560 MergedCutGroups.Batch046.populationMatches560
    PopulationCertificates.Batch018.valid373 PopulationCertificates.Batch018.sound373 WitnessCertificates.Batch018.valid373 WitnessCertificates.Batch018.sound373 CountingCertificates.Batch018.valid373 CountingCertificates.Batch018.sound373 H st hI
theorem probabilityBound186 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch046.certificate560).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate373).dm (WitnessCertificates.Batch018.certificate373).beta (WitnessCertificates.Batch018.certificate373).L) ≤ ((CutFailureCertificates.Budget018.certificate373).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound373 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate373).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch046.certificate560).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch018.certificate373).omega:ℝ)) ≤ ((CutFailureCertificates.Budget018.certificate373).bound:ℝ) at hb
  exact (exponentialBound186 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches187 : (MergedCutGroups.Batch046.certificate563).AnchorMatches CountingCertificates.Batch018.certificate375 := by decide +kernel
theorem exponentialBound187 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch046.certificate563).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate375).dm (WitnessCertificates.Batch018.certificate375).beta (WitnessCertificates.Batch018.certificate375).L) ≤ (2*exp (-((CountingCertificates.Batch018.certificate375).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch046.certificate563).exponent:ℝ)*st.R))/((WitnessCertificates.Batch018.certificate375).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch046.certificate563 CountingCertificates.Batch018.certificate375 matches187 MergedCutGroups.Batch046.numericValid563 MergedCutGroups.Batch046.cellsSound563 MergedCutGroups.Batch046.cellsNumeric563 MergedCutGroups.Batch046.populationMatches563
    PopulationCertificates.Batch018.valid375 PopulationCertificates.Batch018.sound375 WitnessCertificates.Batch018.valid375 WitnessCertificates.Batch018.sound375 CountingCertificates.Batch018.valid375 CountingCertificates.Batch018.sound375 H st hI
theorem probabilityBound187 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch046.certificate563).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate375).dm (WitnessCertificates.Batch018.certificate375).beta (WitnessCertificates.Batch018.certificate375).L) ≤ ((CutFailureCertificates.Budget018.certificate375).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound375 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate375).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch046.certificate563).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch018.certificate375).omega:ℝ)) ≤ ((CutFailureCertificates.Budget018.certificate375).bound:ℝ) at hb
  exact (exponentialBound187 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches188 : (MergedCutGroups.Batch047.certificate566).AnchorMatches CountingCertificates.Batch018.certificate377 := by decide +kernel
theorem exponentialBound188 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch047.certificate566).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate377).dm (WitnessCertificates.Batch018.certificate377).beta (WitnessCertificates.Batch018.certificate377).L) ≤ (2*exp (-((CountingCertificates.Batch018.certificate377).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch047.certificate566).exponent:ℝ)*st.R))/((WitnessCertificates.Batch018.certificate377).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch047.certificate566 CountingCertificates.Batch018.certificate377 matches188 MergedCutGroups.Batch047.numericValid566 MergedCutGroups.Batch047.cellsSound566 MergedCutGroups.Batch047.cellsNumeric566 MergedCutGroups.Batch047.populationMatches566
    PopulationCertificates.Batch018.valid377 PopulationCertificates.Batch018.sound377 WitnessCertificates.Batch018.valid377 WitnessCertificates.Batch018.sound377 CountingCertificates.Batch018.valid377 CountingCertificates.Batch018.sound377 H st hI
theorem probabilityBound188 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch047.certificate566).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate377).dm (WitnessCertificates.Batch018.certificate377).beta (WitnessCertificates.Batch018.certificate377).L) ≤ ((CutFailureCertificates.Budget018.certificate377).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound377 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate377).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch047.certificate566).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch018.certificate377).omega:ℝ)) ≤ ((CutFailureCertificates.Budget018.certificate377).bound:ℝ) at hb
  exact (exponentialBound188 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches189 : (MergedCutGroups.Batch047.certificate569).AnchorMatches CountingCertificates.Batch018.certificate379 := by decide +kernel
theorem exponentialBound189 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch047.certificate569).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate379).dm (WitnessCertificates.Batch018.certificate379).beta (WitnessCertificates.Batch018.certificate379).L) ≤ (2*exp (-((CountingCertificates.Batch018.certificate379).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch047.certificate569).exponent:ℝ)*st.R))/((WitnessCertificates.Batch018.certificate379).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch047.certificate569 CountingCertificates.Batch018.certificate379 matches189 MergedCutGroups.Batch047.numericValid569 MergedCutGroups.Batch047.cellsSound569 MergedCutGroups.Batch047.cellsNumeric569 MergedCutGroups.Batch047.populationMatches569
    PopulationCertificates.Batch018.valid379 PopulationCertificates.Batch018.sound379 WitnessCertificates.Batch018.valid379 WitnessCertificates.Batch018.sound379 CountingCertificates.Batch018.valid379 CountingCertificates.Batch018.sound379 H st hI
theorem probabilityBound189 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch047.certificate569).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch018.certificate379).dm (WitnessCertificates.Batch018.certificate379).beta (WitnessCertificates.Batch018.certificate379).L) ≤ ((CutFailureCertificates.Budget018.certificate379).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound379 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate379).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch047.certificate569).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch018.certificate379).omega:ℝ)) ≤ ((CutFailureCertificates.Budget018.certificate379).bound:ℝ) at hb
  exact (exponentialBound189 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches190 : (MergedCutGroups.Batch047.certificate572).AnchorMatches CountingCertificates.Batch019.certificate381 := by decide +kernel
theorem exponentialBound190 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch047.certificate572).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate381).dm (WitnessCertificates.Batch019.certificate381).beta (WitnessCertificates.Batch019.certificate381).L) ≤ (2*exp (-((CountingCertificates.Batch019.certificate381).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch047.certificate572).exponent:ℝ)*st.R))/((WitnessCertificates.Batch019.certificate381).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch047.certificate572 CountingCertificates.Batch019.certificate381 matches190 MergedCutGroups.Batch047.numericValid572 MergedCutGroups.Batch047.cellsSound572 MergedCutGroups.Batch047.cellsNumeric572 MergedCutGroups.Batch047.populationMatches572
    PopulationCertificates.Batch019.valid381 PopulationCertificates.Batch019.sound381 WitnessCertificates.Batch019.valid381 WitnessCertificates.Batch019.sound381 CountingCertificates.Batch019.valid381 CountingCertificates.Batch019.sound381 H st hI
theorem probabilityBound190 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch047.certificate572).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate381).dm (WitnessCertificates.Batch019.certificate381).beta (WitnessCertificates.Batch019.certificate381).L) ≤ ((CutFailureCertificates.Budget019.certificate381).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound381 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate381).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch047.certificate572).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch019.certificate381).omega:ℝ)) ≤ ((CutFailureCertificates.Budget019.certificate381).bound:ℝ) at hb
  exact (exponentialBound190 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches191 : (MergedCutGroups.Batch047.certificate575).AnchorMatches CountingCertificates.Batch019.certificate383 := by decide +kernel
theorem exponentialBound191 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch047.certificate575).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate383).dm (WitnessCertificates.Batch019.certificate383).beta (WitnessCertificates.Batch019.certificate383).L) ≤ (2*exp (-((CountingCertificates.Batch019.certificate383).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch047.certificate575).exponent:ℝ)*st.R))/((WitnessCertificates.Batch019.certificate383).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch047.certificate575 CountingCertificates.Batch019.certificate383 matches191 MergedCutGroups.Batch047.numericValid575 MergedCutGroups.Batch047.cellsSound575 MergedCutGroups.Batch047.cellsNumeric575 MergedCutGroups.Batch047.populationMatches575
    PopulationCertificates.Batch019.valid383 PopulationCertificates.Batch019.sound383 WitnessCertificates.Batch019.valid383 WitnessCertificates.Batch019.sound383 CountingCertificates.Batch019.valid383 CountingCertificates.Batch019.sound383 H st hI
theorem probabilityBound191 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch047.certificate575).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate383).dm (WitnessCertificates.Batch019.certificate383).beta (WitnessCertificates.Batch019.certificate383).L) ≤ ((CutFailureCertificates.Budget019.certificate383).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound383 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate383).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch047.certificate575).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch019.certificate383).omega:ℝ)) ≤ ((CutFailureCertificates.Budget019.certificate383).bound:ℝ) at hb
  exact (exponentialBound191 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches192 : (MergedCutGroups.Batch048.certificate578).AnchorMatches CountingCertificates.Batch019.certificate385 := by decide +kernel
theorem exponentialBound192 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch048.certificate578).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate385).dm (WitnessCertificates.Batch019.certificate385).beta (WitnessCertificates.Batch019.certificate385).L) ≤ (2*exp (-((CountingCertificates.Batch019.certificate385).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch048.certificate578).exponent:ℝ)*st.R))/((WitnessCertificates.Batch019.certificate385).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch048.certificate578 CountingCertificates.Batch019.certificate385 matches192 MergedCutGroups.Batch048.numericValid578 MergedCutGroups.Batch048.cellsSound578 MergedCutGroups.Batch048.cellsNumeric578 MergedCutGroups.Batch048.populationMatches578
    PopulationCertificates.Batch019.valid385 PopulationCertificates.Batch019.sound385 WitnessCertificates.Batch019.valid385 WitnessCertificates.Batch019.sound385 CountingCertificates.Batch019.valid385 CountingCertificates.Batch019.sound385 H st hI
theorem probabilityBound192 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch048.certificate578).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate385).dm (WitnessCertificates.Batch019.certificate385).beta (WitnessCertificates.Batch019.certificate385).L) ≤ ((CutFailureCertificates.Budget019.certificate385).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound385 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate385).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch048.certificate578).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch019.certificate385).omega:ℝ)) ≤ ((CutFailureCertificates.Budget019.certificate385).bound:ℝ) at hb
  exact (exponentialBound192 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches193 : (MergedCutGroups.Batch048.certificate581).AnchorMatches CountingCertificates.Batch019.certificate387 := by decide +kernel
theorem exponentialBound193 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch048.certificate581).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate387).dm (WitnessCertificates.Batch019.certificate387).beta (WitnessCertificates.Batch019.certificate387).L) ≤ (2*exp (-((CountingCertificates.Batch019.certificate387).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch048.certificate581).exponent:ℝ)*st.R))/((WitnessCertificates.Batch019.certificate387).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch048.certificate581 CountingCertificates.Batch019.certificate387 matches193 MergedCutGroups.Batch048.numericValid581 MergedCutGroups.Batch048.cellsSound581 MergedCutGroups.Batch048.cellsNumeric581 MergedCutGroups.Batch048.populationMatches581
    PopulationCertificates.Batch019.valid387 PopulationCertificates.Batch019.sound387 WitnessCertificates.Batch019.valid387 WitnessCertificates.Batch019.sound387 CountingCertificates.Batch019.valid387 CountingCertificates.Batch019.sound387 H st hI
theorem probabilityBound193 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch048.certificate581).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate387).dm (WitnessCertificates.Batch019.certificate387).beta (WitnessCertificates.Batch019.certificate387).L) ≤ ((CutFailureCertificates.Budget019.certificate387).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound387 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate387).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch048.certificate581).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch019.certificate387).omega:ℝ)) ≤ ((CutFailureCertificates.Budget019.certificate387).bound:ℝ) at hb
  exact (exponentialBound193 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches194 : (MergedCutGroups.Batch048.certificate584).AnchorMatches CountingCertificates.Batch019.certificate389 := by decide +kernel
theorem exponentialBound194 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch048.certificate584).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate389).dm (WitnessCertificates.Batch019.certificate389).beta (WitnessCertificates.Batch019.certificate389).L) ≤ (2*exp (-((CountingCertificates.Batch019.certificate389).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch048.certificate584).exponent:ℝ)*st.R))/((WitnessCertificates.Batch019.certificate389).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch048.certificate584 CountingCertificates.Batch019.certificate389 matches194 MergedCutGroups.Batch048.numericValid584 MergedCutGroups.Batch048.cellsSound584 MergedCutGroups.Batch048.cellsNumeric584 MergedCutGroups.Batch048.populationMatches584
    PopulationCertificates.Batch019.valid389 PopulationCertificates.Batch019.sound389 WitnessCertificates.Batch019.valid389 WitnessCertificates.Batch019.sound389 CountingCertificates.Batch019.valid389 CountingCertificates.Batch019.sound389 H st hI
theorem probabilityBound194 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch048.certificate584).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate389).dm (WitnessCertificates.Batch019.certificate389).beta (WitnessCertificates.Batch019.certificate389).L) ≤ ((CutFailureCertificates.Budget019.certificate389).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound389 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate389).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch048.certificate584).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch019.certificate389).omega:ℝ)) ≤ ((CutFailureCertificates.Budget019.certificate389).bound:ℝ) at hb
  exact (exponentialBound194 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches195 : (MergedCutGroups.Batch048.certificate587).AnchorMatches CountingCertificates.Batch019.certificate391 := by decide +kernel
theorem exponentialBound195 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch048.certificate587).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate391).dm (WitnessCertificates.Batch019.certificate391).beta (WitnessCertificates.Batch019.certificate391).L) ≤ (2*exp (-((CountingCertificates.Batch019.certificate391).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch048.certificate587).exponent:ℝ)*st.R))/((WitnessCertificates.Batch019.certificate391).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch048.certificate587 CountingCertificates.Batch019.certificate391 matches195 MergedCutGroups.Batch048.numericValid587 MergedCutGroups.Batch048.cellsSound587 MergedCutGroups.Batch048.cellsNumeric587 MergedCutGroups.Batch048.populationMatches587
    PopulationCertificates.Batch019.valid391 PopulationCertificates.Batch019.sound391 WitnessCertificates.Batch019.valid391 WitnessCertificates.Batch019.sound391 CountingCertificates.Batch019.valid391 CountingCertificates.Batch019.sound391 H st hI
theorem probabilityBound195 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch048.certificate587).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate391).dm (WitnessCertificates.Batch019.certificate391).beta (WitnessCertificates.Batch019.certificate391).L) ≤ ((CutFailureCertificates.Budget019.certificate391).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound391 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate391).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch048.certificate587).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch019.certificate391).omega:ℝ)) ≤ ((CutFailureCertificates.Budget019.certificate391).bound:ℝ) at hb
  exact (exponentialBound195 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches196 : (MergedCutGroups.Batch049.certificate590).AnchorMatches CountingCertificates.Batch019.certificate393 := by decide +kernel
theorem exponentialBound196 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch049.certificate590).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate393).dm (WitnessCertificates.Batch019.certificate393).beta (WitnessCertificates.Batch019.certificate393).L) ≤ (2*exp (-((CountingCertificates.Batch019.certificate393).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch049.certificate590).exponent:ℝ)*st.R))/((WitnessCertificates.Batch019.certificate393).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch049.certificate590 CountingCertificates.Batch019.certificate393 matches196 MergedCutGroups.Batch049.numericValid590 MergedCutGroups.Batch049.cellsSound590 MergedCutGroups.Batch049.cellsNumeric590 MergedCutGroups.Batch049.populationMatches590
    PopulationCertificates.Batch019.valid393 PopulationCertificates.Batch019.sound393 WitnessCertificates.Batch019.valid393 WitnessCertificates.Batch019.sound393 CountingCertificates.Batch019.valid393 CountingCertificates.Batch019.sound393 H st hI
theorem probabilityBound196 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch049.certificate590).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate393).dm (WitnessCertificates.Batch019.certificate393).beta (WitnessCertificates.Batch019.certificate393).L) ≤ ((CutFailureCertificates.Budget019.certificate393).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound393 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate393).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch049.certificate590).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch019.certificate393).omega:ℝ)) ≤ ((CutFailureCertificates.Budget019.certificate393).bound:ℝ) at hb
  exact (exponentialBound196 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches197 : (MergedCutGroups.Batch049.certificate593).AnchorMatches CountingCertificates.Batch019.certificate395 := by decide +kernel
theorem exponentialBound197 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch049.certificate593).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate395).dm (WitnessCertificates.Batch019.certificate395).beta (WitnessCertificates.Batch019.certificate395).L) ≤ (2*exp (-((CountingCertificates.Batch019.certificate395).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch049.certificate593).exponent:ℝ)*st.R))/((WitnessCertificates.Batch019.certificate395).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch049.certificate593 CountingCertificates.Batch019.certificate395 matches197 MergedCutGroups.Batch049.numericValid593 MergedCutGroups.Batch049.cellsSound593 MergedCutGroups.Batch049.cellsNumeric593 MergedCutGroups.Batch049.populationMatches593
    PopulationCertificates.Batch019.valid395 PopulationCertificates.Batch019.sound395 WitnessCertificates.Batch019.valid395 WitnessCertificates.Batch019.sound395 CountingCertificates.Batch019.valid395 CountingCertificates.Batch019.sound395 H st hI
theorem probabilityBound197 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch049.certificate593).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate395).dm (WitnessCertificates.Batch019.certificate395).beta (WitnessCertificates.Batch019.certificate395).L) ≤ ((CutFailureCertificates.Budget019.certificate395).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound395 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate395).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch049.certificate593).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch019.certificate395).omega:ℝ)) ≤ ((CutFailureCertificates.Budget019.certificate395).bound:ℝ) at hb
  exact (exponentialBound197 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches198 : (MergedCutGroups.Batch049.certificate596).AnchorMatches CountingCertificates.Batch019.certificate397 := by decide +kernel
theorem exponentialBound198 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch049.certificate596).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate397).dm (WitnessCertificates.Batch019.certificate397).beta (WitnessCertificates.Batch019.certificate397).L) ≤ (2*exp (-((CountingCertificates.Batch019.certificate397).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch049.certificate596).exponent:ℝ)*st.R))/((WitnessCertificates.Batch019.certificate397).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch049.certificate596 CountingCertificates.Batch019.certificate397 matches198 MergedCutGroups.Batch049.numericValid596 MergedCutGroups.Batch049.cellsSound596 MergedCutGroups.Batch049.cellsNumeric596 MergedCutGroups.Batch049.populationMatches596
    PopulationCertificates.Batch019.valid397 PopulationCertificates.Batch019.sound397 WitnessCertificates.Batch019.valid397 WitnessCertificates.Batch019.sound397 CountingCertificates.Batch019.valid397 CountingCertificates.Batch019.sound397 H st hI
theorem probabilityBound198 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch049.certificate596).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate397).dm (WitnessCertificates.Batch019.certificate397).beta (WitnessCertificates.Batch019.certificate397).L) ≤ ((CutFailureCertificates.Budget019.certificate397).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound397 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate397).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch049.certificate596).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch019.certificate397).omega:ℝ)) ≤ ((CutFailureCertificates.Budget019.certificate397).bound:ℝ) at hb
  exact (exponentialBound198 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches199 : (MergedCutGroups.Batch049.certificate599).AnchorMatches CountingCertificates.Batch019.certificate399 := by decide +kernel
theorem exponentialBound199 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch049.certificate599).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate399).dm (WitnessCertificates.Batch019.certificate399).beta (WitnessCertificates.Batch019.certificate399).L) ≤ (2*exp (-((CountingCertificates.Batch019.certificate399).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch049.certificate599).exponent:ℝ)*st.R))/((WitnessCertificates.Batch019.certificate399).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch049.certificate599 CountingCertificates.Batch019.certificate399 matches199 MergedCutGroups.Batch049.numericValid599 MergedCutGroups.Batch049.cellsSound599 MergedCutGroups.Batch049.cellsNumeric599 MergedCutGroups.Batch049.populationMatches599
    PopulationCertificates.Batch019.valid399 PopulationCertificates.Batch019.sound399 WitnessCertificates.Batch019.valid399 WitnessCertificates.Batch019.sound399 CountingCertificates.Batch019.valid399 CountingCertificates.Batch019.sound399 H st hI
theorem probabilityBound199 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch049.certificate599).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch019.certificate399).dm (WitnessCertificates.Batch019.certificate399).beta (WitnessCertificates.Batch019.certificate399).L) ≤ ((CutFailureCertificates.Budget019.certificate399).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound399 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate399).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch049.certificate599).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch019.certificate399).omega:ℝ)) ≤ ((CutFailureCertificates.Budget019.certificate399).bound:ℝ) at hb
  exact (exponentialBound199 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch009
