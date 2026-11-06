import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch032
import Cycle12.CountingCertificates.Batch033
import Cycle12.CutFailureCertificates.Budget032
import Cycle12.CutFailureCertificates.Budget033
import Cycle12.MergedCutGroups.Batch080
import Cycle12.MergedCutGroups.Batch081
import Cycle12.MergedCutGroups.Batch082
import Cycle12.MergedCutGroups.Batch083
import Cycle12.MergedCutGroups.Batch084
import Cycle12.PopulationCertificates.Batch032
import Cycle12.PopulationCertificates.Batch033
import Cycle12.WitnessCertificates.Batch032
import Cycle12.WitnessCertificates.Batch033

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedAnchorFailures.Batch016
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches320 : (MergedCutGroups.Batch080.certificate962).AnchorMatches CountingCertificates.Batch032.certificate641 := by decide +kernel
theorem exponentialBound320 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch080.certificate962).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate641).dm (WitnessCertificates.Batch032.certificate641).beta (WitnessCertificates.Batch032.certificate641).L) ≤ (2*exp (-((CountingCertificates.Batch032.certificate641).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch080.certificate962).exponent:ℝ)*st.R))/((WitnessCertificates.Batch032.certificate641).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch080.certificate962 CountingCertificates.Batch032.certificate641 matches320 MergedCutGroups.Batch080.numericValid962 MergedCutGroups.Batch080.cellsSound962 MergedCutGroups.Batch080.cellsNumeric962 MergedCutGroups.Batch080.populationMatches962
    PopulationCertificates.Batch032.valid641 PopulationCertificates.Batch032.sound641 WitnessCertificates.Batch032.valid641 WitnessCertificates.Batch032.sound641 CountingCertificates.Batch032.valid641 CountingCertificates.Batch032.sound641 H st hI
theorem probabilityBound320 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch080.certificate962).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate641).dm (WitnessCertificates.Batch032.certificate641).beta (WitnessCertificates.Batch032.certificate641).L) ≤ ((CutFailureCertificates.Budget032.certificate641).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound641 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate641).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch080.certificate962).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch032.certificate641).omega:ℝ)) ≤ ((CutFailureCertificates.Budget032.certificate641).bound:ℝ) at hb
  exact (exponentialBound320 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches321 : (MergedCutGroups.Batch080.certificate965).AnchorMatches CountingCertificates.Batch032.certificate643 := by decide +kernel
theorem exponentialBound321 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch080.certificate965).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate643).dm (WitnessCertificates.Batch032.certificate643).beta (WitnessCertificates.Batch032.certificate643).L) ≤ (2*exp (-((CountingCertificates.Batch032.certificate643).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch080.certificate965).exponent:ℝ)*st.R))/((WitnessCertificates.Batch032.certificate643).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch080.certificate965 CountingCertificates.Batch032.certificate643 matches321 MergedCutGroups.Batch080.numericValid965 MergedCutGroups.Batch080.cellsSound965 MergedCutGroups.Batch080.cellsNumeric965 MergedCutGroups.Batch080.populationMatches965
    PopulationCertificates.Batch032.valid643 PopulationCertificates.Batch032.sound643 WitnessCertificates.Batch032.valid643 WitnessCertificates.Batch032.sound643 CountingCertificates.Batch032.valid643 CountingCertificates.Batch032.sound643 H st hI
theorem probabilityBound321 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch080.certificate965).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate643).dm (WitnessCertificates.Batch032.certificate643).beta (WitnessCertificates.Batch032.certificate643).L) ≤ ((CutFailureCertificates.Budget032.certificate643).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound643 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate643).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch080.certificate965).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch032.certificate643).omega:ℝ)) ≤ ((CutFailureCertificates.Budget032.certificate643).bound:ℝ) at hb
  exact (exponentialBound321 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches322 : (MergedCutGroups.Batch080.certificate968).AnchorMatches CountingCertificates.Batch032.certificate645 := by decide +kernel
theorem exponentialBound322 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch080.certificate968).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate645).dm (WitnessCertificates.Batch032.certificate645).beta (WitnessCertificates.Batch032.certificate645).L) ≤ (2*exp (-((CountingCertificates.Batch032.certificate645).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch080.certificate968).exponent:ℝ)*st.R))/((WitnessCertificates.Batch032.certificate645).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch080.certificate968 CountingCertificates.Batch032.certificate645 matches322 MergedCutGroups.Batch080.numericValid968 MergedCutGroups.Batch080.cellsSound968 MergedCutGroups.Batch080.cellsNumeric968 MergedCutGroups.Batch080.populationMatches968
    PopulationCertificates.Batch032.valid645 PopulationCertificates.Batch032.sound645 WitnessCertificates.Batch032.valid645 WitnessCertificates.Batch032.sound645 CountingCertificates.Batch032.valid645 CountingCertificates.Batch032.sound645 H st hI
theorem probabilityBound322 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch080.certificate968).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate645).dm (WitnessCertificates.Batch032.certificate645).beta (WitnessCertificates.Batch032.certificate645).L) ≤ ((CutFailureCertificates.Budget032.certificate645).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound645 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate645).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch080.certificate968).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch032.certificate645).omega:ℝ)) ≤ ((CutFailureCertificates.Budget032.certificate645).bound:ℝ) at hb
  exact (exponentialBound322 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches323 : (MergedCutGroups.Batch080.certificate971).AnchorMatches CountingCertificates.Batch032.certificate647 := by decide +kernel
theorem exponentialBound323 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch080.certificate971).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate647).dm (WitnessCertificates.Batch032.certificate647).beta (WitnessCertificates.Batch032.certificate647).L) ≤ (2*exp (-((CountingCertificates.Batch032.certificate647).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch080.certificate971).exponent:ℝ)*st.R))/((WitnessCertificates.Batch032.certificate647).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch080.certificate971 CountingCertificates.Batch032.certificate647 matches323 MergedCutGroups.Batch080.numericValid971 MergedCutGroups.Batch080.cellsSound971 MergedCutGroups.Batch080.cellsNumeric971 MergedCutGroups.Batch080.populationMatches971
    PopulationCertificates.Batch032.valid647 PopulationCertificates.Batch032.sound647 WitnessCertificates.Batch032.valid647 WitnessCertificates.Batch032.sound647 CountingCertificates.Batch032.valid647 CountingCertificates.Batch032.sound647 H st hI
theorem probabilityBound323 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch080.certificate971).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate647).dm (WitnessCertificates.Batch032.certificate647).beta (WitnessCertificates.Batch032.certificate647).L) ≤ ((CutFailureCertificates.Budget032.certificate647).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound647 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate647).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch080.certificate971).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch032.certificate647).omega:ℝ)) ≤ ((CutFailureCertificates.Budget032.certificate647).bound:ℝ) at hb
  exact (exponentialBound323 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches324 : (MergedCutGroups.Batch081.certificate974).AnchorMatches CountingCertificates.Batch032.certificate649 := by decide +kernel
theorem exponentialBound324 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch081.certificate974).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate649).dm (WitnessCertificates.Batch032.certificate649).beta (WitnessCertificates.Batch032.certificate649).L) ≤ (2*exp (-((CountingCertificates.Batch032.certificate649).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch081.certificate974).exponent:ℝ)*st.R))/((WitnessCertificates.Batch032.certificate649).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch081.certificate974 CountingCertificates.Batch032.certificate649 matches324 MergedCutGroups.Batch081.numericValid974 MergedCutGroups.Batch081.cellsSound974 MergedCutGroups.Batch081.cellsNumeric974 MergedCutGroups.Batch081.populationMatches974
    PopulationCertificates.Batch032.valid649 PopulationCertificates.Batch032.sound649 WitnessCertificates.Batch032.valid649 WitnessCertificates.Batch032.sound649 CountingCertificates.Batch032.valid649 CountingCertificates.Batch032.sound649 H st hI
theorem probabilityBound324 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch081.certificate974).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate649).dm (WitnessCertificates.Batch032.certificate649).beta (WitnessCertificates.Batch032.certificate649).L) ≤ ((CutFailureCertificates.Budget032.certificate649).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound649 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate649).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch081.certificate974).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch032.certificate649).omega:ℝ)) ≤ ((CutFailureCertificates.Budget032.certificate649).bound:ℝ) at hb
  exact (exponentialBound324 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches325 : (MergedCutGroups.Batch081.certificate977).AnchorMatches CountingCertificates.Batch032.certificate651 := by decide +kernel
theorem exponentialBound325 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch081.certificate977).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate651).dm (WitnessCertificates.Batch032.certificate651).beta (WitnessCertificates.Batch032.certificate651).L) ≤ (2*exp (-((CountingCertificates.Batch032.certificate651).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch081.certificate977).exponent:ℝ)*st.R))/((WitnessCertificates.Batch032.certificate651).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch081.certificate977 CountingCertificates.Batch032.certificate651 matches325 MergedCutGroups.Batch081.numericValid977 MergedCutGroups.Batch081.cellsSound977 MergedCutGroups.Batch081.cellsNumeric977 MergedCutGroups.Batch081.populationMatches977
    PopulationCertificates.Batch032.valid651 PopulationCertificates.Batch032.sound651 WitnessCertificates.Batch032.valid651 WitnessCertificates.Batch032.sound651 CountingCertificates.Batch032.valid651 CountingCertificates.Batch032.sound651 H st hI
theorem probabilityBound325 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch081.certificate977).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate651).dm (WitnessCertificates.Batch032.certificate651).beta (WitnessCertificates.Batch032.certificate651).L) ≤ ((CutFailureCertificates.Budget032.certificate651).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound651 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate651).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch081.certificate977).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch032.certificate651).omega:ℝ)) ≤ ((CutFailureCertificates.Budget032.certificate651).bound:ℝ) at hb
  exact (exponentialBound325 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches326 : (MergedCutGroups.Batch081.certificate980).AnchorMatches CountingCertificates.Batch032.certificate653 := by decide +kernel
theorem exponentialBound326 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch081.certificate980).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate653).dm (WitnessCertificates.Batch032.certificate653).beta (WitnessCertificates.Batch032.certificate653).L) ≤ (2*exp (-((CountingCertificates.Batch032.certificate653).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch081.certificate980).exponent:ℝ)*st.R))/((WitnessCertificates.Batch032.certificate653).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch081.certificate980 CountingCertificates.Batch032.certificate653 matches326 MergedCutGroups.Batch081.numericValid980 MergedCutGroups.Batch081.cellsSound980 MergedCutGroups.Batch081.cellsNumeric980 MergedCutGroups.Batch081.populationMatches980
    PopulationCertificates.Batch032.valid653 PopulationCertificates.Batch032.sound653 WitnessCertificates.Batch032.valid653 WitnessCertificates.Batch032.sound653 CountingCertificates.Batch032.valid653 CountingCertificates.Batch032.sound653 H st hI
theorem probabilityBound326 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch081.certificate980).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate653).dm (WitnessCertificates.Batch032.certificate653).beta (WitnessCertificates.Batch032.certificate653).L) ≤ ((CutFailureCertificates.Budget032.certificate653).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound653 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate653).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch081.certificate980).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch032.certificate653).omega:ℝ)) ≤ ((CutFailureCertificates.Budget032.certificate653).bound:ℝ) at hb
  exact (exponentialBound326 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches327 : (MergedCutGroups.Batch081.certificate983).AnchorMatches CountingCertificates.Batch032.certificate655 := by decide +kernel
theorem exponentialBound327 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch081.certificate983).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate655).dm (WitnessCertificates.Batch032.certificate655).beta (WitnessCertificates.Batch032.certificate655).L) ≤ (2*exp (-((CountingCertificates.Batch032.certificate655).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch081.certificate983).exponent:ℝ)*st.R))/((WitnessCertificates.Batch032.certificate655).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch081.certificate983 CountingCertificates.Batch032.certificate655 matches327 MergedCutGroups.Batch081.numericValid983 MergedCutGroups.Batch081.cellsSound983 MergedCutGroups.Batch081.cellsNumeric983 MergedCutGroups.Batch081.populationMatches983
    PopulationCertificates.Batch032.valid655 PopulationCertificates.Batch032.sound655 WitnessCertificates.Batch032.valid655 WitnessCertificates.Batch032.sound655 CountingCertificates.Batch032.valid655 CountingCertificates.Batch032.sound655 H st hI
theorem probabilityBound327 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch081.certificate983).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate655).dm (WitnessCertificates.Batch032.certificate655).beta (WitnessCertificates.Batch032.certificate655).L) ≤ ((CutFailureCertificates.Budget032.certificate655).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound655 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate655).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch081.certificate983).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch032.certificate655).omega:ℝ)) ≤ ((CutFailureCertificates.Budget032.certificate655).bound:ℝ) at hb
  exact (exponentialBound327 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches328 : (MergedCutGroups.Batch082.certificate986).AnchorMatches CountingCertificates.Batch032.certificate657 := by decide +kernel
theorem exponentialBound328 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch082.certificate986).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate657).dm (WitnessCertificates.Batch032.certificate657).beta (WitnessCertificates.Batch032.certificate657).L) ≤ (2*exp (-((CountingCertificates.Batch032.certificate657).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch082.certificate986).exponent:ℝ)*st.R))/((WitnessCertificates.Batch032.certificate657).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch082.certificate986 CountingCertificates.Batch032.certificate657 matches328 MergedCutGroups.Batch082.numericValid986 MergedCutGroups.Batch082.cellsSound986 MergedCutGroups.Batch082.cellsNumeric986 MergedCutGroups.Batch082.populationMatches986
    PopulationCertificates.Batch032.valid657 PopulationCertificates.Batch032.sound657 WitnessCertificates.Batch032.valid657 WitnessCertificates.Batch032.sound657 CountingCertificates.Batch032.valid657 CountingCertificates.Batch032.sound657 H st hI
theorem probabilityBound328 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch082.certificate986).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate657).dm (WitnessCertificates.Batch032.certificate657).beta (WitnessCertificates.Batch032.certificate657).L) ≤ ((CutFailureCertificates.Budget032.certificate657).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound657 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate657).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch082.certificate986).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch032.certificate657).omega:ℝ)) ≤ ((CutFailureCertificates.Budget032.certificate657).bound:ℝ) at hb
  exact (exponentialBound328 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches329 : (MergedCutGroups.Batch082.certificate989).AnchorMatches CountingCertificates.Batch032.certificate659 := by decide +kernel
theorem exponentialBound329 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch082.certificate989).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate659).dm (WitnessCertificates.Batch032.certificate659).beta (WitnessCertificates.Batch032.certificate659).L) ≤ (2*exp (-((CountingCertificates.Batch032.certificate659).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch082.certificate989).exponent:ℝ)*st.R))/((WitnessCertificates.Batch032.certificate659).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch082.certificate989 CountingCertificates.Batch032.certificate659 matches329 MergedCutGroups.Batch082.numericValid989 MergedCutGroups.Batch082.cellsSound989 MergedCutGroups.Batch082.cellsNumeric989 MergedCutGroups.Batch082.populationMatches989
    PopulationCertificates.Batch032.valid659 PopulationCertificates.Batch032.sound659 WitnessCertificates.Batch032.valid659 WitnessCertificates.Batch032.sound659 CountingCertificates.Batch032.valid659 CountingCertificates.Batch032.sound659 H st hI
theorem probabilityBound329 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch082.certificate989).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch032.certificate659).dm (WitnessCertificates.Batch032.certificate659).beta (WitnessCertificates.Batch032.certificate659).L) ≤ ((CutFailureCertificates.Budget032.certificate659).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound659 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate659).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch082.certificate989).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch032.certificate659).omega:ℝ)) ≤ ((CutFailureCertificates.Budget032.certificate659).bound:ℝ) at hb
  exact (exponentialBound329 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches330 : (MergedCutGroups.Batch082.certificate992).AnchorMatches CountingCertificates.Batch033.certificate661 := by decide +kernel
theorem exponentialBound330 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch082.certificate992).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate661).dm (WitnessCertificates.Batch033.certificate661).beta (WitnessCertificates.Batch033.certificate661).L) ≤ (2*exp (-((CountingCertificates.Batch033.certificate661).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch082.certificate992).exponent:ℝ)*st.R))/((WitnessCertificates.Batch033.certificate661).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch082.certificate992 CountingCertificates.Batch033.certificate661 matches330 MergedCutGroups.Batch082.numericValid992 MergedCutGroups.Batch082.cellsSound992 MergedCutGroups.Batch082.cellsNumeric992 MergedCutGroups.Batch082.populationMatches992
    PopulationCertificates.Batch033.valid661 PopulationCertificates.Batch033.sound661 WitnessCertificates.Batch033.valid661 WitnessCertificates.Batch033.sound661 CountingCertificates.Batch033.valid661 CountingCertificates.Batch033.sound661 H st hI
theorem probabilityBound330 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch082.certificate992).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate661).dm (WitnessCertificates.Batch033.certificate661).beta (WitnessCertificates.Batch033.certificate661).L) ≤ ((CutFailureCertificates.Budget033.certificate661).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound661 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate661).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch082.certificate992).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch033.certificate661).omega:ℝ)) ≤ ((CutFailureCertificates.Budget033.certificate661).bound:ℝ) at hb
  exact (exponentialBound330 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches331 : (MergedCutGroups.Batch082.certificate995).AnchorMatches CountingCertificates.Batch033.certificate663 := by decide +kernel
theorem exponentialBound331 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch082.certificate995).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate663).dm (WitnessCertificates.Batch033.certificate663).beta (WitnessCertificates.Batch033.certificate663).L) ≤ (2*exp (-((CountingCertificates.Batch033.certificate663).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch082.certificate995).exponent:ℝ)*st.R))/((WitnessCertificates.Batch033.certificate663).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch082.certificate995 CountingCertificates.Batch033.certificate663 matches331 MergedCutGroups.Batch082.numericValid995 MergedCutGroups.Batch082.cellsSound995 MergedCutGroups.Batch082.cellsNumeric995 MergedCutGroups.Batch082.populationMatches995
    PopulationCertificates.Batch033.valid663 PopulationCertificates.Batch033.sound663 WitnessCertificates.Batch033.valid663 WitnessCertificates.Batch033.sound663 CountingCertificates.Batch033.valid663 CountingCertificates.Batch033.sound663 H st hI
theorem probabilityBound331 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch082.certificate995).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate663).dm (WitnessCertificates.Batch033.certificate663).beta (WitnessCertificates.Batch033.certificate663).L) ≤ ((CutFailureCertificates.Budget033.certificate663).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound663 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate663).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch082.certificate995).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch033.certificate663).omega:ℝ)) ≤ ((CutFailureCertificates.Budget033.certificate663).bound:ℝ) at hb
  exact (exponentialBound331 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches332 : (MergedCutGroups.Batch083.certificate998).AnchorMatches CountingCertificates.Batch033.certificate665 := by decide +kernel
theorem exponentialBound332 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch083.certificate998).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate665).dm (WitnessCertificates.Batch033.certificate665).beta (WitnessCertificates.Batch033.certificate665).L) ≤ (2*exp (-((CountingCertificates.Batch033.certificate665).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch083.certificate998).exponent:ℝ)*st.R))/((WitnessCertificates.Batch033.certificate665).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch083.certificate998 CountingCertificates.Batch033.certificate665 matches332 MergedCutGroups.Batch083.numericValid998 MergedCutGroups.Batch083.cellsSound998 MergedCutGroups.Batch083.cellsNumeric998 MergedCutGroups.Batch083.populationMatches998
    PopulationCertificates.Batch033.valid665 PopulationCertificates.Batch033.sound665 WitnessCertificates.Batch033.valid665 WitnessCertificates.Batch033.sound665 CountingCertificates.Batch033.valid665 CountingCertificates.Batch033.sound665 H st hI
theorem probabilityBound332 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch083.certificate998).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate665).dm (WitnessCertificates.Batch033.certificate665).beta (WitnessCertificates.Batch033.certificate665).L) ≤ ((CutFailureCertificates.Budget033.certificate665).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound665 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate665).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch083.certificate998).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch033.certificate665).omega:ℝ)) ≤ ((CutFailureCertificates.Budget033.certificate665).bound:ℝ) at hb
  exact (exponentialBound332 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches333 : (MergedCutGroups.Batch083.certificate1001).AnchorMatches CountingCertificates.Batch033.certificate667 := by decide +kernel
theorem exponentialBound333 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch083.certificate1001).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate667).dm (WitnessCertificates.Batch033.certificate667).beta (WitnessCertificates.Batch033.certificate667).L) ≤ (2*exp (-((CountingCertificates.Batch033.certificate667).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch083.certificate1001).exponent:ℝ)*st.R))/((WitnessCertificates.Batch033.certificate667).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch083.certificate1001 CountingCertificates.Batch033.certificate667 matches333 MergedCutGroups.Batch083.numericValid1001 MergedCutGroups.Batch083.cellsSound1001 MergedCutGroups.Batch083.cellsNumeric1001 MergedCutGroups.Batch083.populationMatches1001
    PopulationCertificates.Batch033.valid667 PopulationCertificates.Batch033.sound667 WitnessCertificates.Batch033.valid667 WitnessCertificates.Batch033.sound667 CountingCertificates.Batch033.valid667 CountingCertificates.Batch033.sound667 H st hI
theorem probabilityBound333 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch083.certificate1001).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate667).dm (WitnessCertificates.Batch033.certificate667).beta (WitnessCertificates.Batch033.certificate667).L) ≤ ((CutFailureCertificates.Budget033.certificate667).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound667 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate667).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch083.certificate1001).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch033.certificate667).omega:ℝ)) ≤ ((CutFailureCertificates.Budget033.certificate667).bound:ℝ) at hb
  exact (exponentialBound333 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches334 : (MergedCutGroups.Batch083.certificate1004).AnchorMatches CountingCertificates.Batch033.certificate669 := by decide +kernel
theorem exponentialBound334 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch083.certificate1004).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate669).dm (WitnessCertificates.Batch033.certificate669).beta (WitnessCertificates.Batch033.certificate669).L) ≤ (2*exp (-((CountingCertificates.Batch033.certificate669).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch083.certificate1004).exponent:ℝ)*st.R))/((WitnessCertificates.Batch033.certificate669).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch083.certificate1004 CountingCertificates.Batch033.certificate669 matches334 MergedCutGroups.Batch083.numericValid1004 MergedCutGroups.Batch083.cellsSound1004 MergedCutGroups.Batch083.cellsNumeric1004 MergedCutGroups.Batch083.populationMatches1004
    PopulationCertificates.Batch033.valid669 PopulationCertificates.Batch033.sound669 WitnessCertificates.Batch033.valid669 WitnessCertificates.Batch033.sound669 CountingCertificates.Batch033.valid669 CountingCertificates.Batch033.sound669 H st hI
theorem probabilityBound334 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch083.certificate1004).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate669).dm (WitnessCertificates.Batch033.certificate669).beta (WitnessCertificates.Batch033.certificate669).L) ≤ ((CutFailureCertificates.Budget033.certificate669).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound669 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate669).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch083.certificate1004).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch033.certificate669).omega:ℝ)) ≤ ((CutFailureCertificates.Budget033.certificate669).bound:ℝ) at hb
  exact (exponentialBound334 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches335 : (MergedCutGroups.Batch083.certificate1007).AnchorMatches CountingCertificates.Batch033.certificate671 := by decide +kernel
theorem exponentialBound335 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch083.certificate1007).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate671).dm (WitnessCertificates.Batch033.certificate671).beta (WitnessCertificates.Batch033.certificate671).L) ≤ (2*exp (-((CountingCertificates.Batch033.certificate671).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch083.certificate1007).exponent:ℝ)*st.R))/((WitnessCertificates.Batch033.certificate671).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch083.certificate1007 CountingCertificates.Batch033.certificate671 matches335 MergedCutGroups.Batch083.numericValid1007 MergedCutGroups.Batch083.cellsSound1007 MergedCutGroups.Batch083.cellsNumeric1007 MergedCutGroups.Batch083.populationMatches1007
    PopulationCertificates.Batch033.valid671 PopulationCertificates.Batch033.sound671 WitnessCertificates.Batch033.valid671 WitnessCertificates.Batch033.sound671 CountingCertificates.Batch033.valid671 CountingCertificates.Batch033.sound671 H st hI
theorem probabilityBound335 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch083.certificate1007).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate671).dm (WitnessCertificates.Batch033.certificate671).beta (WitnessCertificates.Batch033.certificate671).L) ≤ ((CutFailureCertificates.Budget033.certificate671).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound671 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate671).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch083.certificate1007).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch033.certificate671).omega:ℝ)) ≤ ((CutFailureCertificates.Budget033.certificate671).bound:ℝ) at hb
  exact (exponentialBound335 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches336 : (MergedCutGroups.Batch084.certificate1010).AnchorMatches CountingCertificates.Batch033.certificate673 := by decide +kernel
theorem exponentialBound336 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch084.certificate1010).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate673).dm (WitnessCertificates.Batch033.certificate673).beta (WitnessCertificates.Batch033.certificate673).L) ≤ (2*exp (-((CountingCertificates.Batch033.certificate673).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch084.certificate1010).exponent:ℝ)*st.R))/((WitnessCertificates.Batch033.certificate673).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch084.certificate1010 CountingCertificates.Batch033.certificate673 matches336 MergedCutGroups.Batch084.numericValid1010 MergedCutGroups.Batch084.cellsSound1010 MergedCutGroups.Batch084.cellsNumeric1010 MergedCutGroups.Batch084.populationMatches1010
    PopulationCertificates.Batch033.valid673 PopulationCertificates.Batch033.sound673 WitnessCertificates.Batch033.valid673 WitnessCertificates.Batch033.sound673 CountingCertificates.Batch033.valid673 CountingCertificates.Batch033.sound673 H st hI
theorem probabilityBound336 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch084.certificate1010).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate673).dm (WitnessCertificates.Batch033.certificate673).beta (WitnessCertificates.Batch033.certificate673).L) ≤ ((CutFailureCertificates.Budget033.certificate673).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound673 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate673).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch084.certificate1010).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch033.certificate673).omega:ℝ)) ≤ ((CutFailureCertificates.Budget033.certificate673).bound:ℝ) at hb
  exact (exponentialBound336 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches337 : (MergedCutGroups.Batch084.certificate1013).AnchorMatches CountingCertificates.Batch033.certificate675 := by decide +kernel
theorem exponentialBound337 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch084.certificate1013).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate675).dm (WitnessCertificates.Batch033.certificate675).beta (WitnessCertificates.Batch033.certificate675).L) ≤ (2*exp (-((CountingCertificates.Batch033.certificate675).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch084.certificate1013).exponent:ℝ)*st.R))/((WitnessCertificates.Batch033.certificate675).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch084.certificate1013 CountingCertificates.Batch033.certificate675 matches337 MergedCutGroups.Batch084.numericValid1013 MergedCutGroups.Batch084.cellsSound1013 MergedCutGroups.Batch084.cellsNumeric1013 MergedCutGroups.Batch084.populationMatches1013
    PopulationCertificates.Batch033.valid675 PopulationCertificates.Batch033.sound675 WitnessCertificates.Batch033.valid675 WitnessCertificates.Batch033.sound675 CountingCertificates.Batch033.valid675 CountingCertificates.Batch033.sound675 H st hI
theorem probabilityBound337 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch084.certificate1013).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate675).dm (WitnessCertificates.Batch033.certificate675).beta (WitnessCertificates.Batch033.certificate675).L) ≤ ((CutFailureCertificates.Budget033.certificate675).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound675 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate675).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch084.certificate1013).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch033.certificate675).omega:ℝ)) ≤ ((CutFailureCertificates.Budget033.certificate675).bound:ℝ) at hb
  exact (exponentialBound337 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches338 : (MergedCutGroups.Batch084.certificate1016).AnchorMatches CountingCertificates.Batch033.certificate677 := by decide +kernel
theorem exponentialBound338 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch084.certificate1016).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate677).dm (WitnessCertificates.Batch033.certificate677).beta (WitnessCertificates.Batch033.certificate677).L) ≤ (2*exp (-((CountingCertificates.Batch033.certificate677).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch084.certificate1016).exponent:ℝ)*st.R))/((WitnessCertificates.Batch033.certificate677).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch084.certificate1016 CountingCertificates.Batch033.certificate677 matches338 MergedCutGroups.Batch084.numericValid1016 MergedCutGroups.Batch084.cellsSound1016 MergedCutGroups.Batch084.cellsNumeric1016 MergedCutGroups.Batch084.populationMatches1016
    PopulationCertificates.Batch033.valid677 PopulationCertificates.Batch033.sound677 WitnessCertificates.Batch033.valid677 WitnessCertificates.Batch033.sound677 CountingCertificates.Batch033.valid677 CountingCertificates.Batch033.sound677 H st hI
theorem probabilityBound338 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch084.certificate1016).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate677).dm (WitnessCertificates.Batch033.certificate677).beta (WitnessCertificates.Batch033.certificate677).L) ≤ ((CutFailureCertificates.Budget033.certificate677).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound677 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate677).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch084.certificate1016).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch033.certificate677).omega:ℝ)) ≤ ((CutFailureCertificates.Budget033.certificate677).bound:ℝ) at hb
  exact (exponentialBound338 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches339 : (MergedCutGroups.Batch084.certificate1019).AnchorMatches CountingCertificates.Batch033.certificate679 := by decide +kernel
theorem exponentialBound339 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch084.certificate1019).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate679).dm (WitnessCertificates.Batch033.certificate679).beta (WitnessCertificates.Batch033.certificate679).L) ≤ (2*exp (-((CountingCertificates.Batch033.certificate679).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch084.certificate1019).exponent:ℝ)*st.R))/((WitnessCertificates.Batch033.certificate679).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch084.certificate1019 CountingCertificates.Batch033.certificate679 matches339 MergedCutGroups.Batch084.numericValid1019 MergedCutGroups.Batch084.cellsSound1019 MergedCutGroups.Batch084.cellsNumeric1019 MergedCutGroups.Batch084.populationMatches1019
    PopulationCertificates.Batch033.valid679 PopulationCertificates.Batch033.sound679 WitnessCertificates.Batch033.valid679 WitnessCertificates.Batch033.sound679 CountingCertificates.Batch033.valid679 CountingCertificates.Batch033.sound679 H st hI
theorem probabilityBound339 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch084.certificate1019).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch033.certificate679).dm (WitnessCertificates.Batch033.certificate679).beta (WitnessCertificates.Batch033.certificate679).L) ≤ ((CutFailureCertificates.Budget033.certificate679).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound679 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate679).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch084.certificate1019).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch033.certificate679).omega:ℝ)) ≤ ((CutFailureCertificates.Budget033.certificate679).bound:ℝ) at hb
  exact (exponentialBound339 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch016
