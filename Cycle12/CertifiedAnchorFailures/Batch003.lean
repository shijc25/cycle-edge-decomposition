import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch006
import Cycle12.CountingCertificates.Batch007
import Cycle12.CutFailureCertificates.Budget006
import Cycle12.CutFailureCertificates.Budget007
import Cycle12.MergedCutGroups.Batch015
import Cycle12.MergedCutGroups.Batch016
import Cycle12.MergedCutGroups.Batch017
import Cycle12.MergedCutGroups.Batch018
import Cycle12.MergedCutGroups.Batch019
import Cycle12.PopulationCertificates.Batch006
import Cycle12.PopulationCertificates.Batch007
import Cycle12.WitnessCertificates.Batch006
import Cycle12.WitnessCertificates.Batch007

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedAnchorFailures.Batch003
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches60 : (MergedCutGroups.Batch015.certificate182).AnchorMatches CountingCertificates.Batch006.certificate121 := by decide +kernel
theorem exponentialBound60 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch015.certificate182).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate121).dm (WitnessCertificates.Batch006.certificate121).beta (WitnessCertificates.Batch006.certificate121).L) ≤ (2*exp (-((CountingCertificates.Batch006.certificate121).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch015.certificate182).exponent:ℝ)*st.R))/((WitnessCertificates.Batch006.certificate121).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch015.certificate182 CountingCertificates.Batch006.certificate121 matches60 MergedCutGroups.Batch015.numericValid182 MergedCutGroups.Batch015.cellsSound182 MergedCutGroups.Batch015.cellsNumeric182 MergedCutGroups.Batch015.populationMatches182
    PopulationCertificates.Batch006.valid121 PopulationCertificates.Batch006.sound121 WitnessCertificates.Batch006.valid121 WitnessCertificates.Batch006.sound121 CountingCertificates.Batch006.valid121 CountingCertificates.Batch006.sound121 H st hI
theorem probabilityBound60 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch015.certificate182).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate121).dm (WitnessCertificates.Batch006.certificate121).beta (WitnessCertificates.Batch006.certificate121).L) ≤ ((CutFailureCertificates.Budget006.certificate121).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound121 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate121).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch015.certificate182).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch006.certificate121).omega:ℝ)) ≤ ((CutFailureCertificates.Budget006.certificate121).bound:ℝ) at hb
  exact (exponentialBound60 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches61 : (MergedCutGroups.Batch015.certificate185).AnchorMatches CountingCertificates.Batch006.certificate123 := by decide +kernel
theorem exponentialBound61 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch015.certificate185).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate123).dm (WitnessCertificates.Batch006.certificate123).beta (WitnessCertificates.Batch006.certificate123).L) ≤ (2*exp (-((CountingCertificates.Batch006.certificate123).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch015.certificate185).exponent:ℝ)*st.R))/((WitnessCertificates.Batch006.certificate123).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch015.certificate185 CountingCertificates.Batch006.certificate123 matches61 MergedCutGroups.Batch015.numericValid185 MergedCutGroups.Batch015.cellsSound185 MergedCutGroups.Batch015.cellsNumeric185 MergedCutGroups.Batch015.populationMatches185
    PopulationCertificates.Batch006.valid123 PopulationCertificates.Batch006.sound123 WitnessCertificates.Batch006.valid123 WitnessCertificates.Batch006.sound123 CountingCertificates.Batch006.valid123 CountingCertificates.Batch006.sound123 H st hI
theorem probabilityBound61 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch015.certificate185).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate123).dm (WitnessCertificates.Batch006.certificate123).beta (WitnessCertificates.Batch006.certificate123).L) ≤ ((CutFailureCertificates.Budget006.certificate123).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound123 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate123).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch015.certificate185).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch006.certificate123).omega:ℝ)) ≤ ((CutFailureCertificates.Budget006.certificate123).bound:ℝ) at hb
  exact (exponentialBound61 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches62 : (MergedCutGroups.Batch015.certificate188).AnchorMatches CountingCertificates.Batch006.certificate125 := by decide +kernel
theorem exponentialBound62 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch015.certificate188).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate125).dm (WitnessCertificates.Batch006.certificate125).beta (WitnessCertificates.Batch006.certificate125).L) ≤ (2*exp (-((CountingCertificates.Batch006.certificate125).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch015.certificate188).exponent:ℝ)*st.R))/((WitnessCertificates.Batch006.certificate125).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch015.certificate188 CountingCertificates.Batch006.certificate125 matches62 MergedCutGroups.Batch015.numericValid188 MergedCutGroups.Batch015.cellsSound188 MergedCutGroups.Batch015.cellsNumeric188 MergedCutGroups.Batch015.populationMatches188
    PopulationCertificates.Batch006.valid125 PopulationCertificates.Batch006.sound125 WitnessCertificates.Batch006.valid125 WitnessCertificates.Batch006.sound125 CountingCertificates.Batch006.valid125 CountingCertificates.Batch006.sound125 H st hI
theorem probabilityBound62 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch015.certificate188).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate125).dm (WitnessCertificates.Batch006.certificate125).beta (WitnessCertificates.Batch006.certificate125).L) ≤ ((CutFailureCertificates.Budget006.certificate125).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound125 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate125).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch015.certificate188).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch006.certificate125).omega:ℝ)) ≤ ((CutFailureCertificates.Budget006.certificate125).bound:ℝ) at hb
  exact (exponentialBound62 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches63 : (MergedCutGroups.Batch015.certificate191).AnchorMatches CountingCertificates.Batch006.certificate127 := by decide +kernel
theorem exponentialBound63 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch015.certificate191).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate127).dm (WitnessCertificates.Batch006.certificate127).beta (WitnessCertificates.Batch006.certificate127).L) ≤ (2*exp (-((CountingCertificates.Batch006.certificate127).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch015.certificate191).exponent:ℝ)*st.R))/((WitnessCertificates.Batch006.certificate127).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch015.certificate191 CountingCertificates.Batch006.certificate127 matches63 MergedCutGroups.Batch015.numericValid191 MergedCutGroups.Batch015.cellsSound191 MergedCutGroups.Batch015.cellsNumeric191 MergedCutGroups.Batch015.populationMatches191
    PopulationCertificates.Batch006.valid127 PopulationCertificates.Batch006.sound127 WitnessCertificates.Batch006.valid127 WitnessCertificates.Batch006.sound127 CountingCertificates.Batch006.valid127 CountingCertificates.Batch006.sound127 H st hI
theorem probabilityBound63 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch015.certificate191).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate127).dm (WitnessCertificates.Batch006.certificate127).beta (WitnessCertificates.Batch006.certificate127).L) ≤ ((CutFailureCertificates.Budget006.certificate127).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound127 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate127).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch015.certificate191).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch006.certificate127).omega:ℝ)) ≤ ((CutFailureCertificates.Budget006.certificate127).bound:ℝ) at hb
  exact (exponentialBound63 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches64 : (MergedCutGroups.Batch016.certificate194).AnchorMatches CountingCertificates.Batch006.certificate129 := by decide +kernel
theorem exponentialBound64 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch016.certificate194).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate129).dm (WitnessCertificates.Batch006.certificate129).beta (WitnessCertificates.Batch006.certificate129).L) ≤ (2*exp (-((CountingCertificates.Batch006.certificate129).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch016.certificate194).exponent:ℝ)*st.R))/((WitnessCertificates.Batch006.certificate129).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch016.certificate194 CountingCertificates.Batch006.certificate129 matches64 MergedCutGroups.Batch016.numericValid194 MergedCutGroups.Batch016.cellsSound194 MergedCutGroups.Batch016.cellsNumeric194 MergedCutGroups.Batch016.populationMatches194
    PopulationCertificates.Batch006.valid129 PopulationCertificates.Batch006.sound129 WitnessCertificates.Batch006.valid129 WitnessCertificates.Batch006.sound129 CountingCertificates.Batch006.valid129 CountingCertificates.Batch006.sound129 H st hI
theorem probabilityBound64 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch016.certificate194).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate129).dm (WitnessCertificates.Batch006.certificate129).beta (WitnessCertificates.Batch006.certificate129).L) ≤ ((CutFailureCertificates.Budget006.certificate129).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound129 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate129).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch016.certificate194).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch006.certificate129).omega:ℝ)) ≤ ((CutFailureCertificates.Budget006.certificate129).bound:ℝ) at hb
  exact (exponentialBound64 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches65 : (MergedCutGroups.Batch016.certificate197).AnchorMatches CountingCertificates.Batch006.certificate131 := by decide +kernel
theorem exponentialBound65 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch016.certificate197).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate131).dm (WitnessCertificates.Batch006.certificate131).beta (WitnessCertificates.Batch006.certificate131).L) ≤ (2*exp (-((CountingCertificates.Batch006.certificate131).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch016.certificate197).exponent:ℝ)*st.R))/((WitnessCertificates.Batch006.certificate131).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch016.certificate197 CountingCertificates.Batch006.certificate131 matches65 MergedCutGroups.Batch016.numericValid197 MergedCutGroups.Batch016.cellsSound197 MergedCutGroups.Batch016.cellsNumeric197 MergedCutGroups.Batch016.populationMatches197
    PopulationCertificates.Batch006.valid131 PopulationCertificates.Batch006.sound131 WitnessCertificates.Batch006.valid131 WitnessCertificates.Batch006.sound131 CountingCertificates.Batch006.valid131 CountingCertificates.Batch006.sound131 H st hI
theorem probabilityBound65 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch016.certificate197).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate131).dm (WitnessCertificates.Batch006.certificate131).beta (WitnessCertificates.Batch006.certificate131).L) ≤ ((CutFailureCertificates.Budget006.certificate131).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound131 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate131).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch016.certificate197).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch006.certificate131).omega:ℝ)) ≤ ((CutFailureCertificates.Budget006.certificate131).bound:ℝ) at hb
  exact (exponentialBound65 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches66 : (MergedCutGroups.Batch016.certificate200).AnchorMatches CountingCertificates.Batch006.certificate133 := by decide +kernel
theorem exponentialBound66 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch016.certificate200).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate133).dm (WitnessCertificates.Batch006.certificate133).beta (WitnessCertificates.Batch006.certificate133).L) ≤ (2*exp (-((CountingCertificates.Batch006.certificate133).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch016.certificate200).exponent:ℝ)*st.R))/((WitnessCertificates.Batch006.certificate133).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch016.certificate200 CountingCertificates.Batch006.certificate133 matches66 MergedCutGroups.Batch016.numericValid200 MergedCutGroups.Batch016.cellsSound200 MergedCutGroups.Batch016.cellsNumeric200 MergedCutGroups.Batch016.populationMatches200
    PopulationCertificates.Batch006.valid133 PopulationCertificates.Batch006.sound133 WitnessCertificates.Batch006.valid133 WitnessCertificates.Batch006.sound133 CountingCertificates.Batch006.valid133 CountingCertificates.Batch006.sound133 H st hI
theorem probabilityBound66 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch016.certificate200).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate133).dm (WitnessCertificates.Batch006.certificate133).beta (WitnessCertificates.Batch006.certificate133).L) ≤ ((CutFailureCertificates.Budget006.certificate133).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound133 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate133).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch016.certificate200).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch006.certificate133).omega:ℝ)) ≤ ((CutFailureCertificates.Budget006.certificate133).bound:ℝ) at hb
  exact (exponentialBound66 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches67 : (MergedCutGroups.Batch016.certificate203).AnchorMatches CountingCertificates.Batch006.certificate135 := by decide +kernel
theorem exponentialBound67 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch016.certificate203).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate135).dm (WitnessCertificates.Batch006.certificate135).beta (WitnessCertificates.Batch006.certificate135).L) ≤ (2*exp (-((CountingCertificates.Batch006.certificate135).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch016.certificate203).exponent:ℝ)*st.R))/((WitnessCertificates.Batch006.certificate135).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch016.certificate203 CountingCertificates.Batch006.certificate135 matches67 MergedCutGroups.Batch016.numericValid203 MergedCutGroups.Batch016.cellsSound203 MergedCutGroups.Batch016.cellsNumeric203 MergedCutGroups.Batch016.populationMatches203
    PopulationCertificates.Batch006.valid135 PopulationCertificates.Batch006.sound135 WitnessCertificates.Batch006.valid135 WitnessCertificates.Batch006.sound135 CountingCertificates.Batch006.valid135 CountingCertificates.Batch006.sound135 H st hI
theorem probabilityBound67 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch016.certificate203).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate135).dm (WitnessCertificates.Batch006.certificate135).beta (WitnessCertificates.Batch006.certificate135).L) ≤ ((CutFailureCertificates.Budget006.certificate135).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound135 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate135).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch016.certificate203).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch006.certificate135).omega:ℝ)) ≤ ((CutFailureCertificates.Budget006.certificate135).bound:ℝ) at hb
  exact (exponentialBound67 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches68 : (MergedCutGroups.Batch017.certificate206).AnchorMatches CountingCertificates.Batch006.certificate137 := by decide +kernel
theorem exponentialBound68 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch017.certificate206).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate137).dm (WitnessCertificates.Batch006.certificate137).beta (WitnessCertificates.Batch006.certificate137).L) ≤ (2*exp (-((CountingCertificates.Batch006.certificate137).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch017.certificate206).exponent:ℝ)*st.R))/((WitnessCertificates.Batch006.certificate137).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch017.certificate206 CountingCertificates.Batch006.certificate137 matches68 MergedCutGroups.Batch017.numericValid206 MergedCutGroups.Batch017.cellsSound206 MergedCutGroups.Batch017.cellsNumeric206 MergedCutGroups.Batch017.populationMatches206
    PopulationCertificates.Batch006.valid137 PopulationCertificates.Batch006.sound137 WitnessCertificates.Batch006.valid137 WitnessCertificates.Batch006.sound137 CountingCertificates.Batch006.valid137 CountingCertificates.Batch006.sound137 H st hI
theorem probabilityBound68 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch017.certificate206).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate137).dm (WitnessCertificates.Batch006.certificate137).beta (WitnessCertificates.Batch006.certificate137).L) ≤ ((CutFailureCertificates.Budget006.certificate137).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound137 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate137).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch017.certificate206).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch006.certificate137).omega:ℝ)) ≤ ((CutFailureCertificates.Budget006.certificate137).bound:ℝ) at hb
  exact (exponentialBound68 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches69 : (MergedCutGroups.Batch017.certificate209).AnchorMatches CountingCertificates.Batch006.certificate139 := by decide +kernel
theorem exponentialBound69 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch017.certificate209).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate139).dm (WitnessCertificates.Batch006.certificate139).beta (WitnessCertificates.Batch006.certificate139).L) ≤ (2*exp (-((CountingCertificates.Batch006.certificate139).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch017.certificate209).exponent:ℝ)*st.R))/((WitnessCertificates.Batch006.certificate139).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch017.certificate209 CountingCertificates.Batch006.certificate139 matches69 MergedCutGroups.Batch017.numericValid209 MergedCutGroups.Batch017.cellsSound209 MergedCutGroups.Batch017.cellsNumeric209 MergedCutGroups.Batch017.populationMatches209
    PopulationCertificates.Batch006.valid139 PopulationCertificates.Batch006.sound139 WitnessCertificates.Batch006.valid139 WitnessCertificates.Batch006.sound139 CountingCertificates.Batch006.valid139 CountingCertificates.Batch006.sound139 H st hI
theorem probabilityBound69 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch017.certificate209).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch006.certificate139).dm (WitnessCertificates.Batch006.certificate139).beta (WitnessCertificates.Batch006.certificate139).L) ≤ ((CutFailureCertificates.Budget006.certificate139).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound139 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate139).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch017.certificate209).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch006.certificate139).omega:ℝ)) ≤ ((CutFailureCertificates.Budget006.certificate139).bound:ℝ) at hb
  exact (exponentialBound69 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches70 : (MergedCutGroups.Batch017.certificate212).AnchorMatches CountingCertificates.Batch007.certificate141 := by decide +kernel
theorem exponentialBound70 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch017.certificate212).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate141).dm (WitnessCertificates.Batch007.certificate141).beta (WitnessCertificates.Batch007.certificate141).L) ≤ (2*exp (-((CountingCertificates.Batch007.certificate141).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch017.certificate212).exponent:ℝ)*st.R))/((WitnessCertificates.Batch007.certificate141).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch017.certificate212 CountingCertificates.Batch007.certificate141 matches70 MergedCutGroups.Batch017.numericValid212 MergedCutGroups.Batch017.cellsSound212 MergedCutGroups.Batch017.cellsNumeric212 MergedCutGroups.Batch017.populationMatches212
    PopulationCertificates.Batch007.valid141 PopulationCertificates.Batch007.sound141 WitnessCertificates.Batch007.valid141 WitnessCertificates.Batch007.sound141 CountingCertificates.Batch007.valid141 CountingCertificates.Batch007.sound141 H st hI
theorem probabilityBound70 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch017.certificate212).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate141).dm (WitnessCertificates.Batch007.certificate141).beta (WitnessCertificates.Batch007.certificate141).L) ≤ ((CutFailureCertificates.Budget007.certificate141).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound141 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate141).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch017.certificate212).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch007.certificate141).omega:ℝ)) ≤ ((CutFailureCertificates.Budget007.certificate141).bound:ℝ) at hb
  exact (exponentialBound70 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches71 : (MergedCutGroups.Batch017.certificate215).AnchorMatches CountingCertificates.Batch007.certificate143 := by decide +kernel
theorem exponentialBound71 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch017.certificate215).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate143).dm (WitnessCertificates.Batch007.certificate143).beta (WitnessCertificates.Batch007.certificate143).L) ≤ (2*exp (-((CountingCertificates.Batch007.certificate143).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch017.certificate215).exponent:ℝ)*st.R))/((WitnessCertificates.Batch007.certificate143).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch017.certificate215 CountingCertificates.Batch007.certificate143 matches71 MergedCutGroups.Batch017.numericValid215 MergedCutGroups.Batch017.cellsSound215 MergedCutGroups.Batch017.cellsNumeric215 MergedCutGroups.Batch017.populationMatches215
    PopulationCertificates.Batch007.valid143 PopulationCertificates.Batch007.sound143 WitnessCertificates.Batch007.valid143 WitnessCertificates.Batch007.sound143 CountingCertificates.Batch007.valid143 CountingCertificates.Batch007.sound143 H st hI
theorem probabilityBound71 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch017.certificate215).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate143).dm (WitnessCertificates.Batch007.certificate143).beta (WitnessCertificates.Batch007.certificate143).L) ≤ ((CutFailureCertificates.Budget007.certificate143).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound143 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate143).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch017.certificate215).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch007.certificate143).omega:ℝ)) ≤ ((CutFailureCertificates.Budget007.certificate143).bound:ℝ) at hb
  exact (exponentialBound71 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches72 : (MergedCutGroups.Batch018.certificate218).AnchorMatches CountingCertificates.Batch007.certificate145 := by decide +kernel
theorem exponentialBound72 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch018.certificate218).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate145).dm (WitnessCertificates.Batch007.certificate145).beta (WitnessCertificates.Batch007.certificate145).L) ≤ (2*exp (-((CountingCertificates.Batch007.certificate145).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch018.certificate218).exponent:ℝ)*st.R))/((WitnessCertificates.Batch007.certificate145).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch018.certificate218 CountingCertificates.Batch007.certificate145 matches72 MergedCutGroups.Batch018.numericValid218 MergedCutGroups.Batch018.cellsSound218 MergedCutGroups.Batch018.cellsNumeric218 MergedCutGroups.Batch018.populationMatches218
    PopulationCertificates.Batch007.valid145 PopulationCertificates.Batch007.sound145 WitnessCertificates.Batch007.valid145 WitnessCertificates.Batch007.sound145 CountingCertificates.Batch007.valid145 CountingCertificates.Batch007.sound145 H st hI
theorem probabilityBound72 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch018.certificate218).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate145).dm (WitnessCertificates.Batch007.certificate145).beta (WitnessCertificates.Batch007.certificate145).L) ≤ ((CutFailureCertificates.Budget007.certificate145).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound145 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate145).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch018.certificate218).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch007.certificate145).omega:ℝ)) ≤ ((CutFailureCertificates.Budget007.certificate145).bound:ℝ) at hb
  exact (exponentialBound72 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches73 : (MergedCutGroups.Batch018.certificate221).AnchorMatches CountingCertificates.Batch007.certificate147 := by decide +kernel
theorem exponentialBound73 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch018.certificate221).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate147).dm (WitnessCertificates.Batch007.certificate147).beta (WitnessCertificates.Batch007.certificate147).L) ≤ (2*exp (-((CountingCertificates.Batch007.certificate147).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch018.certificate221).exponent:ℝ)*st.R))/((WitnessCertificates.Batch007.certificate147).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch018.certificate221 CountingCertificates.Batch007.certificate147 matches73 MergedCutGroups.Batch018.numericValid221 MergedCutGroups.Batch018.cellsSound221 MergedCutGroups.Batch018.cellsNumeric221 MergedCutGroups.Batch018.populationMatches221
    PopulationCertificates.Batch007.valid147 PopulationCertificates.Batch007.sound147 WitnessCertificates.Batch007.valid147 WitnessCertificates.Batch007.sound147 CountingCertificates.Batch007.valid147 CountingCertificates.Batch007.sound147 H st hI
theorem probabilityBound73 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch018.certificate221).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate147).dm (WitnessCertificates.Batch007.certificate147).beta (WitnessCertificates.Batch007.certificate147).L) ≤ ((CutFailureCertificates.Budget007.certificate147).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound147 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate147).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch018.certificate221).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch007.certificate147).omega:ℝ)) ≤ ((CutFailureCertificates.Budget007.certificate147).bound:ℝ) at hb
  exact (exponentialBound73 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches74 : (MergedCutGroups.Batch018.certificate224).AnchorMatches CountingCertificates.Batch007.certificate149 := by decide +kernel
theorem exponentialBound74 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch018.certificate224).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate149).dm (WitnessCertificates.Batch007.certificate149).beta (WitnessCertificates.Batch007.certificate149).L) ≤ (2*exp (-((CountingCertificates.Batch007.certificate149).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch018.certificate224).exponent:ℝ)*st.R))/((WitnessCertificates.Batch007.certificate149).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch018.certificate224 CountingCertificates.Batch007.certificate149 matches74 MergedCutGroups.Batch018.numericValid224 MergedCutGroups.Batch018.cellsSound224 MergedCutGroups.Batch018.cellsNumeric224 MergedCutGroups.Batch018.populationMatches224
    PopulationCertificates.Batch007.valid149 PopulationCertificates.Batch007.sound149 WitnessCertificates.Batch007.valid149 WitnessCertificates.Batch007.sound149 CountingCertificates.Batch007.valid149 CountingCertificates.Batch007.sound149 H st hI
theorem probabilityBound74 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch018.certificate224).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate149).dm (WitnessCertificates.Batch007.certificate149).beta (WitnessCertificates.Batch007.certificate149).L) ≤ ((CutFailureCertificates.Budget007.certificate149).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound149 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate149).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch018.certificate224).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch007.certificate149).omega:ℝ)) ≤ ((CutFailureCertificates.Budget007.certificate149).bound:ℝ) at hb
  exact (exponentialBound74 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches75 : (MergedCutGroups.Batch018.certificate227).AnchorMatches CountingCertificates.Batch007.certificate151 := by decide +kernel
theorem exponentialBound75 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch018.certificate227).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate151).dm (WitnessCertificates.Batch007.certificate151).beta (WitnessCertificates.Batch007.certificate151).L) ≤ (2*exp (-((CountingCertificates.Batch007.certificate151).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch018.certificate227).exponent:ℝ)*st.R))/((WitnessCertificates.Batch007.certificate151).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch018.certificate227 CountingCertificates.Batch007.certificate151 matches75 MergedCutGroups.Batch018.numericValid227 MergedCutGroups.Batch018.cellsSound227 MergedCutGroups.Batch018.cellsNumeric227 MergedCutGroups.Batch018.populationMatches227
    PopulationCertificates.Batch007.valid151 PopulationCertificates.Batch007.sound151 WitnessCertificates.Batch007.valid151 WitnessCertificates.Batch007.sound151 CountingCertificates.Batch007.valid151 CountingCertificates.Batch007.sound151 H st hI
theorem probabilityBound75 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch018.certificate227).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate151).dm (WitnessCertificates.Batch007.certificate151).beta (WitnessCertificates.Batch007.certificate151).L) ≤ ((CutFailureCertificates.Budget007.certificate151).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound151 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate151).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch018.certificate227).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch007.certificate151).omega:ℝ)) ≤ ((CutFailureCertificates.Budget007.certificate151).bound:ℝ) at hb
  exact (exponentialBound75 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches76 : (MergedCutGroups.Batch019.certificate230).AnchorMatches CountingCertificates.Batch007.certificate153 := by decide +kernel
theorem exponentialBound76 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch019.certificate230).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate153).dm (WitnessCertificates.Batch007.certificate153).beta (WitnessCertificates.Batch007.certificate153).L) ≤ (2*exp (-((CountingCertificates.Batch007.certificate153).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch019.certificate230).exponent:ℝ)*st.R))/((WitnessCertificates.Batch007.certificate153).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch019.certificate230 CountingCertificates.Batch007.certificate153 matches76 MergedCutGroups.Batch019.numericValid230 MergedCutGroups.Batch019.cellsSound230 MergedCutGroups.Batch019.cellsNumeric230 MergedCutGroups.Batch019.populationMatches230
    PopulationCertificates.Batch007.valid153 PopulationCertificates.Batch007.sound153 WitnessCertificates.Batch007.valid153 WitnessCertificates.Batch007.sound153 CountingCertificates.Batch007.valid153 CountingCertificates.Batch007.sound153 H st hI
theorem probabilityBound76 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch019.certificate230).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate153).dm (WitnessCertificates.Batch007.certificate153).beta (WitnessCertificates.Batch007.certificate153).L) ≤ ((CutFailureCertificates.Budget007.certificate153).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound153 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate153).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch019.certificate230).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch007.certificate153).omega:ℝ)) ≤ ((CutFailureCertificates.Budget007.certificate153).bound:ℝ) at hb
  exact (exponentialBound76 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches77 : (MergedCutGroups.Batch019.certificate233).AnchorMatches CountingCertificates.Batch007.certificate155 := by decide +kernel
theorem exponentialBound77 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch019.certificate233).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate155).dm (WitnessCertificates.Batch007.certificate155).beta (WitnessCertificates.Batch007.certificate155).L) ≤ (2*exp (-((CountingCertificates.Batch007.certificate155).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch019.certificate233).exponent:ℝ)*st.R))/((WitnessCertificates.Batch007.certificate155).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch019.certificate233 CountingCertificates.Batch007.certificate155 matches77 MergedCutGroups.Batch019.numericValid233 MergedCutGroups.Batch019.cellsSound233 MergedCutGroups.Batch019.cellsNumeric233 MergedCutGroups.Batch019.populationMatches233
    PopulationCertificates.Batch007.valid155 PopulationCertificates.Batch007.sound155 WitnessCertificates.Batch007.valid155 WitnessCertificates.Batch007.sound155 CountingCertificates.Batch007.valid155 CountingCertificates.Batch007.sound155 H st hI
theorem probabilityBound77 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch019.certificate233).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate155).dm (WitnessCertificates.Batch007.certificate155).beta (WitnessCertificates.Batch007.certificate155).L) ≤ ((CutFailureCertificates.Budget007.certificate155).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound155 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate155).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch019.certificate233).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch007.certificate155).omega:ℝ)) ≤ ((CutFailureCertificates.Budget007.certificate155).bound:ℝ) at hb
  exact (exponentialBound77 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches78 : (MergedCutGroups.Batch019.certificate236).AnchorMatches CountingCertificates.Batch007.certificate157 := by decide +kernel
theorem exponentialBound78 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch019.certificate236).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate157).dm (WitnessCertificates.Batch007.certificate157).beta (WitnessCertificates.Batch007.certificate157).L) ≤ (2*exp (-((CountingCertificates.Batch007.certificate157).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch019.certificate236).exponent:ℝ)*st.R))/((WitnessCertificates.Batch007.certificate157).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch019.certificate236 CountingCertificates.Batch007.certificate157 matches78 MergedCutGroups.Batch019.numericValid236 MergedCutGroups.Batch019.cellsSound236 MergedCutGroups.Batch019.cellsNumeric236 MergedCutGroups.Batch019.populationMatches236
    PopulationCertificates.Batch007.valid157 PopulationCertificates.Batch007.sound157 WitnessCertificates.Batch007.valid157 WitnessCertificates.Batch007.sound157 CountingCertificates.Batch007.valid157 CountingCertificates.Batch007.sound157 H st hI
theorem probabilityBound78 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch019.certificate236).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate157).dm (WitnessCertificates.Batch007.certificate157).beta (WitnessCertificates.Batch007.certificate157).L) ≤ ((CutFailureCertificates.Budget007.certificate157).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound157 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate157).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch019.certificate236).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch007.certificate157).omega:ℝ)) ≤ ((CutFailureCertificates.Budget007.certificate157).bound:ℝ) at hb
  exact (exponentialBound78 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches79 : (MergedCutGroups.Batch019.certificate239).AnchorMatches CountingCertificates.Batch007.certificate159 := by decide +kernel
theorem exponentialBound79 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch019.certificate239).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate159).dm (WitnessCertificates.Batch007.certificate159).beta (WitnessCertificates.Batch007.certificate159).L) ≤ (2*exp (-((CountingCertificates.Batch007.certificate159).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch019.certificate239).exponent:ℝ)*st.R))/((WitnessCertificates.Batch007.certificate159).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch019.certificate239 CountingCertificates.Batch007.certificate159 matches79 MergedCutGroups.Batch019.numericValid239 MergedCutGroups.Batch019.cellsSound239 MergedCutGroups.Batch019.cellsNumeric239 MergedCutGroups.Batch019.populationMatches239
    PopulationCertificates.Batch007.valid159 PopulationCertificates.Batch007.sound159 WitnessCertificates.Batch007.valid159 WitnessCertificates.Batch007.sound159 CountingCertificates.Batch007.valid159 CountingCertificates.Batch007.sound159 H st hI
theorem probabilityBound79 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch019.certificate239).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch007.certificate159).dm (WitnessCertificates.Batch007.certificate159).beta (WitnessCertificates.Batch007.certificate159).L) ≤ ((CutFailureCertificates.Budget007.certificate159).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound159 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate159).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch019.certificate239).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch007.certificate159).omega:ℝ)) ≤ ((CutFailureCertificates.Budget007.certificate159).bound:ℝ) at hb
  exact (exponentialBound79 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch003
