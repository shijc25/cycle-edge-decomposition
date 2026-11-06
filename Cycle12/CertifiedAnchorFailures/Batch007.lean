import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch014
import Cycle12.CountingCertificates.Batch015
import Cycle12.CutFailureCertificates.Budget014
import Cycle12.CutFailureCertificates.Budget015
import Cycle12.MergedCutGroups.Batch035
import Cycle12.MergedCutGroups.Batch036
import Cycle12.MergedCutGroups.Batch037
import Cycle12.MergedCutGroups.Batch038
import Cycle12.MergedCutGroups.Batch039
import Cycle12.PopulationCertificates.Batch014
import Cycle12.PopulationCertificates.Batch015
import Cycle12.WitnessCertificates.Batch014
import Cycle12.WitnessCertificates.Batch015

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedAnchorFailures.Batch007
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches140 : (MergedCutGroups.Batch035.certificate422).AnchorMatches CountingCertificates.Batch014.certificate281 := by decide +kernel
theorem exponentialBound140 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch035.certificate422).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate281).dm (WitnessCertificates.Batch014.certificate281).beta (WitnessCertificates.Batch014.certificate281).L) ≤ (2*exp (-((CountingCertificates.Batch014.certificate281).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch035.certificate422).exponent:ℝ)*st.R))/((WitnessCertificates.Batch014.certificate281).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch035.certificate422 CountingCertificates.Batch014.certificate281 matches140 MergedCutGroups.Batch035.numericValid422 MergedCutGroups.Batch035.cellsSound422 MergedCutGroups.Batch035.cellsNumeric422 MergedCutGroups.Batch035.populationMatches422
    PopulationCertificates.Batch014.valid281 PopulationCertificates.Batch014.sound281 WitnessCertificates.Batch014.valid281 WitnessCertificates.Batch014.sound281 CountingCertificates.Batch014.valid281 CountingCertificates.Batch014.sound281 H st hI
theorem probabilityBound140 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch035.certificate422).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate281).dm (WitnessCertificates.Batch014.certificate281).beta (WitnessCertificates.Batch014.certificate281).L) ≤ ((CutFailureCertificates.Budget014.certificate281).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound281 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate281).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch035.certificate422).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch014.certificate281).omega:ℝ)) ≤ ((CutFailureCertificates.Budget014.certificate281).bound:ℝ) at hb
  exact (exponentialBound140 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches141 : (MergedCutGroups.Batch035.certificate425).AnchorMatches CountingCertificates.Batch014.certificate283 := by decide +kernel
theorem exponentialBound141 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch035.certificate425).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate283).dm (WitnessCertificates.Batch014.certificate283).beta (WitnessCertificates.Batch014.certificate283).L) ≤ (2*exp (-((CountingCertificates.Batch014.certificate283).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch035.certificate425).exponent:ℝ)*st.R))/((WitnessCertificates.Batch014.certificate283).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch035.certificate425 CountingCertificates.Batch014.certificate283 matches141 MergedCutGroups.Batch035.numericValid425 MergedCutGroups.Batch035.cellsSound425 MergedCutGroups.Batch035.cellsNumeric425 MergedCutGroups.Batch035.populationMatches425
    PopulationCertificates.Batch014.valid283 PopulationCertificates.Batch014.sound283 WitnessCertificates.Batch014.valid283 WitnessCertificates.Batch014.sound283 CountingCertificates.Batch014.valid283 CountingCertificates.Batch014.sound283 H st hI
theorem probabilityBound141 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch035.certificate425).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate283).dm (WitnessCertificates.Batch014.certificate283).beta (WitnessCertificates.Batch014.certificate283).L) ≤ ((CutFailureCertificates.Budget014.certificate283).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound283 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate283).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch035.certificate425).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch014.certificate283).omega:ℝ)) ≤ ((CutFailureCertificates.Budget014.certificate283).bound:ℝ) at hb
  exact (exponentialBound141 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches142 : (MergedCutGroups.Batch035.certificate428).AnchorMatches CountingCertificates.Batch014.certificate285 := by decide +kernel
theorem exponentialBound142 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch035.certificate428).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate285).dm (WitnessCertificates.Batch014.certificate285).beta (WitnessCertificates.Batch014.certificate285).L) ≤ (2*exp (-((CountingCertificates.Batch014.certificate285).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch035.certificate428).exponent:ℝ)*st.R))/((WitnessCertificates.Batch014.certificate285).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch035.certificate428 CountingCertificates.Batch014.certificate285 matches142 MergedCutGroups.Batch035.numericValid428 MergedCutGroups.Batch035.cellsSound428 MergedCutGroups.Batch035.cellsNumeric428 MergedCutGroups.Batch035.populationMatches428
    PopulationCertificates.Batch014.valid285 PopulationCertificates.Batch014.sound285 WitnessCertificates.Batch014.valid285 WitnessCertificates.Batch014.sound285 CountingCertificates.Batch014.valid285 CountingCertificates.Batch014.sound285 H st hI
theorem probabilityBound142 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch035.certificate428).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate285).dm (WitnessCertificates.Batch014.certificate285).beta (WitnessCertificates.Batch014.certificate285).L) ≤ ((CutFailureCertificates.Budget014.certificate285).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound285 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate285).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch035.certificate428).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch014.certificate285).omega:ℝ)) ≤ ((CutFailureCertificates.Budget014.certificate285).bound:ℝ) at hb
  exact (exponentialBound142 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches143 : (MergedCutGroups.Batch035.certificate431).AnchorMatches CountingCertificates.Batch014.certificate287 := by decide +kernel
theorem exponentialBound143 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch035.certificate431).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate287).dm (WitnessCertificates.Batch014.certificate287).beta (WitnessCertificates.Batch014.certificate287).L) ≤ (2*exp (-((CountingCertificates.Batch014.certificate287).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch035.certificate431).exponent:ℝ)*st.R))/((WitnessCertificates.Batch014.certificate287).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch035.certificate431 CountingCertificates.Batch014.certificate287 matches143 MergedCutGroups.Batch035.numericValid431 MergedCutGroups.Batch035.cellsSound431 MergedCutGroups.Batch035.cellsNumeric431 MergedCutGroups.Batch035.populationMatches431
    PopulationCertificates.Batch014.valid287 PopulationCertificates.Batch014.sound287 WitnessCertificates.Batch014.valid287 WitnessCertificates.Batch014.sound287 CountingCertificates.Batch014.valid287 CountingCertificates.Batch014.sound287 H st hI
theorem probabilityBound143 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch035.certificate431).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate287).dm (WitnessCertificates.Batch014.certificate287).beta (WitnessCertificates.Batch014.certificate287).L) ≤ ((CutFailureCertificates.Budget014.certificate287).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound287 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate287).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch035.certificate431).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch014.certificate287).omega:ℝ)) ≤ ((CutFailureCertificates.Budget014.certificate287).bound:ℝ) at hb
  exact (exponentialBound143 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches144 : (MergedCutGroups.Batch036.certificate434).AnchorMatches CountingCertificates.Batch014.certificate289 := by decide +kernel
theorem exponentialBound144 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch036.certificate434).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate289).dm (WitnessCertificates.Batch014.certificate289).beta (WitnessCertificates.Batch014.certificate289).L) ≤ (2*exp (-((CountingCertificates.Batch014.certificate289).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch036.certificate434).exponent:ℝ)*st.R))/((WitnessCertificates.Batch014.certificate289).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch036.certificate434 CountingCertificates.Batch014.certificate289 matches144 MergedCutGroups.Batch036.numericValid434 MergedCutGroups.Batch036.cellsSound434 MergedCutGroups.Batch036.cellsNumeric434 MergedCutGroups.Batch036.populationMatches434
    PopulationCertificates.Batch014.valid289 PopulationCertificates.Batch014.sound289 WitnessCertificates.Batch014.valid289 WitnessCertificates.Batch014.sound289 CountingCertificates.Batch014.valid289 CountingCertificates.Batch014.sound289 H st hI
theorem probabilityBound144 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch036.certificate434).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate289).dm (WitnessCertificates.Batch014.certificate289).beta (WitnessCertificates.Batch014.certificate289).L) ≤ ((CutFailureCertificates.Budget014.certificate289).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound289 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate289).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch036.certificate434).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch014.certificate289).omega:ℝ)) ≤ ((CutFailureCertificates.Budget014.certificate289).bound:ℝ) at hb
  exact (exponentialBound144 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches145 : (MergedCutGroups.Batch036.certificate437).AnchorMatches CountingCertificates.Batch014.certificate291 := by decide +kernel
theorem exponentialBound145 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch036.certificate437).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate291).dm (WitnessCertificates.Batch014.certificate291).beta (WitnessCertificates.Batch014.certificate291).L) ≤ (2*exp (-((CountingCertificates.Batch014.certificate291).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch036.certificate437).exponent:ℝ)*st.R))/((WitnessCertificates.Batch014.certificate291).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch036.certificate437 CountingCertificates.Batch014.certificate291 matches145 MergedCutGroups.Batch036.numericValid437 MergedCutGroups.Batch036.cellsSound437 MergedCutGroups.Batch036.cellsNumeric437 MergedCutGroups.Batch036.populationMatches437
    PopulationCertificates.Batch014.valid291 PopulationCertificates.Batch014.sound291 WitnessCertificates.Batch014.valid291 WitnessCertificates.Batch014.sound291 CountingCertificates.Batch014.valid291 CountingCertificates.Batch014.sound291 H st hI
theorem probabilityBound145 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch036.certificate437).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate291).dm (WitnessCertificates.Batch014.certificate291).beta (WitnessCertificates.Batch014.certificate291).L) ≤ ((CutFailureCertificates.Budget014.certificate291).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound291 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate291).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch036.certificate437).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch014.certificate291).omega:ℝ)) ≤ ((CutFailureCertificates.Budget014.certificate291).bound:ℝ) at hb
  exact (exponentialBound145 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches146 : (MergedCutGroups.Batch036.certificate440).AnchorMatches CountingCertificates.Batch014.certificate293 := by decide +kernel
theorem exponentialBound146 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch036.certificate440).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate293).dm (WitnessCertificates.Batch014.certificate293).beta (WitnessCertificates.Batch014.certificate293).L) ≤ (2*exp (-((CountingCertificates.Batch014.certificate293).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch036.certificate440).exponent:ℝ)*st.R))/((WitnessCertificates.Batch014.certificate293).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch036.certificate440 CountingCertificates.Batch014.certificate293 matches146 MergedCutGroups.Batch036.numericValid440 MergedCutGroups.Batch036.cellsSound440 MergedCutGroups.Batch036.cellsNumeric440 MergedCutGroups.Batch036.populationMatches440
    PopulationCertificates.Batch014.valid293 PopulationCertificates.Batch014.sound293 WitnessCertificates.Batch014.valid293 WitnessCertificates.Batch014.sound293 CountingCertificates.Batch014.valid293 CountingCertificates.Batch014.sound293 H st hI
theorem probabilityBound146 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch036.certificate440).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate293).dm (WitnessCertificates.Batch014.certificate293).beta (WitnessCertificates.Batch014.certificate293).L) ≤ ((CutFailureCertificates.Budget014.certificate293).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound293 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate293).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch036.certificate440).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch014.certificate293).omega:ℝ)) ≤ ((CutFailureCertificates.Budget014.certificate293).bound:ℝ) at hb
  exact (exponentialBound146 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches147 : (MergedCutGroups.Batch036.certificate443).AnchorMatches CountingCertificates.Batch014.certificate295 := by decide +kernel
theorem exponentialBound147 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch036.certificate443).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate295).dm (WitnessCertificates.Batch014.certificate295).beta (WitnessCertificates.Batch014.certificate295).L) ≤ (2*exp (-((CountingCertificates.Batch014.certificate295).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch036.certificate443).exponent:ℝ)*st.R))/((WitnessCertificates.Batch014.certificate295).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch036.certificate443 CountingCertificates.Batch014.certificate295 matches147 MergedCutGroups.Batch036.numericValid443 MergedCutGroups.Batch036.cellsSound443 MergedCutGroups.Batch036.cellsNumeric443 MergedCutGroups.Batch036.populationMatches443
    PopulationCertificates.Batch014.valid295 PopulationCertificates.Batch014.sound295 WitnessCertificates.Batch014.valid295 WitnessCertificates.Batch014.sound295 CountingCertificates.Batch014.valid295 CountingCertificates.Batch014.sound295 H st hI
theorem probabilityBound147 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch036.certificate443).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate295).dm (WitnessCertificates.Batch014.certificate295).beta (WitnessCertificates.Batch014.certificate295).L) ≤ ((CutFailureCertificates.Budget014.certificate295).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound295 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate295).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch036.certificate443).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch014.certificate295).omega:ℝ)) ≤ ((CutFailureCertificates.Budget014.certificate295).bound:ℝ) at hb
  exact (exponentialBound147 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches148 : (MergedCutGroups.Batch037.certificate446).AnchorMatches CountingCertificates.Batch014.certificate297 := by decide +kernel
theorem exponentialBound148 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch037.certificate446).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate297).dm (WitnessCertificates.Batch014.certificate297).beta (WitnessCertificates.Batch014.certificate297).L) ≤ (2*exp (-((CountingCertificates.Batch014.certificate297).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch037.certificate446).exponent:ℝ)*st.R))/((WitnessCertificates.Batch014.certificate297).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch037.certificate446 CountingCertificates.Batch014.certificate297 matches148 MergedCutGroups.Batch037.numericValid446 MergedCutGroups.Batch037.cellsSound446 MergedCutGroups.Batch037.cellsNumeric446 MergedCutGroups.Batch037.populationMatches446
    PopulationCertificates.Batch014.valid297 PopulationCertificates.Batch014.sound297 WitnessCertificates.Batch014.valid297 WitnessCertificates.Batch014.sound297 CountingCertificates.Batch014.valid297 CountingCertificates.Batch014.sound297 H st hI
theorem probabilityBound148 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch037.certificate446).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate297).dm (WitnessCertificates.Batch014.certificate297).beta (WitnessCertificates.Batch014.certificate297).L) ≤ ((CutFailureCertificates.Budget014.certificate297).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound297 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate297).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch037.certificate446).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch014.certificate297).omega:ℝ)) ≤ ((CutFailureCertificates.Budget014.certificate297).bound:ℝ) at hb
  exact (exponentialBound148 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches149 : (MergedCutGroups.Batch037.certificate449).AnchorMatches CountingCertificates.Batch014.certificate299 := by decide +kernel
theorem exponentialBound149 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch037.certificate449).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate299).dm (WitnessCertificates.Batch014.certificate299).beta (WitnessCertificates.Batch014.certificate299).L) ≤ (2*exp (-((CountingCertificates.Batch014.certificate299).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch037.certificate449).exponent:ℝ)*st.R))/((WitnessCertificates.Batch014.certificate299).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch037.certificate449 CountingCertificates.Batch014.certificate299 matches149 MergedCutGroups.Batch037.numericValid449 MergedCutGroups.Batch037.cellsSound449 MergedCutGroups.Batch037.cellsNumeric449 MergedCutGroups.Batch037.populationMatches449
    PopulationCertificates.Batch014.valid299 PopulationCertificates.Batch014.sound299 WitnessCertificates.Batch014.valid299 WitnessCertificates.Batch014.sound299 CountingCertificates.Batch014.valid299 CountingCertificates.Batch014.sound299 H st hI
theorem probabilityBound149 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch037.certificate449).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch014.certificate299).dm (WitnessCertificates.Batch014.certificate299).beta (WitnessCertificates.Batch014.certificate299).L) ≤ ((CutFailureCertificates.Budget014.certificate299).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound299 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate299).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch037.certificate449).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch014.certificate299).omega:ℝ)) ≤ ((CutFailureCertificates.Budget014.certificate299).bound:ℝ) at hb
  exact (exponentialBound149 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches150 : (MergedCutGroups.Batch037.certificate452).AnchorMatches CountingCertificates.Batch015.certificate301 := by decide +kernel
theorem exponentialBound150 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch037.certificate452).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate301).dm (WitnessCertificates.Batch015.certificate301).beta (WitnessCertificates.Batch015.certificate301).L) ≤ (2*exp (-((CountingCertificates.Batch015.certificate301).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch037.certificate452).exponent:ℝ)*st.R))/((WitnessCertificates.Batch015.certificate301).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch037.certificate452 CountingCertificates.Batch015.certificate301 matches150 MergedCutGroups.Batch037.numericValid452 MergedCutGroups.Batch037.cellsSound452 MergedCutGroups.Batch037.cellsNumeric452 MergedCutGroups.Batch037.populationMatches452
    PopulationCertificates.Batch015.valid301 PopulationCertificates.Batch015.sound301 WitnessCertificates.Batch015.valid301 WitnessCertificates.Batch015.sound301 CountingCertificates.Batch015.valid301 CountingCertificates.Batch015.sound301 H st hI
theorem probabilityBound150 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch037.certificate452).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate301).dm (WitnessCertificates.Batch015.certificate301).beta (WitnessCertificates.Batch015.certificate301).L) ≤ ((CutFailureCertificates.Budget015.certificate301).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound301 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate301).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch037.certificate452).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch015.certificate301).omega:ℝ)) ≤ ((CutFailureCertificates.Budget015.certificate301).bound:ℝ) at hb
  exact (exponentialBound150 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches151 : (MergedCutGroups.Batch037.certificate455).AnchorMatches CountingCertificates.Batch015.certificate303 := by decide +kernel
theorem exponentialBound151 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch037.certificate455).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate303).dm (WitnessCertificates.Batch015.certificate303).beta (WitnessCertificates.Batch015.certificate303).L) ≤ (2*exp (-((CountingCertificates.Batch015.certificate303).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch037.certificate455).exponent:ℝ)*st.R))/((WitnessCertificates.Batch015.certificate303).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch037.certificate455 CountingCertificates.Batch015.certificate303 matches151 MergedCutGroups.Batch037.numericValid455 MergedCutGroups.Batch037.cellsSound455 MergedCutGroups.Batch037.cellsNumeric455 MergedCutGroups.Batch037.populationMatches455
    PopulationCertificates.Batch015.valid303 PopulationCertificates.Batch015.sound303 WitnessCertificates.Batch015.valid303 WitnessCertificates.Batch015.sound303 CountingCertificates.Batch015.valid303 CountingCertificates.Batch015.sound303 H st hI
theorem probabilityBound151 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch037.certificate455).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate303).dm (WitnessCertificates.Batch015.certificate303).beta (WitnessCertificates.Batch015.certificate303).L) ≤ ((CutFailureCertificates.Budget015.certificate303).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound303 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate303).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch037.certificate455).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch015.certificate303).omega:ℝ)) ≤ ((CutFailureCertificates.Budget015.certificate303).bound:ℝ) at hb
  exact (exponentialBound151 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches152 : (MergedCutGroups.Batch038.certificate458).AnchorMatches CountingCertificates.Batch015.certificate305 := by decide +kernel
theorem exponentialBound152 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch038.certificate458).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate305).dm (WitnessCertificates.Batch015.certificate305).beta (WitnessCertificates.Batch015.certificate305).L) ≤ (2*exp (-((CountingCertificates.Batch015.certificate305).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch038.certificate458).exponent:ℝ)*st.R))/((WitnessCertificates.Batch015.certificate305).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch038.certificate458 CountingCertificates.Batch015.certificate305 matches152 MergedCutGroups.Batch038.numericValid458 MergedCutGroups.Batch038.cellsSound458 MergedCutGroups.Batch038.cellsNumeric458 MergedCutGroups.Batch038.populationMatches458
    PopulationCertificates.Batch015.valid305 PopulationCertificates.Batch015.sound305 WitnessCertificates.Batch015.valid305 WitnessCertificates.Batch015.sound305 CountingCertificates.Batch015.valid305 CountingCertificates.Batch015.sound305 H st hI
theorem probabilityBound152 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch038.certificate458).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate305).dm (WitnessCertificates.Batch015.certificate305).beta (WitnessCertificates.Batch015.certificate305).L) ≤ ((CutFailureCertificates.Budget015.certificate305).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound305 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate305).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch038.certificate458).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch015.certificate305).omega:ℝ)) ≤ ((CutFailureCertificates.Budget015.certificate305).bound:ℝ) at hb
  exact (exponentialBound152 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches153 : (MergedCutGroups.Batch038.certificate461).AnchorMatches CountingCertificates.Batch015.certificate307 := by decide +kernel
theorem exponentialBound153 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch038.certificate461).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate307).dm (WitnessCertificates.Batch015.certificate307).beta (WitnessCertificates.Batch015.certificate307).L) ≤ (2*exp (-((CountingCertificates.Batch015.certificate307).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch038.certificate461).exponent:ℝ)*st.R))/((WitnessCertificates.Batch015.certificate307).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch038.certificate461 CountingCertificates.Batch015.certificate307 matches153 MergedCutGroups.Batch038.numericValid461 MergedCutGroups.Batch038.cellsSound461 MergedCutGroups.Batch038.cellsNumeric461 MergedCutGroups.Batch038.populationMatches461
    PopulationCertificates.Batch015.valid307 PopulationCertificates.Batch015.sound307 WitnessCertificates.Batch015.valid307 WitnessCertificates.Batch015.sound307 CountingCertificates.Batch015.valid307 CountingCertificates.Batch015.sound307 H st hI
theorem probabilityBound153 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch038.certificate461).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate307).dm (WitnessCertificates.Batch015.certificate307).beta (WitnessCertificates.Batch015.certificate307).L) ≤ ((CutFailureCertificates.Budget015.certificate307).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound307 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate307).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch038.certificate461).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch015.certificate307).omega:ℝ)) ≤ ((CutFailureCertificates.Budget015.certificate307).bound:ℝ) at hb
  exact (exponentialBound153 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches154 : (MergedCutGroups.Batch038.certificate464).AnchorMatches CountingCertificates.Batch015.certificate309 := by decide +kernel
theorem exponentialBound154 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch038.certificate464).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate309).dm (WitnessCertificates.Batch015.certificate309).beta (WitnessCertificates.Batch015.certificate309).L) ≤ (2*exp (-((CountingCertificates.Batch015.certificate309).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch038.certificate464).exponent:ℝ)*st.R))/((WitnessCertificates.Batch015.certificate309).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch038.certificate464 CountingCertificates.Batch015.certificate309 matches154 MergedCutGroups.Batch038.numericValid464 MergedCutGroups.Batch038.cellsSound464 MergedCutGroups.Batch038.cellsNumeric464 MergedCutGroups.Batch038.populationMatches464
    PopulationCertificates.Batch015.valid309 PopulationCertificates.Batch015.sound309 WitnessCertificates.Batch015.valid309 WitnessCertificates.Batch015.sound309 CountingCertificates.Batch015.valid309 CountingCertificates.Batch015.sound309 H st hI
theorem probabilityBound154 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch038.certificate464).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate309).dm (WitnessCertificates.Batch015.certificate309).beta (WitnessCertificates.Batch015.certificate309).L) ≤ ((CutFailureCertificates.Budget015.certificate309).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound309 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate309).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch038.certificate464).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch015.certificate309).omega:ℝ)) ≤ ((CutFailureCertificates.Budget015.certificate309).bound:ℝ) at hb
  exact (exponentialBound154 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches155 : (MergedCutGroups.Batch038.certificate467).AnchorMatches CountingCertificates.Batch015.certificate311 := by decide +kernel
theorem exponentialBound155 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch038.certificate467).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate311).dm (WitnessCertificates.Batch015.certificate311).beta (WitnessCertificates.Batch015.certificate311).L) ≤ (2*exp (-((CountingCertificates.Batch015.certificate311).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch038.certificate467).exponent:ℝ)*st.R))/((WitnessCertificates.Batch015.certificate311).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch038.certificate467 CountingCertificates.Batch015.certificate311 matches155 MergedCutGroups.Batch038.numericValid467 MergedCutGroups.Batch038.cellsSound467 MergedCutGroups.Batch038.cellsNumeric467 MergedCutGroups.Batch038.populationMatches467
    PopulationCertificates.Batch015.valid311 PopulationCertificates.Batch015.sound311 WitnessCertificates.Batch015.valid311 WitnessCertificates.Batch015.sound311 CountingCertificates.Batch015.valid311 CountingCertificates.Batch015.sound311 H st hI
theorem probabilityBound155 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch038.certificate467).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate311).dm (WitnessCertificates.Batch015.certificate311).beta (WitnessCertificates.Batch015.certificate311).L) ≤ ((CutFailureCertificates.Budget015.certificate311).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound311 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate311).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch038.certificate467).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch015.certificate311).omega:ℝ)) ≤ ((CutFailureCertificates.Budget015.certificate311).bound:ℝ) at hb
  exact (exponentialBound155 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches156 : (MergedCutGroups.Batch039.certificate470).AnchorMatches CountingCertificates.Batch015.certificate313 := by decide +kernel
theorem exponentialBound156 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch039.certificate470).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate313).dm (WitnessCertificates.Batch015.certificate313).beta (WitnessCertificates.Batch015.certificate313).L) ≤ (2*exp (-((CountingCertificates.Batch015.certificate313).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch039.certificate470).exponent:ℝ)*st.R))/((WitnessCertificates.Batch015.certificate313).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch039.certificate470 CountingCertificates.Batch015.certificate313 matches156 MergedCutGroups.Batch039.numericValid470 MergedCutGroups.Batch039.cellsSound470 MergedCutGroups.Batch039.cellsNumeric470 MergedCutGroups.Batch039.populationMatches470
    PopulationCertificates.Batch015.valid313 PopulationCertificates.Batch015.sound313 WitnessCertificates.Batch015.valid313 WitnessCertificates.Batch015.sound313 CountingCertificates.Batch015.valid313 CountingCertificates.Batch015.sound313 H st hI
theorem probabilityBound156 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch039.certificate470).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate313).dm (WitnessCertificates.Batch015.certificate313).beta (WitnessCertificates.Batch015.certificate313).L) ≤ ((CutFailureCertificates.Budget015.certificate313).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound313 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate313).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch039.certificate470).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch015.certificate313).omega:ℝ)) ≤ ((CutFailureCertificates.Budget015.certificate313).bound:ℝ) at hb
  exact (exponentialBound156 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches157 : (MergedCutGroups.Batch039.certificate473).AnchorMatches CountingCertificates.Batch015.certificate315 := by decide +kernel
theorem exponentialBound157 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch039.certificate473).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate315).dm (WitnessCertificates.Batch015.certificate315).beta (WitnessCertificates.Batch015.certificate315).L) ≤ (2*exp (-((CountingCertificates.Batch015.certificate315).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch039.certificate473).exponent:ℝ)*st.R))/((WitnessCertificates.Batch015.certificate315).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch039.certificate473 CountingCertificates.Batch015.certificate315 matches157 MergedCutGroups.Batch039.numericValid473 MergedCutGroups.Batch039.cellsSound473 MergedCutGroups.Batch039.cellsNumeric473 MergedCutGroups.Batch039.populationMatches473
    PopulationCertificates.Batch015.valid315 PopulationCertificates.Batch015.sound315 WitnessCertificates.Batch015.valid315 WitnessCertificates.Batch015.sound315 CountingCertificates.Batch015.valid315 CountingCertificates.Batch015.sound315 H st hI
theorem probabilityBound157 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch039.certificate473).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate315).dm (WitnessCertificates.Batch015.certificate315).beta (WitnessCertificates.Batch015.certificate315).L) ≤ ((CutFailureCertificates.Budget015.certificate315).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound315 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate315).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch039.certificate473).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch015.certificate315).omega:ℝ)) ≤ ((CutFailureCertificates.Budget015.certificate315).bound:ℝ) at hb
  exact (exponentialBound157 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches158 : (MergedCutGroups.Batch039.certificate476).AnchorMatches CountingCertificates.Batch015.certificate317 := by decide +kernel
theorem exponentialBound158 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch039.certificate476).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate317).dm (WitnessCertificates.Batch015.certificate317).beta (WitnessCertificates.Batch015.certificate317).L) ≤ (2*exp (-((CountingCertificates.Batch015.certificate317).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch039.certificate476).exponent:ℝ)*st.R))/((WitnessCertificates.Batch015.certificate317).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch039.certificate476 CountingCertificates.Batch015.certificate317 matches158 MergedCutGroups.Batch039.numericValid476 MergedCutGroups.Batch039.cellsSound476 MergedCutGroups.Batch039.cellsNumeric476 MergedCutGroups.Batch039.populationMatches476
    PopulationCertificates.Batch015.valid317 PopulationCertificates.Batch015.sound317 WitnessCertificates.Batch015.valid317 WitnessCertificates.Batch015.sound317 CountingCertificates.Batch015.valid317 CountingCertificates.Batch015.sound317 H st hI
theorem probabilityBound158 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch039.certificate476).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate317).dm (WitnessCertificates.Batch015.certificate317).beta (WitnessCertificates.Batch015.certificate317).L) ≤ ((CutFailureCertificates.Budget015.certificate317).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound317 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate317).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch039.certificate476).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch015.certificate317).omega:ℝ)) ≤ ((CutFailureCertificates.Budget015.certificate317).bound:ℝ) at hb
  exact (exponentialBound158 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches159 : (MergedCutGroups.Batch039.certificate479).AnchorMatches CountingCertificates.Batch015.certificate319 := by decide +kernel
theorem exponentialBound159 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch039.certificate479).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate319).dm (WitnessCertificates.Batch015.certificate319).beta (WitnessCertificates.Batch015.certificate319).L) ≤ (2*exp (-((CountingCertificates.Batch015.certificate319).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch039.certificate479).exponent:ℝ)*st.R))/((WitnessCertificates.Batch015.certificate319).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch039.certificate479 CountingCertificates.Batch015.certificate319 matches159 MergedCutGroups.Batch039.numericValid479 MergedCutGroups.Batch039.cellsSound479 MergedCutGroups.Batch039.cellsNumeric479 MergedCutGroups.Batch039.populationMatches479
    PopulationCertificates.Batch015.valid319 PopulationCertificates.Batch015.sound319 WitnessCertificates.Batch015.valid319 WitnessCertificates.Batch015.sound319 CountingCertificates.Batch015.valid319 CountingCertificates.Batch015.sound319 H st hI
theorem probabilityBound159 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch039.certificate479).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch015.certificate319).dm (WitnessCertificates.Batch015.certificate319).beta (WitnessCertificates.Batch015.certificate319).L) ≤ ((CutFailureCertificates.Budget015.certificate319).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound319 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate319).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch039.certificate479).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch015.certificate319).omega:ℝ)) ≤ ((CutFailureCertificates.Budget015.certificate319).bound:ℝ) at hb
  exact (exponentialBound159 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch007
