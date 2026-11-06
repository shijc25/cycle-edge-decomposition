import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch026
import Cycle12.CountingCertificates.Batch027
import Cycle12.CutFailureCertificates.Budget026
import Cycle12.CutFailureCertificates.Budget027
import Cycle12.CutLabelCertificates.Entropy013
import Cycle12.CutLabelCertificates.Entropy014
import Cycle12.CutLabelCertificates.Minority013
import Cycle12.MergedCutGroups.Batch065
import Cycle12.MergedCutGroups.Batch066
import Cycle12.MergedCutGroups.Batch067
import Cycle12.MergedCutGroups.Batch068
import Cycle12.MergedCutGroups.Batch069
import Cycle12.PopulationCertificates.Batch026
import Cycle12.PopulationCertificates.Batch027
import Cycle12.WitnessCertificates.Batch026
import Cycle12.WitnessCertificates.Batch027

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch013
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches260 : (MergedCutGroups.Batch065.certificate780).GlobalMatches MergedCutGroups.Batch065.certificate781 CountingCertificates.Batch026.certificate520 CutLabelCertificates.Entropy013.certificate261 CutLabelCertificates.Minority013.certificate260 := by decide +kernel
theorem exponentialBound260 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch065.certificate780).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate520).dm (WitnessCertificates.Batch026.certificate520).beta) ≤ (2*exp (-((CountingCertificates.Batch026.certificate520).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch065.certificate780).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch065.certificate781).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch026.certificate520).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch065.certificate780 MergedCutGroups.Batch065.certificate781 CountingCertificates.Batch026.certificate520 CutLabelCertificates.Entropy013.certificate261 CutLabelCertificates.Minority013.certificate260 matches260 rfl rfl
    MergedCutGroups.Batch065.numericValid780 MergedCutGroups.Batch065.numericValid781 MergedCutGroups.Batch065.cellsSound780 MergedCutGroups.Batch065.cellsSound781
    MergedCutGroups.Batch065.cellsNumeric780 MergedCutGroups.Batch065.cellsNumeric781 MergedCutGroups.Batch065.populationMatches780 MergedCutGroups.Batch065.populationMatches781
    PopulationCertificates.Batch026.valid520 PopulationCertificates.Batch026.sound520 WitnessCertificates.Batch026.valid520 WitnessCertificates.Batch026.sound520 CountingCertificates.Batch026.valid520 CountingCertificates.Batch026.sound520
    CutLabelCertificates.Entropy013.valid261 CutLabelCertificates.Minority013.valid260 CutLabelCertificates.Minority013.sound260 H st hI
theorem probabilityBound260 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch065.certificate780).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate520).dm (WitnessCertificates.Batch026.certificate520).beta) ≤ ((CutFailureCertificates.Budget026.certificate520).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound520 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate520).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch065.certificate780).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch065.certificate781).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch026.certificate520).omega:ℝ) ≤ ((CutFailureCertificates.Budget026.certificate520).bound:ℝ) at hb
  exact (exponentialBound260 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches261 : (MergedCutGroups.Batch065.certificate783).GlobalMatches MergedCutGroups.Batch065.certificate784 CountingCertificates.Batch026.certificate522 CutLabelCertificates.Entropy013.certificate262 CutLabelCertificates.Minority013.certificate261 := by decide +kernel
theorem exponentialBound261 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch065.certificate783).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate522).dm (WitnessCertificates.Batch026.certificate522).beta) ≤ (2*exp (-((CountingCertificates.Batch026.certificate522).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch065.certificate783).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch065.certificate784).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch026.certificate522).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch065.certificate783 MergedCutGroups.Batch065.certificate784 CountingCertificates.Batch026.certificate522 CutLabelCertificates.Entropy013.certificate262 CutLabelCertificates.Minority013.certificate261 matches261 rfl rfl
    MergedCutGroups.Batch065.numericValid783 MergedCutGroups.Batch065.numericValid784 MergedCutGroups.Batch065.cellsSound783 MergedCutGroups.Batch065.cellsSound784
    MergedCutGroups.Batch065.cellsNumeric783 MergedCutGroups.Batch065.cellsNumeric784 MergedCutGroups.Batch065.populationMatches783 MergedCutGroups.Batch065.populationMatches784
    PopulationCertificates.Batch026.valid522 PopulationCertificates.Batch026.sound522 WitnessCertificates.Batch026.valid522 WitnessCertificates.Batch026.sound522 CountingCertificates.Batch026.valid522 CountingCertificates.Batch026.sound522
    CutLabelCertificates.Entropy013.valid262 CutLabelCertificates.Minority013.valid261 CutLabelCertificates.Minority013.sound261 H st hI
theorem probabilityBound261 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch065.certificate783).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate522).dm (WitnessCertificates.Batch026.certificate522).beta) ≤ ((CutFailureCertificates.Budget026.certificate522).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound522 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate522).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch065.certificate783).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch065.certificate784).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch026.certificate522).omega:ℝ) ≤ ((CutFailureCertificates.Budget026.certificate522).bound:ℝ) at hb
  exact (exponentialBound261 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches262 : (MergedCutGroups.Batch065.certificate786).GlobalMatches MergedCutGroups.Batch065.certificate787 CountingCertificates.Batch026.certificate524 CutLabelCertificates.Entropy013.certificate263 CutLabelCertificates.Minority013.certificate262 := by decide +kernel
theorem exponentialBound262 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch065.certificate786).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate524).dm (WitnessCertificates.Batch026.certificate524).beta) ≤ (2*exp (-((CountingCertificates.Batch026.certificate524).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch065.certificate786).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch065.certificate787).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch026.certificate524).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch065.certificate786 MergedCutGroups.Batch065.certificate787 CountingCertificates.Batch026.certificate524 CutLabelCertificates.Entropy013.certificate263 CutLabelCertificates.Minority013.certificate262 matches262 rfl rfl
    MergedCutGroups.Batch065.numericValid786 MergedCutGroups.Batch065.numericValid787 MergedCutGroups.Batch065.cellsSound786 MergedCutGroups.Batch065.cellsSound787
    MergedCutGroups.Batch065.cellsNumeric786 MergedCutGroups.Batch065.cellsNumeric787 MergedCutGroups.Batch065.populationMatches786 MergedCutGroups.Batch065.populationMatches787
    PopulationCertificates.Batch026.valid524 PopulationCertificates.Batch026.sound524 WitnessCertificates.Batch026.valid524 WitnessCertificates.Batch026.sound524 CountingCertificates.Batch026.valid524 CountingCertificates.Batch026.sound524
    CutLabelCertificates.Entropy013.valid263 CutLabelCertificates.Minority013.valid262 CutLabelCertificates.Minority013.sound262 H st hI
theorem probabilityBound262 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch065.certificate786).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate524).dm (WitnessCertificates.Batch026.certificate524).beta) ≤ ((CutFailureCertificates.Budget026.certificate524).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound524 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate524).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch065.certificate786).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch065.certificate787).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch026.certificate524).omega:ℝ) ≤ ((CutFailureCertificates.Budget026.certificate524).bound:ℝ) at hb
  exact (exponentialBound262 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches263 : (MergedCutGroups.Batch065.certificate789).GlobalMatches MergedCutGroups.Batch065.certificate790 CountingCertificates.Batch026.certificate526 CutLabelCertificates.Entropy013.certificate264 CutLabelCertificates.Minority013.certificate263 := by decide +kernel
theorem exponentialBound263 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch065.certificate789).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate526).dm (WitnessCertificates.Batch026.certificate526).beta) ≤ (2*exp (-((CountingCertificates.Batch026.certificate526).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch065.certificate789).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch065.certificate790).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch026.certificate526).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch065.certificate789 MergedCutGroups.Batch065.certificate790 CountingCertificates.Batch026.certificate526 CutLabelCertificates.Entropy013.certificate264 CutLabelCertificates.Minority013.certificate263 matches263 rfl rfl
    MergedCutGroups.Batch065.numericValid789 MergedCutGroups.Batch065.numericValid790 MergedCutGroups.Batch065.cellsSound789 MergedCutGroups.Batch065.cellsSound790
    MergedCutGroups.Batch065.cellsNumeric789 MergedCutGroups.Batch065.cellsNumeric790 MergedCutGroups.Batch065.populationMatches789 MergedCutGroups.Batch065.populationMatches790
    PopulationCertificates.Batch026.valid526 PopulationCertificates.Batch026.sound526 WitnessCertificates.Batch026.valid526 WitnessCertificates.Batch026.sound526 CountingCertificates.Batch026.valid526 CountingCertificates.Batch026.sound526
    CutLabelCertificates.Entropy013.valid264 CutLabelCertificates.Minority013.valid263 CutLabelCertificates.Minority013.sound263 H st hI
theorem probabilityBound263 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch065.certificate789).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate526).dm (WitnessCertificates.Batch026.certificate526).beta) ≤ ((CutFailureCertificates.Budget026.certificate526).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound526 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate526).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch065.certificate789).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch065.certificate790).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch026.certificate526).omega:ℝ) ≤ ((CutFailureCertificates.Budget026.certificate526).bound:ℝ) at hb
  exact (exponentialBound263 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches264 : (MergedCutGroups.Batch066.certificate792).GlobalMatches MergedCutGroups.Batch066.certificate793 CountingCertificates.Batch026.certificate528 CutLabelCertificates.Entropy013.certificate265 CutLabelCertificates.Minority013.certificate264 := by decide +kernel
theorem exponentialBound264 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch066.certificate792).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate528).dm (WitnessCertificates.Batch026.certificate528).beta) ≤ (2*exp (-((CountingCertificates.Batch026.certificate528).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch066.certificate792).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch066.certificate793).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch026.certificate528).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch066.certificate792 MergedCutGroups.Batch066.certificate793 CountingCertificates.Batch026.certificate528 CutLabelCertificates.Entropy013.certificate265 CutLabelCertificates.Minority013.certificate264 matches264 rfl rfl
    MergedCutGroups.Batch066.numericValid792 MergedCutGroups.Batch066.numericValid793 MergedCutGroups.Batch066.cellsSound792 MergedCutGroups.Batch066.cellsSound793
    MergedCutGroups.Batch066.cellsNumeric792 MergedCutGroups.Batch066.cellsNumeric793 MergedCutGroups.Batch066.populationMatches792 MergedCutGroups.Batch066.populationMatches793
    PopulationCertificates.Batch026.valid528 PopulationCertificates.Batch026.sound528 WitnessCertificates.Batch026.valid528 WitnessCertificates.Batch026.sound528 CountingCertificates.Batch026.valid528 CountingCertificates.Batch026.sound528
    CutLabelCertificates.Entropy013.valid265 CutLabelCertificates.Minority013.valid264 CutLabelCertificates.Minority013.sound264 H st hI
theorem probabilityBound264 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch066.certificate792).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate528).dm (WitnessCertificates.Batch026.certificate528).beta) ≤ ((CutFailureCertificates.Budget026.certificate528).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound528 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate528).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch066.certificate792).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch066.certificate793).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch026.certificate528).omega:ℝ) ≤ ((CutFailureCertificates.Budget026.certificate528).bound:ℝ) at hb
  exact (exponentialBound264 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches265 : (MergedCutGroups.Batch066.certificate795).GlobalMatches MergedCutGroups.Batch066.certificate796 CountingCertificates.Batch026.certificate530 CutLabelCertificates.Entropy013.certificate266 CutLabelCertificates.Minority013.certificate265 := by decide +kernel
theorem exponentialBound265 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch066.certificate795).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate530).dm (WitnessCertificates.Batch026.certificate530).beta) ≤ (2*exp (-((CountingCertificates.Batch026.certificate530).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch066.certificate795).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch066.certificate796).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch026.certificate530).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch066.certificate795 MergedCutGroups.Batch066.certificate796 CountingCertificates.Batch026.certificate530 CutLabelCertificates.Entropy013.certificate266 CutLabelCertificates.Minority013.certificate265 matches265 rfl rfl
    MergedCutGroups.Batch066.numericValid795 MergedCutGroups.Batch066.numericValid796 MergedCutGroups.Batch066.cellsSound795 MergedCutGroups.Batch066.cellsSound796
    MergedCutGroups.Batch066.cellsNumeric795 MergedCutGroups.Batch066.cellsNumeric796 MergedCutGroups.Batch066.populationMatches795 MergedCutGroups.Batch066.populationMatches796
    PopulationCertificates.Batch026.valid530 PopulationCertificates.Batch026.sound530 WitnessCertificates.Batch026.valid530 WitnessCertificates.Batch026.sound530 CountingCertificates.Batch026.valid530 CountingCertificates.Batch026.sound530
    CutLabelCertificates.Entropy013.valid266 CutLabelCertificates.Minority013.valid265 CutLabelCertificates.Minority013.sound265 H st hI
theorem probabilityBound265 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch066.certificate795).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate530).dm (WitnessCertificates.Batch026.certificate530).beta) ≤ ((CutFailureCertificates.Budget026.certificate530).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound530 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate530).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch066.certificate795).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch066.certificate796).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch026.certificate530).omega:ℝ) ≤ ((CutFailureCertificates.Budget026.certificate530).bound:ℝ) at hb
  exact (exponentialBound265 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches266 : (MergedCutGroups.Batch066.certificate798).GlobalMatches MergedCutGroups.Batch066.certificate799 CountingCertificates.Batch026.certificate532 CutLabelCertificates.Entropy013.certificate267 CutLabelCertificates.Minority013.certificate266 := by decide +kernel
theorem exponentialBound266 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch066.certificate798).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate532).dm (WitnessCertificates.Batch026.certificate532).beta) ≤ (2*exp (-((CountingCertificates.Batch026.certificate532).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch066.certificate798).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch066.certificate799).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch026.certificate532).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch066.certificate798 MergedCutGroups.Batch066.certificate799 CountingCertificates.Batch026.certificate532 CutLabelCertificates.Entropy013.certificate267 CutLabelCertificates.Minority013.certificate266 matches266 rfl rfl
    MergedCutGroups.Batch066.numericValid798 MergedCutGroups.Batch066.numericValid799 MergedCutGroups.Batch066.cellsSound798 MergedCutGroups.Batch066.cellsSound799
    MergedCutGroups.Batch066.cellsNumeric798 MergedCutGroups.Batch066.cellsNumeric799 MergedCutGroups.Batch066.populationMatches798 MergedCutGroups.Batch066.populationMatches799
    PopulationCertificates.Batch026.valid532 PopulationCertificates.Batch026.sound532 WitnessCertificates.Batch026.valid532 WitnessCertificates.Batch026.sound532 CountingCertificates.Batch026.valid532 CountingCertificates.Batch026.sound532
    CutLabelCertificates.Entropy013.valid267 CutLabelCertificates.Minority013.valid266 CutLabelCertificates.Minority013.sound266 H st hI
theorem probabilityBound266 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch066.certificate798).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate532).dm (WitnessCertificates.Batch026.certificate532).beta) ≤ ((CutFailureCertificates.Budget026.certificate532).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound532 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate532).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch066.certificate798).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch066.certificate799).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch026.certificate532).omega:ℝ) ≤ ((CutFailureCertificates.Budget026.certificate532).bound:ℝ) at hb
  exact (exponentialBound266 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches267 : (MergedCutGroups.Batch066.certificate801).GlobalMatches MergedCutGroups.Batch066.certificate802 CountingCertificates.Batch026.certificate534 CutLabelCertificates.Entropy013.certificate268 CutLabelCertificates.Minority013.certificate267 := by decide +kernel
theorem exponentialBound267 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch066.certificate801).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate534).dm (WitnessCertificates.Batch026.certificate534).beta) ≤ (2*exp (-((CountingCertificates.Batch026.certificate534).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch066.certificate801).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch066.certificate802).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch026.certificate534).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch066.certificate801 MergedCutGroups.Batch066.certificate802 CountingCertificates.Batch026.certificate534 CutLabelCertificates.Entropy013.certificate268 CutLabelCertificates.Minority013.certificate267 matches267 rfl rfl
    MergedCutGroups.Batch066.numericValid801 MergedCutGroups.Batch066.numericValid802 MergedCutGroups.Batch066.cellsSound801 MergedCutGroups.Batch066.cellsSound802
    MergedCutGroups.Batch066.cellsNumeric801 MergedCutGroups.Batch066.cellsNumeric802 MergedCutGroups.Batch066.populationMatches801 MergedCutGroups.Batch066.populationMatches802
    PopulationCertificates.Batch026.valid534 PopulationCertificates.Batch026.sound534 WitnessCertificates.Batch026.valid534 WitnessCertificates.Batch026.sound534 CountingCertificates.Batch026.valid534 CountingCertificates.Batch026.sound534
    CutLabelCertificates.Entropy013.valid268 CutLabelCertificates.Minority013.valid267 CutLabelCertificates.Minority013.sound267 H st hI
theorem probabilityBound267 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch066.certificate801).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate534).dm (WitnessCertificates.Batch026.certificate534).beta) ≤ ((CutFailureCertificates.Budget026.certificate534).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound534 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate534).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch066.certificate801).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch066.certificate802).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch026.certificate534).omega:ℝ) ≤ ((CutFailureCertificates.Budget026.certificate534).bound:ℝ) at hb
  exact (exponentialBound267 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches268 : (MergedCutGroups.Batch067.certificate804).GlobalMatches MergedCutGroups.Batch067.certificate805 CountingCertificates.Batch026.certificate536 CutLabelCertificates.Entropy013.certificate269 CutLabelCertificates.Minority013.certificate268 := by decide +kernel
theorem exponentialBound268 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch067.certificate804).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate536).dm (WitnessCertificates.Batch026.certificate536).beta) ≤ (2*exp (-((CountingCertificates.Batch026.certificate536).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch067.certificate804).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch067.certificate805).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch026.certificate536).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch067.certificate804 MergedCutGroups.Batch067.certificate805 CountingCertificates.Batch026.certificate536 CutLabelCertificates.Entropy013.certificate269 CutLabelCertificates.Minority013.certificate268 matches268 rfl rfl
    MergedCutGroups.Batch067.numericValid804 MergedCutGroups.Batch067.numericValid805 MergedCutGroups.Batch067.cellsSound804 MergedCutGroups.Batch067.cellsSound805
    MergedCutGroups.Batch067.cellsNumeric804 MergedCutGroups.Batch067.cellsNumeric805 MergedCutGroups.Batch067.populationMatches804 MergedCutGroups.Batch067.populationMatches805
    PopulationCertificates.Batch026.valid536 PopulationCertificates.Batch026.sound536 WitnessCertificates.Batch026.valid536 WitnessCertificates.Batch026.sound536 CountingCertificates.Batch026.valid536 CountingCertificates.Batch026.sound536
    CutLabelCertificates.Entropy013.valid269 CutLabelCertificates.Minority013.valid268 CutLabelCertificates.Minority013.sound268 H st hI
theorem probabilityBound268 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch067.certificate804).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate536).dm (WitnessCertificates.Batch026.certificate536).beta) ≤ ((CutFailureCertificates.Budget026.certificate536).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound536 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate536).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch067.certificate804).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch067.certificate805).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch026.certificate536).omega:ℝ) ≤ ((CutFailureCertificates.Budget026.certificate536).bound:ℝ) at hb
  exact (exponentialBound268 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches269 : (MergedCutGroups.Batch067.certificate807).GlobalMatches MergedCutGroups.Batch067.certificate808 CountingCertificates.Batch026.certificate538 CutLabelCertificates.Entropy013.certificate270 CutLabelCertificates.Minority013.certificate269 := by decide +kernel
theorem exponentialBound269 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch067.certificate807).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate538).dm (WitnessCertificates.Batch026.certificate538).beta) ≤ (2*exp (-((CountingCertificates.Batch026.certificate538).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch067.certificate807).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch067.certificate808).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch026.certificate538).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch067.certificate807 MergedCutGroups.Batch067.certificate808 CountingCertificates.Batch026.certificate538 CutLabelCertificates.Entropy013.certificate270 CutLabelCertificates.Minority013.certificate269 matches269 rfl rfl
    MergedCutGroups.Batch067.numericValid807 MergedCutGroups.Batch067.numericValid808 MergedCutGroups.Batch067.cellsSound807 MergedCutGroups.Batch067.cellsSound808
    MergedCutGroups.Batch067.cellsNumeric807 MergedCutGroups.Batch067.cellsNumeric808 MergedCutGroups.Batch067.populationMatches807 MergedCutGroups.Batch067.populationMatches808
    PopulationCertificates.Batch026.valid538 PopulationCertificates.Batch026.sound538 WitnessCertificates.Batch026.valid538 WitnessCertificates.Batch026.sound538 CountingCertificates.Batch026.valid538 CountingCertificates.Batch026.sound538
    CutLabelCertificates.Entropy013.valid270 CutLabelCertificates.Minority013.valid269 CutLabelCertificates.Minority013.sound269 H st hI
theorem probabilityBound269 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch067.certificate807).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch026.certificate538).dm (WitnessCertificates.Batch026.certificate538).beta) ≤ ((CutFailureCertificates.Budget026.certificate538).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound538 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate538).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch067.certificate807).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch067.certificate808).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch026.certificate538).omega:ℝ) ≤ ((CutFailureCertificates.Budget026.certificate538).bound:ℝ) at hb
  exact (exponentialBound269 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches270 : (MergedCutGroups.Batch067.certificate810).GlobalMatches MergedCutGroups.Batch067.certificate811 CountingCertificates.Batch027.certificate540 CutLabelCertificates.Entropy013.certificate271 CutLabelCertificates.Minority013.certificate270 := by decide +kernel
theorem exponentialBound270 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch067.certificate810).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate540).dm (WitnessCertificates.Batch027.certificate540).beta) ≤ (2*exp (-((CountingCertificates.Batch027.certificate540).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch067.certificate810).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch067.certificate811).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch027.certificate540).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch067.certificate810 MergedCutGroups.Batch067.certificate811 CountingCertificates.Batch027.certificate540 CutLabelCertificates.Entropy013.certificate271 CutLabelCertificates.Minority013.certificate270 matches270 rfl rfl
    MergedCutGroups.Batch067.numericValid810 MergedCutGroups.Batch067.numericValid811 MergedCutGroups.Batch067.cellsSound810 MergedCutGroups.Batch067.cellsSound811
    MergedCutGroups.Batch067.cellsNumeric810 MergedCutGroups.Batch067.cellsNumeric811 MergedCutGroups.Batch067.populationMatches810 MergedCutGroups.Batch067.populationMatches811
    PopulationCertificates.Batch027.valid540 PopulationCertificates.Batch027.sound540 WitnessCertificates.Batch027.valid540 WitnessCertificates.Batch027.sound540 CountingCertificates.Batch027.valid540 CountingCertificates.Batch027.sound540
    CutLabelCertificates.Entropy013.valid271 CutLabelCertificates.Minority013.valid270 CutLabelCertificates.Minority013.sound270 H st hI
theorem probabilityBound270 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch067.certificate810).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate540).dm (WitnessCertificates.Batch027.certificate540).beta) ≤ ((CutFailureCertificates.Budget027.certificate540).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound540 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate540).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch067.certificate810).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch067.certificate811).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch027.certificate540).omega:ℝ) ≤ ((CutFailureCertificates.Budget027.certificate540).bound:ℝ) at hb
  exact (exponentialBound270 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches271 : (MergedCutGroups.Batch067.certificate813).GlobalMatches MergedCutGroups.Batch067.certificate814 CountingCertificates.Batch027.certificate542 CutLabelCertificates.Entropy013.certificate272 CutLabelCertificates.Minority013.certificate271 := by decide +kernel
theorem exponentialBound271 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch067.certificate813).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate542).dm (WitnessCertificates.Batch027.certificate542).beta) ≤ (2*exp (-((CountingCertificates.Batch027.certificate542).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch067.certificate813).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch067.certificate814).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch027.certificate542).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch067.certificate813 MergedCutGroups.Batch067.certificate814 CountingCertificates.Batch027.certificate542 CutLabelCertificates.Entropy013.certificate272 CutLabelCertificates.Minority013.certificate271 matches271 rfl rfl
    MergedCutGroups.Batch067.numericValid813 MergedCutGroups.Batch067.numericValid814 MergedCutGroups.Batch067.cellsSound813 MergedCutGroups.Batch067.cellsSound814
    MergedCutGroups.Batch067.cellsNumeric813 MergedCutGroups.Batch067.cellsNumeric814 MergedCutGroups.Batch067.populationMatches813 MergedCutGroups.Batch067.populationMatches814
    PopulationCertificates.Batch027.valid542 PopulationCertificates.Batch027.sound542 WitnessCertificates.Batch027.valid542 WitnessCertificates.Batch027.sound542 CountingCertificates.Batch027.valid542 CountingCertificates.Batch027.sound542
    CutLabelCertificates.Entropy013.valid272 CutLabelCertificates.Minority013.valid271 CutLabelCertificates.Minority013.sound271 H st hI
theorem probabilityBound271 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch067.certificate813).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate542).dm (WitnessCertificates.Batch027.certificate542).beta) ≤ ((CutFailureCertificates.Budget027.certificate542).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound542 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate542).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch067.certificate813).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch067.certificate814).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch027.certificate542).omega:ℝ) ≤ ((CutFailureCertificates.Budget027.certificate542).bound:ℝ) at hb
  exact (exponentialBound271 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches272 : (MergedCutGroups.Batch068.certificate816).GlobalMatches MergedCutGroups.Batch068.certificate817 CountingCertificates.Batch027.certificate544 CutLabelCertificates.Entropy013.certificate273 CutLabelCertificates.Minority013.certificate272 := by decide +kernel
theorem exponentialBound272 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch068.certificate816).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate544).dm (WitnessCertificates.Batch027.certificate544).beta) ≤ (2*exp (-((CountingCertificates.Batch027.certificate544).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch068.certificate816).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch068.certificate817).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch027.certificate544).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch068.certificate816 MergedCutGroups.Batch068.certificate817 CountingCertificates.Batch027.certificate544 CutLabelCertificates.Entropy013.certificate273 CutLabelCertificates.Minority013.certificate272 matches272 rfl rfl
    MergedCutGroups.Batch068.numericValid816 MergedCutGroups.Batch068.numericValid817 MergedCutGroups.Batch068.cellsSound816 MergedCutGroups.Batch068.cellsSound817
    MergedCutGroups.Batch068.cellsNumeric816 MergedCutGroups.Batch068.cellsNumeric817 MergedCutGroups.Batch068.populationMatches816 MergedCutGroups.Batch068.populationMatches817
    PopulationCertificates.Batch027.valid544 PopulationCertificates.Batch027.sound544 WitnessCertificates.Batch027.valid544 WitnessCertificates.Batch027.sound544 CountingCertificates.Batch027.valid544 CountingCertificates.Batch027.sound544
    CutLabelCertificates.Entropy013.valid273 CutLabelCertificates.Minority013.valid272 CutLabelCertificates.Minority013.sound272 H st hI
theorem probabilityBound272 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch068.certificate816).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate544).dm (WitnessCertificates.Batch027.certificate544).beta) ≤ ((CutFailureCertificates.Budget027.certificate544).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound544 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate544).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch068.certificate816).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch068.certificate817).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch027.certificate544).omega:ℝ) ≤ ((CutFailureCertificates.Budget027.certificate544).bound:ℝ) at hb
  exact (exponentialBound272 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches273 : (MergedCutGroups.Batch068.certificate819).GlobalMatches MergedCutGroups.Batch068.certificate820 CountingCertificates.Batch027.certificate546 CutLabelCertificates.Entropy013.certificate274 CutLabelCertificates.Minority013.certificate273 := by decide +kernel
theorem exponentialBound273 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch068.certificate819).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate546).dm (WitnessCertificates.Batch027.certificate546).beta) ≤ (2*exp (-((CountingCertificates.Batch027.certificate546).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch068.certificate819).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch068.certificate820).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch027.certificate546).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch068.certificate819 MergedCutGroups.Batch068.certificate820 CountingCertificates.Batch027.certificate546 CutLabelCertificates.Entropy013.certificate274 CutLabelCertificates.Minority013.certificate273 matches273 rfl rfl
    MergedCutGroups.Batch068.numericValid819 MergedCutGroups.Batch068.numericValid820 MergedCutGroups.Batch068.cellsSound819 MergedCutGroups.Batch068.cellsSound820
    MergedCutGroups.Batch068.cellsNumeric819 MergedCutGroups.Batch068.cellsNumeric820 MergedCutGroups.Batch068.populationMatches819 MergedCutGroups.Batch068.populationMatches820
    PopulationCertificates.Batch027.valid546 PopulationCertificates.Batch027.sound546 WitnessCertificates.Batch027.valid546 WitnessCertificates.Batch027.sound546 CountingCertificates.Batch027.valid546 CountingCertificates.Batch027.sound546
    CutLabelCertificates.Entropy013.valid274 CutLabelCertificates.Minority013.valid273 CutLabelCertificates.Minority013.sound273 H st hI
theorem probabilityBound273 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch068.certificate819).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate546).dm (WitnessCertificates.Batch027.certificate546).beta) ≤ ((CutFailureCertificates.Budget027.certificate546).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound546 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate546).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch068.certificate819).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch068.certificate820).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch027.certificate546).omega:ℝ) ≤ ((CutFailureCertificates.Budget027.certificate546).bound:ℝ) at hb
  exact (exponentialBound273 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches274 : (MergedCutGroups.Batch068.certificate822).GlobalMatches MergedCutGroups.Batch068.certificate823 CountingCertificates.Batch027.certificate548 CutLabelCertificates.Entropy013.certificate275 CutLabelCertificates.Minority013.certificate274 := by decide +kernel
theorem exponentialBound274 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch068.certificate822).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate548).dm (WitnessCertificates.Batch027.certificate548).beta) ≤ (2*exp (-((CountingCertificates.Batch027.certificate548).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch068.certificate822).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch068.certificate823).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch027.certificate548).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch068.certificate822 MergedCutGroups.Batch068.certificate823 CountingCertificates.Batch027.certificate548 CutLabelCertificates.Entropy013.certificate275 CutLabelCertificates.Minority013.certificate274 matches274 rfl rfl
    MergedCutGroups.Batch068.numericValid822 MergedCutGroups.Batch068.numericValid823 MergedCutGroups.Batch068.cellsSound822 MergedCutGroups.Batch068.cellsSound823
    MergedCutGroups.Batch068.cellsNumeric822 MergedCutGroups.Batch068.cellsNumeric823 MergedCutGroups.Batch068.populationMatches822 MergedCutGroups.Batch068.populationMatches823
    PopulationCertificates.Batch027.valid548 PopulationCertificates.Batch027.sound548 WitnessCertificates.Batch027.valid548 WitnessCertificates.Batch027.sound548 CountingCertificates.Batch027.valid548 CountingCertificates.Batch027.sound548
    CutLabelCertificates.Entropy013.valid275 CutLabelCertificates.Minority013.valid274 CutLabelCertificates.Minority013.sound274 H st hI
theorem probabilityBound274 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch068.certificate822).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate548).dm (WitnessCertificates.Batch027.certificate548).beta) ≤ ((CutFailureCertificates.Budget027.certificate548).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound548 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate548).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch068.certificate822).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch068.certificate823).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch027.certificate548).omega:ℝ) ≤ ((CutFailureCertificates.Budget027.certificate548).bound:ℝ) at hb
  exact (exponentialBound274 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches275 : (MergedCutGroups.Batch068.certificate825).GlobalMatches MergedCutGroups.Batch068.certificate826 CountingCertificates.Batch027.certificate550 CutLabelCertificates.Entropy013.certificate276 CutLabelCertificates.Minority013.certificate275 := by decide +kernel
theorem exponentialBound275 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch068.certificate825).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate550).dm (WitnessCertificates.Batch027.certificate550).beta) ≤ (2*exp (-((CountingCertificates.Batch027.certificate550).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch068.certificate825).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch068.certificate826).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch027.certificate550).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch068.certificate825 MergedCutGroups.Batch068.certificate826 CountingCertificates.Batch027.certificate550 CutLabelCertificates.Entropy013.certificate276 CutLabelCertificates.Minority013.certificate275 matches275 rfl rfl
    MergedCutGroups.Batch068.numericValid825 MergedCutGroups.Batch068.numericValid826 MergedCutGroups.Batch068.cellsSound825 MergedCutGroups.Batch068.cellsSound826
    MergedCutGroups.Batch068.cellsNumeric825 MergedCutGroups.Batch068.cellsNumeric826 MergedCutGroups.Batch068.populationMatches825 MergedCutGroups.Batch068.populationMatches826
    PopulationCertificates.Batch027.valid550 PopulationCertificates.Batch027.sound550 WitnessCertificates.Batch027.valid550 WitnessCertificates.Batch027.sound550 CountingCertificates.Batch027.valid550 CountingCertificates.Batch027.sound550
    CutLabelCertificates.Entropy013.valid276 CutLabelCertificates.Minority013.valid275 CutLabelCertificates.Minority013.sound275 H st hI
theorem probabilityBound275 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch068.certificate825).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate550).dm (WitnessCertificates.Batch027.certificate550).beta) ≤ ((CutFailureCertificates.Budget027.certificate550).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound550 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate550).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch068.certificate825).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch068.certificate826).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch027.certificate550).omega:ℝ) ≤ ((CutFailureCertificates.Budget027.certificate550).bound:ℝ) at hb
  exact (exponentialBound275 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches276 : (MergedCutGroups.Batch069.certificate828).GlobalMatches MergedCutGroups.Batch069.certificate829 CountingCertificates.Batch027.certificate552 CutLabelCertificates.Entropy013.certificate277 CutLabelCertificates.Minority013.certificate276 := by decide +kernel
theorem exponentialBound276 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch069.certificate828).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate552).dm (WitnessCertificates.Batch027.certificate552).beta) ≤ (2*exp (-((CountingCertificates.Batch027.certificate552).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch069.certificate828).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch069.certificate829).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch027.certificate552).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch069.certificate828 MergedCutGroups.Batch069.certificate829 CountingCertificates.Batch027.certificate552 CutLabelCertificates.Entropy013.certificate277 CutLabelCertificates.Minority013.certificate276 matches276 rfl rfl
    MergedCutGroups.Batch069.numericValid828 MergedCutGroups.Batch069.numericValid829 MergedCutGroups.Batch069.cellsSound828 MergedCutGroups.Batch069.cellsSound829
    MergedCutGroups.Batch069.cellsNumeric828 MergedCutGroups.Batch069.cellsNumeric829 MergedCutGroups.Batch069.populationMatches828 MergedCutGroups.Batch069.populationMatches829
    PopulationCertificates.Batch027.valid552 PopulationCertificates.Batch027.sound552 WitnessCertificates.Batch027.valid552 WitnessCertificates.Batch027.sound552 CountingCertificates.Batch027.valid552 CountingCertificates.Batch027.sound552
    CutLabelCertificates.Entropy013.valid277 CutLabelCertificates.Minority013.valid276 CutLabelCertificates.Minority013.sound276 H st hI
theorem probabilityBound276 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch069.certificate828).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate552).dm (WitnessCertificates.Batch027.certificate552).beta) ≤ ((CutFailureCertificates.Budget027.certificate552).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound552 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate552).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch069.certificate828).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch069.certificate829).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch027.certificate552).omega:ℝ) ≤ ((CutFailureCertificates.Budget027.certificate552).bound:ℝ) at hb
  exact (exponentialBound276 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches277 : (MergedCutGroups.Batch069.certificate831).GlobalMatches MergedCutGroups.Batch069.certificate832 CountingCertificates.Batch027.certificate554 CutLabelCertificates.Entropy013.certificate278 CutLabelCertificates.Minority013.certificate277 := by decide +kernel
theorem exponentialBound277 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch069.certificate831).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate554).dm (WitnessCertificates.Batch027.certificate554).beta) ≤ (2*exp (-((CountingCertificates.Batch027.certificate554).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch069.certificate831).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch069.certificate832).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch027.certificate554).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch069.certificate831 MergedCutGroups.Batch069.certificate832 CountingCertificates.Batch027.certificate554 CutLabelCertificates.Entropy013.certificate278 CutLabelCertificates.Minority013.certificate277 matches277 rfl rfl
    MergedCutGroups.Batch069.numericValid831 MergedCutGroups.Batch069.numericValid832 MergedCutGroups.Batch069.cellsSound831 MergedCutGroups.Batch069.cellsSound832
    MergedCutGroups.Batch069.cellsNumeric831 MergedCutGroups.Batch069.cellsNumeric832 MergedCutGroups.Batch069.populationMatches831 MergedCutGroups.Batch069.populationMatches832
    PopulationCertificates.Batch027.valid554 PopulationCertificates.Batch027.sound554 WitnessCertificates.Batch027.valid554 WitnessCertificates.Batch027.sound554 CountingCertificates.Batch027.valid554 CountingCertificates.Batch027.sound554
    CutLabelCertificates.Entropy013.valid278 CutLabelCertificates.Minority013.valid277 CutLabelCertificates.Minority013.sound277 H st hI
theorem probabilityBound277 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch069.certificate831).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate554).dm (WitnessCertificates.Batch027.certificate554).beta) ≤ ((CutFailureCertificates.Budget027.certificate554).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound554 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate554).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch069.certificate831).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch069.certificate832).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch027.certificate554).omega:ℝ) ≤ ((CutFailureCertificates.Budget027.certificate554).bound:ℝ) at hb
  exact (exponentialBound277 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches278 : (MergedCutGroups.Batch069.certificate834).GlobalMatches MergedCutGroups.Batch069.certificate835 CountingCertificates.Batch027.certificate556 CutLabelCertificates.Entropy013.certificate279 CutLabelCertificates.Minority013.certificate278 := by decide +kernel
theorem exponentialBound278 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch069.certificate834).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate556).dm (WitnessCertificates.Batch027.certificate556).beta) ≤ (2*exp (-((CountingCertificates.Batch027.certificate556).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch069.certificate834).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch069.certificate835).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch027.certificate556).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch069.certificate834 MergedCutGroups.Batch069.certificate835 CountingCertificates.Batch027.certificate556 CutLabelCertificates.Entropy013.certificate279 CutLabelCertificates.Minority013.certificate278 matches278 rfl rfl
    MergedCutGroups.Batch069.numericValid834 MergedCutGroups.Batch069.numericValid835 MergedCutGroups.Batch069.cellsSound834 MergedCutGroups.Batch069.cellsSound835
    MergedCutGroups.Batch069.cellsNumeric834 MergedCutGroups.Batch069.cellsNumeric835 MergedCutGroups.Batch069.populationMatches834 MergedCutGroups.Batch069.populationMatches835
    PopulationCertificates.Batch027.valid556 PopulationCertificates.Batch027.sound556 WitnessCertificates.Batch027.valid556 WitnessCertificates.Batch027.sound556 CountingCertificates.Batch027.valid556 CountingCertificates.Batch027.sound556
    CutLabelCertificates.Entropy013.valid279 CutLabelCertificates.Minority013.valid278 CutLabelCertificates.Minority013.sound278 H st hI
theorem probabilityBound278 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch069.certificate834).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate556).dm (WitnessCertificates.Batch027.certificate556).beta) ≤ ((CutFailureCertificates.Budget027.certificate556).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound556 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate556).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch069.certificate834).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch069.certificate835).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch027.certificate556).omega:ℝ) ≤ ((CutFailureCertificates.Budget027.certificate556).bound:ℝ) at hb
  exact (exponentialBound278 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches279 : (MergedCutGroups.Batch069.certificate837).GlobalMatches MergedCutGroups.Batch069.certificate838 CountingCertificates.Batch027.certificate558 CutLabelCertificates.Entropy014.certificate280 CutLabelCertificates.Minority013.certificate279 := by decide +kernel
theorem exponentialBound279 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch069.certificate837).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate558).dm (WitnessCertificates.Batch027.certificate558).beta) ≤ (2*exp (-((CountingCertificates.Batch027.certificate558).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch069.certificate837).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch069.certificate838).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch027.certificate558).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch069.certificate837 MergedCutGroups.Batch069.certificate838 CountingCertificates.Batch027.certificate558 CutLabelCertificates.Entropy014.certificate280 CutLabelCertificates.Minority013.certificate279 matches279 rfl rfl
    MergedCutGroups.Batch069.numericValid837 MergedCutGroups.Batch069.numericValid838 MergedCutGroups.Batch069.cellsSound837 MergedCutGroups.Batch069.cellsSound838
    MergedCutGroups.Batch069.cellsNumeric837 MergedCutGroups.Batch069.cellsNumeric838 MergedCutGroups.Batch069.populationMatches837 MergedCutGroups.Batch069.populationMatches838
    PopulationCertificates.Batch027.valid558 PopulationCertificates.Batch027.sound558 WitnessCertificates.Batch027.valid558 WitnessCertificates.Batch027.sound558 CountingCertificates.Batch027.valid558 CountingCertificates.Batch027.sound558
    CutLabelCertificates.Entropy014.valid280 CutLabelCertificates.Minority013.valid279 CutLabelCertificates.Minority013.sound279 H st hI
theorem probabilityBound279 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch069.certificate837).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch027.certificate558).dm (WitnessCertificates.Batch027.certificate558).beta) ≤ ((CutFailureCertificates.Budget027.certificate558).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound558 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate558).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch069.certificate837).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch069.certificate838).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch027.certificate558).omega:ℝ) ≤ ((CutFailureCertificates.Budget027.certificate558).bound:ℝ) at hb
  exact (exponentialBound279 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch013
