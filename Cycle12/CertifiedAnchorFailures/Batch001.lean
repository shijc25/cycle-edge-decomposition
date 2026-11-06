import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch002
import Cycle12.CountingCertificates.Batch003
import Cycle12.CutFailureCertificates.Budget002
import Cycle12.CutFailureCertificates.Budget003
import Cycle12.MergedCutGroups.Batch005
import Cycle12.MergedCutGroups.Batch006
import Cycle12.MergedCutGroups.Batch007
import Cycle12.MergedCutGroups.Batch008
import Cycle12.MergedCutGroups.Batch009
import Cycle12.PopulationCertificates.Batch002
import Cycle12.PopulationCertificates.Batch003
import Cycle12.WitnessCertificates.Batch002
import Cycle12.WitnessCertificates.Batch003

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedAnchorFailures.Batch001
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches20 : (MergedCutGroups.Batch005.certificate62).AnchorMatches CountingCertificates.Batch002.certificate41 := by decide +kernel
theorem exponentialBound20 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch005.certificate62).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate41).dm (WitnessCertificates.Batch002.certificate41).beta (WitnessCertificates.Batch002.certificate41).L) ≤ (2*exp (-((CountingCertificates.Batch002.certificate41).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch005.certificate62).exponent:ℝ)*st.R))/((WitnessCertificates.Batch002.certificate41).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch005.certificate62 CountingCertificates.Batch002.certificate41 matches20 MergedCutGroups.Batch005.numericValid62 MergedCutGroups.Batch005.cellsSound62 MergedCutGroups.Batch005.cellsNumeric62 MergedCutGroups.Batch005.populationMatches62
    PopulationCertificates.Batch002.valid41 PopulationCertificates.Batch002.sound41 WitnessCertificates.Batch002.valid41 WitnessCertificates.Batch002.sound41 CountingCertificates.Batch002.valid41 CountingCertificates.Batch002.sound41 H st hI
theorem probabilityBound20 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch005.certificate62).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate41).dm (WitnessCertificates.Batch002.certificate41).beta (WitnessCertificates.Batch002.certificate41).L) ≤ ((CutFailureCertificates.Budget002.certificate41).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound41 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate41).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch005.certificate62).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch002.certificate41).omega:ℝ)) ≤ ((CutFailureCertificates.Budget002.certificate41).bound:ℝ) at hb
  exact (exponentialBound20 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches21 : (MergedCutGroups.Batch005.certificate65).AnchorMatches CountingCertificates.Batch002.certificate43 := by decide +kernel
theorem exponentialBound21 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch005.certificate65).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate43).dm (WitnessCertificates.Batch002.certificate43).beta (WitnessCertificates.Batch002.certificate43).L) ≤ (2*exp (-((CountingCertificates.Batch002.certificate43).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch005.certificate65).exponent:ℝ)*st.R))/((WitnessCertificates.Batch002.certificate43).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch005.certificate65 CountingCertificates.Batch002.certificate43 matches21 MergedCutGroups.Batch005.numericValid65 MergedCutGroups.Batch005.cellsSound65 MergedCutGroups.Batch005.cellsNumeric65 MergedCutGroups.Batch005.populationMatches65
    PopulationCertificates.Batch002.valid43 PopulationCertificates.Batch002.sound43 WitnessCertificates.Batch002.valid43 WitnessCertificates.Batch002.sound43 CountingCertificates.Batch002.valid43 CountingCertificates.Batch002.sound43 H st hI
theorem probabilityBound21 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch005.certificate65).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate43).dm (WitnessCertificates.Batch002.certificate43).beta (WitnessCertificates.Batch002.certificate43).L) ≤ ((CutFailureCertificates.Budget002.certificate43).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound43 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate43).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch005.certificate65).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch002.certificate43).omega:ℝ)) ≤ ((CutFailureCertificates.Budget002.certificate43).bound:ℝ) at hb
  exact (exponentialBound21 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches22 : (MergedCutGroups.Batch005.certificate68).AnchorMatches CountingCertificates.Batch002.certificate45 := by decide +kernel
theorem exponentialBound22 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch005.certificate68).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate45).dm (WitnessCertificates.Batch002.certificate45).beta (WitnessCertificates.Batch002.certificate45).L) ≤ (2*exp (-((CountingCertificates.Batch002.certificate45).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch005.certificate68).exponent:ℝ)*st.R))/((WitnessCertificates.Batch002.certificate45).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch005.certificate68 CountingCertificates.Batch002.certificate45 matches22 MergedCutGroups.Batch005.numericValid68 MergedCutGroups.Batch005.cellsSound68 MergedCutGroups.Batch005.cellsNumeric68 MergedCutGroups.Batch005.populationMatches68
    PopulationCertificates.Batch002.valid45 PopulationCertificates.Batch002.sound45 WitnessCertificates.Batch002.valid45 WitnessCertificates.Batch002.sound45 CountingCertificates.Batch002.valid45 CountingCertificates.Batch002.sound45 H st hI
theorem probabilityBound22 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch005.certificate68).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate45).dm (WitnessCertificates.Batch002.certificate45).beta (WitnessCertificates.Batch002.certificate45).L) ≤ ((CutFailureCertificates.Budget002.certificate45).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound45 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate45).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch005.certificate68).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch002.certificate45).omega:ℝ)) ≤ ((CutFailureCertificates.Budget002.certificate45).bound:ℝ) at hb
  exact (exponentialBound22 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches23 : (MergedCutGroups.Batch005.certificate71).AnchorMatches CountingCertificates.Batch002.certificate47 := by decide +kernel
theorem exponentialBound23 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch005.certificate71).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate47).dm (WitnessCertificates.Batch002.certificate47).beta (WitnessCertificates.Batch002.certificate47).L) ≤ (2*exp (-((CountingCertificates.Batch002.certificate47).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch005.certificate71).exponent:ℝ)*st.R))/((WitnessCertificates.Batch002.certificate47).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch005.certificate71 CountingCertificates.Batch002.certificate47 matches23 MergedCutGroups.Batch005.numericValid71 MergedCutGroups.Batch005.cellsSound71 MergedCutGroups.Batch005.cellsNumeric71 MergedCutGroups.Batch005.populationMatches71
    PopulationCertificates.Batch002.valid47 PopulationCertificates.Batch002.sound47 WitnessCertificates.Batch002.valid47 WitnessCertificates.Batch002.sound47 CountingCertificates.Batch002.valid47 CountingCertificates.Batch002.sound47 H st hI
theorem probabilityBound23 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch005.certificate71).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate47).dm (WitnessCertificates.Batch002.certificate47).beta (WitnessCertificates.Batch002.certificate47).L) ≤ ((CutFailureCertificates.Budget002.certificate47).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound47 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate47).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch005.certificate71).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch002.certificate47).omega:ℝ)) ≤ ((CutFailureCertificates.Budget002.certificate47).bound:ℝ) at hb
  exact (exponentialBound23 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches24 : (MergedCutGroups.Batch006.certificate74).AnchorMatches CountingCertificates.Batch002.certificate49 := by decide +kernel
theorem exponentialBound24 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch006.certificate74).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate49).dm (WitnessCertificates.Batch002.certificate49).beta (WitnessCertificates.Batch002.certificate49).L) ≤ (2*exp (-((CountingCertificates.Batch002.certificate49).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch006.certificate74).exponent:ℝ)*st.R))/((WitnessCertificates.Batch002.certificate49).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch006.certificate74 CountingCertificates.Batch002.certificate49 matches24 MergedCutGroups.Batch006.numericValid74 MergedCutGroups.Batch006.cellsSound74 MergedCutGroups.Batch006.cellsNumeric74 MergedCutGroups.Batch006.populationMatches74
    PopulationCertificates.Batch002.valid49 PopulationCertificates.Batch002.sound49 WitnessCertificates.Batch002.valid49 WitnessCertificates.Batch002.sound49 CountingCertificates.Batch002.valid49 CountingCertificates.Batch002.sound49 H st hI
theorem probabilityBound24 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch006.certificate74).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate49).dm (WitnessCertificates.Batch002.certificate49).beta (WitnessCertificates.Batch002.certificate49).L) ≤ ((CutFailureCertificates.Budget002.certificate49).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound49 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate49).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch006.certificate74).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch002.certificate49).omega:ℝ)) ≤ ((CutFailureCertificates.Budget002.certificate49).bound:ℝ) at hb
  exact (exponentialBound24 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches25 : (MergedCutGroups.Batch006.certificate77).AnchorMatches CountingCertificates.Batch002.certificate51 := by decide +kernel
theorem exponentialBound25 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch006.certificate77).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate51).dm (WitnessCertificates.Batch002.certificate51).beta (WitnessCertificates.Batch002.certificate51).L) ≤ (2*exp (-((CountingCertificates.Batch002.certificate51).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch006.certificate77).exponent:ℝ)*st.R))/((WitnessCertificates.Batch002.certificate51).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch006.certificate77 CountingCertificates.Batch002.certificate51 matches25 MergedCutGroups.Batch006.numericValid77 MergedCutGroups.Batch006.cellsSound77 MergedCutGroups.Batch006.cellsNumeric77 MergedCutGroups.Batch006.populationMatches77
    PopulationCertificates.Batch002.valid51 PopulationCertificates.Batch002.sound51 WitnessCertificates.Batch002.valid51 WitnessCertificates.Batch002.sound51 CountingCertificates.Batch002.valid51 CountingCertificates.Batch002.sound51 H st hI
theorem probabilityBound25 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch006.certificate77).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate51).dm (WitnessCertificates.Batch002.certificate51).beta (WitnessCertificates.Batch002.certificate51).L) ≤ ((CutFailureCertificates.Budget002.certificate51).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound51 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate51).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch006.certificate77).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch002.certificate51).omega:ℝ)) ≤ ((CutFailureCertificates.Budget002.certificate51).bound:ℝ) at hb
  exact (exponentialBound25 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches26 : (MergedCutGroups.Batch006.certificate80).AnchorMatches CountingCertificates.Batch002.certificate53 := by decide +kernel
theorem exponentialBound26 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch006.certificate80).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate53).dm (WitnessCertificates.Batch002.certificate53).beta (WitnessCertificates.Batch002.certificate53).L) ≤ (2*exp (-((CountingCertificates.Batch002.certificate53).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch006.certificate80).exponent:ℝ)*st.R))/((WitnessCertificates.Batch002.certificate53).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch006.certificate80 CountingCertificates.Batch002.certificate53 matches26 MergedCutGroups.Batch006.numericValid80 MergedCutGroups.Batch006.cellsSound80 MergedCutGroups.Batch006.cellsNumeric80 MergedCutGroups.Batch006.populationMatches80
    PopulationCertificates.Batch002.valid53 PopulationCertificates.Batch002.sound53 WitnessCertificates.Batch002.valid53 WitnessCertificates.Batch002.sound53 CountingCertificates.Batch002.valid53 CountingCertificates.Batch002.sound53 H st hI
theorem probabilityBound26 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch006.certificate80).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate53).dm (WitnessCertificates.Batch002.certificate53).beta (WitnessCertificates.Batch002.certificate53).L) ≤ ((CutFailureCertificates.Budget002.certificate53).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound53 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate53).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch006.certificate80).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch002.certificate53).omega:ℝ)) ≤ ((CutFailureCertificates.Budget002.certificate53).bound:ℝ) at hb
  exact (exponentialBound26 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches27 : (MergedCutGroups.Batch006.certificate83).AnchorMatches CountingCertificates.Batch002.certificate55 := by decide +kernel
theorem exponentialBound27 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch006.certificate83).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate55).dm (WitnessCertificates.Batch002.certificate55).beta (WitnessCertificates.Batch002.certificate55).L) ≤ (2*exp (-((CountingCertificates.Batch002.certificate55).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch006.certificate83).exponent:ℝ)*st.R))/((WitnessCertificates.Batch002.certificate55).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch006.certificate83 CountingCertificates.Batch002.certificate55 matches27 MergedCutGroups.Batch006.numericValid83 MergedCutGroups.Batch006.cellsSound83 MergedCutGroups.Batch006.cellsNumeric83 MergedCutGroups.Batch006.populationMatches83
    PopulationCertificates.Batch002.valid55 PopulationCertificates.Batch002.sound55 WitnessCertificates.Batch002.valid55 WitnessCertificates.Batch002.sound55 CountingCertificates.Batch002.valid55 CountingCertificates.Batch002.sound55 H st hI
theorem probabilityBound27 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch006.certificate83).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate55).dm (WitnessCertificates.Batch002.certificate55).beta (WitnessCertificates.Batch002.certificate55).L) ≤ ((CutFailureCertificates.Budget002.certificate55).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound55 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate55).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch006.certificate83).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch002.certificate55).omega:ℝ)) ≤ ((CutFailureCertificates.Budget002.certificate55).bound:ℝ) at hb
  exact (exponentialBound27 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches28 : (MergedCutGroups.Batch007.certificate86).AnchorMatches CountingCertificates.Batch002.certificate57 := by decide +kernel
theorem exponentialBound28 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch007.certificate86).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate57).dm (WitnessCertificates.Batch002.certificate57).beta (WitnessCertificates.Batch002.certificate57).L) ≤ (2*exp (-((CountingCertificates.Batch002.certificate57).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch007.certificate86).exponent:ℝ)*st.R))/((WitnessCertificates.Batch002.certificate57).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch007.certificate86 CountingCertificates.Batch002.certificate57 matches28 MergedCutGroups.Batch007.numericValid86 MergedCutGroups.Batch007.cellsSound86 MergedCutGroups.Batch007.cellsNumeric86 MergedCutGroups.Batch007.populationMatches86
    PopulationCertificates.Batch002.valid57 PopulationCertificates.Batch002.sound57 WitnessCertificates.Batch002.valid57 WitnessCertificates.Batch002.sound57 CountingCertificates.Batch002.valid57 CountingCertificates.Batch002.sound57 H st hI
theorem probabilityBound28 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch007.certificate86).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate57).dm (WitnessCertificates.Batch002.certificate57).beta (WitnessCertificates.Batch002.certificate57).L) ≤ ((CutFailureCertificates.Budget002.certificate57).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound57 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate57).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch007.certificate86).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch002.certificate57).omega:ℝ)) ≤ ((CutFailureCertificates.Budget002.certificate57).bound:ℝ) at hb
  exact (exponentialBound28 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches29 : (MergedCutGroups.Batch007.certificate89).AnchorMatches CountingCertificates.Batch002.certificate59 := by decide +kernel
theorem exponentialBound29 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch007.certificate89).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate59).dm (WitnessCertificates.Batch002.certificate59).beta (WitnessCertificates.Batch002.certificate59).L) ≤ (2*exp (-((CountingCertificates.Batch002.certificate59).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch007.certificate89).exponent:ℝ)*st.R))/((WitnessCertificates.Batch002.certificate59).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch007.certificate89 CountingCertificates.Batch002.certificate59 matches29 MergedCutGroups.Batch007.numericValid89 MergedCutGroups.Batch007.cellsSound89 MergedCutGroups.Batch007.cellsNumeric89 MergedCutGroups.Batch007.populationMatches89
    PopulationCertificates.Batch002.valid59 PopulationCertificates.Batch002.sound59 WitnessCertificates.Batch002.valid59 WitnessCertificates.Batch002.sound59 CountingCertificates.Batch002.valid59 CountingCertificates.Batch002.sound59 H st hI
theorem probabilityBound29 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch007.certificate89).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch002.certificate59).dm (WitnessCertificates.Batch002.certificate59).beta (WitnessCertificates.Batch002.certificate59).L) ≤ ((CutFailureCertificates.Budget002.certificate59).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget002.sound59 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch002.certificate59).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch007.certificate89).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch002.certificate59).omega:ℝ)) ≤ ((CutFailureCertificates.Budget002.certificate59).bound:ℝ) at hb
  exact (exponentialBound29 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches30 : (MergedCutGroups.Batch007.certificate92).AnchorMatches CountingCertificates.Batch003.certificate61 := by decide +kernel
theorem exponentialBound30 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch007.certificate92).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate61).dm (WitnessCertificates.Batch003.certificate61).beta (WitnessCertificates.Batch003.certificate61).L) ≤ (2*exp (-((CountingCertificates.Batch003.certificate61).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch007.certificate92).exponent:ℝ)*st.R))/((WitnessCertificates.Batch003.certificate61).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch007.certificate92 CountingCertificates.Batch003.certificate61 matches30 MergedCutGroups.Batch007.numericValid92 MergedCutGroups.Batch007.cellsSound92 MergedCutGroups.Batch007.cellsNumeric92 MergedCutGroups.Batch007.populationMatches92
    PopulationCertificates.Batch003.valid61 PopulationCertificates.Batch003.sound61 WitnessCertificates.Batch003.valid61 WitnessCertificates.Batch003.sound61 CountingCertificates.Batch003.valid61 CountingCertificates.Batch003.sound61 H st hI
theorem probabilityBound30 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch007.certificate92).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate61).dm (WitnessCertificates.Batch003.certificate61).beta (WitnessCertificates.Batch003.certificate61).L) ≤ ((CutFailureCertificates.Budget003.certificate61).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound61 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate61).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch007.certificate92).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch003.certificate61).omega:ℝ)) ≤ ((CutFailureCertificates.Budget003.certificate61).bound:ℝ) at hb
  exact (exponentialBound30 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches31 : (MergedCutGroups.Batch007.certificate95).AnchorMatches CountingCertificates.Batch003.certificate63 := by decide +kernel
theorem exponentialBound31 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch007.certificate95).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate63).dm (WitnessCertificates.Batch003.certificate63).beta (WitnessCertificates.Batch003.certificate63).L) ≤ (2*exp (-((CountingCertificates.Batch003.certificate63).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch007.certificate95).exponent:ℝ)*st.R))/((WitnessCertificates.Batch003.certificate63).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch007.certificate95 CountingCertificates.Batch003.certificate63 matches31 MergedCutGroups.Batch007.numericValid95 MergedCutGroups.Batch007.cellsSound95 MergedCutGroups.Batch007.cellsNumeric95 MergedCutGroups.Batch007.populationMatches95
    PopulationCertificates.Batch003.valid63 PopulationCertificates.Batch003.sound63 WitnessCertificates.Batch003.valid63 WitnessCertificates.Batch003.sound63 CountingCertificates.Batch003.valid63 CountingCertificates.Batch003.sound63 H st hI
theorem probabilityBound31 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch007.certificate95).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate63).dm (WitnessCertificates.Batch003.certificate63).beta (WitnessCertificates.Batch003.certificate63).L) ≤ ((CutFailureCertificates.Budget003.certificate63).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound63 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate63).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch007.certificate95).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch003.certificate63).omega:ℝ)) ≤ ((CutFailureCertificates.Budget003.certificate63).bound:ℝ) at hb
  exact (exponentialBound31 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches32 : (MergedCutGroups.Batch008.certificate98).AnchorMatches CountingCertificates.Batch003.certificate65 := by decide +kernel
theorem exponentialBound32 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch008.certificate98).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate65).dm (WitnessCertificates.Batch003.certificate65).beta (WitnessCertificates.Batch003.certificate65).L) ≤ (2*exp (-((CountingCertificates.Batch003.certificate65).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch008.certificate98).exponent:ℝ)*st.R))/((WitnessCertificates.Batch003.certificate65).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch008.certificate98 CountingCertificates.Batch003.certificate65 matches32 MergedCutGroups.Batch008.numericValid98 MergedCutGroups.Batch008.cellsSound98 MergedCutGroups.Batch008.cellsNumeric98 MergedCutGroups.Batch008.populationMatches98
    PopulationCertificates.Batch003.valid65 PopulationCertificates.Batch003.sound65 WitnessCertificates.Batch003.valid65 WitnessCertificates.Batch003.sound65 CountingCertificates.Batch003.valid65 CountingCertificates.Batch003.sound65 H st hI
theorem probabilityBound32 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch008.certificate98).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate65).dm (WitnessCertificates.Batch003.certificate65).beta (WitnessCertificates.Batch003.certificate65).L) ≤ ((CutFailureCertificates.Budget003.certificate65).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound65 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate65).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch008.certificate98).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch003.certificate65).omega:ℝ)) ≤ ((CutFailureCertificates.Budget003.certificate65).bound:ℝ) at hb
  exact (exponentialBound32 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches33 : (MergedCutGroups.Batch008.certificate101).AnchorMatches CountingCertificates.Batch003.certificate67 := by decide +kernel
theorem exponentialBound33 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch008.certificate101).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate67).dm (WitnessCertificates.Batch003.certificate67).beta (WitnessCertificates.Batch003.certificate67).L) ≤ (2*exp (-((CountingCertificates.Batch003.certificate67).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch008.certificate101).exponent:ℝ)*st.R))/((WitnessCertificates.Batch003.certificate67).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch008.certificate101 CountingCertificates.Batch003.certificate67 matches33 MergedCutGroups.Batch008.numericValid101 MergedCutGroups.Batch008.cellsSound101 MergedCutGroups.Batch008.cellsNumeric101 MergedCutGroups.Batch008.populationMatches101
    PopulationCertificates.Batch003.valid67 PopulationCertificates.Batch003.sound67 WitnessCertificates.Batch003.valid67 WitnessCertificates.Batch003.sound67 CountingCertificates.Batch003.valid67 CountingCertificates.Batch003.sound67 H st hI
theorem probabilityBound33 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch008.certificate101).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate67).dm (WitnessCertificates.Batch003.certificate67).beta (WitnessCertificates.Batch003.certificate67).L) ≤ ((CutFailureCertificates.Budget003.certificate67).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound67 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate67).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch008.certificate101).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch003.certificate67).omega:ℝ)) ≤ ((CutFailureCertificates.Budget003.certificate67).bound:ℝ) at hb
  exact (exponentialBound33 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches34 : (MergedCutGroups.Batch008.certificate104).AnchorMatches CountingCertificates.Batch003.certificate69 := by decide +kernel
theorem exponentialBound34 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch008.certificate104).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate69).dm (WitnessCertificates.Batch003.certificate69).beta (WitnessCertificates.Batch003.certificate69).L) ≤ (2*exp (-((CountingCertificates.Batch003.certificate69).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch008.certificate104).exponent:ℝ)*st.R))/((WitnessCertificates.Batch003.certificate69).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch008.certificate104 CountingCertificates.Batch003.certificate69 matches34 MergedCutGroups.Batch008.numericValid104 MergedCutGroups.Batch008.cellsSound104 MergedCutGroups.Batch008.cellsNumeric104 MergedCutGroups.Batch008.populationMatches104
    PopulationCertificates.Batch003.valid69 PopulationCertificates.Batch003.sound69 WitnessCertificates.Batch003.valid69 WitnessCertificates.Batch003.sound69 CountingCertificates.Batch003.valid69 CountingCertificates.Batch003.sound69 H st hI
theorem probabilityBound34 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch008.certificate104).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate69).dm (WitnessCertificates.Batch003.certificate69).beta (WitnessCertificates.Batch003.certificate69).L) ≤ ((CutFailureCertificates.Budget003.certificate69).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound69 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate69).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch008.certificate104).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch003.certificate69).omega:ℝ)) ≤ ((CutFailureCertificates.Budget003.certificate69).bound:ℝ) at hb
  exact (exponentialBound34 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches35 : (MergedCutGroups.Batch008.certificate107).AnchorMatches CountingCertificates.Batch003.certificate71 := by decide +kernel
theorem exponentialBound35 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch008.certificate107).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate71).dm (WitnessCertificates.Batch003.certificate71).beta (WitnessCertificates.Batch003.certificate71).L) ≤ (2*exp (-((CountingCertificates.Batch003.certificate71).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch008.certificate107).exponent:ℝ)*st.R))/((WitnessCertificates.Batch003.certificate71).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch008.certificate107 CountingCertificates.Batch003.certificate71 matches35 MergedCutGroups.Batch008.numericValid107 MergedCutGroups.Batch008.cellsSound107 MergedCutGroups.Batch008.cellsNumeric107 MergedCutGroups.Batch008.populationMatches107
    PopulationCertificates.Batch003.valid71 PopulationCertificates.Batch003.sound71 WitnessCertificates.Batch003.valid71 WitnessCertificates.Batch003.sound71 CountingCertificates.Batch003.valid71 CountingCertificates.Batch003.sound71 H st hI
theorem probabilityBound35 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch008.certificate107).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate71).dm (WitnessCertificates.Batch003.certificate71).beta (WitnessCertificates.Batch003.certificate71).L) ≤ ((CutFailureCertificates.Budget003.certificate71).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound71 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate71).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch008.certificate107).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch003.certificate71).omega:ℝ)) ≤ ((CutFailureCertificates.Budget003.certificate71).bound:ℝ) at hb
  exact (exponentialBound35 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches36 : (MergedCutGroups.Batch009.certificate110).AnchorMatches CountingCertificates.Batch003.certificate73 := by decide +kernel
theorem exponentialBound36 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch009.certificate110).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate73).dm (WitnessCertificates.Batch003.certificate73).beta (WitnessCertificates.Batch003.certificate73).L) ≤ (2*exp (-((CountingCertificates.Batch003.certificate73).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch009.certificate110).exponent:ℝ)*st.R))/((WitnessCertificates.Batch003.certificate73).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch009.certificate110 CountingCertificates.Batch003.certificate73 matches36 MergedCutGroups.Batch009.numericValid110 MergedCutGroups.Batch009.cellsSound110 MergedCutGroups.Batch009.cellsNumeric110 MergedCutGroups.Batch009.populationMatches110
    PopulationCertificates.Batch003.valid73 PopulationCertificates.Batch003.sound73 WitnessCertificates.Batch003.valid73 WitnessCertificates.Batch003.sound73 CountingCertificates.Batch003.valid73 CountingCertificates.Batch003.sound73 H st hI
theorem probabilityBound36 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch009.certificate110).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate73).dm (WitnessCertificates.Batch003.certificate73).beta (WitnessCertificates.Batch003.certificate73).L) ≤ ((CutFailureCertificates.Budget003.certificate73).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound73 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate73).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch009.certificate110).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch003.certificate73).omega:ℝ)) ≤ ((CutFailureCertificates.Budget003.certificate73).bound:ℝ) at hb
  exact (exponentialBound36 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches37 : (MergedCutGroups.Batch009.certificate113).AnchorMatches CountingCertificates.Batch003.certificate75 := by decide +kernel
theorem exponentialBound37 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch009.certificate113).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate75).dm (WitnessCertificates.Batch003.certificate75).beta (WitnessCertificates.Batch003.certificate75).L) ≤ (2*exp (-((CountingCertificates.Batch003.certificate75).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch009.certificate113).exponent:ℝ)*st.R))/((WitnessCertificates.Batch003.certificate75).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch009.certificate113 CountingCertificates.Batch003.certificate75 matches37 MergedCutGroups.Batch009.numericValid113 MergedCutGroups.Batch009.cellsSound113 MergedCutGroups.Batch009.cellsNumeric113 MergedCutGroups.Batch009.populationMatches113
    PopulationCertificates.Batch003.valid75 PopulationCertificates.Batch003.sound75 WitnessCertificates.Batch003.valid75 WitnessCertificates.Batch003.sound75 CountingCertificates.Batch003.valid75 CountingCertificates.Batch003.sound75 H st hI
theorem probabilityBound37 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch009.certificate113).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate75).dm (WitnessCertificates.Batch003.certificate75).beta (WitnessCertificates.Batch003.certificate75).L) ≤ ((CutFailureCertificates.Budget003.certificate75).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound75 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate75).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch009.certificate113).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch003.certificate75).omega:ℝ)) ≤ ((CutFailureCertificates.Budget003.certificate75).bound:ℝ) at hb
  exact (exponentialBound37 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches38 : (MergedCutGroups.Batch009.certificate116).AnchorMatches CountingCertificates.Batch003.certificate77 := by decide +kernel
theorem exponentialBound38 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch009.certificate116).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate77).dm (WitnessCertificates.Batch003.certificate77).beta (WitnessCertificates.Batch003.certificate77).L) ≤ (2*exp (-((CountingCertificates.Batch003.certificate77).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch009.certificate116).exponent:ℝ)*st.R))/((WitnessCertificates.Batch003.certificate77).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch009.certificate116 CountingCertificates.Batch003.certificate77 matches38 MergedCutGroups.Batch009.numericValid116 MergedCutGroups.Batch009.cellsSound116 MergedCutGroups.Batch009.cellsNumeric116 MergedCutGroups.Batch009.populationMatches116
    PopulationCertificates.Batch003.valid77 PopulationCertificates.Batch003.sound77 WitnessCertificates.Batch003.valid77 WitnessCertificates.Batch003.sound77 CountingCertificates.Batch003.valid77 CountingCertificates.Batch003.sound77 H st hI
theorem probabilityBound38 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch009.certificate116).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate77).dm (WitnessCertificates.Batch003.certificate77).beta (WitnessCertificates.Batch003.certificate77).L) ≤ ((CutFailureCertificates.Budget003.certificate77).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound77 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate77).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch009.certificate116).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch003.certificate77).omega:ℝ)) ≤ ((CutFailureCertificates.Budget003.certificate77).bound:ℝ) at hb
  exact (exponentialBound38 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches39 : (MergedCutGroups.Batch009.certificate119).AnchorMatches CountingCertificates.Batch003.certificate79 := by decide +kernel
theorem exponentialBound39 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch009.certificate119).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate79).dm (WitnessCertificates.Batch003.certificate79).beta (WitnessCertificates.Batch003.certificate79).L) ≤ (2*exp (-((CountingCertificates.Batch003.certificate79).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch009.certificate119).exponent:ℝ)*st.R))/((WitnessCertificates.Batch003.certificate79).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch009.certificate119 CountingCertificates.Batch003.certificate79 matches39 MergedCutGroups.Batch009.numericValid119 MergedCutGroups.Batch009.cellsSound119 MergedCutGroups.Batch009.cellsNumeric119 MergedCutGroups.Batch009.populationMatches119
    PopulationCertificates.Batch003.valid79 PopulationCertificates.Batch003.sound79 WitnessCertificates.Batch003.valid79 WitnessCertificates.Batch003.sound79 CountingCertificates.Batch003.valid79 CountingCertificates.Batch003.sound79 H st hI
theorem probabilityBound39 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch009.certificate119).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch003.certificate79).dm (WitnessCertificates.Batch003.certificate79).beta (WitnessCertificates.Batch003.certificate79).L) ≤ ((CutFailureCertificates.Budget003.certificate79).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget003.sound79 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch003.certificate79).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch009.certificate119).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch003.certificate79).omega:ℝ)) ≤ ((CutFailureCertificates.Budget003.certificate79).bound:ℝ) at hb
  exact (exponentialBound39 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch001
