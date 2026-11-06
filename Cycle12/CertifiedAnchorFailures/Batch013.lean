import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch026
import Cycle12.CountingCertificates.Batch027
import Cycle12.CutFailureCertificates.Budget026
import Cycle12.CutFailureCertificates.Budget027
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

namespace Cycle12.CertifiedAnchorFailures.Batch013
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches260 : (MergedCutGroups.Batch065.certificate782).AnchorMatches CountingCertificates.Batch026.certificate521 := by decide +kernel
theorem exponentialBound260 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch065.certificate782).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate521).dm (WitnessCertificates.Batch026.certificate521).beta (WitnessCertificates.Batch026.certificate521).L) ≤ (2*exp (-((CountingCertificates.Batch026.certificate521).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch065.certificate782).exponent:ℝ)*st.R))/((WitnessCertificates.Batch026.certificate521).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch065.certificate782 CountingCertificates.Batch026.certificate521 matches260 MergedCutGroups.Batch065.numericValid782 MergedCutGroups.Batch065.cellsSound782 MergedCutGroups.Batch065.cellsNumeric782 MergedCutGroups.Batch065.populationMatches782
    PopulationCertificates.Batch026.valid521 PopulationCertificates.Batch026.sound521 WitnessCertificates.Batch026.valid521 WitnessCertificates.Batch026.sound521 CountingCertificates.Batch026.valid521 CountingCertificates.Batch026.sound521 H st hI
theorem probabilityBound260 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch065.certificate782).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate521).dm (WitnessCertificates.Batch026.certificate521).beta (WitnessCertificates.Batch026.certificate521).L) ≤ ((CutFailureCertificates.Budget026.certificate521).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound521 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate521).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch065.certificate782).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch026.certificate521).omega:ℝ)) ≤ ((CutFailureCertificates.Budget026.certificate521).bound:ℝ) at hb
  exact (exponentialBound260 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches261 : (MergedCutGroups.Batch065.certificate785).AnchorMatches CountingCertificates.Batch026.certificate523 := by decide +kernel
theorem exponentialBound261 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch065.certificate785).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate523).dm (WitnessCertificates.Batch026.certificate523).beta (WitnessCertificates.Batch026.certificate523).L) ≤ (2*exp (-((CountingCertificates.Batch026.certificate523).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch065.certificate785).exponent:ℝ)*st.R))/((WitnessCertificates.Batch026.certificate523).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch065.certificate785 CountingCertificates.Batch026.certificate523 matches261 MergedCutGroups.Batch065.numericValid785 MergedCutGroups.Batch065.cellsSound785 MergedCutGroups.Batch065.cellsNumeric785 MergedCutGroups.Batch065.populationMatches785
    PopulationCertificates.Batch026.valid523 PopulationCertificates.Batch026.sound523 WitnessCertificates.Batch026.valid523 WitnessCertificates.Batch026.sound523 CountingCertificates.Batch026.valid523 CountingCertificates.Batch026.sound523 H st hI
theorem probabilityBound261 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch065.certificate785).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate523).dm (WitnessCertificates.Batch026.certificate523).beta (WitnessCertificates.Batch026.certificate523).L) ≤ ((CutFailureCertificates.Budget026.certificate523).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound523 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate523).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch065.certificate785).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch026.certificate523).omega:ℝ)) ≤ ((CutFailureCertificates.Budget026.certificate523).bound:ℝ) at hb
  exact (exponentialBound261 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches262 : (MergedCutGroups.Batch065.certificate788).AnchorMatches CountingCertificates.Batch026.certificate525 := by decide +kernel
theorem exponentialBound262 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch065.certificate788).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate525).dm (WitnessCertificates.Batch026.certificate525).beta (WitnessCertificates.Batch026.certificate525).L) ≤ (2*exp (-((CountingCertificates.Batch026.certificate525).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch065.certificate788).exponent:ℝ)*st.R))/((WitnessCertificates.Batch026.certificate525).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch065.certificate788 CountingCertificates.Batch026.certificate525 matches262 MergedCutGroups.Batch065.numericValid788 MergedCutGroups.Batch065.cellsSound788 MergedCutGroups.Batch065.cellsNumeric788 MergedCutGroups.Batch065.populationMatches788
    PopulationCertificates.Batch026.valid525 PopulationCertificates.Batch026.sound525 WitnessCertificates.Batch026.valid525 WitnessCertificates.Batch026.sound525 CountingCertificates.Batch026.valid525 CountingCertificates.Batch026.sound525 H st hI
theorem probabilityBound262 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch065.certificate788).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate525).dm (WitnessCertificates.Batch026.certificate525).beta (WitnessCertificates.Batch026.certificate525).L) ≤ ((CutFailureCertificates.Budget026.certificate525).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound525 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate525).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch065.certificate788).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch026.certificate525).omega:ℝ)) ≤ ((CutFailureCertificates.Budget026.certificate525).bound:ℝ) at hb
  exact (exponentialBound262 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches263 : (MergedCutGroups.Batch065.certificate791).AnchorMatches CountingCertificates.Batch026.certificate527 := by decide +kernel
theorem exponentialBound263 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch065.certificate791).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate527).dm (WitnessCertificates.Batch026.certificate527).beta (WitnessCertificates.Batch026.certificate527).L) ≤ (2*exp (-((CountingCertificates.Batch026.certificate527).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch065.certificate791).exponent:ℝ)*st.R))/((WitnessCertificates.Batch026.certificate527).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch065.certificate791 CountingCertificates.Batch026.certificate527 matches263 MergedCutGroups.Batch065.numericValid791 MergedCutGroups.Batch065.cellsSound791 MergedCutGroups.Batch065.cellsNumeric791 MergedCutGroups.Batch065.populationMatches791
    PopulationCertificates.Batch026.valid527 PopulationCertificates.Batch026.sound527 WitnessCertificates.Batch026.valid527 WitnessCertificates.Batch026.sound527 CountingCertificates.Batch026.valid527 CountingCertificates.Batch026.sound527 H st hI
theorem probabilityBound263 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch065.certificate791).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate527).dm (WitnessCertificates.Batch026.certificate527).beta (WitnessCertificates.Batch026.certificate527).L) ≤ ((CutFailureCertificates.Budget026.certificate527).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound527 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate527).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch065.certificate791).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch026.certificate527).omega:ℝ)) ≤ ((CutFailureCertificates.Budget026.certificate527).bound:ℝ) at hb
  exact (exponentialBound263 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches264 : (MergedCutGroups.Batch066.certificate794).AnchorMatches CountingCertificates.Batch026.certificate529 := by decide +kernel
theorem exponentialBound264 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch066.certificate794).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate529).dm (WitnessCertificates.Batch026.certificate529).beta (WitnessCertificates.Batch026.certificate529).L) ≤ (2*exp (-((CountingCertificates.Batch026.certificate529).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch066.certificate794).exponent:ℝ)*st.R))/((WitnessCertificates.Batch026.certificate529).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch066.certificate794 CountingCertificates.Batch026.certificate529 matches264 MergedCutGroups.Batch066.numericValid794 MergedCutGroups.Batch066.cellsSound794 MergedCutGroups.Batch066.cellsNumeric794 MergedCutGroups.Batch066.populationMatches794
    PopulationCertificates.Batch026.valid529 PopulationCertificates.Batch026.sound529 WitnessCertificates.Batch026.valid529 WitnessCertificates.Batch026.sound529 CountingCertificates.Batch026.valid529 CountingCertificates.Batch026.sound529 H st hI
theorem probabilityBound264 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch066.certificate794).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate529).dm (WitnessCertificates.Batch026.certificate529).beta (WitnessCertificates.Batch026.certificate529).L) ≤ ((CutFailureCertificates.Budget026.certificate529).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound529 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate529).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch066.certificate794).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch026.certificate529).omega:ℝ)) ≤ ((CutFailureCertificates.Budget026.certificate529).bound:ℝ) at hb
  exact (exponentialBound264 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches265 : (MergedCutGroups.Batch066.certificate797).AnchorMatches CountingCertificates.Batch026.certificate531 := by decide +kernel
theorem exponentialBound265 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch066.certificate797).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate531).dm (WitnessCertificates.Batch026.certificate531).beta (WitnessCertificates.Batch026.certificate531).L) ≤ (2*exp (-((CountingCertificates.Batch026.certificate531).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch066.certificate797).exponent:ℝ)*st.R))/((WitnessCertificates.Batch026.certificate531).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch066.certificate797 CountingCertificates.Batch026.certificate531 matches265 MergedCutGroups.Batch066.numericValid797 MergedCutGroups.Batch066.cellsSound797 MergedCutGroups.Batch066.cellsNumeric797 MergedCutGroups.Batch066.populationMatches797
    PopulationCertificates.Batch026.valid531 PopulationCertificates.Batch026.sound531 WitnessCertificates.Batch026.valid531 WitnessCertificates.Batch026.sound531 CountingCertificates.Batch026.valid531 CountingCertificates.Batch026.sound531 H st hI
theorem probabilityBound265 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch066.certificate797).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate531).dm (WitnessCertificates.Batch026.certificate531).beta (WitnessCertificates.Batch026.certificate531).L) ≤ ((CutFailureCertificates.Budget026.certificate531).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound531 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate531).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch066.certificate797).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch026.certificate531).omega:ℝ)) ≤ ((CutFailureCertificates.Budget026.certificate531).bound:ℝ) at hb
  exact (exponentialBound265 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches266 : (MergedCutGroups.Batch066.certificate800).AnchorMatches CountingCertificates.Batch026.certificate533 := by decide +kernel
theorem exponentialBound266 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch066.certificate800).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate533).dm (WitnessCertificates.Batch026.certificate533).beta (WitnessCertificates.Batch026.certificate533).L) ≤ (2*exp (-((CountingCertificates.Batch026.certificate533).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch066.certificate800).exponent:ℝ)*st.R))/((WitnessCertificates.Batch026.certificate533).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch066.certificate800 CountingCertificates.Batch026.certificate533 matches266 MergedCutGroups.Batch066.numericValid800 MergedCutGroups.Batch066.cellsSound800 MergedCutGroups.Batch066.cellsNumeric800 MergedCutGroups.Batch066.populationMatches800
    PopulationCertificates.Batch026.valid533 PopulationCertificates.Batch026.sound533 WitnessCertificates.Batch026.valid533 WitnessCertificates.Batch026.sound533 CountingCertificates.Batch026.valid533 CountingCertificates.Batch026.sound533 H st hI
theorem probabilityBound266 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch066.certificate800).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate533).dm (WitnessCertificates.Batch026.certificate533).beta (WitnessCertificates.Batch026.certificate533).L) ≤ ((CutFailureCertificates.Budget026.certificate533).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound533 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate533).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch066.certificate800).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch026.certificate533).omega:ℝ)) ≤ ((CutFailureCertificates.Budget026.certificate533).bound:ℝ) at hb
  exact (exponentialBound266 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches267 : (MergedCutGroups.Batch066.certificate803).AnchorMatches CountingCertificates.Batch026.certificate535 := by decide +kernel
theorem exponentialBound267 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch066.certificate803).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate535).dm (WitnessCertificates.Batch026.certificate535).beta (WitnessCertificates.Batch026.certificate535).L) ≤ (2*exp (-((CountingCertificates.Batch026.certificate535).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch066.certificate803).exponent:ℝ)*st.R))/((WitnessCertificates.Batch026.certificate535).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch066.certificate803 CountingCertificates.Batch026.certificate535 matches267 MergedCutGroups.Batch066.numericValid803 MergedCutGroups.Batch066.cellsSound803 MergedCutGroups.Batch066.cellsNumeric803 MergedCutGroups.Batch066.populationMatches803
    PopulationCertificates.Batch026.valid535 PopulationCertificates.Batch026.sound535 WitnessCertificates.Batch026.valid535 WitnessCertificates.Batch026.sound535 CountingCertificates.Batch026.valid535 CountingCertificates.Batch026.sound535 H st hI
theorem probabilityBound267 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch066.certificate803).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate535).dm (WitnessCertificates.Batch026.certificate535).beta (WitnessCertificates.Batch026.certificate535).L) ≤ ((CutFailureCertificates.Budget026.certificate535).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound535 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate535).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch066.certificate803).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch026.certificate535).omega:ℝ)) ≤ ((CutFailureCertificates.Budget026.certificate535).bound:ℝ) at hb
  exact (exponentialBound267 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches268 : (MergedCutGroups.Batch067.certificate806).AnchorMatches CountingCertificates.Batch026.certificate537 := by decide +kernel
theorem exponentialBound268 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch067.certificate806).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate537).dm (WitnessCertificates.Batch026.certificate537).beta (WitnessCertificates.Batch026.certificate537).L) ≤ (2*exp (-((CountingCertificates.Batch026.certificate537).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch067.certificate806).exponent:ℝ)*st.R))/((WitnessCertificates.Batch026.certificate537).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch067.certificate806 CountingCertificates.Batch026.certificate537 matches268 MergedCutGroups.Batch067.numericValid806 MergedCutGroups.Batch067.cellsSound806 MergedCutGroups.Batch067.cellsNumeric806 MergedCutGroups.Batch067.populationMatches806
    PopulationCertificates.Batch026.valid537 PopulationCertificates.Batch026.sound537 WitnessCertificates.Batch026.valid537 WitnessCertificates.Batch026.sound537 CountingCertificates.Batch026.valid537 CountingCertificates.Batch026.sound537 H st hI
theorem probabilityBound268 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch067.certificate806).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate537).dm (WitnessCertificates.Batch026.certificate537).beta (WitnessCertificates.Batch026.certificate537).L) ≤ ((CutFailureCertificates.Budget026.certificate537).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound537 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate537).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch067.certificate806).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch026.certificate537).omega:ℝ)) ≤ ((CutFailureCertificates.Budget026.certificate537).bound:ℝ) at hb
  exact (exponentialBound268 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches269 : (MergedCutGroups.Batch067.certificate809).AnchorMatches CountingCertificates.Batch026.certificate539 := by decide +kernel
theorem exponentialBound269 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch067.certificate809).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate539).dm (WitnessCertificates.Batch026.certificate539).beta (WitnessCertificates.Batch026.certificate539).L) ≤ (2*exp (-((CountingCertificates.Batch026.certificate539).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch067.certificate809).exponent:ℝ)*st.R))/((WitnessCertificates.Batch026.certificate539).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch067.certificate809 CountingCertificates.Batch026.certificate539 matches269 MergedCutGroups.Batch067.numericValid809 MergedCutGroups.Batch067.cellsSound809 MergedCutGroups.Batch067.cellsNumeric809 MergedCutGroups.Batch067.populationMatches809
    PopulationCertificates.Batch026.valid539 PopulationCertificates.Batch026.sound539 WitnessCertificates.Batch026.valid539 WitnessCertificates.Batch026.sound539 CountingCertificates.Batch026.valid539 CountingCertificates.Batch026.sound539 H st hI
theorem probabilityBound269 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch067.certificate809).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch026.certificate539).dm (WitnessCertificates.Batch026.certificate539).beta (WitnessCertificates.Batch026.certificate539).L) ≤ ((CutFailureCertificates.Budget026.certificate539).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget026.sound539 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch026.certificate539).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch067.certificate809).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch026.certificate539).omega:ℝ)) ≤ ((CutFailureCertificates.Budget026.certificate539).bound:ℝ) at hb
  exact (exponentialBound269 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches270 : (MergedCutGroups.Batch067.certificate812).AnchorMatches CountingCertificates.Batch027.certificate541 := by decide +kernel
theorem exponentialBound270 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch067.certificate812).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate541).dm (WitnessCertificates.Batch027.certificate541).beta (WitnessCertificates.Batch027.certificate541).L) ≤ (2*exp (-((CountingCertificates.Batch027.certificate541).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch067.certificate812).exponent:ℝ)*st.R))/((WitnessCertificates.Batch027.certificate541).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch067.certificate812 CountingCertificates.Batch027.certificate541 matches270 MergedCutGroups.Batch067.numericValid812 MergedCutGroups.Batch067.cellsSound812 MergedCutGroups.Batch067.cellsNumeric812 MergedCutGroups.Batch067.populationMatches812
    PopulationCertificates.Batch027.valid541 PopulationCertificates.Batch027.sound541 WitnessCertificates.Batch027.valid541 WitnessCertificates.Batch027.sound541 CountingCertificates.Batch027.valid541 CountingCertificates.Batch027.sound541 H st hI
theorem probabilityBound270 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch067.certificate812).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate541).dm (WitnessCertificates.Batch027.certificate541).beta (WitnessCertificates.Batch027.certificate541).L) ≤ ((CutFailureCertificates.Budget027.certificate541).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound541 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate541).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch067.certificate812).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch027.certificate541).omega:ℝ)) ≤ ((CutFailureCertificates.Budget027.certificate541).bound:ℝ) at hb
  exact (exponentialBound270 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches271 : (MergedCutGroups.Batch067.certificate815).AnchorMatches CountingCertificates.Batch027.certificate543 := by decide +kernel
theorem exponentialBound271 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch067.certificate815).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate543).dm (WitnessCertificates.Batch027.certificate543).beta (WitnessCertificates.Batch027.certificate543).L) ≤ (2*exp (-((CountingCertificates.Batch027.certificate543).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch067.certificate815).exponent:ℝ)*st.R))/((WitnessCertificates.Batch027.certificate543).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch067.certificate815 CountingCertificates.Batch027.certificate543 matches271 MergedCutGroups.Batch067.numericValid815 MergedCutGroups.Batch067.cellsSound815 MergedCutGroups.Batch067.cellsNumeric815 MergedCutGroups.Batch067.populationMatches815
    PopulationCertificates.Batch027.valid543 PopulationCertificates.Batch027.sound543 WitnessCertificates.Batch027.valid543 WitnessCertificates.Batch027.sound543 CountingCertificates.Batch027.valid543 CountingCertificates.Batch027.sound543 H st hI
theorem probabilityBound271 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch067.certificate815).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate543).dm (WitnessCertificates.Batch027.certificate543).beta (WitnessCertificates.Batch027.certificate543).L) ≤ ((CutFailureCertificates.Budget027.certificate543).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound543 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate543).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch067.certificate815).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch027.certificate543).omega:ℝ)) ≤ ((CutFailureCertificates.Budget027.certificate543).bound:ℝ) at hb
  exact (exponentialBound271 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches272 : (MergedCutGroups.Batch068.certificate818).AnchorMatches CountingCertificates.Batch027.certificate545 := by decide +kernel
theorem exponentialBound272 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch068.certificate818).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate545).dm (WitnessCertificates.Batch027.certificate545).beta (WitnessCertificates.Batch027.certificate545).L) ≤ (2*exp (-((CountingCertificates.Batch027.certificate545).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch068.certificate818).exponent:ℝ)*st.R))/((WitnessCertificates.Batch027.certificate545).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch068.certificate818 CountingCertificates.Batch027.certificate545 matches272 MergedCutGroups.Batch068.numericValid818 MergedCutGroups.Batch068.cellsSound818 MergedCutGroups.Batch068.cellsNumeric818 MergedCutGroups.Batch068.populationMatches818
    PopulationCertificates.Batch027.valid545 PopulationCertificates.Batch027.sound545 WitnessCertificates.Batch027.valid545 WitnessCertificates.Batch027.sound545 CountingCertificates.Batch027.valid545 CountingCertificates.Batch027.sound545 H st hI
theorem probabilityBound272 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch068.certificate818).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate545).dm (WitnessCertificates.Batch027.certificate545).beta (WitnessCertificates.Batch027.certificate545).L) ≤ ((CutFailureCertificates.Budget027.certificate545).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound545 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate545).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch068.certificate818).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch027.certificate545).omega:ℝ)) ≤ ((CutFailureCertificates.Budget027.certificate545).bound:ℝ) at hb
  exact (exponentialBound272 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches273 : (MergedCutGroups.Batch068.certificate821).AnchorMatches CountingCertificates.Batch027.certificate547 := by decide +kernel
theorem exponentialBound273 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch068.certificate821).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate547).dm (WitnessCertificates.Batch027.certificate547).beta (WitnessCertificates.Batch027.certificate547).L) ≤ (2*exp (-((CountingCertificates.Batch027.certificate547).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch068.certificate821).exponent:ℝ)*st.R))/((WitnessCertificates.Batch027.certificate547).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch068.certificate821 CountingCertificates.Batch027.certificate547 matches273 MergedCutGroups.Batch068.numericValid821 MergedCutGroups.Batch068.cellsSound821 MergedCutGroups.Batch068.cellsNumeric821 MergedCutGroups.Batch068.populationMatches821
    PopulationCertificates.Batch027.valid547 PopulationCertificates.Batch027.sound547 WitnessCertificates.Batch027.valid547 WitnessCertificates.Batch027.sound547 CountingCertificates.Batch027.valid547 CountingCertificates.Batch027.sound547 H st hI
theorem probabilityBound273 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch068.certificate821).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate547).dm (WitnessCertificates.Batch027.certificate547).beta (WitnessCertificates.Batch027.certificate547).L) ≤ ((CutFailureCertificates.Budget027.certificate547).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound547 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate547).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch068.certificate821).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch027.certificate547).omega:ℝ)) ≤ ((CutFailureCertificates.Budget027.certificate547).bound:ℝ) at hb
  exact (exponentialBound273 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches274 : (MergedCutGroups.Batch068.certificate824).AnchorMatches CountingCertificates.Batch027.certificate549 := by decide +kernel
theorem exponentialBound274 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch068.certificate824).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate549).dm (WitnessCertificates.Batch027.certificate549).beta (WitnessCertificates.Batch027.certificate549).L) ≤ (2*exp (-((CountingCertificates.Batch027.certificate549).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch068.certificate824).exponent:ℝ)*st.R))/((WitnessCertificates.Batch027.certificate549).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch068.certificate824 CountingCertificates.Batch027.certificate549 matches274 MergedCutGroups.Batch068.numericValid824 MergedCutGroups.Batch068.cellsSound824 MergedCutGroups.Batch068.cellsNumeric824 MergedCutGroups.Batch068.populationMatches824
    PopulationCertificates.Batch027.valid549 PopulationCertificates.Batch027.sound549 WitnessCertificates.Batch027.valid549 WitnessCertificates.Batch027.sound549 CountingCertificates.Batch027.valid549 CountingCertificates.Batch027.sound549 H st hI
theorem probabilityBound274 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch068.certificate824).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate549).dm (WitnessCertificates.Batch027.certificate549).beta (WitnessCertificates.Batch027.certificate549).L) ≤ ((CutFailureCertificates.Budget027.certificate549).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound549 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate549).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch068.certificate824).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch027.certificate549).omega:ℝ)) ≤ ((CutFailureCertificates.Budget027.certificate549).bound:ℝ) at hb
  exact (exponentialBound274 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches275 : (MergedCutGroups.Batch068.certificate827).AnchorMatches CountingCertificates.Batch027.certificate551 := by decide +kernel
theorem exponentialBound275 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch068.certificate827).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate551).dm (WitnessCertificates.Batch027.certificate551).beta (WitnessCertificates.Batch027.certificate551).L) ≤ (2*exp (-((CountingCertificates.Batch027.certificate551).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch068.certificate827).exponent:ℝ)*st.R))/((WitnessCertificates.Batch027.certificate551).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch068.certificate827 CountingCertificates.Batch027.certificate551 matches275 MergedCutGroups.Batch068.numericValid827 MergedCutGroups.Batch068.cellsSound827 MergedCutGroups.Batch068.cellsNumeric827 MergedCutGroups.Batch068.populationMatches827
    PopulationCertificates.Batch027.valid551 PopulationCertificates.Batch027.sound551 WitnessCertificates.Batch027.valid551 WitnessCertificates.Batch027.sound551 CountingCertificates.Batch027.valid551 CountingCertificates.Batch027.sound551 H st hI
theorem probabilityBound275 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch068.certificate827).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate551).dm (WitnessCertificates.Batch027.certificate551).beta (WitnessCertificates.Batch027.certificate551).L) ≤ ((CutFailureCertificates.Budget027.certificate551).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound551 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate551).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch068.certificate827).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch027.certificate551).omega:ℝ)) ≤ ((CutFailureCertificates.Budget027.certificate551).bound:ℝ) at hb
  exact (exponentialBound275 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches276 : (MergedCutGroups.Batch069.certificate830).AnchorMatches CountingCertificates.Batch027.certificate553 := by decide +kernel
theorem exponentialBound276 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch069.certificate830).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate553).dm (WitnessCertificates.Batch027.certificate553).beta (WitnessCertificates.Batch027.certificate553).L) ≤ (2*exp (-((CountingCertificates.Batch027.certificate553).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch069.certificate830).exponent:ℝ)*st.R))/((WitnessCertificates.Batch027.certificate553).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch069.certificate830 CountingCertificates.Batch027.certificate553 matches276 MergedCutGroups.Batch069.numericValid830 MergedCutGroups.Batch069.cellsSound830 MergedCutGroups.Batch069.cellsNumeric830 MergedCutGroups.Batch069.populationMatches830
    PopulationCertificates.Batch027.valid553 PopulationCertificates.Batch027.sound553 WitnessCertificates.Batch027.valid553 WitnessCertificates.Batch027.sound553 CountingCertificates.Batch027.valid553 CountingCertificates.Batch027.sound553 H st hI
theorem probabilityBound276 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch069.certificate830).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate553).dm (WitnessCertificates.Batch027.certificate553).beta (WitnessCertificates.Batch027.certificate553).L) ≤ ((CutFailureCertificates.Budget027.certificate553).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound553 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate553).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch069.certificate830).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch027.certificate553).omega:ℝ)) ≤ ((CutFailureCertificates.Budget027.certificate553).bound:ℝ) at hb
  exact (exponentialBound276 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches277 : (MergedCutGroups.Batch069.certificate833).AnchorMatches CountingCertificates.Batch027.certificate555 := by decide +kernel
theorem exponentialBound277 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch069.certificate833).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate555).dm (WitnessCertificates.Batch027.certificate555).beta (WitnessCertificates.Batch027.certificate555).L) ≤ (2*exp (-((CountingCertificates.Batch027.certificate555).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch069.certificate833).exponent:ℝ)*st.R))/((WitnessCertificates.Batch027.certificate555).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch069.certificate833 CountingCertificates.Batch027.certificate555 matches277 MergedCutGroups.Batch069.numericValid833 MergedCutGroups.Batch069.cellsSound833 MergedCutGroups.Batch069.cellsNumeric833 MergedCutGroups.Batch069.populationMatches833
    PopulationCertificates.Batch027.valid555 PopulationCertificates.Batch027.sound555 WitnessCertificates.Batch027.valid555 WitnessCertificates.Batch027.sound555 CountingCertificates.Batch027.valid555 CountingCertificates.Batch027.sound555 H st hI
theorem probabilityBound277 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch069.certificate833).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate555).dm (WitnessCertificates.Batch027.certificate555).beta (WitnessCertificates.Batch027.certificate555).L) ≤ ((CutFailureCertificates.Budget027.certificate555).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound555 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate555).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch069.certificate833).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch027.certificate555).omega:ℝ)) ≤ ((CutFailureCertificates.Budget027.certificate555).bound:ℝ) at hb
  exact (exponentialBound277 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches278 : (MergedCutGroups.Batch069.certificate836).AnchorMatches CountingCertificates.Batch027.certificate557 := by decide +kernel
theorem exponentialBound278 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch069.certificate836).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate557).dm (WitnessCertificates.Batch027.certificate557).beta (WitnessCertificates.Batch027.certificate557).L) ≤ (2*exp (-((CountingCertificates.Batch027.certificate557).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch069.certificate836).exponent:ℝ)*st.R))/((WitnessCertificates.Batch027.certificate557).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch069.certificate836 CountingCertificates.Batch027.certificate557 matches278 MergedCutGroups.Batch069.numericValid836 MergedCutGroups.Batch069.cellsSound836 MergedCutGroups.Batch069.cellsNumeric836 MergedCutGroups.Batch069.populationMatches836
    PopulationCertificates.Batch027.valid557 PopulationCertificates.Batch027.sound557 WitnessCertificates.Batch027.valid557 WitnessCertificates.Batch027.sound557 CountingCertificates.Batch027.valid557 CountingCertificates.Batch027.sound557 H st hI
theorem probabilityBound278 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch069.certificate836).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate557).dm (WitnessCertificates.Batch027.certificate557).beta (WitnessCertificates.Batch027.certificate557).L) ≤ ((CutFailureCertificates.Budget027.certificate557).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound557 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate557).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch069.certificate836).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch027.certificate557).omega:ℝ)) ≤ ((CutFailureCertificates.Budget027.certificate557).bound:ℝ) at hb
  exact (exponentialBound278 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches279 : (MergedCutGroups.Batch069.certificate839).AnchorMatches CountingCertificates.Batch027.certificate559 := by decide +kernel
theorem exponentialBound279 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch069.certificate839).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate559).dm (WitnessCertificates.Batch027.certificate559).beta (WitnessCertificates.Batch027.certificate559).L) ≤ (2*exp (-((CountingCertificates.Batch027.certificate559).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch069.certificate839).exponent:ℝ)*st.R))/((WitnessCertificates.Batch027.certificate559).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch069.certificate839 CountingCertificates.Batch027.certificate559 matches279 MergedCutGroups.Batch069.numericValid839 MergedCutGroups.Batch069.cellsSound839 MergedCutGroups.Batch069.cellsNumeric839 MergedCutGroups.Batch069.populationMatches839
    PopulationCertificates.Batch027.valid559 PopulationCertificates.Batch027.sound559 WitnessCertificates.Batch027.valid559 WitnessCertificates.Batch027.sound559 CountingCertificates.Batch027.valid559 CountingCertificates.Batch027.sound559 H st hI
theorem probabilityBound279 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch069.certificate839).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch027.certificate559).dm (WitnessCertificates.Batch027.certificate559).beta (WitnessCertificates.Batch027.certificate559).L) ≤ ((CutFailureCertificates.Budget027.certificate559).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget027.sound559 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch027.certificate559).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch069.certificate839).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch027.certificate559).omega:ℝ)) ≤ ((CutFailureCertificates.Budget027.certificate559).bound:ℝ) at hb
  exact (exponentialBound279 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch013
