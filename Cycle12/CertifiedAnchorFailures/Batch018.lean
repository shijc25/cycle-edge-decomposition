import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch036
import Cycle12.CountingCertificates.Batch037
import Cycle12.CutFailureCertificates.Budget036
import Cycle12.CutFailureCertificates.Budget037
import Cycle12.MergedCutGroups.Batch090
import Cycle12.MergedCutGroups.Batch091
import Cycle12.MergedCutGroups.Batch092
import Cycle12.MergedCutGroups.Batch093
import Cycle12.MergedCutGroups.Batch094
import Cycle12.PopulationCertificates.Batch036
import Cycle12.PopulationCertificates.Batch037
import Cycle12.WitnessCertificates.Batch036
import Cycle12.WitnessCertificates.Batch037

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedAnchorFailures.Batch018
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches360 : (MergedCutGroups.Batch090.certificate1082).AnchorMatches CountingCertificates.Batch036.certificate721 := by decide +kernel
theorem exponentialBound360 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch090.certificate1082).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate721).dm (WitnessCertificates.Batch036.certificate721).beta (WitnessCertificates.Batch036.certificate721).L) ≤ (2*exp (-((CountingCertificates.Batch036.certificate721).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch090.certificate1082).exponent:ℝ)*st.R))/((WitnessCertificates.Batch036.certificate721).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch090.certificate1082 CountingCertificates.Batch036.certificate721 matches360 MergedCutGroups.Batch090.numericValid1082 MergedCutGroups.Batch090.cellsSound1082 MergedCutGroups.Batch090.cellsNumeric1082 MergedCutGroups.Batch090.populationMatches1082
    PopulationCertificates.Batch036.valid721 PopulationCertificates.Batch036.sound721 WitnessCertificates.Batch036.valid721 WitnessCertificates.Batch036.sound721 CountingCertificates.Batch036.valid721 CountingCertificates.Batch036.sound721 H st hI
theorem probabilityBound360 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch090.certificate1082).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate721).dm (WitnessCertificates.Batch036.certificate721).beta (WitnessCertificates.Batch036.certificate721).L) ≤ ((CutFailureCertificates.Budget036.certificate721).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound721 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate721).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch090.certificate1082).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch036.certificate721).omega:ℝ)) ≤ ((CutFailureCertificates.Budget036.certificate721).bound:ℝ) at hb
  exact (exponentialBound360 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches361 : (MergedCutGroups.Batch090.certificate1085).AnchorMatches CountingCertificates.Batch036.certificate723 := by decide +kernel
theorem exponentialBound361 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch090.certificate1085).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate723).dm (WitnessCertificates.Batch036.certificate723).beta (WitnessCertificates.Batch036.certificate723).L) ≤ (2*exp (-((CountingCertificates.Batch036.certificate723).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch090.certificate1085).exponent:ℝ)*st.R))/((WitnessCertificates.Batch036.certificate723).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch090.certificate1085 CountingCertificates.Batch036.certificate723 matches361 MergedCutGroups.Batch090.numericValid1085 MergedCutGroups.Batch090.cellsSound1085 MergedCutGroups.Batch090.cellsNumeric1085 MergedCutGroups.Batch090.populationMatches1085
    PopulationCertificates.Batch036.valid723 PopulationCertificates.Batch036.sound723 WitnessCertificates.Batch036.valid723 WitnessCertificates.Batch036.sound723 CountingCertificates.Batch036.valid723 CountingCertificates.Batch036.sound723 H st hI
theorem probabilityBound361 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch090.certificate1085).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate723).dm (WitnessCertificates.Batch036.certificate723).beta (WitnessCertificates.Batch036.certificate723).L) ≤ ((CutFailureCertificates.Budget036.certificate723).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound723 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate723).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch090.certificate1085).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch036.certificate723).omega:ℝ)) ≤ ((CutFailureCertificates.Budget036.certificate723).bound:ℝ) at hb
  exact (exponentialBound361 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches362 : (MergedCutGroups.Batch090.certificate1088).AnchorMatches CountingCertificates.Batch036.certificate725 := by decide +kernel
theorem exponentialBound362 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch090.certificate1088).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate725).dm (WitnessCertificates.Batch036.certificate725).beta (WitnessCertificates.Batch036.certificate725).L) ≤ (2*exp (-((CountingCertificates.Batch036.certificate725).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch090.certificate1088).exponent:ℝ)*st.R))/((WitnessCertificates.Batch036.certificate725).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch090.certificate1088 CountingCertificates.Batch036.certificate725 matches362 MergedCutGroups.Batch090.numericValid1088 MergedCutGroups.Batch090.cellsSound1088 MergedCutGroups.Batch090.cellsNumeric1088 MergedCutGroups.Batch090.populationMatches1088
    PopulationCertificates.Batch036.valid725 PopulationCertificates.Batch036.sound725 WitnessCertificates.Batch036.valid725 WitnessCertificates.Batch036.sound725 CountingCertificates.Batch036.valid725 CountingCertificates.Batch036.sound725 H st hI
theorem probabilityBound362 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch090.certificate1088).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate725).dm (WitnessCertificates.Batch036.certificate725).beta (WitnessCertificates.Batch036.certificate725).L) ≤ ((CutFailureCertificates.Budget036.certificate725).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound725 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate725).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch090.certificate1088).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch036.certificate725).omega:ℝ)) ≤ ((CutFailureCertificates.Budget036.certificate725).bound:ℝ) at hb
  exact (exponentialBound362 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches363 : (MergedCutGroups.Batch090.certificate1091).AnchorMatches CountingCertificates.Batch036.certificate727 := by decide +kernel
theorem exponentialBound363 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch090.certificate1091).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate727).dm (WitnessCertificates.Batch036.certificate727).beta (WitnessCertificates.Batch036.certificate727).L) ≤ (2*exp (-((CountingCertificates.Batch036.certificate727).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch090.certificate1091).exponent:ℝ)*st.R))/((WitnessCertificates.Batch036.certificate727).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch090.certificate1091 CountingCertificates.Batch036.certificate727 matches363 MergedCutGroups.Batch090.numericValid1091 MergedCutGroups.Batch090.cellsSound1091 MergedCutGroups.Batch090.cellsNumeric1091 MergedCutGroups.Batch090.populationMatches1091
    PopulationCertificates.Batch036.valid727 PopulationCertificates.Batch036.sound727 WitnessCertificates.Batch036.valid727 WitnessCertificates.Batch036.sound727 CountingCertificates.Batch036.valid727 CountingCertificates.Batch036.sound727 H st hI
theorem probabilityBound363 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch090.certificate1091).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate727).dm (WitnessCertificates.Batch036.certificate727).beta (WitnessCertificates.Batch036.certificate727).L) ≤ ((CutFailureCertificates.Budget036.certificate727).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound727 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate727).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch090.certificate1091).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch036.certificate727).omega:ℝ)) ≤ ((CutFailureCertificates.Budget036.certificate727).bound:ℝ) at hb
  exact (exponentialBound363 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches364 : (MergedCutGroups.Batch091.certificate1094).AnchorMatches CountingCertificates.Batch036.certificate729 := by decide +kernel
theorem exponentialBound364 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch091.certificate1094).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate729).dm (WitnessCertificates.Batch036.certificate729).beta (WitnessCertificates.Batch036.certificate729).L) ≤ (2*exp (-((CountingCertificates.Batch036.certificate729).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch091.certificate1094).exponent:ℝ)*st.R))/((WitnessCertificates.Batch036.certificate729).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch091.certificate1094 CountingCertificates.Batch036.certificate729 matches364 MergedCutGroups.Batch091.numericValid1094 MergedCutGroups.Batch091.cellsSound1094 MergedCutGroups.Batch091.cellsNumeric1094 MergedCutGroups.Batch091.populationMatches1094
    PopulationCertificates.Batch036.valid729 PopulationCertificates.Batch036.sound729 WitnessCertificates.Batch036.valid729 WitnessCertificates.Batch036.sound729 CountingCertificates.Batch036.valid729 CountingCertificates.Batch036.sound729 H st hI
theorem probabilityBound364 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch091.certificate1094).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate729).dm (WitnessCertificates.Batch036.certificate729).beta (WitnessCertificates.Batch036.certificate729).L) ≤ ((CutFailureCertificates.Budget036.certificate729).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound729 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate729).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch091.certificate1094).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch036.certificate729).omega:ℝ)) ≤ ((CutFailureCertificates.Budget036.certificate729).bound:ℝ) at hb
  exact (exponentialBound364 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches365 : (MergedCutGroups.Batch091.certificate1097).AnchorMatches CountingCertificates.Batch036.certificate731 := by decide +kernel
theorem exponentialBound365 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch091.certificate1097).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate731).dm (WitnessCertificates.Batch036.certificate731).beta (WitnessCertificates.Batch036.certificate731).L) ≤ (2*exp (-((CountingCertificates.Batch036.certificate731).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch091.certificate1097).exponent:ℝ)*st.R))/((WitnessCertificates.Batch036.certificate731).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch091.certificate1097 CountingCertificates.Batch036.certificate731 matches365 MergedCutGroups.Batch091.numericValid1097 MergedCutGroups.Batch091.cellsSound1097 MergedCutGroups.Batch091.cellsNumeric1097 MergedCutGroups.Batch091.populationMatches1097
    PopulationCertificates.Batch036.valid731 PopulationCertificates.Batch036.sound731 WitnessCertificates.Batch036.valid731 WitnessCertificates.Batch036.sound731 CountingCertificates.Batch036.valid731 CountingCertificates.Batch036.sound731 H st hI
theorem probabilityBound365 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch091.certificate1097).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate731).dm (WitnessCertificates.Batch036.certificate731).beta (WitnessCertificates.Batch036.certificate731).L) ≤ ((CutFailureCertificates.Budget036.certificate731).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound731 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate731).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch091.certificate1097).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch036.certificate731).omega:ℝ)) ≤ ((CutFailureCertificates.Budget036.certificate731).bound:ℝ) at hb
  exact (exponentialBound365 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches366 : (MergedCutGroups.Batch091.certificate1100).AnchorMatches CountingCertificates.Batch036.certificate733 := by decide +kernel
theorem exponentialBound366 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch091.certificate1100).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate733).dm (WitnessCertificates.Batch036.certificate733).beta (WitnessCertificates.Batch036.certificate733).L) ≤ (2*exp (-((CountingCertificates.Batch036.certificate733).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch091.certificate1100).exponent:ℝ)*st.R))/((WitnessCertificates.Batch036.certificate733).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch091.certificate1100 CountingCertificates.Batch036.certificate733 matches366 MergedCutGroups.Batch091.numericValid1100 MergedCutGroups.Batch091.cellsSound1100 MergedCutGroups.Batch091.cellsNumeric1100 MergedCutGroups.Batch091.populationMatches1100
    PopulationCertificates.Batch036.valid733 PopulationCertificates.Batch036.sound733 WitnessCertificates.Batch036.valid733 WitnessCertificates.Batch036.sound733 CountingCertificates.Batch036.valid733 CountingCertificates.Batch036.sound733 H st hI
theorem probabilityBound366 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch091.certificate1100).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate733).dm (WitnessCertificates.Batch036.certificate733).beta (WitnessCertificates.Batch036.certificate733).L) ≤ ((CutFailureCertificates.Budget036.certificate733).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound733 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate733).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch091.certificate1100).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch036.certificate733).omega:ℝ)) ≤ ((CutFailureCertificates.Budget036.certificate733).bound:ℝ) at hb
  exact (exponentialBound366 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches367 : (MergedCutGroups.Batch091.certificate1103).AnchorMatches CountingCertificates.Batch036.certificate735 := by decide +kernel
theorem exponentialBound367 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch091.certificate1103).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate735).dm (WitnessCertificates.Batch036.certificate735).beta (WitnessCertificates.Batch036.certificate735).L) ≤ (2*exp (-((CountingCertificates.Batch036.certificate735).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch091.certificate1103).exponent:ℝ)*st.R))/((WitnessCertificates.Batch036.certificate735).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch091.certificate1103 CountingCertificates.Batch036.certificate735 matches367 MergedCutGroups.Batch091.numericValid1103 MergedCutGroups.Batch091.cellsSound1103 MergedCutGroups.Batch091.cellsNumeric1103 MergedCutGroups.Batch091.populationMatches1103
    PopulationCertificates.Batch036.valid735 PopulationCertificates.Batch036.sound735 WitnessCertificates.Batch036.valid735 WitnessCertificates.Batch036.sound735 CountingCertificates.Batch036.valid735 CountingCertificates.Batch036.sound735 H st hI
theorem probabilityBound367 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch091.certificate1103).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate735).dm (WitnessCertificates.Batch036.certificate735).beta (WitnessCertificates.Batch036.certificate735).L) ≤ ((CutFailureCertificates.Budget036.certificate735).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound735 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate735).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch091.certificate1103).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch036.certificate735).omega:ℝ)) ≤ ((CutFailureCertificates.Budget036.certificate735).bound:ℝ) at hb
  exact (exponentialBound367 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches368 : (MergedCutGroups.Batch092.certificate1106).AnchorMatches CountingCertificates.Batch036.certificate737 := by decide +kernel
theorem exponentialBound368 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch092.certificate1106).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate737).dm (WitnessCertificates.Batch036.certificate737).beta (WitnessCertificates.Batch036.certificate737).L) ≤ (2*exp (-((CountingCertificates.Batch036.certificate737).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch092.certificate1106).exponent:ℝ)*st.R))/((WitnessCertificates.Batch036.certificate737).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch092.certificate1106 CountingCertificates.Batch036.certificate737 matches368 MergedCutGroups.Batch092.numericValid1106 MergedCutGroups.Batch092.cellsSound1106 MergedCutGroups.Batch092.cellsNumeric1106 MergedCutGroups.Batch092.populationMatches1106
    PopulationCertificates.Batch036.valid737 PopulationCertificates.Batch036.sound737 WitnessCertificates.Batch036.valid737 WitnessCertificates.Batch036.sound737 CountingCertificates.Batch036.valid737 CountingCertificates.Batch036.sound737 H st hI
theorem probabilityBound368 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch092.certificate1106).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate737).dm (WitnessCertificates.Batch036.certificate737).beta (WitnessCertificates.Batch036.certificate737).L) ≤ ((CutFailureCertificates.Budget036.certificate737).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound737 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate737).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch092.certificate1106).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch036.certificate737).omega:ℝ)) ≤ ((CutFailureCertificates.Budget036.certificate737).bound:ℝ) at hb
  exact (exponentialBound368 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches369 : (MergedCutGroups.Batch092.certificate1109).AnchorMatches CountingCertificates.Batch036.certificate739 := by decide +kernel
theorem exponentialBound369 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch092.certificate1109).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate739).dm (WitnessCertificates.Batch036.certificate739).beta (WitnessCertificates.Batch036.certificate739).L) ≤ (2*exp (-((CountingCertificates.Batch036.certificate739).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch092.certificate1109).exponent:ℝ)*st.R))/((WitnessCertificates.Batch036.certificate739).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch092.certificate1109 CountingCertificates.Batch036.certificate739 matches369 MergedCutGroups.Batch092.numericValid1109 MergedCutGroups.Batch092.cellsSound1109 MergedCutGroups.Batch092.cellsNumeric1109 MergedCutGroups.Batch092.populationMatches1109
    PopulationCertificates.Batch036.valid739 PopulationCertificates.Batch036.sound739 WitnessCertificates.Batch036.valid739 WitnessCertificates.Batch036.sound739 CountingCertificates.Batch036.valid739 CountingCertificates.Batch036.sound739 H st hI
theorem probabilityBound369 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch092.certificate1109).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch036.certificate739).dm (WitnessCertificates.Batch036.certificate739).beta (WitnessCertificates.Batch036.certificate739).L) ≤ ((CutFailureCertificates.Budget036.certificate739).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound739 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate739).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch092.certificate1109).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch036.certificate739).omega:ℝ)) ≤ ((CutFailureCertificates.Budget036.certificate739).bound:ℝ) at hb
  exact (exponentialBound369 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches370 : (MergedCutGroups.Batch092.certificate1112).AnchorMatches CountingCertificates.Batch037.certificate741 := by decide +kernel
theorem exponentialBound370 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch092.certificate1112).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate741).dm (WitnessCertificates.Batch037.certificate741).beta (WitnessCertificates.Batch037.certificate741).L) ≤ (2*exp (-((CountingCertificates.Batch037.certificate741).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch092.certificate1112).exponent:ℝ)*st.R))/((WitnessCertificates.Batch037.certificate741).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch092.certificate1112 CountingCertificates.Batch037.certificate741 matches370 MergedCutGroups.Batch092.numericValid1112 MergedCutGroups.Batch092.cellsSound1112 MergedCutGroups.Batch092.cellsNumeric1112 MergedCutGroups.Batch092.populationMatches1112
    PopulationCertificates.Batch037.valid741 PopulationCertificates.Batch037.sound741 WitnessCertificates.Batch037.valid741 WitnessCertificates.Batch037.sound741 CountingCertificates.Batch037.valid741 CountingCertificates.Batch037.sound741 H st hI
theorem probabilityBound370 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch092.certificate1112).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate741).dm (WitnessCertificates.Batch037.certificate741).beta (WitnessCertificates.Batch037.certificate741).L) ≤ ((CutFailureCertificates.Budget037.certificate741).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound741 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate741).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch092.certificate1112).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch037.certificate741).omega:ℝ)) ≤ ((CutFailureCertificates.Budget037.certificate741).bound:ℝ) at hb
  exact (exponentialBound370 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches371 : (MergedCutGroups.Batch092.certificate1115).AnchorMatches CountingCertificates.Batch037.certificate743 := by decide +kernel
theorem exponentialBound371 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch092.certificate1115).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate743).dm (WitnessCertificates.Batch037.certificate743).beta (WitnessCertificates.Batch037.certificate743).L) ≤ (2*exp (-((CountingCertificates.Batch037.certificate743).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch092.certificate1115).exponent:ℝ)*st.R))/((WitnessCertificates.Batch037.certificate743).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch092.certificate1115 CountingCertificates.Batch037.certificate743 matches371 MergedCutGroups.Batch092.numericValid1115 MergedCutGroups.Batch092.cellsSound1115 MergedCutGroups.Batch092.cellsNumeric1115 MergedCutGroups.Batch092.populationMatches1115
    PopulationCertificates.Batch037.valid743 PopulationCertificates.Batch037.sound743 WitnessCertificates.Batch037.valid743 WitnessCertificates.Batch037.sound743 CountingCertificates.Batch037.valid743 CountingCertificates.Batch037.sound743 H st hI
theorem probabilityBound371 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch092.certificate1115).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate743).dm (WitnessCertificates.Batch037.certificate743).beta (WitnessCertificates.Batch037.certificate743).L) ≤ ((CutFailureCertificates.Budget037.certificate743).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound743 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate743).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch092.certificate1115).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch037.certificate743).omega:ℝ)) ≤ ((CutFailureCertificates.Budget037.certificate743).bound:ℝ) at hb
  exact (exponentialBound371 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches372 : (MergedCutGroups.Batch093.certificate1118).AnchorMatches CountingCertificates.Batch037.certificate745 := by decide +kernel
theorem exponentialBound372 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch093.certificate1118).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate745).dm (WitnessCertificates.Batch037.certificate745).beta (WitnessCertificates.Batch037.certificate745).L) ≤ (2*exp (-((CountingCertificates.Batch037.certificate745).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch093.certificate1118).exponent:ℝ)*st.R))/((WitnessCertificates.Batch037.certificate745).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch093.certificate1118 CountingCertificates.Batch037.certificate745 matches372 MergedCutGroups.Batch093.numericValid1118 MergedCutGroups.Batch093.cellsSound1118 MergedCutGroups.Batch093.cellsNumeric1118 MergedCutGroups.Batch093.populationMatches1118
    PopulationCertificates.Batch037.valid745 PopulationCertificates.Batch037.sound745 WitnessCertificates.Batch037.valid745 WitnessCertificates.Batch037.sound745 CountingCertificates.Batch037.valid745 CountingCertificates.Batch037.sound745 H st hI
theorem probabilityBound372 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch093.certificate1118).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate745).dm (WitnessCertificates.Batch037.certificate745).beta (WitnessCertificates.Batch037.certificate745).L) ≤ ((CutFailureCertificates.Budget037.certificate745).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound745 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate745).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch093.certificate1118).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch037.certificate745).omega:ℝ)) ≤ ((CutFailureCertificates.Budget037.certificate745).bound:ℝ) at hb
  exact (exponentialBound372 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches373 : (MergedCutGroups.Batch093.certificate1121).AnchorMatches CountingCertificates.Batch037.certificate747 := by decide +kernel
theorem exponentialBound373 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch093.certificate1121).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate747).dm (WitnessCertificates.Batch037.certificate747).beta (WitnessCertificates.Batch037.certificate747).L) ≤ (2*exp (-((CountingCertificates.Batch037.certificate747).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch093.certificate1121).exponent:ℝ)*st.R))/((WitnessCertificates.Batch037.certificate747).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch093.certificate1121 CountingCertificates.Batch037.certificate747 matches373 MergedCutGroups.Batch093.numericValid1121 MergedCutGroups.Batch093.cellsSound1121 MergedCutGroups.Batch093.cellsNumeric1121 MergedCutGroups.Batch093.populationMatches1121
    PopulationCertificates.Batch037.valid747 PopulationCertificates.Batch037.sound747 WitnessCertificates.Batch037.valid747 WitnessCertificates.Batch037.sound747 CountingCertificates.Batch037.valid747 CountingCertificates.Batch037.sound747 H st hI
theorem probabilityBound373 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch093.certificate1121).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate747).dm (WitnessCertificates.Batch037.certificate747).beta (WitnessCertificates.Batch037.certificate747).L) ≤ ((CutFailureCertificates.Budget037.certificate747).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound747 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate747).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch093.certificate1121).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch037.certificate747).omega:ℝ)) ≤ ((CutFailureCertificates.Budget037.certificate747).bound:ℝ) at hb
  exact (exponentialBound373 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches374 : (MergedCutGroups.Batch093.certificate1124).AnchorMatches CountingCertificates.Batch037.certificate749 := by decide +kernel
theorem exponentialBound374 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch093.certificate1124).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate749).dm (WitnessCertificates.Batch037.certificate749).beta (WitnessCertificates.Batch037.certificate749).L) ≤ (2*exp (-((CountingCertificates.Batch037.certificate749).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch093.certificate1124).exponent:ℝ)*st.R))/((WitnessCertificates.Batch037.certificate749).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch093.certificate1124 CountingCertificates.Batch037.certificate749 matches374 MergedCutGroups.Batch093.numericValid1124 MergedCutGroups.Batch093.cellsSound1124 MergedCutGroups.Batch093.cellsNumeric1124 MergedCutGroups.Batch093.populationMatches1124
    PopulationCertificates.Batch037.valid749 PopulationCertificates.Batch037.sound749 WitnessCertificates.Batch037.valid749 WitnessCertificates.Batch037.sound749 CountingCertificates.Batch037.valid749 CountingCertificates.Batch037.sound749 H st hI
theorem probabilityBound374 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch093.certificate1124).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate749).dm (WitnessCertificates.Batch037.certificate749).beta (WitnessCertificates.Batch037.certificate749).L) ≤ ((CutFailureCertificates.Budget037.certificate749).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound749 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate749).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch093.certificate1124).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch037.certificate749).omega:ℝ)) ≤ ((CutFailureCertificates.Budget037.certificate749).bound:ℝ) at hb
  exact (exponentialBound374 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches375 : (MergedCutGroups.Batch093.certificate1127).AnchorMatches CountingCertificates.Batch037.certificate751 := by decide +kernel
theorem exponentialBound375 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch093.certificate1127).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate751).dm (WitnessCertificates.Batch037.certificate751).beta (WitnessCertificates.Batch037.certificate751).L) ≤ (2*exp (-((CountingCertificates.Batch037.certificate751).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch093.certificate1127).exponent:ℝ)*st.R))/((WitnessCertificates.Batch037.certificate751).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch093.certificate1127 CountingCertificates.Batch037.certificate751 matches375 MergedCutGroups.Batch093.numericValid1127 MergedCutGroups.Batch093.cellsSound1127 MergedCutGroups.Batch093.cellsNumeric1127 MergedCutGroups.Batch093.populationMatches1127
    PopulationCertificates.Batch037.valid751 PopulationCertificates.Batch037.sound751 WitnessCertificates.Batch037.valid751 WitnessCertificates.Batch037.sound751 CountingCertificates.Batch037.valid751 CountingCertificates.Batch037.sound751 H st hI
theorem probabilityBound375 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch093.certificate1127).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate751).dm (WitnessCertificates.Batch037.certificate751).beta (WitnessCertificates.Batch037.certificate751).L) ≤ ((CutFailureCertificates.Budget037.certificate751).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound751 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate751).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch093.certificate1127).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch037.certificate751).omega:ℝ)) ≤ ((CutFailureCertificates.Budget037.certificate751).bound:ℝ) at hb
  exact (exponentialBound375 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches376 : (MergedCutGroups.Batch094.certificate1130).AnchorMatches CountingCertificates.Batch037.certificate753 := by decide +kernel
theorem exponentialBound376 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch094.certificate1130).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate753).dm (WitnessCertificates.Batch037.certificate753).beta (WitnessCertificates.Batch037.certificate753).L) ≤ (2*exp (-((CountingCertificates.Batch037.certificate753).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch094.certificate1130).exponent:ℝ)*st.R))/((WitnessCertificates.Batch037.certificate753).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch094.certificate1130 CountingCertificates.Batch037.certificate753 matches376 MergedCutGroups.Batch094.numericValid1130 MergedCutGroups.Batch094.cellsSound1130 MergedCutGroups.Batch094.cellsNumeric1130 MergedCutGroups.Batch094.populationMatches1130
    PopulationCertificates.Batch037.valid753 PopulationCertificates.Batch037.sound753 WitnessCertificates.Batch037.valid753 WitnessCertificates.Batch037.sound753 CountingCertificates.Batch037.valid753 CountingCertificates.Batch037.sound753 H st hI
theorem probabilityBound376 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch094.certificate1130).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate753).dm (WitnessCertificates.Batch037.certificate753).beta (WitnessCertificates.Batch037.certificate753).L) ≤ ((CutFailureCertificates.Budget037.certificate753).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound753 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate753).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch094.certificate1130).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch037.certificate753).omega:ℝ)) ≤ ((CutFailureCertificates.Budget037.certificate753).bound:ℝ) at hb
  exact (exponentialBound376 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches377 : (MergedCutGroups.Batch094.certificate1133).AnchorMatches CountingCertificates.Batch037.certificate755 := by decide +kernel
theorem exponentialBound377 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch094.certificate1133).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate755).dm (WitnessCertificates.Batch037.certificate755).beta (WitnessCertificates.Batch037.certificate755).L) ≤ (2*exp (-((CountingCertificates.Batch037.certificate755).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch094.certificate1133).exponent:ℝ)*st.R))/((WitnessCertificates.Batch037.certificate755).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch094.certificate1133 CountingCertificates.Batch037.certificate755 matches377 MergedCutGroups.Batch094.numericValid1133 MergedCutGroups.Batch094.cellsSound1133 MergedCutGroups.Batch094.cellsNumeric1133 MergedCutGroups.Batch094.populationMatches1133
    PopulationCertificates.Batch037.valid755 PopulationCertificates.Batch037.sound755 WitnessCertificates.Batch037.valid755 WitnessCertificates.Batch037.sound755 CountingCertificates.Batch037.valid755 CountingCertificates.Batch037.sound755 H st hI
theorem probabilityBound377 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch094.certificate1133).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate755).dm (WitnessCertificates.Batch037.certificate755).beta (WitnessCertificates.Batch037.certificate755).L) ≤ ((CutFailureCertificates.Budget037.certificate755).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound755 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate755).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch094.certificate1133).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch037.certificate755).omega:ℝ)) ≤ ((CutFailureCertificates.Budget037.certificate755).bound:ℝ) at hb
  exact (exponentialBound377 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches378 : (MergedCutGroups.Batch094.certificate1136).AnchorMatches CountingCertificates.Batch037.certificate757 := by decide +kernel
theorem exponentialBound378 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch094.certificate1136).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate757).dm (WitnessCertificates.Batch037.certificate757).beta (WitnessCertificates.Batch037.certificate757).L) ≤ (2*exp (-((CountingCertificates.Batch037.certificate757).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch094.certificate1136).exponent:ℝ)*st.R))/((WitnessCertificates.Batch037.certificate757).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch094.certificate1136 CountingCertificates.Batch037.certificate757 matches378 MergedCutGroups.Batch094.numericValid1136 MergedCutGroups.Batch094.cellsSound1136 MergedCutGroups.Batch094.cellsNumeric1136 MergedCutGroups.Batch094.populationMatches1136
    PopulationCertificates.Batch037.valid757 PopulationCertificates.Batch037.sound757 WitnessCertificates.Batch037.valid757 WitnessCertificates.Batch037.sound757 CountingCertificates.Batch037.valid757 CountingCertificates.Batch037.sound757 H st hI
theorem probabilityBound378 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch094.certificate1136).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate757).dm (WitnessCertificates.Batch037.certificate757).beta (WitnessCertificates.Batch037.certificate757).L) ≤ ((CutFailureCertificates.Budget037.certificate757).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound757 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate757).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch094.certificate1136).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch037.certificate757).omega:ℝ)) ≤ ((CutFailureCertificates.Budget037.certificate757).bound:ℝ) at hb
  exact (exponentialBound378 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches379 : (MergedCutGroups.Batch094.certificate1139).AnchorMatches CountingCertificates.Batch037.certificate759 := by decide +kernel
theorem exponentialBound379 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch094.certificate1139).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate759).dm (WitnessCertificates.Batch037.certificate759).beta (WitnessCertificates.Batch037.certificate759).L) ≤ (2*exp (-((CountingCertificates.Batch037.certificate759).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch094.certificate1139).exponent:ℝ)*st.R))/((WitnessCertificates.Batch037.certificate759).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch094.certificate1139 CountingCertificates.Batch037.certificate759 matches379 MergedCutGroups.Batch094.numericValid1139 MergedCutGroups.Batch094.cellsSound1139 MergedCutGroups.Batch094.cellsNumeric1139 MergedCutGroups.Batch094.populationMatches1139
    PopulationCertificates.Batch037.valid759 PopulationCertificates.Batch037.sound759 WitnessCertificates.Batch037.valid759 WitnessCertificates.Batch037.sound759 CountingCertificates.Batch037.valid759 CountingCertificates.Batch037.sound759 H st hI
theorem probabilityBound379 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch094.certificate1139).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch037.certificate759).dm (WitnessCertificates.Batch037.certificate759).beta (WitnessCertificates.Batch037.certificate759).L) ≤ ((CutFailureCertificates.Budget037.certificate759).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound759 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate759).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch094.certificate1139).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch037.certificate759).omega:ℝ)) ≤ ((CutFailureCertificates.Budget037.certificate759).bound:ℝ) at hb
  exact (exponentialBound379 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch018
