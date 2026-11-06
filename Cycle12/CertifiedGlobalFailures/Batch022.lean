import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch045
import Cycle12.CountingCertificates.Batch046
import Cycle12.CountingCertificates.Batch047
import Cycle12.CountingCertificates.Batch048
import Cycle12.CutFailureCertificates.Budget045
import Cycle12.CutFailureCertificates.Budget046
import Cycle12.CutFailureCertificates.Budget047
import Cycle12.CutFailureCertificates.Budget048
import Cycle12.CutLabelCertificates.Entropy026
import Cycle12.CutLabelCertificates.Entropy027
import Cycle12.CutLabelCertificates.Entropy028
import Cycle12.CutLabelCertificates.Entropy029
import Cycle12.CutLabelCertificates.Entropy030
import Cycle12.CutLabelCertificates.Entropy031
import Cycle12.CutLabelCertificates.Minority026
import Cycle12.CutLabelCertificates.Minority027
import Cycle12.CutLabelCertificates.Minority028
import Cycle12.CutLabelCertificates.Minority029
import Cycle12.CutLabelCertificates.Minority030
import Cycle12.CutLabelCertificates.Minority031
import Cycle12.MergedCutGroups.Batch112
import Cycle12.MergedCutGroups.Batch113
import Cycle12.MergedCutGroups.Batch114
import Cycle12.MergedCutGroups.Batch115
import Cycle12.MergedCutGroups.Batch116
import Cycle12.MergedCutGroups.Batch117
import Cycle12.MergedCutGroups.Batch118
import Cycle12.PopulationCertificates.Batch045
import Cycle12.PopulationCertificates.Batch046
import Cycle12.PopulationCertificates.Batch047
import Cycle12.PopulationCertificates.Batch048
import Cycle12.WitnessCertificates.Batch045
import Cycle12.WitnessCertificates.Batch046
import Cycle12.WitnessCertificates.Batch047
import Cycle12.WitnessCertificates.Batch048

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch022
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches440 : (MergedCutGroups.Batch112.certificate1345).GlobalMatches MergedCutGroups.Batch112.certificate1346 CountingCertificates.Batch045.certificate905 CutLabelCertificates.Entropy026.certificate532 CutLabelCertificates.Minority026.certificate531 := by decide +kernel
theorem exponentialBound440 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch112.certificate1345).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate905).dm (WitnessCertificates.Batch045.certificate905).beta) ≤ (2*exp (-((CountingCertificates.Batch045.certificate905).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch112.certificate1345).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch112.certificate1346).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch045.certificate905).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch112.certificate1345 MergedCutGroups.Batch112.certificate1346 CountingCertificates.Batch045.certificate905 CutLabelCertificates.Entropy026.certificate532 CutLabelCertificates.Minority026.certificate531 matches440 rfl rfl
    MergedCutGroups.Batch112.numericValid1345 MergedCutGroups.Batch112.numericValid1346 MergedCutGroups.Batch112.cellsSound1345 MergedCutGroups.Batch112.cellsSound1346
    MergedCutGroups.Batch112.cellsNumeric1345 MergedCutGroups.Batch112.cellsNumeric1346 MergedCutGroups.Batch112.populationMatches1345 MergedCutGroups.Batch112.populationMatches1346
    PopulationCertificates.Batch045.valid905 PopulationCertificates.Batch045.sound905 WitnessCertificates.Batch045.valid905 WitnessCertificates.Batch045.sound905 CountingCertificates.Batch045.valid905 CountingCertificates.Batch045.sound905
    CutLabelCertificates.Entropy026.valid532 CutLabelCertificates.Minority026.valid531 CutLabelCertificates.Minority026.sound531 H st hI
theorem probabilityBound440 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch112.certificate1345).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate905).dm (WitnessCertificates.Batch045.certificate905).beta) ≤ ((CutFailureCertificates.Budget045.certificate905).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound905 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate905).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch112.certificate1345).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch112.certificate1346).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch045.certificate905).omega:ℝ) ≤ ((CutFailureCertificates.Budget045.certificate905).bound:ℝ) at hb
  exact (exponentialBound440 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches441 : (MergedCutGroups.Batch112.certificate1349).GlobalMatches MergedCutGroups.Batch112.certificate1350 CountingCertificates.Batch045.certificate908 CutLabelCertificates.Entropy026.certificate537 CutLabelCertificates.Minority026.certificate536 := by decide +kernel
theorem exponentialBound441 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch112.certificate1349).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate908).dm (WitnessCertificates.Batch045.certificate908).beta) ≤ (2*exp (-((CountingCertificates.Batch045.certificate908).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch112.certificate1349).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch112.certificate1350).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch045.certificate908).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch112.certificate1349 MergedCutGroups.Batch112.certificate1350 CountingCertificates.Batch045.certificate908 CutLabelCertificates.Entropy026.certificate537 CutLabelCertificates.Minority026.certificate536 matches441 rfl rfl
    MergedCutGroups.Batch112.numericValid1349 MergedCutGroups.Batch112.numericValid1350 MergedCutGroups.Batch112.cellsSound1349 MergedCutGroups.Batch112.cellsSound1350
    MergedCutGroups.Batch112.cellsNumeric1349 MergedCutGroups.Batch112.cellsNumeric1350 MergedCutGroups.Batch112.populationMatches1349 MergedCutGroups.Batch112.populationMatches1350
    PopulationCertificates.Batch045.valid908 PopulationCertificates.Batch045.sound908 WitnessCertificates.Batch045.valid908 WitnessCertificates.Batch045.sound908 CountingCertificates.Batch045.valid908 CountingCertificates.Batch045.sound908
    CutLabelCertificates.Entropy026.valid537 CutLabelCertificates.Minority026.valid536 CutLabelCertificates.Minority026.sound536 H st hI
theorem probabilityBound441 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch112.certificate1349).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate908).dm (WitnessCertificates.Batch045.certificate908).beta) ≤ ((CutFailureCertificates.Budget045.certificate908).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound908 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate908).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch112.certificate1349).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch112.certificate1350).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch045.certificate908).omega:ℝ) ≤ ((CutFailureCertificates.Budget045.certificate908).bound:ℝ) at hb
  exact (exponentialBound441 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches442 : (MergedCutGroups.Batch112.certificate1353).GlobalMatches MergedCutGroups.Batch112.certificate1354 CountingCertificates.Batch045.certificate911 CutLabelCertificates.Entropy027.certificate542 CutLabelCertificates.Minority027.certificate541 := by decide +kernel
theorem exponentialBound442 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch112.certificate1353).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate911).dm (WitnessCertificates.Batch045.certificate911).beta) ≤ (2*exp (-((CountingCertificates.Batch045.certificate911).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch112.certificate1353).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch112.certificate1354).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch045.certificate911).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch112.certificate1353 MergedCutGroups.Batch112.certificate1354 CountingCertificates.Batch045.certificate911 CutLabelCertificates.Entropy027.certificate542 CutLabelCertificates.Minority027.certificate541 matches442 rfl rfl
    MergedCutGroups.Batch112.numericValid1353 MergedCutGroups.Batch112.numericValid1354 MergedCutGroups.Batch112.cellsSound1353 MergedCutGroups.Batch112.cellsSound1354
    MergedCutGroups.Batch112.cellsNumeric1353 MergedCutGroups.Batch112.cellsNumeric1354 MergedCutGroups.Batch112.populationMatches1353 MergedCutGroups.Batch112.populationMatches1354
    PopulationCertificates.Batch045.valid911 PopulationCertificates.Batch045.sound911 WitnessCertificates.Batch045.valid911 WitnessCertificates.Batch045.sound911 CountingCertificates.Batch045.valid911 CountingCertificates.Batch045.sound911
    CutLabelCertificates.Entropy027.valid542 CutLabelCertificates.Minority027.valid541 CutLabelCertificates.Minority027.sound541 H st hI
theorem probabilityBound442 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch112.certificate1353).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate911).dm (WitnessCertificates.Batch045.certificate911).beta) ≤ ((CutFailureCertificates.Budget045.certificate911).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound911 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate911).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch112.certificate1353).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch112.certificate1354).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch045.certificate911).omega:ℝ) ≤ ((CutFailureCertificates.Budget045.certificate911).bound:ℝ) at hb
  exact (exponentialBound442 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches443 : (MergedCutGroups.Batch113.certificate1357).GlobalMatches MergedCutGroups.Batch113.certificate1358 CountingCertificates.Batch045.certificate914 CutLabelCertificates.Entropy027.certificate547 CutLabelCertificates.Minority027.certificate546 := by decide +kernel
theorem exponentialBound443 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch113.certificate1357).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate914).dm (WitnessCertificates.Batch045.certificate914).beta) ≤ (2*exp (-((CountingCertificates.Batch045.certificate914).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch113.certificate1357).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch113.certificate1358).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch045.certificate914).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch113.certificate1357 MergedCutGroups.Batch113.certificate1358 CountingCertificates.Batch045.certificate914 CutLabelCertificates.Entropy027.certificate547 CutLabelCertificates.Minority027.certificate546 matches443 rfl rfl
    MergedCutGroups.Batch113.numericValid1357 MergedCutGroups.Batch113.numericValid1358 MergedCutGroups.Batch113.cellsSound1357 MergedCutGroups.Batch113.cellsSound1358
    MergedCutGroups.Batch113.cellsNumeric1357 MergedCutGroups.Batch113.cellsNumeric1358 MergedCutGroups.Batch113.populationMatches1357 MergedCutGroups.Batch113.populationMatches1358
    PopulationCertificates.Batch045.valid914 PopulationCertificates.Batch045.sound914 WitnessCertificates.Batch045.valid914 WitnessCertificates.Batch045.sound914 CountingCertificates.Batch045.valid914 CountingCertificates.Batch045.sound914
    CutLabelCertificates.Entropy027.valid547 CutLabelCertificates.Minority027.valid546 CutLabelCertificates.Minority027.sound546 H st hI
theorem probabilityBound443 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch113.certificate1357).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate914).dm (WitnessCertificates.Batch045.certificate914).beta) ≤ ((CutFailureCertificates.Budget045.certificate914).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound914 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate914).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch113.certificate1357).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch113.certificate1358).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch045.certificate914).omega:ℝ) ≤ ((CutFailureCertificates.Budget045.certificate914).bound:ℝ) at hb
  exact (exponentialBound443 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches444 : (MergedCutGroups.Batch113.certificate1361).GlobalMatches MergedCutGroups.Batch113.certificate1362 CountingCertificates.Batch045.certificate917 CutLabelCertificates.Entropy027.certificate552 CutLabelCertificates.Minority027.certificate551 := by decide +kernel
theorem exponentialBound444 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch113.certificate1361).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate917).dm (WitnessCertificates.Batch045.certificate917).beta) ≤ (2*exp (-((CountingCertificates.Batch045.certificate917).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch113.certificate1361).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch113.certificate1362).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch045.certificate917).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch113.certificate1361 MergedCutGroups.Batch113.certificate1362 CountingCertificates.Batch045.certificate917 CutLabelCertificates.Entropy027.certificate552 CutLabelCertificates.Minority027.certificate551 matches444 rfl rfl
    MergedCutGroups.Batch113.numericValid1361 MergedCutGroups.Batch113.numericValid1362 MergedCutGroups.Batch113.cellsSound1361 MergedCutGroups.Batch113.cellsSound1362
    MergedCutGroups.Batch113.cellsNumeric1361 MergedCutGroups.Batch113.cellsNumeric1362 MergedCutGroups.Batch113.populationMatches1361 MergedCutGroups.Batch113.populationMatches1362
    PopulationCertificates.Batch045.valid917 PopulationCertificates.Batch045.sound917 WitnessCertificates.Batch045.valid917 WitnessCertificates.Batch045.sound917 CountingCertificates.Batch045.valid917 CountingCertificates.Batch045.sound917
    CutLabelCertificates.Entropy027.valid552 CutLabelCertificates.Minority027.valid551 CutLabelCertificates.Minority027.sound551 H st hI
theorem probabilityBound444 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch113.certificate1361).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate917).dm (WitnessCertificates.Batch045.certificate917).beta) ≤ ((CutFailureCertificates.Budget045.certificate917).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound917 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate917).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch113.certificate1361).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch113.certificate1362).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch045.certificate917).omega:ℝ) ≤ ((CutFailureCertificates.Budget045.certificate917).bound:ℝ) at hb
  exact (exponentialBound444 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches445 : (MergedCutGroups.Batch113.certificate1365).GlobalMatches MergedCutGroups.Batch113.certificate1366 CountingCertificates.Batch046.certificate920 CutLabelCertificates.Entropy027.certificate557 CutLabelCertificates.Minority027.certificate556 := by decide +kernel
theorem exponentialBound445 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch113.certificate1365).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate920).dm (WitnessCertificates.Batch046.certificate920).beta) ≤ (2*exp (-((CountingCertificates.Batch046.certificate920).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch113.certificate1365).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch113.certificate1366).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch046.certificate920).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch113.certificate1365 MergedCutGroups.Batch113.certificate1366 CountingCertificates.Batch046.certificate920 CutLabelCertificates.Entropy027.certificate557 CutLabelCertificates.Minority027.certificate556 matches445 rfl rfl
    MergedCutGroups.Batch113.numericValid1365 MergedCutGroups.Batch113.numericValid1366 MergedCutGroups.Batch113.cellsSound1365 MergedCutGroups.Batch113.cellsSound1366
    MergedCutGroups.Batch113.cellsNumeric1365 MergedCutGroups.Batch113.cellsNumeric1366 MergedCutGroups.Batch113.populationMatches1365 MergedCutGroups.Batch113.populationMatches1366
    PopulationCertificates.Batch046.valid920 PopulationCertificates.Batch046.sound920 WitnessCertificates.Batch046.valid920 WitnessCertificates.Batch046.sound920 CountingCertificates.Batch046.valid920 CountingCertificates.Batch046.sound920
    CutLabelCertificates.Entropy027.valid557 CutLabelCertificates.Minority027.valid556 CutLabelCertificates.Minority027.sound556 H st hI
theorem probabilityBound445 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch113.certificate1365).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate920).dm (WitnessCertificates.Batch046.certificate920).beta) ≤ ((CutFailureCertificates.Budget046.certificate920).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound920 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate920).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch113.certificate1365).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch113.certificate1366).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch046.certificate920).omega:ℝ) ≤ ((CutFailureCertificates.Budget046.certificate920).bound:ℝ) at hb
  exact (exponentialBound445 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches446 : (MergedCutGroups.Batch114.certificate1369).GlobalMatches MergedCutGroups.Batch114.certificate1370 CountingCertificates.Batch046.certificate923 CutLabelCertificates.Entropy028.certificate562 CutLabelCertificates.Minority028.certificate561 := by decide +kernel
theorem exponentialBound446 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch114.certificate1369).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate923).dm (WitnessCertificates.Batch046.certificate923).beta) ≤ (2*exp (-((CountingCertificates.Batch046.certificate923).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch114.certificate1369).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch114.certificate1370).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch046.certificate923).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch114.certificate1369 MergedCutGroups.Batch114.certificate1370 CountingCertificates.Batch046.certificate923 CutLabelCertificates.Entropy028.certificate562 CutLabelCertificates.Minority028.certificate561 matches446 rfl rfl
    MergedCutGroups.Batch114.numericValid1369 MergedCutGroups.Batch114.numericValid1370 MergedCutGroups.Batch114.cellsSound1369 MergedCutGroups.Batch114.cellsSound1370
    MergedCutGroups.Batch114.cellsNumeric1369 MergedCutGroups.Batch114.cellsNumeric1370 MergedCutGroups.Batch114.populationMatches1369 MergedCutGroups.Batch114.populationMatches1370
    PopulationCertificates.Batch046.valid923 PopulationCertificates.Batch046.sound923 WitnessCertificates.Batch046.valid923 WitnessCertificates.Batch046.sound923 CountingCertificates.Batch046.valid923 CountingCertificates.Batch046.sound923
    CutLabelCertificates.Entropy028.valid562 CutLabelCertificates.Minority028.valid561 CutLabelCertificates.Minority028.sound561 H st hI
theorem probabilityBound446 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch114.certificate1369).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate923).dm (WitnessCertificates.Batch046.certificate923).beta) ≤ ((CutFailureCertificates.Budget046.certificate923).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound923 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate923).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch114.certificate1369).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch114.certificate1370).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch046.certificate923).omega:ℝ) ≤ ((CutFailureCertificates.Budget046.certificate923).bound:ℝ) at hb
  exact (exponentialBound446 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches447 : (MergedCutGroups.Batch114.certificate1373).GlobalMatches MergedCutGroups.Batch114.certificate1374 CountingCertificates.Batch046.certificate926 CutLabelCertificates.Entropy028.certificate567 CutLabelCertificates.Minority028.certificate566 := by decide +kernel
theorem exponentialBound447 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch114.certificate1373).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate926).dm (WitnessCertificates.Batch046.certificate926).beta) ≤ (2*exp (-((CountingCertificates.Batch046.certificate926).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch114.certificate1373).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch114.certificate1374).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch046.certificate926).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch114.certificate1373 MergedCutGroups.Batch114.certificate1374 CountingCertificates.Batch046.certificate926 CutLabelCertificates.Entropy028.certificate567 CutLabelCertificates.Minority028.certificate566 matches447 rfl rfl
    MergedCutGroups.Batch114.numericValid1373 MergedCutGroups.Batch114.numericValid1374 MergedCutGroups.Batch114.cellsSound1373 MergedCutGroups.Batch114.cellsSound1374
    MergedCutGroups.Batch114.cellsNumeric1373 MergedCutGroups.Batch114.cellsNumeric1374 MergedCutGroups.Batch114.populationMatches1373 MergedCutGroups.Batch114.populationMatches1374
    PopulationCertificates.Batch046.valid926 PopulationCertificates.Batch046.sound926 WitnessCertificates.Batch046.valid926 WitnessCertificates.Batch046.sound926 CountingCertificates.Batch046.valid926 CountingCertificates.Batch046.sound926
    CutLabelCertificates.Entropy028.valid567 CutLabelCertificates.Minority028.valid566 CutLabelCertificates.Minority028.sound566 H st hI
theorem probabilityBound447 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch114.certificate1373).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate926).dm (WitnessCertificates.Batch046.certificate926).beta) ≤ ((CutFailureCertificates.Budget046.certificate926).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound926 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate926).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch114.certificate1373).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch114.certificate1374).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch046.certificate926).omega:ℝ) ≤ ((CutFailureCertificates.Budget046.certificate926).bound:ℝ) at hb
  exact (exponentialBound447 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches448 : (MergedCutGroups.Batch114.certificate1377).GlobalMatches MergedCutGroups.Batch114.certificate1378 CountingCertificates.Batch046.certificate929 CutLabelCertificates.Entropy028.certificate572 CutLabelCertificates.Minority028.certificate571 := by decide +kernel
theorem exponentialBound448 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch114.certificate1377).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate929).dm (WitnessCertificates.Batch046.certificate929).beta) ≤ (2*exp (-((CountingCertificates.Batch046.certificate929).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch114.certificate1377).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch114.certificate1378).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch046.certificate929).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch114.certificate1377 MergedCutGroups.Batch114.certificate1378 CountingCertificates.Batch046.certificate929 CutLabelCertificates.Entropy028.certificate572 CutLabelCertificates.Minority028.certificate571 matches448 rfl rfl
    MergedCutGroups.Batch114.numericValid1377 MergedCutGroups.Batch114.numericValid1378 MergedCutGroups.Batch114.cellsSound1377 MergedCutGroups.Batch114.cellsSound1378
    MergedCutGroups.Batch114.cellsNumeric1377 MergedCutGroups.Batch114.cellsNumeric1378 MergedCutGroups.Batch114.populationMatches1377 MergedCutGroups.Batch114.populationMatches1378
    PopulationCertificates.Batch046.valid929 PopulationCertificates.Batch046.sound929 WitnessCertificates.Batch046.valid929 WitnessCertificates.Batch046.sound929 CountingCertificates.Batch046.valid929 CountingCertificates.Batch046.sound929
    CutLabelCertificates.Entropy028.valid572 CutLabelCertificates.Minority028.valid571 CutLabelCertificates.Minority028.sound571 H st hI
theorem probabilityBound448 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch114.certificate1377).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate929).dm (WitnessCertificates.Batch046.certificate929).beta) ≤ ((CutFailureCertificates.Budget046.certificate929).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound929 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate929).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch114.certificate1377).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch114.certificate1378).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch046.certificate929).omega:ℝ) ≤ ((CutFailureCertificates.Budget046.certificate929).bound:ℝ) at hb
  exact (exponentialBound448 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches449 : (MergedCutGroups.Batch115.certificate1381).GlobalMatches MergedCutGroups.Batch115.certificate1382 CountingCertificates.Batch046.certificate932 CutLabelCertificates.Entropy028.certificate577 CutLabelCertificates.Minority028.certificate576 := by decide +kernel
theorem exponentialBound449 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch115.certificate1381).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate932).dm (WitnessCertificates.Batch046.certificate932).beta) ≤ (2*exp (-((CountingCertificates.Batch046.certificate932).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch115.certificate1381).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch115.certificate1382).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch046.certificate932).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch115.certificate1381 MergedCutGroups.Batch115.certificate1382 CountingCertificates.Batch046.certificate932 CutLabelCertificates.Entropy028.certificate577 CutLabelCertificates.Minority028.certificate576 matches449 rfl rfl
    MergedCutGroups.Batch115.numericValid1381 MergedCutGroups.Batch115.numericValid1382 MergedCutGroups.Batch115.cellsSound1381 MergedCutGroups.Batch115.cellsSound1382
    MergedCutGroups.Batch115.cellsNumeric1381 MergedCutGroups.Batch115.cellsNumeric1382 MergedCutGroups.Batch115.populationMatches1381 MergedCutGroups.Batch115.populationMatches1382
    PopulationCertificates.Batch046.valid932 PopulationCertificates.Batch046.sound932 WitnessCertificates.Batch046.valid932 WitnessCertificates.Batch046.sound932 CountingCertificates.Batch046.valid932 CountingCertificates.Batch046.sound932
    CutLabelCertificates.Entropy028.valid577 CutLabelCertificates.Minority028.valid576 CutLabelCertificates.Minority028.sound576 H st hI
theorem probabilityBound449 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch115.certificate1381).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate932).dm (WitnessCertificates.Batch046.certificate932).beta) ≤ ((CutFailureCertificates.Budget046.certificate932).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound932 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate932).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch115.certificate1381).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch115.certificate1382).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch046.certificate932).omega:ℝ) ≤ ((CutFailureCertificates.Budget046.certificate932).bound:ℝ) at hb
  exact (exponentialBound449 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches450 : (MergedCutGroups.Batch115.certificate1385).GlobalMatches MergedCutGroups.Batch115.certificate1386 CountingCertificates.Batch046.certificate935 CutLabelCertificates.Entropy029.certificate582 CutLabelCertificates.Minority029.certificate581 := by decide +kernel
theorem exponentialBound450 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch115.certificate1385).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate935).dm (WitnessCertificates.Batch046.certificate935).beta) ≤ (2*exp (-((CountingCertificates.Batch046.certificate935).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch115.certificate1385).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch115.certificate1386).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch046.certificate935).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch115.certificate1385 MergedCutGroups.Batch115.certificate1386 CountingCertificates.Batch046.certificate935 CutLabelCertificates.Entropy029.certificate582 CutLabelCertificates.Minority029.certificate581 matches450 rfl rfl
    MergedCutGroups.Batch115.numericValid1385 MergedCutGroups.Batch115.numericValid1386 MergedCutGroups.Batch115.cellsSound1385 MergedCutGroups.Batch115.cellsSound1386
    MergedCutGroups.Batch115.cellsNumeric1385 MergedCutGroups.Batch115.cellsNumeric1386 MergedCutGroups.Batch115.populationMatches1385 MergedCutGroups.Batch115.populationMatches1386
    PopulationCertificates.Batch046.valid935 PopulationCertificates.Batch046.sound935 WitnessCertificates.Batch046.valid935 WitnessCertificates.Batch046.sound935 CountingCertificates.Batch046.valid935 CountingCertificates.Batch046.sound935
    CutLabelCertificates.Entropy029.valid582 CutLabelCertificates.Minority029.valid581 CutLabelCertificates.Minority029.sound581 H st hI
theorem probabilityBound450 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch115.certificate1385).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate935).dm (WitnessCertificates.Batch046.certificate935).beta) ≤ ((CutFailureCertificates.Budget046.certificate935).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound935 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate935).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch115.certificate1385).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch115.certificate1386).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch046.certificate935).omega:ℝ) ≤ ((CutFailureCertificates.Budget046.certificate935).bound:ℝ) at hb
  exact (exponentialBound450 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches451 : (MergedCutGroups.Batch115.certificate1389).GlobalMatches MergedCutGroups.Batch115.certificate1390 CountingCertificates.Batch046.certificate938 CutLabelCertificates.Entropy029.certificate587 CutLabelCertificates.Minority029.certificate586 := by decide +kernel
theorem exponentialBound451 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch115.certificate1389).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate938).dm (WitnessCertificates.Batch046.certificate938).beta) ≤ (2*exp (-((CountingCertificates.Batch046.certificate938).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch115.certificate1389).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch115.certificate1390).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch046.certificate938).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch115.certificate1389 MergedCutGroups.Batch115.certificate1390 CountingCertificates.Batch046.certificate938 CutLabelCertificates.Entropy029.certificate587 CutLabelCertificates.Minority029.certificate586 matches451 rfl rfl
    MergedCutGroups.Batch115.numericValid1389 MergedCutGroups.Batch115.numericValid1390 MergedCutGroups.Batch115.cellsSound1389 MergedCutGroups.Batch115.cellsSound1390
    MergedCutGroups.Batch115.cellsNumeric1389 MergedCutGroups.Batch115.cellsNumeric1390 MergedCutGroups.Batch115.populationMatches1389 MergedCutGroups.Batch115.populationMatches1390
    PopulationCertificates.Batch046.valid938 PopulationCertificates.Batch046.sound938 WitnessCertificates.Batch046.valid938 WitnessCertificates.Batch046.sound938 CountingCertificates.Batch046.valid938 CountingCertificates.Batch046.sound938
    CutLabelCertificates.Entropy029.valid587 CutLabelCertificates.Minority029.valid586 CutLabelCertificates.Minority029.sound586 H st hI
theorem probabilityBound451 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch115.certificate1389).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate938).dm (WitnessCertificates.Batch046.certificate938).beta) ≤ ((CutFailureCertificates.Budget046.certificate938).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound938 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate938).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch115.certificate1389).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch115.certificate1390).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch046.certificate938).omega:ℝ) ≤ ((CutFailureCertificates.Budget046.certificate938).bound:ℝ) at hb
  exact (exponentialBound451 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches452 : (MergedCutGroups.Batch116.certificate1393).GlobalMatches MergedCutGroups.Batch116.certificate1394 CountingCertificates.Batch047.certificate941 CutLabelCertificates.Entropy029.certificate592 CutLabelCertificates.Minority029.certificate591 := by decide +kernel
theorem exponentialBound452 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch116.certificate1393).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate941).dm (WitnessCertificates.Batch047.certificate941).beta) ≤ (2*exp (-((CountingCertificates.Batch047.certificate941).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch116.certificate1393).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch116.certificate1394).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch047.certificate941).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch116.certificate1393 MergedCutGroups.Batch116.certificate1394 CountingCertificates.Batch047.certificate941 CutLabelCertificates.Entropy029.certificate592 CutLabelCertificates.Minority029.certificate591 matches452 rfl rfl
    MergedCutGroups.Batch116.numericValid1393 MergedCutGroups.Batch116.numericValid1394 MergedCutGroups.Batch116.cellsSound1393 MergedCutGroups.Batch116.cellsSound1394
    MergedCutGroups.Batch116.cellsNumeric1393 MergedCutGroups.Batch116.cellsNumeric1394 MergedCutGroups.Batch116.populationMatches1393 MergedCutGroups.Batch116.populationMatches1394
    PopulationCertificates.Batch047.valid941 PopulationCertificates.Batch047.sound941 WitnessCertificates.Batch047.valid941 WitnessCertificates.Batch047.sound941 CountingCertificates.Batch047.valid941 CountingCertificates.Batch047.sound941
    CutLabelCertificates.Entropy029.valid592 CutLabelCertificates.Minority029.valid591 CutLabelCertificates.Minority029.sound591 H st hI
theorem probabilityBound452 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch116.certificate1393).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate941).dm (WitnessCertificates.Batch047.certificate941).beta) ≤ ((CutFailureCertificates.Budget047.certificate941).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound941 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate941).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch116.certificate1393).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch116.certificate1394).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch047.certificate941).omega:ℝ) ≤ ((CutFailureCertificates.Budget047.certificate941).bound:ℝ) at hb
  exact (exponentialBound452 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches453 : (MergedCutGroups.Batch116.certificate1397).GlobalMatches MergedCutGroups.Batch116.certificate1398 CountingCertificates.Batch047.certificate944 CutLabelCertificates.Entropy029.certificate597 CutLabelCertificates.Minority029.certificate596 := by decide +kernel
theorem exponentialBound453 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch116.certificate1397).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate944).dm (WitnessCertificates.Batch047.certificate944).beta) ≤ (2*exp (-((CountingCertificates.Batch047.certificate944).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch116.certificate1397).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch116.certificate1398).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch047.certificate944).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch116.certificate1397 MergedCutGroups.Batch116.certificate1398 CountingCertificates.Batch047.certificate944 CutLabelCertificates.Entropy029.certificate597 CutLabelCertificates.Minority029.certificate596 matches453 rfl rfl
    MergedCutGroups.Batch116.numericValid1397 MergedCutGroups.Batch116.numericValid1398 MergedCutGroups.Batch116.cellsSound1397 MergedCutGroups.Batch116.cellsSound1398
    MergedCutGroups.Batch116.cellsNumeric1397 MergedCutGroups.Batch116.cellsNumeric1398 MergedCutGroups.Batch116.populationMatches1397 MergedCutGroups.Batch116.populationMatches1398
    PopulationCertificates.Batch047.valid944 PopulationCertificates.Batch047.sound944 WitnessCertificates.Batch047.valid944 WitnessCertificates.Batch047.sound944 CountingCertificates.Batch047.valid944 CountingCertificates.Batch047.sound944
    CutLabelCertificates.Entropy029.valid597 CutLabelCertificates.Minority029.valid596 CutLabelCertificates.Minority029.sound596 H st hI
theorem probabilityBound453 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch116.certificate1397).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate944).dm (WitnessCertificates.Batch047.certificate944).beta) ≤ ((CutFailureCertificates.Budget047.certificate944).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound944 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate944).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch116.certificate1397).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch116.certificate1398).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch047.certificate944).omega:ℝ) ≤ ((CutFailureCertificates.Budget047.certificate944).bound:ℝ) at hb
  exact (exponentialBound453 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches454 : (MergedCutGroups.Batch116.certificate1401).GlobalMatches MergedCutGroups.Batch116.certificate1402 CountingCertificates.Batch047.certificate947 CutLabelCertificates.Entropy030.certificate602 CutLabelCertificates.Minority030.certificate601 := by decide +kernel
theorem exponentialBound454 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch116.certificate1401).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate947).dm (WitnessCertificates.Batch047.certificate947).beta) ≤ (2*exp (-((CountingCertificates.Batch047.certificate947).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch116.certificate1401).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch116.certificate1402).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch047.certificate947).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch116.certificate1401 MergedCutGroups.Batch116.certificate1402 CountingCertificates.Batch047.certificate947 CutLabelCertificates.Entropy030.certificate602 CutLabelCertificates.Minority030.certificate601 matches454 rfl rfl
    MergedCutGroups.Batch116.numericValid1401 MergedCutGroups.Batch116.numericValid1402 MergedCutGroups.Batch116.cellsSound1401 MergedCutGroups.Batch116.cellsSound1402
    MergedCutGroups.Batch116.cellsNumeric1401 MergedCutGroups.Batch116.cellsNumeric1402 MergedCutGroups.Batch116.populationMatches1401 MergedCutGroups.Batch116.populationMatches1402
    PopulationCertificates.Batch047.valid947 PopulationCertificates.Batch047.sound947 WitnessCertificates.Batch047.valid947 WitnessCertificates.Batch047.sound947 CountingCertificates.Batch047.valid947 CountingCertificates.Batch047.sound947
    CutLabelCertificates.Entropy030.valid602 CutLabelCertificates.Minority030.valid601 CutLabelCertificates.Minority030.sound601 H st hI
theorem probabilityBound454 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch116.certificate1401).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate947).dm (WitnessCertificates.Batch047.certificate947).beta) ≤ ((CutFailureCertificates.Budget047.certificate947).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound947 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate947).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch116.certificate1401).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch116.certificate1402).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch047.certificate947).omega:ℝ) ≤ ((CutFailureCertificates.Budget047.certificate947).bound:ℝ) at hb
  exact (exponentialBound454 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches455 : (MergedCutGroups.Batch117.certificate1405).GlobalMatches MergedCutGroups.Batch117.certificate1406 CountingCertificates.Batch047.certificate950 CutLabelCertificates.Entropy030.certificate607 CutLabelCertificates.Minority030.certificate606 := by decide +kernel
theorem exponentialBound455 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch117.certificate1405).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate950).dm (WitnessCertificates.Batch047.certificate950).beta) ≤ (2*exp (-((CountingCertificates.Batch047.certificate950).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch117.certificate1405).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch117.certificate1406).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch047.certificate950).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch117.certificate1405 MergedCutGroups.Batch117.certificate1406 CountingCertificates.Batch047.certificate950 CutLabelCertificates.Entropy030.certificate607 CutLabelCertificates.Minority030.certificate606 matches455 rfl rfl
    MergedCutGroups.Batch117.numericValid1405 MergedCutGroups.Batch117.numericValid1406 MergedCutGroups.Batch117.cellsSound1405 MergedCutGroups.Batch117.cellsSound1406
    MergedCutGroups.Batch117.cellsNumeric1405 MergedCutGroups.Batch117.cellsNumeric1406 MergedCutGroups.Batch117.populationMatches1405 MergedCutGroups.Batch117.populationMatches1406
    PopulationCertificates.Batch047.valid950 PopulationCertificates.Batch047.sound950 WitnessCertificates.Batch047.valid950 WitnessCertificates.Batch047.sound950 CountingCertificates.Batch047.valid950 CountingCertificates.Batch047.sound950
    CutLabelCertificates.Entropy030.valid607 CutLabelCertificates.Minority030.valid606 CutLabelCertificates.Minority030.sound606 H st hI
theorem probabilityBound455 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch117.certificate1405).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate950).dm (WitnessCertificates.Batch047.certificate950).beta) ≤ ((CutFailureCertificates.Budget047.certificate950).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound950 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate950).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch117.certificate1405).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch117.certificate1406).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch047.certificate950).omega:ℝ) ≤ ((CutFailureCertificates.Budget047.certificate950).bound:ℝ) at hb
  exact (exponentialBound455 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches456 : (MergedCutGroups.Batch117.certificate1409).GlobalMatches MergedCutGroups.Batch117.certificate1410 CountingCertificates.Batch047.certificate953 CutLabelCertificates.Entropy030.certificate612 CutLabelCertificates.Minority030.certificate611 := by decide +kernel
theorem exponentialBound456 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch117.certificate1409).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate953).dm (WitnessCertificates.Batch047.certificate953).beta) ≤ (2*exp (-((CountingCertificates.Batch047.certificate953).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch117.certificate1409).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch117.certificate1410).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch047.certificate953).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch117.certificate1409 MergedCutGroups.Batch117.certificate1410 CountingCertificates.Batch047.certificate953 CutLabelCertificates.Entropy030.certificate612 CutLabelCertificates.Minority030.certificate611 matches456 rfl rfl
    MergedCutGroups.Batch117.numericValid1409 MergedCutGroups.Batch117.numericValid1410 MergedCutGroups.Batch117.cellsSound1409 MergedCutGroups.Batch117.cellsSound1410
    MergedCutGroups.Batch117.cellsNumeric1409 MergedCutGroups.Batch117.cellsNumeric1410 MergedCutGroups.Batch117.populationMatches1409 MergedCutGroups.Batch117.populationMatches1410
    PopulationCertificates.Batch047.valid953 PopulationCertificates.Batch047.sound953 WitnessCertificates.Batch047.valid953 WitnessCertificates.Batch047.sound953 CountingCertificates.Batch047.valid953 CountingCertificates.Batch047.sound953
    CutLabelCertificates.Entropy030.valid612 CutLabelCertificates.Minority030.valid611 CutLabelCertificates.Minority030.sound611 H st hI
theorem probabilityBound456 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch117.certificate1409).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate953).dm (WitnessCertificates.Batch047.certificate953).beta) ≤ ((CutFailureCertificates.Budget047.certificate953).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound953 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate953).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch117.certificate1409).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch117.certificate1410).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch047.certificate953).omega:ℝ) ≤ ((CutFailureCertificates.Budget047.certificate953).bound:ℝ) at hb
  exact (exponentialBound456 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches457 : (MergedCutGroups.Batch117.certificate1413).GlobalMatches MergedCutGroups.Batch117.certificate1414 CountingCertificates.Batch047.certificate956 CutLabelCertificates.Entropy030.certificate617 CutLabelCertificates.Minority030.certificate616 := by decide +kernel
theorem exponentialBound457 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch117.certificate1413).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate956).dm (WitnessCertificates.Batch047.certificate956).beta) ≤ (2*exp (-((CountingCertificates.Batch047.certificate956).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch117.certificate1413).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch117.certificate1414).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch047.certificate956).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch117.certificate1413 MergedCutGroups.Batch117.certificate1414 CountingCertificates.Batch047.certificate956 CutLabelCertificates.Entropy030.certificate617 CutLabelCertificates.Minority030.certificate616 matches457 rfl rfl
    MergedCutGroups.Batch117.numericValid1413 MergedCutGroups.Batch117.numericValid1414 MergedCutGroups.Batch117.cellsSound1413 MergedCutGroups.Batch117.cellsSound1414
    MergedCutGroups.Batch117.cellsNumeric1413 MergedCutGroups.Batch117.cellsNumeric1414 MergedCutGroups.Batch117.populationMatches1413 MergedCutGroups.Batch117.populationMatches1414
    PopulationCertificates.Batch047.valid956 PopulationCertificates.Batch047.sound956 WitnessCertificates.Batch047.valid956 WitnessCertificates.Batch047.sound956 CountingCertificates.Batch047.valid956 CountingCertificates.Batch047.sound956
    CutLabelCertificates.Entropy030.valid617 CutLabelCertificates.Minority030.valid616 CutLabelCertificates.Minority030.sound616 H st hI
theorem probabilityBound457 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch117.certificate1413).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate956).dm (WitnessCertificates.Batch047.certificate956).beta) ≤ ((CutFailureCertificates.Budget047.certificate956).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound956 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate956).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch117.certificate1413).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch117.certificate1414).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch047.certificate956).omega:ℝ) ≤ ((CutFailureCertificates.Budget047.certificate956).bound:ℝ) at hb
  exact (exponentialBound457 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches458 : (MergedCutGroups.Batch118.certificate1417).GlobalMatches MergedCutGroups.Batch118.certificate1418 CountingCertificates.Batch047.certificate959 CutLabelCertificates.Entropy031.certificate622 CutLabelCertificates.Minority031.certificate621 := by decide +kernel
theorem exponentialBound458 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch118.certificate1417).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate959).dm (WitnessCertificates.Batch047.certificate959).beta) ≤ (2*exp (-((CountingCertificates.Batch047.certificate959).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch118.certificate1417).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch118.certificate1418).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch047.certificate959).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch118.certificate1417 MergedCutGroups.Batch118.certificate1418 CountingCertificates.Batch047.certificate959 CutLabelCertificates.Entropy031.certificate622 CutLabelCertificates.Minority031.certificate621 matches458 rfl rfl
    MergedCutGroups.Batch118.numericValid1417 MergedCutGroups.Batch118.numericValid1418 MergedCutGroups.Batch118.cellsSound1417 MergedCutGroups.Batch118.cellsSound1418
    MergedCutGroups.Batch118.cellsNumeric1417 MergedCutGroups.Batch118.cellsNumeric1418 MergedCutGroups.Batch118.populationMatches1417 MergedCutGroups.Batch118.populationMatches1418
    PopulationCertificates.Batch047.valid959 PopulationCertificates.Batch047.sound959 WitnessCertificates.Batch047.valid959 WitnessCertificates.Batch047.sound959 CountingCertificates.Batch047.valid959 CountingCertificates.Batch047.sound959
    CutLabelCertificates.Entropy031.valid622 CutLabelCertificates.Minority031.valid621 CutLabelCertificates.Minority031.sound621 H st hI
theorem probabilityBound458 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch118.certificate1417).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate959).dm (WitnessCertificates.Batch047.certificate959).beta) ≤ ((CutFailureCertificates.Budget047.certificate959).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound959 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate959).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch118.certificate1417).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch118.certificate1418).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch047.certificate959).omega:ℝ) ≤ ((CutFailureCertificates.Budget047.certificate959).bound:ℝ) at hb
  exact (exponentialBound458 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches459 : (MergedCutGroups.Batch118.certificate1421).GlobalMatches MergedCutGroups.Batch118.certificate1422 CountingCertificates.Batch048.certificate962 CutLabelCertificates.Entropy031.certificate627 CutLabelCertificates.Minority031.certificate626 := by decide +kernel
theorem exponentialBound459 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch118.certificate1421).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate962).dm (WitnessCertificates.Batch048.certificate962).beta) ≤ (2*exp (-((CountingCertificates.Batch048.certificate962).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch118.certificate1421).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch118.certificate1422).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch048.certificate962).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch118.certificate1421 MergedCutGroups.Batch118.certificate1422 CountingCertificates.Batch048.certificate962 CutLabelCertificates.Entropy031.certificate627 CutLabelCertificates.Minority031.certificate626 matches459 rfl rfl
    MergedCutGroups.Batch118.numericValid1421 MergedCutGroups.Batch118.numericValid1422 MergedCutGroups.Batch118.cellsSound1421 MergedCutGroups.Batch118.cellsSound1422
    MergedCutGroups.Batch118.cellsNumeric1421 MergedCutGroups.Batch118.cellsNumeric1422 MergedCutGroups.Batch118.populationMatches1421 MergedCutGroups.Batch118.populationMatches1422
    PopulationCertificates.Batch048.valid962 PopulationCertificates.Batch048.sound962 WitnessCertificates.Batch048.valid962 WitnessCertificates.Batch048.sound962 CountingCertificates.Batch048.valid962 CountingCertificates.Batch048.sound962
    CutLabelCertificates.Entropy031.valid627 CutLabelCertificates.Minority031.valid626 CutLabelCertificates.Minority031.sound626 H st hI
theorem probabilityBound459 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch118.certificate1421).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate962).dm (WitnessCertificates.Batch048.certificate962).beta) ≤ ((CutFailureCertificates.Budget048.certificate962).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound962 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate962).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch118.certificate1421).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch118.certificate1422).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch048.certificate962).omega:ℝ) ≤ ((CutFailureCertificates.Budget048.certificate962).bound:ℝ) at hb
  exact (exponentialBound459 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch022
