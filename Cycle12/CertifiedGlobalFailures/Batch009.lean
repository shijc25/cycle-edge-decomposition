import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch018
import Cycle12.CountingCertificates.Batch019
import Cycle12.CutFailureCertificates.Budget018
import Cycle12.CutFailureCertificates.Budget019
import Cycle12.CutLabelCertificates.Entropy009
import Cycle12.CutLabelCertificates.Entropy010
import Cycle12.CutLabelCertificates.Minority009
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

namespace Cycle12.CertifiedGlobalFailures.Batch009
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches180 : (MergedCutGroups.Batch045.certificate540).GlobalMatches MergedCutGroups.Batch045.certificate541 CountingCertificates.Batch018.certificate360 CutLabelCertificates.Entropy009.certificate181 CutLabelCertificates.Minority009.certificate180 := by decide +kernel
theorem exponentialBound180 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch045.certificate540).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate360).dm (WitnessCertificates.Batch018.certificate360).beta) ≤ (2*exp (-((CountingCertificates.Batch018.certificate360).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch045.certificate540).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch045.certificate541).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch018.certificate360).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch045.certificate540 MergedCutGroups.Batch045.certificate541 CountingCertificates.Batch018.certificate360 CutLabelCertificates.Entropy009.certificate181 CutLabelCertificates.Minority009.certificate180 matches180 rfl rfl
    MergedCutGroups.Batch045.numericValid540 MergedCutGroups.Batch045.numericValid541 MergedCutGroups.Batch045.cellsSound540 MergedCutGroups.Batch045.cellsSound541
    MergedCutGroups.Batch045.cellsNumeric540 MergedCutGroups.Batch045.cellsNumeric541 MergedCutGroups.Batch045.populationMatches540 MergedCutGroups.Batch045.populationMatches541
    PopulationCertificates.Batch018.valid360 PopulationCertificates.Batch018.sound360 WitnessCertificates.Batch018.valid360 WitnessCertificates.Batch018.sound360 CountingCertificates.Batch018.valid360 CountingCertificates.Batch018.sound360
    CutLabelCertificates.Entropy009.valid181 CutLabelCertificates.Minority009.valid180 CutLabelCertificates.Minority009.sound180 H st hI
theorem probabilityBound180 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch045.certificate540).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate360).dm (WitnessCertificates.Batch018.certificate360).beta) ≤ ((CutFailureCertificates.Budget018.certificate360).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound360 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate360).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch045.certificate540).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch045.certificate541).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch018.certificate360).omega:ℝ) ≤ ((CutFailureCertificates.Budget018.certificate360).bound:ℝ) at hb
  exact (exponentialBound180 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches181 : (MergedCutGroups.Batch045.certificate543).GlobalMatches MergedCutGroups.Batch045.certificate544 CountingCertificates.Batch018.certificate362 CutLabelCertificates.Entropy009.certificate182 CutLabelCertificates.Minority009.certificate181 := by decide +kernel
theorem exponentialBound181 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch045.certificate543).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate362).dm (WitnessCertificates.Batch018.certificate362).beta) ≤ (2*exp (-((CountingCertificates.Batch018.certificate362).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch045.certificate543).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch045.certificate544).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch018.certificate362).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch045.certificate543 MergedCutGroups.Batch045.certificate544 CountingCertificates.Batch018.certificate362 CutLabelCertificates.Entropy009.certificate182 CutLabelCertificates.Minority009.certificate181 matches181 rfl rfl
    MergedCutGroups.Batch045.numericValid543 MergedCutGroups.Batch045.numericValid544 MergedCutGroups.Batch045.cellsSound543 MergedCutGroups.Batch045.cellsSound544
    MergedCutGroups.Batch045.cellsNumeric543 MergedCutGroups.Batch045.cellsNumeric544 MergedCutGroups.Batch045.populationMatches543 MergedCutGroups.Batch045.populationMatches544
    PopulationCertificates.Batch018.valid362 PopulationCertificates.Batch018.sound362 WitnessCertificates.Batch018.valid362 WitnessCertificates.Batch018.sound362 CountingCertificates.Batch018.valid362 CountingCertificates.Batch018.sound362
    CutLabelCertificates.Entropy009.valid182 CutLabelCertificates.Minority009.valid181 CutLabelCertificates.Minority009.sound181 H st hI
theorem probabilityBound181 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch045.certificate543).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate362).dm (WitnessCertificates.Batch018.certificate362).beta) ≤ ((CutFailureCertificates.Budget018.certificate362).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound362 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate362).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch045.certificate543).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch045.certificate544).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch018.certificate362).omega:ℝ) ≤ ((CutFailureCertificates.Budget018.certificate362).bound:ℝ) at hb
  exact (exponentialBound181 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches182 : (MergedCutGroups.Batch045.certificate546).GlobalMatches MergedCutGroups.Batch045.certificate547 CountingCertificates.Batch018.certificate364 CutLabelCertificates.Entropy009.certificate183 CutLabelCertificates.Minority009.certificate182 := by decide +kernel
theorem exponentialBound182 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch045.certificate546).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate364).dm (WitnessCertificates.Batch018.certificate364).beta) ≤ (2*exp (-((CountingCertificates.Batch018.certificate364).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch045.certificate546).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch045.certificate547).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch018.certificate364).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch045.certificate546 MergedCutGroups.Batch045.certificate547 CountingCertificates.Batch018.certificate364 CutLabelCertificates.Entropy009.certificate183 CutLabelCertificates.Minority009.certificate182 matches182 rfl rfl
    MergedCutGroups.Batch045.numericValid546 MergedCutGroups.Batch045.numericValid547 MergedCutGroups.Batch045.cellsSound546 MergedCutGroups.Batch045.cellsSound547
    MergedCutGroups.Batch045.cellsNumeric546 MergedCutGroups.Batch045.cellsNumeric547 MergedCutGroups.Batch045.populationMatches546 MergedCutGroups.Batch045.populationMatches547
    PopulationCertificates.Batch018.valid364 PopulationCertificates.Batch018.sound364 WitnessCertificates.Batch018.valid364 WitnessCertificates.Batch018.sound364 CountingCertificates.Batch018.valid364 CountingCertificates.Batch018.sound364
    CutLabelCertificates.Entropy009.valid183 CutLabelCertificates.Minority009.valid182 CutLabelCertificates.Minority009.sound182 H st hI
theorem probabilityBound182 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch045.certificate546).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate364).dm (WitnessCertificates.Batch018.certificate364).beta) ≤ ((CutFailureCertificates.Budget018.certificate364).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound364 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate364).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch045.certificate546).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch045.certificate547).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch018.certificate364).omega:ℝ) ≤ ((CutFailureCertificates.Budget018.certificate364).bound:ℝ) at hb
  exact (exponentialBound182 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches183 : (MergedCutGroups.Batch045.certificate549).GlobalMatches MergedCutGroups.Batch045.certificate550 CountingCertificates.Batch018.certificate366 CutLabelCertificates.Entropy009.certificate184 CutLabelCertificates.Minority009.certificate183 := by decide +kernel
theorem exponentialBound183 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch045.certificate549).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate366).dm (WitnessCertificates.Batch018.certificate366).beta) ≤ (2*exp (-((CountingCertificates.Batch018.certificate366).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch045.certificate549).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch045.certificate550).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch018.certificate366).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch045.certificate549 MergedCutGroups.Batch045.certificate550 CountingCertificates.Batch018.certificate366 CutLabelCertificates.Entropy009.certificate184 CutLabelCertificates.Minority009.certificate183 matches183 rfl rfl
    MergedCutGroups.Batch045.numericValid549 MergedCutGroups.Batch045.numericValid550 MergedCutGroups.Batch045.cellsSound549 MergedCutGroups.Batch045.cellsSound550
    MergedCutGroups.Batch045.cellsNumeric549 MergedCutGroups.Batch045.cellsNumeric550 MergedCutGroups.Batch045.populationMatches549 MergedCutGroups.Batch045.populationMatches550
    PopulationCertificates.Batch018.valid366 PopulationCertificates.Batch018.sound366 WitnessCertificates.Batch018.valid366 WitnessCertificates.Batch018.sound366 CountingCertificates.Batch018.valid366 CountingCertificates.Batch018.sound366
    CutLabelCertificates.Entropy009.valid184 CutLabelCertificates.Minority009.valid183 CutLabelCertificates.Minority009.sound183 H st hI
theorem probabilityBound183 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch045.certificate549).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate366).dm (WitnessCertificates.Batch018.certificate366).beta) ≤ ((CutFailureCertificates.Budget018.certificate366).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound366 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate366).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch045.certificate549).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch045.certificate550).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch018.certificate366).omega:ℝ) ≤ ((CutFailureCertificates.Budget018.certificate366).bound:ℝ) at hb
  exact (exponentialBound183 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches184 : (MergedCutGroups.Batch046.certificate552).GlobalMatches MergedCutGroups.Batch046.certificate553 CountingCertificates.Batch018.certificate368 CutLabelCertificates.Entropy009.certificate185 CutLabelCertificates.Minority009.certificate184 := by decide +kernel
theorem exponentialBound184 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch046.certificate552).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate368).dm (WitnessCertificates.Batch018.certificate368).beta) ≤ (2*exp (-((CountingCertificates.Batch018.certificate368).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch046.certificate552).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch046.certificate553).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch018.certificate368).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch046.certificate552 MergedCutGroups.Batch046.certificate553 CountingCertificates.Batch018.certificate368 CutLabelCertificates.Entropy009.certificate185 CutLabelCertificates.Minority009.certificate184 matches184 rfl rfl
    MergedCutGroups.Batch046.numericValid552 MergedCutGroups.Batch046.numericValid553 MergedCutGroups.Batch046.cellsSound552 MergedCutGroups.Batch046.cellsSound553
    MergedCutGroups.Batch046.cellsNumeric552 MergedCutGroups.Batch046.cellsNumeric553 MergedCutGroups.Batch046.populationMatches552 MergedCutGroups.Batch046.populationMatches553
    PopulationCertificates.Batch018.valid368 PopulationCertificates.Batch018.sound368 WitnessCertificates.Batch018.valid368 WitnessCertificates.Batch018.sound368 CountingCertificates.Batch018.valid368 CountingCertificates.Batch018.sound368
    CutLabelCertificates.Entropy009.valid185 CutLabelCertificates.Minority009.valid184 CutLabelCertificates.Minority009.sound184 H st hI
theorem probabilityBound184 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch046.certificate552).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate368).dm (WitnessCertificates.Batch018.certificate368).beta) ≤ ((CutFailureCertificates.Budget018.certificate368).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound368 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate368).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch046.certificate552).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch046.certificate553).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch018.certificate368).omega:ℝ) ≤ ((CutFailureCertificates.Budget018.certificate368).bound:ℝ) at hb
  exact (exponentialBound184 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches185 : (MergedCutGroups.Batch046.certificate555).GlobalMatches MergedCutGroups.Batch046.certificate556 CountingCertificates.Batch018.certificate370 CutLabelCertificates.Entropy009.certificate186 CutLabelCertificates.Minority009.certificate185 := by decide +kernel
theorem exponentialBound185 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch046.certificate555).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate370).dm (WitnessCertificates.Batch018.certificate370).beta) ≤ (2*exp (-((CountingCertificates.Batch018.certificate370).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch046.certificate555).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch046.certificate556).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch018.certificate370).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch046.certificate555 MergedCutGroups.Batch046.certificate556 CountingCertificates.Batch018.certificate370 CutLabelCertificates.Entropy009.certificate186 CutLabelCertificates.Minority009.certificate185 matches185 rfl rfl
    MergedCutGroups.Batch046.numericValid555 MergedCutGroups.Batch046.numericValid556 MergedCutGroups.Batch046.cellsSound555 MergedCutGroups.Batch046.cellsSound556
    MergedCutGroups.Batch046.cellsNumeric555 MergedCutGroups.Batch046.cellsNumeric556 MergedCutGroups.Batch046.populationMatches555 MergedCutGroups.Batch046.populationMatches556
    PopulationCertificates.Batch018.valid370 PopulationCertificates.Batch018.sound370 WitnessCertificates.Batch018.valid370 WitnessCertificates.Batch018.sound370 CountingCertificates.Batch018.valid370 CountingCertificates.Batch018.sound370
    CutLabelCertificates.Entropy009.valid186 CutLabelCertificates.Minority009.valid185 CutLabelCertificates.Minority009.sound185 H st hI
theorem probabilityBound185 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch046.certificate555).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate370).dm (WitnessCertificates.Batch018.certificate370).beta) ≤ ((CutFailureCertificates.Budget018.certificate370).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound370 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate370).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch046.certificate555).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch046.certificate556).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch018.certificate370).omega:ℝ) ≤ ((CutFailureCertificates.Budget018.certificate370).bound:ℝ) at hb
  exact (exponentialBound185 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches186 : (MergedCutGroups.Batch046.certificate558).GlobalMatches MergedCutGroups.Batch046.certificate559 CountingCertificates.Batch018.certificate372 CutLabelCertificates.Entropy009.certificate187 CutLabelCertificates.Minority009.certificate186 := by decide +kernel
theorem exponentialBound186 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch046.certificate558).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate372).dm (WitnessCertificates.Batch018.certificate372).beta) ≤ (2*exp (-((CountingCertificates.Batch018.certificate372).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch046.certificate558).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch046.certificate559).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch018.certificate372).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch046.certificate558 MergedCutGroups.Batch046.certificate559 CountingCertificates.Batch018.certificate372 CutLabelCertificates.Entropy009.certificate187 CutLabelCertificates.Minority009.certificate186 matches186 rfl rfl
    MergedCutGroups.Batch046.numericValid558 MergedCutGroups.Batch046.numericValid559 MergedCutGroups.Batch046.cellsSound558 MergedCutGroups.Batch046.cellsSound559
    MergedCutGroups.Batch046.cellsNumeric558 MergedCutGroups.Batch046.cellsNumeric559 MergedCutGroups.Batch046.populationMatches558 MergedCutGroups.Batch046.populationMatches559
    PopulationCertificates.Batch018.valid372 PopulationCertificates.Batch018.sound372 WitnessCertificates.Batch018.valid372 WitnessCertificates.Batch018.sound372 CountingCertificates.Batch018.valid372 CountingCertificates.Batch018.sound372
    CutLabelCertificates.Entropy009.valid187 CutLabelCertificates.Minority009.valid186 CutLabelCertificates.Minority009.sound186 H st hI
theorem probabilityBound186 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch046.certificate558).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate372).dm (WitnessCertificates.Batch018.certificate372).beta) ≤ ((CutFailureCertificates.Budget018.certificate372).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound372 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate372).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch046.certificate558).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch046.certificate559).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch018.certificate372).omega:ℝ) ≤ ((CutFailureCertificates.Budget018.certificate372).bound:ℝ) at hb
  exact (exponentialBound186 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches187 : (MergedCutGroups.Batch046.certificate561).GlobalMatches MergedCutGroups.Batch046.certificate562 CountingCertificates.Batch018.certificate374 CutLabelCertificates.Entropy009.certificate188 CutLabelCertificates.Minority009.certificate187 := by decide +kernel
theorem exponentialBound187 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch046.certificate561).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate374).dm (WitnessCertificates.Batch018.certificate374).beta) ≤ (2*exp (-((CountingCertificates.Batch018.certificate374).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch046.certificate561).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch046.certificate562).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch018.certificate374).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch046.certificate561 MergedCutGroups.Batch046.certificate562 CountingCertificates.Batch018.certificate374 CutLabelCertificates.Entropy009.certificate188 CutLabelCertificates.Minority009.certificate187 matches187 rfl rfl
    MergedCutGroups.Batch046.numericValid561 MergedCutGroups.Batch046.numericValid562 MergedCutGroups.Batch046.cellsSound561 MergedCutGroups.Batch046.cellsSound562
    MergedCutGroups.Batch046.cellsNumeric561 MergedCutGroups.Batch046.cellsNumeric562 MergedCutGroups.Batch046.populationMatches561 MergedCutGroups.Batch046.populationMatches562
    PopulationCertificates.Batch018.valid374 PopulationCertificates.Batch018.sound374 WitnessCertificates.Batch018.valid374 WitnessCertificates.Batch018.sound374 CountingCertificates.Batch018.valid374 CountingCertificates.Batch018.sound374
    CutLabelCertificates.Entropy009.valid188 CutLabelCertificates.Minority009.valid187 CutLabelCertificates.Minority009.sound187 H st hI
theorem probabilityBound187 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch046.certificate561).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate374).dm (WitnessCertificates.Batch018.certificate374).beta) ≤ ((CutFailureCertificates.Budget018.certificate374).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound374 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate374).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch046.certificate561).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch046.certificate562).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch018.certificate374).omega:ℝ) ≤ ((CutFailureCertificates.Budget018.certificate374).bound:ℝ) at hb
  exact (exponentialBound187 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches188 : (MergedCutGroups.Batch047.certificate564).GlobalMatches MergedCutGroups.Batch047.certificate565 CountingCertificates.Batch018.certificate376 CutLabelCertificates.Entropy009.certificate189 CutLabelCertificates.Minority009.certificate188 := by decide +kernel
theorem exponentialBound188 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch047.certificate564).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate376).dm (WitnessCertificates.Batch018.certificate376).beta) ≤ (2*exp (-((CountingCertificates.Batch018.certificate376).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch047.certificate564).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch047.certificate565).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch018.certificate376).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch047.certificate564 MergedCutGroups.Batch047.certificate565 CountingCertificates.Batch018.certificate376 CutLabelCertificates.Entropy009.certificate189 CutLabelCertificates.Minority009.certificate188 matches188 rfl rfl
    MergedCutGroups.Batch047.numericValid564 MergedCutGroups.Batch047.numericValid565 MergedCutGroups.Batch047.cellsSound564 MergedCutGroups.Batch047.cellsSound565
    MergedCutGroups.Batch047.cellsNumeric564 MergedCutGroups.Batch047.cellsNumeric565 MergedCutGroups.Batch047.populationMatches564 MergedCutGroups.Batch047.populationMatches565
    PopulationCertificates.Batch018.valid376 PopulationCertificates.Batch018.sound376 WitnessCertificates.Batch018.valid376 WitnessCertificates.Batch018.sound376 CountingCertificates.Batch018.valid376 CountingCertificates.Batch018.sound376
    CutLabelCertificates.Entropy009.valid189 CutLabelCertificates.Minority009.valid188 CutLabelCertificates.Minority009.sound188 H st hI
theorem probabilityBound188 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch047.certificate564).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate376).dm (WitnessCertificates.Batch018.certificate376).beta) ≤ ((CutFailureCertificates.Budget018.certificate376).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound376 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate376).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch047.certificate564).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch047.certificate565).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch018.certificate376).omega:ℝ) ≤ ((CutFailureCertificates.Budget018.certificate376).bound:ℝ) at hb
  exact (exponentialBound188 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches189 : (MergedCutGroups.Batch047.certificate567).GlobalMatches MergedCutGroups.Batch047.certificate568 CountingCertificates.Batch018.certificate378 CutLabelCertificates.Entropy009.certificate190 CutLabelCertificates.Minority009.certificate189 := by decide +kernel
theorem exponentialBound189 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch047.certificate567).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate378).dm (WitnessCertificates.Batch018.certificate378).beta) ≤ (2*exp (-((CountingCertificates.Batch018.certificate378).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch047.certificate567).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch047.certificate568).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch018.certificate378).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch047.certificate567 MergedCutGroups.Batch047.certificate568 CountingCertificates.Batch018.certificate378 CutLabelCertificates.Entropy009.certificate190 CutLabelCertificates.Minority009.certificate189 matches189 rfl rfl
    MergedCutGroups.Batch047.numericValid567 MergedCutGroups.Batch047.numericValid568 MergedCutGroups.Batch047.cellsSound567 MergedCutGroups.Batch047.cellsSound568
    MergedCutGroups.Batch047.cellsNumeric567 MergedCutGroups.Batch047.cellsNumeric568 MergedCutGroups.Batch047.populationMatches567 MergedCutGroups.Batch047.populationMatches568
    PopulationCertificates.Batch018.valid378 PopulationCertificates.Batch018.sound378 WitnessCertificates.Batch018.valid378 WitnessCertificates.Batch018.sound378 CountingCertificates.Batch018.valid378 CountingCertificates.Batch018.sound378
    CutLabelCertificates.Entropy009.valid190 CutLabelCertificates.Minority009.valid189 CutLabelCertificates.Minority009.sound189 H st hI
theorem probabilityBound189 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch047.certificate567).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch018.certificate378).dm (WitnessCertificates.Batch018.certificate378).beta) ≤ ((CutFailureCertificates.Budget018.certificate378).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget018.sound378 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch018.certificate378).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch047.certificate567).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch047.certificate568).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch018.certificate378).omega:ℝ) ≤ ((CutFailureCertificates.Budget018.certificate378).bound:ℝ) at hb
  exact (exponentialBound189 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches190 : (MergedCutGroups.Batch047.certificate570).GlobalMatches MergedCutGroups.Batch047.certificate571 CountingCertificates.Batch019.certificate380 CutLabelCertificates.Entropy009.certificate191 CutLabelCertificates.Minority009.certificate190 := by decide +kernel
theorem exponentialBound190 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch047.certificate570).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate380).dm (WitnessCertificates.Batch019.certificate380).beta) ≤ (2*exp (-((CountingCertificates.Batch019.certificate380).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch047.certificate570).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch047.certificate571).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch019.certificate380).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch047.certificate570 MergedCutGroups.Batch047.certificate571 CountingCertificates.Batch019.certificate380 CutLabelCertificates.Entropy009.certificate191 CutLabelCertificates.Minority009.certificate190 matches190 rfl rfl
    MergedCutGroups.Batch047.numericValid570 MergedCutGroups.Batch047.numericValid571 MergedCutGroups.Batch047.cellsSound570 MergedCutGroups.Batch047.cellsSound571
    MergedCutGroups.Batch047.cellsNumeric570 MergedCutGroups.Batch047.cellsNumeric571 MergedCutGroups.Batch047.populationMatches570 MergedCutGroups.Batch047.populationMatches571
    PopulationCertificates.Batch019.valid380 PopulationCertificates.Batch019.sound380 WitnessCertificates.Batch019.valid380 WitnessCertificates.Batch019.sound380 CountingCertificates.Batch019.valid380 CountingCertificates.Batch019.sound380
    CutLabelCertificates.Entropy009.valid191 CutLabelCertificates.Minority009.valid190 CutLabelCertificates.Minority009.sound190 H st hI
theorem probabilityBound190 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch047.certificate570).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate380).dm (WitnessCertificates.Batch019.certificate380).beta) ≤ ((CutFailureCertificates.Budget019.certificate380).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound380 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate380).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch047.certificate570).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch047.certificate571).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch019.certificate380).omega:ℝ) ≤ ((CutFailureCertificates.Budget019.certificate380).bound:ℝ) at hb
  exact (exponentialBound190 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches191 : (MergedCutGroups.Batch047.certificate573).GlobalMatches MergedCutGroups.Batch047.certificate574 CountingCertificates.Batch019.certificate382 CutLabelCertificates.Entropy009.certificate192 CutLabelCertificates.Minority009.certificate191 := by decide +kernel
theorem exponentialBound191 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch047.certificate573).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate382).dm (WitnessCertificates.Batch019.certificate382).beta) ≤ (2*exp (-((CountingCertificates.Batch019.certificate382).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch047.certificate573).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch047.certificate574).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch019.certificate382).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch047.certificate573 MergedCutGroups.Batch047.certificate574 CountingCertificates.Batch019.certificate382 CutLabelCertificates.Entropy009.certificate192 CutLabelCertificates.Minority009.certificate191 matches191 rfl rfl
    MergedCutGroups.Batch047.numericValid573 MergedCutGroups.Batch047.numericValid574 MergedCutGroups.Batch047.cellsSound573 MergedCutGroups.Batch047.cellsSound574
    MergedCutGroups.Batch047.cellsNumeric573 MergedCutGroups.Batch047.cellsNumeric574 MergedCutGroups.Batch047.populationMatches573 MergedCutGroups.Batch047.populationMatches574
    PopulationCertificates.Batch019.valid382 PopulationCertificates.Batch019.sound382 WitnessCertificates.Batch019.valid382 WitnessCertificates.Batch019.sound382 CountingCertificates.Batch019.valid382 CountingCertificates.Batch019.sound382
    CutLabelCertificates.Entropy009.valid192 CutLabelCertificates.Minority009.valid191 CutLabelCertificates.Minority009.sound191 H st hI
theorem probabilityBound191 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch047.certificate573).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate382).dm (WitnessCertificates.Batch019.certificate382).beta) ≤ ((CutFailureCertificates.Budget019.certificate382).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound382 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate382).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch047.certificate573).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch047.certificate574).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch019.certificate382).omega:ℝ) ≤ ((CutFailureCertificates.Budget019.certificate382).bound:ℝ) at hb
  exact (exponentialBound191 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches192 : (MergedCutGroups.Batch048.certificate576).GlobalMatches MergedCutGroups.Batch048.certificate577 CountingCertificates.Batch019.certificate384 CutLabelCertificates.Entropy009.certificate193 CutLabelCertificates.Minority009.certificate192 := by decide +kernel
theorem exponentialBound192 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch048.certificate576).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate384).dm (WitnessCertificates.Batch019.certificate384).beta) ≤ (2*exp (-((CountingCertificates.Batch019.certificate384).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch048.certificate576).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch048.certificate577).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch019.certificate384).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch048.certificate576 MergedCutGroups.Batch048.certificate577 CountingCertificates.Batch019.certificate384 CutLabelCertificates.Entropy009.certificate193 CutLabelCertificates.Minority009.certificate192 matches192 rfl rfl
    MergedCutGroups.Batch048.numericValid576 MergedCutGroups.Batch048.numericValid577 MergedCutGroups.Batch048.cellsSound576 MergedCutGroups.Batch048.cellsSound577
    MergedCutGroups.Batch048.cellsNumeric576 MergedCutGroups.Batch048.cellsNumeric577 MergedCutGroups.Batch048.populationMatches576 MergedCutGroups.Batch048.populationMatches577
    PopulationCertificates.Batch019.valid384 PopulationCertificates.Batch019.sound384 WitnessCertificates.Batch019.valid384 WitnessCertificates.Batch019.sound384 CountingCertificates.Batch019.valid384 CountingCertificates.Batch019.sound384
    CutLabelCertificates.Entropy009.valid193 CutLabelCertificates.Minority009.valid192 CutLabelCertificates.Minority009.sound192 H st hI
theorem probabilityBound192 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch048.certificate576).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate384).dm (WitnessCertificates.Batch019.certificate384).beta) ≤ ((CutFailureCertificates.Budget019.certificate384).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound384 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate384).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch048.certificate576).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch048.certificate577).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch019.certificate384).omega:ℝ) ≤ ((CutFailureCertificates.Budget019.certificate384).bound:ℝ) at hb
  exact (exponentialBound192 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches193 : (MergedCutGroups.Batch048.certificate579).GlobalMatches MergedCutGroups.Batch048.certificate580 CountingCertificates.Batch019.certificate386 CutLabelCertificates.Entropy009.certificate194 CutLabelCertificates.Minority009.certificate193 := by decide +kernel
theorem exponentialBound193 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch048.certificate579).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate386).dm (WitnessCertificates.Batch019.certificate386).beta) ≤ (2*exp (-((CountingCertificates.Batch019.certificate386).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch048.certificate579).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch048.certificate580).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch019.certificate386).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch048.certificate579 MergedCutGroups.Batch048.certificate580 CountingCertificates.Batch019.certificate386 CutLabelCertificates.Entropy009.certificate194 CutLabelCertificates.Minority009.certificate193 matches193 rfl rfl
    MergedCutGroups.Batch048.numericValid579 MergedCutGroups.Batch048.numericValid580 MergedCutGroups.Batch048.cellsSound579 MergedCutGroups.Batch048.cellsSound580
    MergedCutGroups.Batch048.cellsNumeric579 MergedCutGroups.Batch048.cellsNumeric580 MergedCutGroups.Batch048.populationMatches579 MergedCutGroups.Batch048.populationMatches580
    PopulationCertificates.Batch019.valid386 PopulationCertificates.Batch019.sound386 WitnessCertificates.Batch019.valid386 WitnessCertificates.Batch019.sound386 CountingCertificates.Batch019.valid386 CountingCertificates.Batch019.sound386
    CutLabelCertificates.Entropy009.valid194 CutLabelCertificates.Minority009.valid193 CutLabelCertificates.Minority009.sound193 H st hI
theorem probabilityBound193 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch048.certificate579).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate386).dm (WitnessCertificates.Batch019.certificate386).beta) ≤ ((CutFailureCertificates.Budget019.certificate386).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound386 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate386).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch048.certificate579).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch048.certificate580).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch019.certificate386).omega:ℝ) ≤ ((CutFailureCertificates.Budget019.certificate386).bound:ℝ) at hb
  exact (exponentialBound193 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches194 : (MergedCutGroups.Batch048.certificate582).GlobalMatches MergedCutGroups.Batch048.certificate583 CountingCertificates.Batch019.certificate388 CutLabelCertificates.Entropy009.certificate195 CutLabelCertificates.Minority009.certificate194 := by decide +kernel
theorem exponentialBound194 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch048.certificate582).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate388).dm (WitnessCertificates.Batch019.certificate388).beta) ≤ (2*exp (-((CountingCertificates.Batch019.certificate388).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch048.certificate582).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch048.certificate583).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch019.certificate388).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch048.certificate582 MergedCutGroups.Batch048.certificate583 CountingCertificates.Batch019.certificate388 CutLabelCertificates.Entropy009.certificate195 CutLabelCertificates.Minority009.certificate194 matches194 rfl rfl
    MergedCutGroups.Batch048.numericValid582 MergedCutGroups.Batch048.numericValid583 MergedCutGroups.Batch048.cellsSound582 MergedCutGroups.Batch048.cellsSound583
    MergedCutGroups.Batch048.cellsNumeric582 MergedCutGroups.Batch048.cellsNumeric583 MergedCutGroups.Batch048.populationMatches582 MergedCutGroups.Batch048.populationMatches583
    PopulationCertificates.Batch019.valid388 PopulationCertificates.Batch019.sound388 WitnessCertificates.Batch019.valid388 WitnessCertificates.Batch019.sound388 CountingCertificates.Batch019.valid388 CountingCertificates.Batch019.sound388
    CutLabelCertificates.Entropy009.valid195 CutLabelCertificates.Minority009.valid194 CutLabelCertificates.Minority009.sound194 H st hI
theorem probabilityBound194 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch048.certificate582).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate388).dm (WitnessCertificates.Batch019.certificate388).beta) ≤ ((CutFailureCertificates.Budget019.certificate388).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound388 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate388).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch048.certificate582).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch048.certificate583).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch019.certificate388).omega:ℝ) ≤ ((CutFailureCertificates.Budget019.certificate388).bound:ℝ) at hb
  exact (exponentialBound194 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches195 : (MergedCutGroups.Batch048.certificate585).GlobalMatches MergedCutGroups.Batch048.certificate586 CountingCertificates.Batch019.certificate390 CutLabelCertificates.Entropy009.certificate196 CutLabelCertificates.Minority009.certificate195 := by decide +kernel
theorem exponentialBound195 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch048.certificate585).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate390).dm (WitnessCertificates.Batch019.certificate390).beta) ≤ (2*exp (-((CountingCertificates.Batch019.certificate390).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch048.certificate585).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch048.certificate586).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch019.certificate390).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch048.certificate585 MergedCutGroups.Batch048.certificate586 CountingCertificates.Batch019.certificate390 CutLabelCertificates.Entropy009.certificate196 CutLabelCertificates.Minority009.certificate195 matches195 rfl rfl
    MergedCutGroups.Batch048.numericValid585 MergedCutGroups.Batch048.numericValid586 MergedCutGroups.Batch048.cellsSound585 MergedCutGroups.Batch048.cellsSound586
    MergedCutGroups.Batch048.cellsNumeric585 MergedCutGroups.Batch048.cellsNumeric586 MergedCutGroups.Batch048.populationMatches585 MergedCutGroups.Batch048.populationMatches586
    PopulationCertificates.Batch019.valid390 PopulationCertificates.Batch019.sound390 WitnessCertificates.Batch019.valid390 WitnessCertificates.Batch019.sound390 CountingCertificates.Batch019.valid390 CountingCertificates.Batch019.sound390
    CutLabelCertificates.Entropy009.valid196 CutLabelCertificates.Minority009.valid195 CutLabelCertificates.Minority009.sound195 H st hI
theorem probabilityBound195 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch048.certificate585).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate390).dm (WitnessCertificates.Batch019.certificate390).beta) ≤ ((CutFailureCertificates.Budget019.certificate390).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound390 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate390).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch048.certificate585).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch048.certificate586).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch019.certificate390).omega:ℝ) ≤ ((CutFailureCertificates.Budget019.certificate390).bound:ℝ) at hb
  exact (exponentialBound195 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches196 : (MergedCutGroups.Batch049.certificate588).GlobalMatches MergedCutGroups.Batch049.certificate589 CountingCertificates.Batch019.certificate392 CutLabelCertificates.Entropy009.certificate197 CutLabelCertificates.Minority009.certificate196 := by decide +kernel
theorem exponentialBound196 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch049.certificate588).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate392).dm (WitnessCertificates.Batch019.certificate392).beta) ≤ (2*exp (-((CountingCertificates.Batch019.certificate392).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch049.certificate588).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch049.certificate589).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch019.certificate392).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch049.certificate588 MergedCutGroups.Batch049.certificate589 CountingCertificates.Batch019.certificate392 CutLabelCertificates.Entropy009.certificate197 CutLabelCertificates.Minority009.certificate196 matches196 rfl rfl
    MergedCutGroups.Batch049.numericValid588 MergedCutGroups.Batch049.numericValid589 MergedCutGroups.Batch049.cellsSound588 MergedCutGroups.Batch049.cellsSound589
    MergedCutGroups.Batch049.cellsNumeric588 MergedCutGroups.Batch049.cellsNumeric589 MergedCutGroups.Batch049.populationMatches588 MergedCutGroups.Batch049.populationMatches589
    PopulationCertificates.Batch019.valid392 PopulationCertificates.Batch019.sound392 WitnessCertificates.Batch019.valid392 WitnessCertificates.Batch019.sound392 CountingCertificates.Batch019.valid392 CountingCertificates.Batch019.sound392
    CutLabelCertificates.Entropy009.valid197 CutLabelCertificates.Minority009.valid196 CutLabelCertificates.Minority009.sound196 H st hI
theorem probabilityBound196 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch049.certificate588).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate392).dm (WitnessCertificates.Batch019.certificate392).beta) ≤ ((CutFailureCertificates.Budget019.certificate392).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound392 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate392).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch049.certificate588).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch049.certificate589).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch019.certificate392).omega:ℝ) ≤ ((CutFailureCertificates.Budget019.certificate392).bound:ℝ) at hb
  exact (exponentialBound196 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches197 : (MergedCutGroups.Batch049.certificate591).GlobalMatches MergedCutGroups.Batch049.certificate592 CountingCertificates.Batch019.certificate394 CutLabelCertificates.Entropy009.certificate198 CutLabelCertificates.Minority009.certificate197 := by decide +kernel
theorem exponentialBound197 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch049.certificate591).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate394).dm (WitnessCertificates.Batch019.certificate394).beta) ≤ (2*exp (-((CountingCertificates.Batch019.certificate394).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch049.certificate591).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch049.certificate592).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch019.certificate394).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch049.certificate591 MergedCutGroups.Batch049.certificate592 CountingCertificates.Batch019.certificate394 CutLabelCertificates.Entropy009.certificate198 CutLabelCertificates.Minority009.certificate197 matches197 rfl rfl
    MergedCutGroups.Batch049.numericValid591 MergedCutGroups.Batch049.numericValid592 MergedCutGroups.Batch049.cellsSound591 MergedCutGroups.Batch049.cellsSound592
    MergedCutGroups.Batch049.cellsNumeric591 MergedCutGroups.Batch049.cellsNumeric592 MergedCutGroups.Batch049.populationMatches591 MergedCutGroups.Batch049.populationMatches592
    PopulationCertificates.Batch019.valid394 PopulationCertificates.Batch019.sound394 WitnessCertificates.Batch019.valid394 WitnessCertificates.Batch019.sound394 CountingCertificates.Batch019.valid394 CountingCertificates.Batch019.sound394
    CutLabelCertificates.Entropy009.valid198 CutLabelCertificates.Minority009.valid197 CutLabelCertificates.Minority009.sound197 H st hI
theorem probabilityBound197 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch049.certificate591).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate394).dm (WitnessCertificates.Batch019.certificate394).beta) ≤ ((CutFailureCertificates.Budget019.certificate394).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound394 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate394).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch049.certificate591).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch049.certificate592).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch019.certificate394).omega:ℝ) ≤ ((CutFailureCertificates.Budget019.certificate394).bound:ℝ) at hb
  exact (exponentialBound197 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches198 : (MergedCutGroups.Batch049.certificate594).GlobalMatches MergedCutGroups.Batch049.certificate595 CountingCertificates.Batch019.certificate396 CutLabelCertificates.Entropy009.certificate199 CutLabelCertificates.Minority009.certificate198 := by decide +kernel
theorem exponentialBound198 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch049.certificate594).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate396).dm (WitnessCertificates.Batch019.certificate396).beta) ≤ (2*exp (-((CountingCertificates.Batch019.certificate396).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch049.certificate594).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch049.certificate595).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch019.certificate396).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch049.certificate594 MergedCutGroups.Batch049.certificate595 CountingCertificates.Batch019.certificate396 CutLabelCertificates.Entropy009.certificate199 CutLabelCertificates.Minority009.certificate198 matches198 rfl rfl
    MergedCutGroups.Batch049.numericValid594 MergedCutGroups.Batch049.numericValid595 MergedCutGroups.Batch049.cellsSound594 MergedCutGroups.Batch049.cellsSound595
    MergedCutGroups.Batch049.cellsNumeric594 MergedCutGroups.Batch049.cellsNumeric595 MergedCutGroups.Batch049.populationMatches594 MergedCutGroups.Batch049.populationMatches595
    PopulationCertificates.Batch019.valid396 PopulationCertificates.Batch019.sound396 WitnessCertificates.Batch019.valid396 WitnessCertificates.Batch019.sound396 CountingCertificates.Batch019.valid396 CountingCertificates.Batch019.sound396
    CutLabelCertificates.Entropy009.valid199 CutLabelCertificates.Minority009.valid198 CutLabelCertificates.Minority009.sound198 H st hI
theorem probabilityBound198 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch049.certificate594).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate396).dm (WitnessCertificates.Batch019.certificate396).beta) ≤ ((CutFailureCertificates.Budget019.certificate396).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound396 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate396).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch049.certificate594).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch049.certificate595).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch019.certificate396).omega:ℝ) ≤ ((CutFailureCertificates.Budget019.certificate396).bound:ℝ) at hb
  exact (exponentialBound198 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches199 : (MergedCutGroups.Batch049.certificate597).GlobalMatches MergedCutGroups.Batch049.certificate598 CountingCertificates.Batch019.certificate398 CutLabelCertificates.Entropy010.certificate200 CutLabelCertificates.Minority009.certificate199 := by decide +kernel
theorem exponentialBound199 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch049.certificate597).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate398).dm (WitnessCertificates.Batch019.certificate398).beta) ≤ (2*exp (-((CountingCertificates.Batch019.certificate398).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch049.certificate597).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch049.certificate598).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch019.certificate398).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch049.certificate597 MergedCutGroups.Batch049.certificate598 CountingCertificates.Batch019.certificate398 CutLabelCertificates.Entropy010.certificate200 CutLabelCertificates.Minority009.certificate199 matches199 rfl rfl
    MergedCutGroups.Batch049.numericValid597 MergedCutGroups.Batch049.numericValid598 MergedCutGroups.Batch049.cellsSound597 MergedCutGroups.Batch049.cellsSound598
    MergedCutGroups.Batch049.cellsNumeric597 MergedCutGroups.Batch049.cellsNumeric598 MergedCutGroups.Batch049.populationMatches597 MergedCutGroups.Batch049.populationMatches598
    PopulationCertificates.Batch019.valid398 PopulationCertificates.Batch019.sound398 WitnessCertificates.Batch019.valid398 WitnessCertificates.Batch019.sound398 CountingCertificates.Batch019.valid398 CountingCertificates.Batch019.sound398
    CutLabelCertificates.Entropy010.valid200 CutLabelCertificates.Minority009.valid199 CutLabelCertificates.Minority009.sound199 H st hI
theorem probabilityBound199 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch049.certificate597).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch019.certificate398).dm (WitnessCertificates.Batch019.certificate398).beta) ≤ ((CutFailureCertificates.Budget019.certificate398).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget019.sound398 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch019.certificate398).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch049.certificate597).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch049.certificate598).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch019.certificate398).omega:ℝ) ≤ ((CutFailureCertificates.Budget019.certificate398).bound:ℝ) at hb
  exact (exponentialBound199 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch009
