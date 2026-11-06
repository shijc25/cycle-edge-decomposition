import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch016
import Cycle12.CountingCertificates.Batch017
import Cycle12.CutFailureCertificates.Budget016
import Cycle12.CutFailureCertificates.Budget017
import Cycle12.CutLabelCertificates.Entropy008
import Cycle12.CutLabelCertificates.Entropy009
import Cycle12.CutLabelCertificates.Minority008
import Cycle12.MergedCutGroups.Batch040
import Cycle12.MergedCutGroups.Batch041
import Cycle12.MergedCutGroups.Batch042
import Cycle12.MergedCutGroups.Batch043
import Cycle12.MergedCutGroups.Batch044
import Cycle12.PopulationCertificates.Batch016
import Cycle12.PopulationCertificates.Batch017
import Cycle12.WitnessCertificates.Batch016
import Cycle12.WitnessCertificates.Batch017

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch008
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches160 : (MergedCutGroups.Batch040.certificate480).GlobalMatches MergedCutGroups.Batch040.certificate481 CountingCertificates.Batch016.certificate320 CutLabelCertificates.Entropy008.certificate161 CutLabelCertificates.Minority008.certificate160 := by decide +kernel
theorem exponentialBound160 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch040.certificate480).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate320).dm (WitnessCertificates.Batch016.certificate320).beta) ≤ (2*exp (-((CountingCertificates.Batch016.certificate320).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch040.certificate480).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch040.certificate481).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch016.certificate320).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch040.certificate480 MergedCutGroups.Batch040.certificate481 CountingCertificates.Batch016.certificate320 CutLabelCertificates.Entropy008.certificate161 CutLabelCertificates.Minority008.certificate160 matches160 rfl rfl
    MergedCutGroups.Batch040.numericValid480 MergedCutGroups.Batch040.numericValid481 MergedCutGroups.Batch040.cellsSound480 MergedCutGroups.Batch040.cellsSound481
    MergedCutGroups.Batch040.cellsNumeric480 MergedCutGroups.Batch040.cellsNumeric481 MergedCutGroups.Batch040.populationMatches480 MergedCutGroups.Batch040.populationMatches481
    PopulationCertificates.Batch016.valid320 PopulationCertificates.Batch016.sound320 WitnessCertificates.Batch016.valid320 WitnessCertificates.Batch016.sound320 CountingCertificates.Batch016.valid320 CountingCertificates.Batch016.sound320
    CutLabelCertificates.Entropy008.valid161 CutLabelCertificates.Minority008.valid160 CutLabelCertificates.Minority008.sound160 H st hI
theorem probabilityBound160 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch040.certificate480).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate320).dm (WitnessCertificates.Batch016.certificate320).beta) ≤ ((CutFailureCertificates.Budget016.certificate320).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound320 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate320).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch040.certificate480).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch040.certificate481).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch016.certificate320).omega:ℝ) ≤ ((CutFailureCertificates.Budget016.certificate320).bound:ℝ) at hb
  exact (exponentialBound160 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches161 : (MergedCutGroups.Batch040.certificate483).GlobalMatches MergedCutGroups.Batch040.certificate484 CountingCertificates.Batch016.certificate322 CutLabelCertificates.Entropy008.certificate162 CutLabelCertificates.Minority008.certificate161 := by decide +kernel
theorem exponentialBound161 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch040.certificate483).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate322).dm (WitnessCertificates.Batch016.certificate322).beta) ≤ (2*exp (-((CountingCertificates.Batch016.certificate322).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch040.certificate483).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch040.certificate484).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch016.certificate322).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch040.certificate483 MergedCutGroups.Batch040.certificate484 CountingCertificates.Batch016.certificate322 CutLabelCertificates.Entropy008.certificate162 CutLabelCertificates.Minority008.certificate161 matches161 rfl rfl
    MergedCutGroups.Batch040.numericValid483 MergedCutGroups.Batch040.numericValid484 MergedCutGroups.Batch040.cellsSound483 MergedCutGroups.Batch040.cellsSound484
    MergedCutGroups.Batch040.cellsNumeric483 MergedCutGroups.Batch040.cellsNumeric484 MergedCutGroups.Batch040.populationMatches483 MergedCutGroups.Batch040.populationMatches484
    PopulationCertificates.Batch016.valid322 PopulationCertificates.Batch016.sound322 WitnessCertificates.Batch016.valid322 WitnessCertificates.Batch016.sound322 CountingCertificates.Batch016.valid322 CountingCertificates.Batch016.sound322
    CutLabelCertificates.Entropy008.valid162 CutLabelCertificates.Minority008.valid161 CutLabelCertificates.Minority008.sound161 H st hI
theorem probabilityBound161 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch040.certificate483).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate322).dm (WitnessCertificates.Batch016.certificate322).beta) ≤ ((CutFailureCertificates.Budget016.certificate322).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound322 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate322).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch040.certificate483).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch040.certificate484).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch016.certificate322).omega:ℝ) ≤ ((CutFailureCertificates.Budget016.certificate322).bound:ℝ) at hb
  exact (exponentialBound161 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches162 : (MergedCutGroups.Batch040.certificate486).GlobalMatches MergedCutGroups.Batch040.certificate487 CountingCertificates.Batch016.certificate324 CutLabelCertificates.Entropy008.certificate163 CutLabelCertificates.Minority008.certificate162 := by decide +kernel
theorem exponentialBound162 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch040.certificate486).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate324).dm (WitnessCertificates.Batch016.certificate324).beta) ≤ (2*exp (-((CountingCertificates.Batch016.certificate324).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch040.certificate486).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch040.certificate487).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch016.certificate324).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch040.certificate486 MergedCutGroups.Batch040.certificate487 CountingCertificates.Batch016.certificate324 CutLabelCertificates.Entropy008.certificate163 CutLabelCertificates.Minority008.certificate162 matches162 rfl rfl
    MergedCutGroups.Batch040.numericValid486 MergedCutGroups.Batch040.numericValid487 MergedCutGroups.Batch040.cellsSound486 MergedCutGroups.Batch040.cellsSound487
    MergedCutGroups.Batch040.cellsNumeric486 MergedCutGroups.Batch040.cellsNumeric487 MergedCutGroups.Batch040.populationMatches486 MergedCutGroups.Batch040.populationMatches487
    PopulationCertificates.Batch016.valid324 PopulationCertificates.Batch016.sound324 WitnessCertificates.Batch016.valid324 WitnessCertificates.Batch016.sound324 CountingCertificates.Batch016.valid324 CountingCertificates.Batch016.sound324
    CutLabelCertificates.Entropy008.valid163 CutLabelCertificates.Minority008.valid162 CutLabelCertificates.Minority008.sound162 H st hI
theorem probabilityBound162 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch040.certificate486).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate324).dm (WitnessCertificates.Batch016.certificate324).beta) ≤ ((CutFailureCertificates.Budget016.certificate324).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound324 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate324).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch040.certificate486).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch040.certificate487).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch016.certificate324).omega:ℝ) ≤ ((CutFailureCertificates.Budget016.certificate324).bound:ℝ) at hb
  exact (exponentialBound162 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches163 : (MergedCutGroups.Batch040.certificate489).GlobalMatches MergedCutGroups.Batch040.certificate490 CountingCertificates.Batch016.certificate326 CutLabelCertificates.Entropy008.certificate164 CutLabelCertificates.Minority008.certificate163 := by decide +kernel
theorem exponentialBound163 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch040.certificate489).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate326).dm (WitnessCertificates.Batch016.certificate326).beta) ≤ (2*exp (-((CountingCertificates.Batch016.certificate326).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch040.certificate489).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch040.certificate490).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch016.certificate326).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch040.certificate489 MergedCutGroups.Batch040.certificate490 CountingCertificates.Batch016.certificate326 CutLabelCertificates.Entropy008.certificate164 CutLabelCertificates.Minority008.certificate163 matches163 rfl rfl
    MergedCutGroups.Batch040.numericValid489 MergedCutGroups.Batch040.numericValid490 MergedCutGroups.Batch040.cellsSound489 MergedCutGroups.Batch040.cellsSound490
    MergedCutGroups.Batch040.cellsNumeric489 MergedCutGroups.Batch040.cellsNumeric490 MergedCutGroups.Batch040.populationMatches489 MergedCutGroups.Batch040.populationMatches490
    PopulationCertificates.Batch016.valid326 PopulationCertificates.Batch016.sound326 WitnessCertificates.Batch016.valid326 WitnessCertificates.Batch016.sound326 CountingCertificates.Batch016.valid326 CountingCertificates.Batch016.sound326
    CutLabelCertificates.Entropy008.valid164 CutLabelCertificates.Minority008.valid163 CutLabelCertificates.Minority008.sound163 H st hI
theorem probabilityBound163 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch040.certificate489).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate326).dm (WitnessCertificates.Batch016.certificate326).beta) ≤ ((CutFailureCertificates.Budget016.certificate326).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound326 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate326).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch040.certificate489).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch040.certificate490).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch016.certificate326).omega:ℝ) ≤ ((CutFailureCertificates.Budget016.certificate326).bound:ℝ) at hb
  exact (exponentialBound163 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches164 : (MergedCutGroups.Batch041.certificate492).GlobalMatches MergedCutGroups.Batch041.certificate493 CountingCertificates.Batch016.certificate328 CutLabelCertificates.Entropy008.certificate165 CutLabelCertificates.Minority008.certificate164 := by decide +kernel
theorem exponentialBound164 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch041.certificate492).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate328).dm (WitnessCertificates.Batch016.certificate328).beta) ≤ (2*exp (-((CountingCertificates.Batch016.certificate328).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch041.certificate492).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch041.certificate493).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch016.certificate328).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch041.certificate492 MergedCutGroups.Batch041.certificate493 CountingCertificates.Batch016.certificate328 CutLabelCertificates.Entropy008.certificate165 CutLabelCertificates.Minority008.certificate164 matches164 rfl rfl
    MergedCutGroups.Batch041.numericValid492 MergedCutGroups.Batch041.numericValid493 MergedCutGroups.Batch041.cellsSound492 MergedCutGroups.Batch041.cellsSound493
    MergedCutGroups.Batch041.cellsNumeric492 MergedCutGroups.Batch041.cellsNumeric493 MergedCutGroups.Batch041.populationMatches492 MergedCutGroups.Batch041.populationMatches493
    PopulationCertificates.Batch016.valid328 PopulationCertificates.Batch016.sound328 WitnessCertificates.Batch016.valid328 WitnessCertificates.Batch016.sound328 CountingCertificates.Batch016.valid328 CountingCertificates.Batch016.sound328
    CutLabelCertificates.Entropy008.valid165 CutLabelCertificates.Minority008.valid164 CutLabelCertificates.Minority008.sound164 H st hI
theorem probabilityBound164 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch041.certificate492).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate328).dm (WitnessCertificates.Batch016.certificate328).beta) ≤ ((CutFailureCertificates.Budget016.certificate328).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound328 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate328).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch041.certificate492).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch041.certificate493).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch016.certificate328).omega:ℝ) ≤ ((CutFailureCertificates.Budget016.certificate328).bound:ℝ) at hb
  exact (exponentialBound164 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches165 : (MergedCutGroups.Batch041.certificate495).GlobalMatches MergedCutGroups.Batch041.certificate496 CountingCertificates.Batch016.certificate330 CutLabelCertificates.Entropy008.certificate166 CutLabelCertificates.Minority008.certificate165 := by decide +kernel
theorem exponentialBound165 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch041.certificate495).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate330).dm (WitnessCertificates.Batch016.certificate330).beta) ≤ (2*exp (-((CountingCertificates.Batch016.certificate330).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch041.certificate495).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch041.certificate496).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch016.certificate330).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch041.certificate495 MergedCutGroups.Batch041.certificate496 CountingCertificates.Batch016.certificate330 CutLabelCertificates.Entropy008.certificate166 CutLabelCertificates.Minority008.certificate165 matches165 rfl rfl
    MergedCutGroups.Batch041.numericValid495 MergedCutGroups.Batch041.numericValid496 MergedCutGroups.Batch041.cellsSound495 MergedCutGroups.Batch041.cellsSound496
    MergedCutGroups.Batch041.cellsNumeric495 MergedCutGroups.Batch041.cellsNumeric496 MergedCutGroups.Batch041.populationMatches495 MergedCutGroups.Batch041.populationMatches496
    PopulationCertificates.Batch016.valid330 PopulationCertificates.Batch016.sound330 WitnessCertificates.Batch016.valid330 WitnessCertificates.Batch016.sound330 CountingCertificates.Batch016.valid330 CountingCertificates.Batch016.sound330
    CutLabelCertificates.Entropy008.valid166 CutLabelCertificates.Minority008.valid165 CutLabelCertificates.Minority008.sound165 H st hI
theorem probabilityBound165 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch041.certificate495).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate330).dm (WitnessCertificates.Batch016.certificate330).beta) ≤ ((CutFailureCertificates.Budget016.certificate330).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound330 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate330).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch041.certificate495).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch041.certificate496).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch016.certificate330).omega:ℝ) ≤ ((CutFailureCertificates.Budget016.certificate330).bound:ℝ) at hb
  exact (exponentialBound165 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches166 : (MergedCutGroups.Batch041.certificate498).GlobalMatches MergedCutGroups.Batch041.certificate499 CountingCertificates.Batch016.certificate332 CutLabelCertificates.Entropy008.certificate167 CutLabelCertificates.Minority008.certificate166 := by decide +kernel
theorem exponentialBound166 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch041.certificate498).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate332).dm (WitnessCertificates.Batch016.certificate332).beta) ≤ (2*exp (-((CountingCertificates.Batch016.certificate332).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch041.certificate498).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch041.certificate499).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch016.certificate332).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch041.certificate498 MergedCutGroups.Batch041.certificate499 CountingCertificates.Batch016.certificate332 CutLabelCertificates.Entropy008.certificate167 CutLabelCertificates.Minority008.certificate166 matches166 rfl rfl
    MergedCutGroups.Batch041.numericValid498 MergedCutGroups.Batch041.numericValid499 MergedCutGroups.Batch041.cellsSound498 MergedCutGroups.Batch041.cellsSound499
    MergedCutGroups.Batch041.cellsNumeric498 MergedCutGroups.Batch041.cellsNumeric499 MergedCutGroups.Batch041.populationMatches498 MergedCutGroups.Batch041.populationMatches499
    PopulationCertificates.Batch016.valid332 PopulationCertificates.Batch016.sound332 WitnessCertificates.Batch016.valid332 WitnessCertificates.Batch016.sound332 CountingCertificates.Batch016.valid332 CountingCertificates.Batch016.sound332
    CutLabelCertificates.Entropy008.valid167 CutLabelCertificates.Minority008.valid166 CutLabelCertificates.Minority008.sound166 H st hI
theorem probabilityBound166 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch041.certificate498).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate332).dm (WitnessCertificates.Batch016.certificate332).beta) ≤ ((CutFailureCertificates.Budget016.certificate332).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound332 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate332).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch041.certificate498).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch041.certificate499).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch016.certificate332).omega:ℝ) ≤ ((CutFailureCertificates.Budget016.certificate332).bound:ℝ) at hb
  exact (exponentialBound166 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches167 : (MergedCutGroups.Batch041.certificate501).GlobalMatches MergedCutGroups.Batch041.certificate502 CountingCertificates.Batch016.certificate334 CutLabelCertificates.Entropy008.certificate168 CutLabelCertificates.Minority008.certificate167 := by decide +kernel
theorem exponentialBound167 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch041.certificate501).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate334).dm (WitnessCertificates.Batch016.certificate334).beta) ≤ (2*exp (-((CountingCertificates.Batch016.certificate334).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch041.certificate501).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch041.certificate502).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch016.certificate334).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch041.certificate501 MergedCutGroups.Batch041.certificate502 CountingCertificates.Batch016.certificate334 CutLabelCertificates.Entropy008.certificate168 CutLabelCertificates.Minority008.certificate167 matches167 rfl rfl
    MergedCutGroups.Batch041.numericValid501 MergedCutGroups.Batch041.numericValid502 MergedCutGroups.Batch041.cellsSound501 MergedCutGroups.Batch041.cellsSound502
    MergedCutGroups.Batch041.cellsNumeric501 MergedCutGroups.Batch041.cellsNumeric502 MergedCutGroups.Batch041.populationMatches501 MergedCutGroups.Batch041.populationMatches502
    PopulationCertificates.Batch016.valid334 PopulationCertificates.Batch016.sound334 WitnessCertificates.Batch016.valid334 WitnessCertificates.Batch016.sound334 CountingCertificates.Batch016.valid334 CountingCertificates.Batch016.sound334
    CutLabelCertificates.Entropy008.valid168 CutLabelCertificates.Minority008.valid167 CutLabelCertificates.Minority008.sound167 H st hI
theorem probabilityBound167 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch041.certificate501).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate334).dm (WitnessCertificates.Batch016.certificate334).beta) ≤ ((CutFailureCertificates.Budget016.certificate334).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound334 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate334).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch041.certificate501).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch041.certificate502).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch016.certificate334).omega:ℝ) ≤ ((CutFailureCertificates.Budget016.certificate334).bound:ℝ) at hb
  exact (exponentialBound167 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches168 : (MergedCutGroups.Batch042.certificate504).GlobalMatches MergedCutGroups.Batch042.certificate505 CountingCertificates.Batch016.certificate336 CutLabelCertificates.Entropy008.certificate169 CutLabelCertificates.Minority008.certificate168 := by decide +kernel
theorem exponentialBound168 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch042.certificate504).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate336).dm (WitnessCertificates.Batch016.certificate336).beta) ≤ (2*exp (-((CountingCertificates.Batch016.certificate336).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch042.certificate504).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch042.certificate505).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch016.certificate336).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch042.certificate504 MergedCutGroups.Batch042.certificate505 CountingCertificates.Batch016.certificate336 CutLabelCertificates.Entropy008.certificate169 CutLabelCertificates.Minority008.certificate168 matches168 rfl rfl
    MergedCutGroups.Batch042.numericValid504 MergedCutGroups.Batch042.numericValid505 MergedCutGroups.Batch042.cellsSound504 MergedCutGroups.Batch042.cellsSound505
    MergedCutGroups.Batch042.cellsNumeric504 MergedCutGroups.Batch042.cellsNumeric505 MergedCutGroups.Batch042.populationMatches504 MergedCutGroups.Batch042.populationMatches505
    PopulationCertificates.Batch016.valid336 PopulationCertificates.Batch016.sound336 WitnessCertificates.Batch016.valid336 WitnessCertificates.Batch016.sound336 CountingCertificates.Batch016.valid336 CountingCertificates.Batch016.sound336
    CutLabelCertificates.Entropy008.valid169 CutLabelCertificates.Minority008.valid168 CutLabelCertificates.Minority008.sound168 H st hI
theorem probabilityBound168 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch042.certificate504).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate336).dm (WitnessCertificates.Batch016.certificate336).beta) ≤ ((CutFailureCertificates.Budget016.certificate336).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound336 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate336).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch042.certificate504).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch042.certificate505).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch016.certificate336).omega:ℝ) ≤ ((CutFailureCertificates.Budget016.certificate336).bound:ℝ) at hb
  exact (exponentialBound168 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches169 : (MergedCutGroups.Batch042.certificate507).GlobalMatches MergedCutGroups.Batch042.certificate508 CountingCertificates.Batch016.certificate338 CutLabelCertificates.Entropy008.certificate170 CutLabelCertificates.Minority008.certificate169 := by decide +kernel
theorem exponentialBound169 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch042.certificate507).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate338).dm (WitnessCertificates.Batch016.certificate338).beta) ≤ (2*exp (-((CountingCertificates.Batch016.certificate338).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch042.certificate507).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch042.certificate508).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch016.certificate338).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch042.certificate507 MergedCutGroups.Batch042.certificate508 CountingCertificates.Batch016.certificate338 CutLabelCertificates.Entropy008.certificate170 CutLabelCertificates.Minority008.certificate169 matches169 rfl rfl
    MergedCutGroups.Batch042.numericValid507 MergedCutGroups.Batch042.numericValid508 MergedCutGroups.Batch042.cellsSound507 MergedCutGroups.Batch042.cellsSound508
    MergedCutGroups.Batch042.cellsNumeric507 MergedCutGroups.Batch042.cellsNumeric508 MergedCutGroups.Batch042.populationMatches507 MergedCutGroups.Batch042.populationMatches508
    PopulationCertificates.Batch016.valid338 PopulationCertificates.Batch016.sound338 WitnessCertificates.Batch016.valid338 WitnessCertificates.Batch016.sound338 CountingCertificates.Batch016.valid338 CountingCertificates.Batch016.sound338
    CutLabelCertificates.Entropy008.valid170 CutLabelCertificates.Minority008.valid169 CutLabelCertificates.Minority008.sound169 H st hI
theorem probabilityBound169 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch042.certificate507).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch016.certificate338).dm (WitnessCertificates.Batch016.certificate338).beta) ≤ ((CutFailureCertificates.Budget016.certificate338).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound338 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate338).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch042.certificate507).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch042.certificate508).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch016.certificate338).omega:ℝ) ≤ ((CutFailureCertificates.Budget016.certificate338).bound:ℝ) at hb
  exact (exponentialBound169 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches170 : (MergedCutGroups.Batch042.certificate510).GlobalMatches MergedCutGroups.Batch042.certificate511 CountingCertificates.Batch017.certificate340 CutLabelCertificates.Entropy008.certificate171 CutLabelCertificates.Minority008.certificate170 := by decide +kernel
theorem exponentialBound170 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch042.certificate510).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate340).dm (WitnessCertificates.Batch017.certificate340).beta) ≤ (2*exp (-((CountingCertificates.Batch017.certificate340).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch042.certificate510).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch042.certificate511).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch017.certificate340).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch042.certificate510 MergedCutGroups.Batch042.certificate511 CountingCertificates.Batch017.certificate340 CutLabelCertificates.Entropy008.certificate171 CutLabelCertificates.Minority008.certificate170 matches170 rfl rfl
    MergedCutGroups.Batch042.numericValid510 MergedCutGroups.Batch042.numericValid511 MergedCutGroups.Batch042.cellsSound510 MergedCutGroups.Batch042.cellsSound511
    MergedCutGroups.Batch042.cellsNumeric510 MergedCutGroups.Batch042.cellsNumeric511 MergedCutGroups.Batch042.populationMatches510 MergedCutGroups.Batch042.populationMatches511
    PopulationCertificates.Batch017.valid340 PopulationCertificates.Batch017.sound340 WitnessCertificates.Batch017.valid340 WitnessCertificates.Batch017.sound340 CountingCertificates.Batch017.valid340 CountingCertificates.Batch017.sound340
    CutLabelCertificates.Entropy008.valid171 CutLabelCertificates.Minority008.valid170 CutLabelCertificates.Minority008.sound170 H st hI
theorem probabilityBound170 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch042.certificate510).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate340).dm (WitnessCertificates.Batch017.certificate340).beta) ≤ ((CutFailureCertificates.Budget017.certificate340).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound340 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate340).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch042.certificate510).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch042.certificate511).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch017.certificate340).omega:ℝ) ≤ ((CutFailureCertificates.Budget017.certificate340).bound:ℝ) at hb
  exact (exponentialBound170 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches171 : (MergedCutGroups.Batch042.certificate513).GlobalMatches MergedCutGroups.Batch042.certificate514 CountingCertificates.Batch017.certificate342 CutLabelCertificates.Entropy008.certificate172 CutLabelCertificates.Minority008.certificate171 := by decide +kernel
theorem exponentialBound171 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch042.certificate513).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate342).dm (WitnessCertificates.Batch017.certificate342).beta) ≤ (2*exp (-((CountingCertificates.Batch017.certificate342).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch042.certificate513).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch042.certificate514).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch017.certificate342).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch042.certificate513 MergedCutGroups.Batch042.certificate514 CountingCertificates.Batch017.certificate342 CutLabelCertificates.Entropy008.certificate172 CutLabelCertificates.Minority008.certificate171 matches171 rfl rfl
    MergedCutGroups.Batch042.numericValid513 MergedCutGroups.Batch042.numericValid514 MergedCutGroups.Batch042.cellsSound513 MergedCutGroups.Batch042.cellsSound514
    MergedCutGroups.Batch042.cellsNumeric513 MergedCutGroups.Batch042.cellsNumeric514 MergedCutGroups.Batch042.populationMatches513 MergedCutGroups.Batch042.populationMatches514
    PopulationCertificates.Batch017.valid342 PopulationCertificates.Batch017.sound342 WitnessCertificates.Batch017.valid342 WitnessCertificates.Batch017.sound342 CountingCertificates.Batch017.valid342 CountingCertificates.Batch017.sound342
    CutLabelCertificates.Entropy008.valid172 CutLabelCertificates.Minority008.valid171 CutLabelCertificates.Minority008.sound171 H st hI
theorem probabilityBound171 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch042.certificate513).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate342).dm (WitnessCertificates.Batch017.certificate342).beta) ≤ ((CutFailureCertificates.Budget017.certificate342).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound342 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate342).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch042.certificate513).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch042.certificate514).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch017.certificate342).omega:ℝ) ≤ ((CutFailureCertificates.Budget017.certificate342).bound:ℝ) at hb
  exact (exponentialBound171 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches172 : (MergedCutGroups.Batch043.certificate516).GlobalMatches MergedCutGroups.Batch043.certificate517 CountingCertificates.Batch017.certificate344 CutLabelCertificates.Entropy008.certificate173 CutLabelCertificates.Minority008.certificate172 := by decide +kernel
theorem exponentialBound172 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch043.certificate516).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate344).dm (WitnessCertificates.Batch017.certificate344).beta) ≤ (2*exp (-((CountingCertificates.Batch017.certificate344).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch043.certificate516).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch043.certificate517).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch017.certificate344).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch043.certificate516 MergedCutGroups.Batch043.certificate517 CountingCertificates.Batch017.certificate344 CutLabelCertificates.Entropy008.certificate173 CutLabelCertificates.Minority008.certificate172 matches172 rfl rfl
    MergedCutGroups.Batch043.numericValid516 MergedCutGroups.Batch043.numericValid517 MergedCutGroups.Batch043.cellsSound516 MergedCutGroups.Batch043.cellsSound517
    MergedCutGroups.Batch043.cellsNumeric516 MergedCutGroups.Batch043.cellsNumeric517 MergedCutGroups.Batch043.populationMatches516 MergedCutGroups.Batch043.populationMatches517
    PopulationCertificates.Batch017.valid344 PopulationCertificates.Batch017.sound344 WitnessCertificates.Batch017.valid344 WitnessCertificates.Batch017.sound344 CountingCertificates.Batch017.valid344 CountingCertificates.Batch017.sound344
    CutLabelCertificates.Entropy008.valid173 CutLabelCertificates.Minority008.valid172 CutLabelCertificates.Minority008.sound172 H st hI
theorem probabilityBound172 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch043.certificate516).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate344).dm (WitnessCertificates.Batch017.certificate344).beta) ≤ ((CutFailureCertificates.Budget017.certificate344).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound344 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate344).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch043.certificate516).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch043.certificate517).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch017.certificate344).omega:ℝ) ≤ ((CutFailureCertificates.Budget017.certificate344).bound:ℝ) at hb
  exact (exponentialBound172 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches173 : (MergedCutGroups.Batch043.certificate519).GlobalMatches MergedCutGroups.Batch043.certificate520 CountingCertificates.Batch017.certificate346 CutLabelCertificates.Entropy008.certificate174 CutLabelCertificates.Minority008.certificate173 := by decide +kernel
theorem exponentialBound173 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch043.certificate519).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate346).dm (WitnessCertificates.Batch017.certificate346).beta) ≤ (2*exp (-((CountingCertificates.Batch017.certificate346).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch043.certificate519).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch043.certificate520).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch017.certificate346).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch043.certificate519 MergedCutGroups.Batch043.certificate520 CountingCertificates.Batch017.certificate346 CutLabelCertificates.Entropy008.certificate174 CutLabelCertificates.Minority008.certificate173 matches173 rfl rfl
    MergedCutGroups.Batch043.numericValid519 MergedCutGroups.Batch043.numericValid520 MergedCutGroups.Batch043.cellsSound519 MergedCutGroups.Batch043.cellsSound520
    MergedCutGroups.Batch043.cellsNumeric519 MergedCutGroups.Batch043.cellsNumeric520 MergedCutGroups.Batch043.populationMatches519 MergedCutGroups.Batch043.populationMatches520
    PopulationCertificates.Batch017.valid346 PopulationCertificates.Batch017.sound346 WitnessCertificates.Batch017.valid346 WitnessCertificates.Batch017.sound346 CountingCertificates.Batch017.valid346 CountingCertificates.Batch017.sound346
    CutLabelCertificates.Entropy008.valid174 CutLabelCertificates.Minority008.valid173 CutLabelCertificates.Minority008.sound173 H st hI
theorem probabilityBound173 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch043.certificate519).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate346).dm (WitnessCertificates.Batch017.certificate346).beta) ≤ ((CutFailureCertificates.Budget017.certificate346).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound346 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate346).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch043.certificate519).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch043.certificate520).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch017.certificate346).omega:ℝ) ≤ ((CutFailureCertificates.Budget017.certificate346).bound:ℝ) at hb
  exact (exponentialBound173 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches174 : (MergedCutGroups.Batch043.certificate522).GlobalMatches MergedCutGroups.Batch043.certificate523 CountingCertificates.Batch017.certificate348 CutLabelCertificates.Entropy008.certificate175 CutLabelCertificates.Minority008.certificate174 := by decide +kernel
theorem exponentialBound174 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch043.certificate522).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate348).dm (WitnessCertificates.Batch017.certificate348).beta) ≤ (2*exp (-((CountingCertificates.Batch017.certificate348).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch043.certificate522).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch043.certificate523).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch017.certificate348).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch043.certificate522 MergedCutGroups.Batch043.certificate523 CountingCertificates.Batch017.certificate348 CutLabelCertificates.Entropy008.certificate175 CutLabelCertificates.Minority008.certificate174 matches174 rfl rfl
    MergedCutGroups.Batch043.numericValid522 MergedCutGroups.Batch043.numericValid523 MergedCutGroups.Batch043.cellsSound522 MergedCutGroups.Batch043.cellsSound523
    MergedCutGroups.Batch043.cellsNumeric522 MergedCutGroups.Batch043.cellsNumeric523 MergedCutGroups.Batch043.populationMatches522 MergedCutGroups.Batch043.populationMatches523
    PopulationCertificates.Batch017.valid348 PopulationCertificates.Batch017.sound348 WitnessCertificates.Batch017.valid348 WitnessCertificates.Batch017.sound348 CountingCertificates.Batch017.valid348 CountingCertificates.Batch017.sound348
    CutLabelCertificates.Entropy008.valid175 CutLabelCertificates.Minority008.valid174 CutLabelCertificates.Minority008.sound174 H st hI
theorem probabilityBound174 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch043.certificate522).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate348).dm (WitnessCertificates.Batch017.certificate348).beta) ≤ ((CutFailureCertificates.Budget017.certificate348).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound348 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate348).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch043.certificate522).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch043.certificate523).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch017.certificate348).omega:ℝ) ≤ ((CutFailureCertificates.Budget017.certificate348).bound:ℝ) at hb
  exact (exponentialBound174 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches175 : (MergedCutGroups.Batch043.certificate525).GlobalMatches MergedCutGroups.Batch043.certificate526 CountingCertificates.Batch017.certificate350 CutLabelCertificates.Entropy008.certificate176 CutLabelCertificates.Minority008.certificate175 := by decide +kernel
theorem exponentialBound175 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch043.certificate525).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate350).dm (WitnessCertificates.Batch017.certificate350).beta) ≤ (2*exp (-((CountingCertificates.Batch017.certificate350).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch043.certificate525).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch043.certificate526).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch017.certificate350).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch043.certificate525 MergedCutGroups.Batch043.certificate526 CountingCertificates.Batch017.certificate350 CutLabelCertificates.Entropy008.certificate176 CutLabelCertificates.Minority008.certificate175 matches175 rfl rfl
    MergedCutGroups.Batch043.numericValid525 MergedCutGroups.Batch043.numericValid526 MergedCutGroups.Batch043.cellsSound525 MergedCutGroups.Batch043.cellsSound526
    MergedCutGroups.Batch043.cellsNumeric525 MergedCutGroups.Batch043.cellsNumeric526 MergedCutGroups.Batch043.populationMatches525 MergedCutGroups.Batch043.populationMatches526
    PopulationCertificates.Batch017.valid350 PopulationCertificates.Batch017.sound350 WitnessCertificates.Batch017.valid350 WitnessCertificates.Batch017.sound350 CountingCertificates.Batch017.valid350 CountingCertificates.Batch017.sound350
    CutLabelCertificates.Entropy008.valid176 CutLabelCertificates.Minority008.valid175 CutLabelCertificates.Minority008.sound175 H st hI
theorem probabilityBound175 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch043.certificate525).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate350).dm (WitnessCertificates.Batch017.certificate350).beta) ≤ ((CutFailureCertificates.Budget017.certificate350).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound350 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate350).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch043.certificate525).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch043.certificate526).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch017.certificate350).omega:ℝ) ≤ ((CutFailureCertificates.Budget017.certificate350).bound:ℝ) at hb
  exact (exponentialBound175 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches176 : (MergedCutGroups.Batch044.certificate528).GlobalMatches MergedCutGroups.Batch044.certificate529 CountingCertificates.Batch017.certificate352 CutLabelCertificates.Entropy008.certificate177 CutLabelCertificates.Minority008.certificate176 := by decide +kernel
theorem exponentialBound176 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch044.certificate528).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate352).dm (WitnessCertificates.Batch017.certificate352).beta) ≤ (2*exp (-((CountingCertificates.Batch017.certificate352).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch044.certificate528).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch044.certificate529).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch017.certificate352).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch044.certificate528 MergedCutGroups.Batch044.certificate529 CountingCertificates.Batch017.certificate352 CutLabelCertificates.Entropy008.certificate177 CutLabelCertificates.Minority008.certificate176 matches176 rfl rfl
    MergedCutGroups.Batch044.numericValid528 MergedCutGroups.Batch044.numericValid529 MergedCutGroups.Batch044.cellsSound528 MergedCutGroups.Batch044.cellsSound529
    MergedCutGroups.Batch044.cellsNumeric528 MergedCutGroups.Batch044.cellsNumeric529 MergedCutGroups.Batch044.populationMatches528 MergedCutGroups.Batch044.populationMatches529
    PopulationCertificates.Batch017.valid352 PopulationCertificates.Batch017.sound352 WitnessCertificates.Batch017.valid352 WitnessCertificates.Batch017.sound352 CountingCertificates.Batch017.valid352 CountingCertificates.Batch017.sound352
    CutLabelCertificates.Entropy008.valid177 CutLabelCertificates.Minority008.valid176 CutLabelCertificates.Minority008.sound176 H st hI
theorem probabilityBound176 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch044.certificate528).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate352).dm (WitnessCertificates.Batch017.certificate352).beta) ≤ ((CutFailureCertificates.Budget017.certificate352).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound352 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate352).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch044.certificate528).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch044.certificate529).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch017.certificate352).omega:ℝ) ≤ ((CutFailureCertificates.Budget017.certificate352).bound:ℝ) at hb
  exact (exponentialBound176 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches177 : (MergedCutGroups.Batch044.certificate531).GlobalMatches MergedCutGroups.Batch044.certificate532 CountingCertificates.Batch017.certificate354 CutLabelCertificates.Entropy008.certificate178 CutLabelCertificates.Minority008.certificate177 := by decide +kernel
theorem exponentialBound177 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch044.certificate531).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate354).dm (WitnessCertificates.Batch017.certificate354).beta) ≤ (2*exp (-((CountingCertificates.Batch017.certificate354).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch044.certificate531).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch044.certificate532).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch017.certificate354).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch044.certificate531 MergedCutGroups.Batch044.certificate532 CountingCertificates.Batch017.certificate354 CutLabelCertificates.Entropy008.certificate178 CutLabelCertificates.Minority008.certificate177 matches177 rfl rfl
    MergedCutGroups.Batch044.numericValid531 MergedCutGroups.Batch044.numericValid532 MergedCutGroups.Batch044.cellsSound531 MergedCutGroups.Batch044.cellsSound532
    MergedCutGroups.Batch044.cellsNumeric531 MergedCutGroups.Batch044.cellsNumeric532 MergedCutGroups.Batch044.populationMatches531 MergedCutGroups.Batch044.populationMatches532
    PopulationCertificates.Batch017.valid354 PopulationCertificates.Batch017.sound354 WitnessCertificates.Batch017.valid354 WitnessCertificates.Batch017.sound354 CountingCertificates.Batch017.valid354 CountingCertificates.Batch017.sound354
    CutLabelCertificates.Entropy008.valid178 CutLabelCertificates.Minority008.valid177 CutLabelCertificates.Minority008.sound177 H st hI
theorem probabilityBound177 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch044.certificate531).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate354).dm (WitnessCertificates.Batch017.certificate354).beta) ≤ ((CutFailureCertificates.Budget017.certificate354).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound354 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate354).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch044.certificate531).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch044.certificate532).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch017.certificate354).omega:ℝ) ≤ ((CutFailureCertificates.Budget017.certificate354).bound:ℝ) at hb
  exact (exponentialBound177 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches178 : (MergedCutGroups.Batch044.certificate534).GlobalMatches MergedCutGroups.Batch044.certificate535 CountingCertificates.Batch017.certificate356 CutLabelCertificates.Entropy008.certificate179 CutLabelCertificates.Minority008.certificate178 := by decide +kernel
theorem exponentialBound178 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch044.certificate534).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate356).dm (WitnessCertificates.Batch017.certificate356).beta) ≤ (2*exp (-((CountingCertificates.Batch017.certificate356).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch044.certificate534).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch044.certificate535).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch017.certificate356).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch044.certificate534 MergedCutGroups.Batch044.certificate535 CountingCertificates.Batch017.certificate356 CutLabelCertificates.Entropy008.certificate179 CutLabelCertificates.Minority008.certificate178 matches178 rfl rfl
    MergedCutGroups.Batch044.numericValid534 MergedCutGroups.Batch044.numericValid535 MergedCutGroups.Batch044.cellsSound534 MergedCutGroups.Batch044.cellsSound535
    MergedCutGroups.Batch044.cellsNumeric534 MergedCutGroups.Batch044.cellsNumeric535 MergedCutGroups.Batch044.populationMatches534 MergedCutGroups.Batch044.populationMatches535
    PopulationCertificates.Batch017.valid356 PopulationCertificates.Batch017.sound356 WitnessCertificates.Batch017.valid356 WitnessCertificates.Batch017.sound356 CountingCertificates.Batch017.valid356 CountingCertificates.Batch017.sound356
    CutLabelCertificates.Entropy008.valid179 CutLabelCertificates.Minority008.valid178 CutLabelCertificates.Minority008.sound178 H st hI
theorem probabilityBound178 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch044.certificate534).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate356).dm (WitnessCertificates.Batch017.certificate356).beta) ≤ ((CutFailureCertificates.Budget017.certificate356).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound356 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate356).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch044.certificate534).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch044.certificate535).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch017.certificate356).omega:ℝ) ≤ ((CutFailureCertificates.Budget017.certificate356).bound:ℝ) at hb
  exact (exponentialBound178 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches179 : (MergedCutGroups.Batch044.certificate537).GlobalMatches MergedCutGroups.Batch044.certificate538 CountingCertificates.Batch017.certificate358 CutLabelCertificates.Entropy009.certificate180 CutLabelCertificates.Minority008.certificate179 := by decide +kernel
theorem exponentialBound179 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch044.certificate537).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate358).dm (WitnessCertificates.Batch017.certificate358).beta) ≤ (2*exp (-((CountingCertificates.Batch017.certificate358).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch044.certificate537).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch044.certificate538).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch017.certificate358).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch044.certificate537 MergedCutGroups.Batch044.certificate538 CountingCertificates.Batch017.certificate358 CutLabelCertificates.Entropy009.certificate180 CutLabelCertificates.Minority008.certificate179 matches179 rfl rfl
    MergedCutGroups.Batch044.numericValid537 MergedCutGroups.Batch044.numericValid538 MergedCutGroups.Batch044.cellsSound537 MergedCutGroups.Batch044.cellsSound538
    MergedCutGroups.Batch044.cellsNumeric537 MergedCutGroups.Batch044.cellsNumeric538 MergedCutGroups.Batch044.populationMatches537 MergedCutGroups.Batch044.populationMatches538
    PopulationCertificates.Batch017.valid358 PopulationCertificates.Batch017.sound358 WitnessCertificates.Batch017.valid358 WitnessCertificates.Batch017.sound358 CountingCertificates.Batch017.valid358 CountingCertificates.Batch017.sound358
    CutLabelCertificates.Entropy009.valid180 CutLabelCertificates.Minority008.valid179 CutLabelCertificates.Minority008.sound179 H st hI
theorem probabilityBound179 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch044.certificate537).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch017.certificate358).dm (WitnessCertificates.Batch017.certificate358).beta) ≤ ((CutFailureCertificates.Budget017.certificate358).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound358 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate358).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch044.certificate537).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch044.certificate538).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch017.certificate358).omega:ℝ) ≤ ((CutFailureCertificates.Budget017.certificate358).bound:ℝ) at hb
  exact (exponentialBound179 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch008
