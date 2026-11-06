import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch012
import Cycle12.CountingCertificates.Batch013
import Cycle12.CutFailureCertificates.Budget012
import Cycle12.CutFailureCertificates.Budget013
import Cycle12.CutLabelCertificates.Entropy006
import Cycle12.CutLabelCertificates.Entropy007
import Cycle12.CutLabelCertificates.Minority006
import Cycle12.MergedCutGroups.Batch030
import Cycle12.MergedCutGroups.Batch031
import Cycle12.MergedCutGroups.Batch032
import Cycle12.MergedCutGroups.Batch033
import Cycle12.MergedCutGroups.Batch034
import Cycle12.PopulationCertificates.Batch012
import Cycle12.PopulationCertificates.Batch013
import Cycle12.WitnessCertificates.Batch012
import Cycle12.WitnessCertificates.Batch013

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch006
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches120 : (MergedCutGroups.Batch030.certificate360).GlobalMatches MergedCutGroups.Batch030.certificate361 CountingCertificates.Batch012.certificate240 CutLabelCertificates.Entropy006.certificate121 CutLabelCertificates.Minority006.certificate120 := by decide +kernel
theorem exponentialBound120 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch030.certificate360).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate240).dm (WitnessCertificates.Batch012.certificate240).beta) ≤ (2*exp (-((CountingCertificates.Batch012.certificate240).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch030.certificate360).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch030.certificate361).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch012.certificate240).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch030.certificate360 MergedCutGroups.Batch030.certificate361 CountingCertificates.Batch012.certificate240 CutLabelCertificates.Entropy006.certificate121 CutLabelCertificates.Minority006.certificate120 matches120 rfl rfl
    MergedCutGroups.Batch030.numericValid360 MergedCutGroups.Batch030.numericValid361 MergedCutGroups.Batch030.cellsSound360 MergedCutGroups.Batch030.cellsSound361
    MergedCutGroups.Batch030.cellsNumeric360 MergedCutGroups.Batch030.cellsNumeric361 MergedCutGroups.Batch030.populationMatches360 MergedCutGroups.Batch030.populationMatches361
    PopulationCertificates.Batch012.valid240 PopulationCertificates.Batch012.sound240 WitnessCertificates.Batch012.valid240 WitnessCertificates.Batch012.sound240 CountingCertificates.Batch012.valid240 CountingCertificates.Batch012.sound240
    CutLabelCertificates.Entropy006.valid121 CutLabelCertificates.Minority006.valid120 CutLabelCertificates.Minority006.sound120 H st hI
theorem probabilityBound120 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch030.certificate360).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate240).dm (WitnessCertificates.Batch012.certificate240).beta) ≤ ((CutFailureCertificates.Budget012.certificate240).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound240 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate240).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch030.certificate360).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch030.certificate361).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch012.certificate240).omega:ℝ) ≤ ((CutFailureCertificates.Budget012.certificate240).bound:ℝ) at hb
  exact (exponentialBound120 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches121 : (MergedCutGroups.Batch030.certificate363).GlobalMatches MergedCutGroups.Batch030.certificate364 CountingCertificates.Batch012.certificate242 CutLabelCertificates.Entropy006.certificate122 CutLabelCertificates.Minority006.certificate121 := by decide +kernel
theorem exponentialBound121 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch030.certificate363).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate242).dm (WitnessCertificates.Batch012.certificate242).beta) ≤ (2*exp (-((CountingCertificates.Batch012.certificate242).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch030.certificate363).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch030.certificate364).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch012.certificate242).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch030.certificate363 MergedCutGroups.Batch030.certificate364 CountingCertificates.Batch012.certificate242 CutLabelCertificates.Entropy006.certificate122 CutLabelCertificates.Minority006.certificate121 matches121 rfl rfl
    MergedCutGroups.Batch030.numericValid363 MergedCutGroups.Batch030.numericValid364 MergedCutGroups.Batch030.cellsSound363 MergedCutGroups.Batch030.cellsSound364
    MergedCutGroups.Batch030.cellsNumeric363 MergedCutGroups.Batch030.cellsNumeric364 MergedCutGroups.Batch030.populationMatches363 MergedCutGroups.Batch030.populationMatches364
    PopulationCertificates.Batch012.valid242 PopulationCertificates.Batch012.sound242 WitnessCertificates.Batch012.valid242 WitnessCertificates.Batch012.sound242 CountingCertificates.Batch012.valid242 CountingCertificates.Batch012.sound242
    CutLabelCertificates.Entropy006.valid122 CutLabelCertificates.Minority006.valid121 CutLabelCertificates.Minority006.sound121 H st hI
theorem probabilityBound121 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch030.certificate363).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate242).dm (WitnessCertificates.Batch012.certificate242).beta) ≤ ((CutFailureCertificates.Budget012.certificate242).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound242 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate242).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch030.certificate363).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch030.certificate364).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch012.certificate242).omega:ℝ) ≤ ((CutFailureCertificates.Budget012.certificate242).bound:ℝ) at hb
  exact (exponentialBound121 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches122 : (MergedCutGroups.Batch030.certificate366).GlobalMatches MergedCutGroups.Batch030.certificate367 CountingCertificates.Batch012.certificate244 CutLabelCertificates.Entropy006.certificate123 CutLabelCertificates.Minority006.certificate122 := by decide +kernel
theorem exponentialBound122 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch030.certificate366).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate244).dm (WitnessCertificates.Batch012.certificate244).beta) ≤ (2*exp (-((CountingCertificates.Batch012.certificate244).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch030.certificate366).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch030.certificate367).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch012.certificate244).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch030.certificate366 MergedCutGroups.Batch030.certificate367 CountingCertificates.Batch012.certificate244 CutLabelCertificates.Entropy006.certificate123 CutLabelCertificates.Minority006.certificate122 matches122 rfl rfl
    MergedCutGroups.Batch030.numericValid366 MergedCutGroups.Batch030.numericValid367 MergedCutGroups.Batch030.cellsSound366 MergedCutGroups.Batch030.cellsSound367
    MergedCutGroups.Batch030.cellsNumeric366 MergedCutGroups.Batch030.cellsNumeric367 MergedCutGroups.Batch030.populationMatches366 MergedCutGroups.Batch030.populationMatches367
    PopulationCertificates.Batch012.valid244 PopulationCertificates.Batch012.sound244 WitnessCertificates.Batch012.valid244 WitnessCertificates.Batch012.sound244 CountingCertificates.Batch012.valid244 CountingCertificates.Batch012.sound244
    CutLabelCertificates.Entropy006.valid123 CutLabelCertificates.Minority006.valid122 CutLabelCertificates.Minority006.sound122 H st hI
theorem probabilityBound122 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch030.certificate366).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate244).dm (WitnessCertificates.Batch012.certificate244).beta) ≤ ((CutFailureCertificates.Budget012.certificate244).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound244 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate244).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch030.certificate366).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch030.certificate367).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch012.certificate244).omega:ℝ) ≤ ((CutFailureCertificates.Budget012.certificate244).bound:ℝ) at hb
  exact (exponentialBound122 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches123 : (MergedCutGroups.Batch030.certificate369).GlobalMatches MergedCutGroups.Batch030.certificate370 CountingCertificates.Batch012.certificate246 CutLabelCertificates.Entropy006.certificate124 CutLabelCertificates.Minority006.certificate123 := by decide +kernel
theorem exponentialBound123 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch030.certificate369).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate246).dm (WitnessCertificates.Batch012.certificate246).beta) ≤ (2*exp (-((CountingCertificates.Batch012.certificate246).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch030.certificate369).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch030.certificate370).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch012.certificate246).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch030.certificate369 MergedCutGroups.Batch030.certificate370 CountingCertificates.Batch012.certificate246 CutLabelCertificates.Entropy006.certificate124 CutLabelCertificates.Minority006.certificate123 matches123 rfl rfl
    MergedCutGroups.Batch030.numericValid369 MergedCutGroups.Batch030.numericValid370 MergedCutGroups.Batch030.cellsSound369 MergedCutGroups.Batch030.cellsSound370
    MergedCutGroups.Batch030.cellsNumeric369 MergedCutGroups.Batch030.cellsNumeric370 MergedCutGroups.Batch030.populationMatches369 MergedCutGroups.Batch030.populationMatches370
    PopulationCertificates.Batch012.valid246 PopulationCertificates.Batch012.sound246 WitnessCertificates.Batch012.valid246 WitnessCertificates.Batch012.sound246 CountingCertificates.Batch012.valid246 CountingCertificates.Batch012.sound246
    CutLabelCertificates.Entropy006.valid124 CutLabelCertificates.Minority006.valid123 CutLabelCertificates.Minority006.sound123 H st hI
theorem probabilityBound123 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch030.certificate369).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate246).dm (WitnessCertificates.Batch012.certificate246).beta) ≤ ((CutFailureCertificates.Budget012.certificate246).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound246 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate246).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch030.certificate369).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch030.certificate370).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch012.certificate246).omega:ℝ) ≤ ((CutFailureCertificates.Budget012.certificate246).bound:ℝ) at hb
  exact (exponentialBound123 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches124 : (MergedCutGroups.Batch031.certificate372).GlobalMatches MergedCutGroups.Batch031.certificate373 CountingCertificates.Batch012.certificate248 CutLabelCertificates.Entropy006.certificate125 CutLabelCertificates.Minority006.certificate124 := by decide +kernel
theorem exponentialBound124 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch031.certificate372).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate248).dm (WitnessCertificates.Batch012.certificate248).beta) ≤ (2*exp (-((CountingCertificates.Batch012.certificate248).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch031.certificate372).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch031.certificate373).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch012.certificate248).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch031.certificate372 MergedCutGroups.Batch031.certificate373 CountingCertificates.Batch012.certificate248 CutLabelCertificates.Entropy006.certificate125 CutLabelCertificates.Minority006.certificate124 matches124 rfl rfl
    MergedCutGroups.Batch031.numericValid372 MergedCutGroups.Batch031.numericValid373 MergedCutGroups.Batch031.cellsSound372 MergedCutGroups.Batch031.cellsSound373
    MergedCutGroups.Batch031.cellsNumeric372 MergedCutGroups.Batch031.cellsNumeric373 MergedCutGroups.Batch031.populationMatches372 MergedCutGroups.Batch031.populationMatches373
    PopulationCertificates.Batch012.valid248 PopulationCertificates.Batch012.sound248 WitnessCertificates.Batch012.valid248 WitnessCertificates.Batch012.sound248 CountingCertificates.Batch012.valid248 CountingCertificates.Batch012.sound248
    CutLabelCertificates.Entropy006.valid125 CutLabelCertificates.Minority006.valid124 CutLabelCertificates.Minority006.sound124 H st hI
theorem probabilityBound124 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch031.certificate372).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate248).dm (WitnessCertificates.Batch012.certificate248).beta) ≤ ((CutFailureCertificates.Budget012.certificate248).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound248 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate248).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch031.certificate372).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch031.certificate373).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch012.certificate248).omega:ℝ) ≤ ((CutFailureCertificates.Budget012.certificate248).bound:ℝ) at hb
  exact (exponentialBound124 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches125 : (MergedCutGroups.Batch031.certificate375).GlobalMatches MergedCutGroups.Batch031.certificate376 CountingCertificates.Batch012.certificate250 CutLabelCertificates.Entropy006.certificate126 CutLabelCertificates.Minority006.certificate125 := by decide +kernel
theorem exponentialBound125 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch031.certificate375).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate250).dm (WitnessCertificates.Batch012.certificate250).beta) ≤ (2*exp (-((CountingCertificates.Batch012.certificate250).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch031.certificate375).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch031.certificate376).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch012.certificate250).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch031.certificate375 MergedCutGroups.Batch031.certificate376 CountingCertificates.Batch012.certificate250 CutLabelCertificates.Entropy006.certificate126 CutLabelCertificates.Minority006.certificate125 matches125 rfl rfl
    MergedCutGroups.Batch031.numericValid375 MergedCutGroups.Batch031.numericValid376 MergedCutGroups.Batch031.cellsSound375 MergedCutGroups.Batch031.cellsSound376
    MergedCutGroups.Batch031.cellsNumeric375 MergedCutGroups.Batch031.cellsNumeric376 MergedCutGroups.Batch031.populationMatches375 MergedCutGroups.Batch031.populationMatches376
    PopulationCertificates.Batch012.valid250 PopulationCertificates.Batch012.sound250 WitnessCertificates.Batch012.valid250 WitnessCertificates.Batch012.sound250 CountingCertificates.Batch012.valid250 CountingCertificates.Batch012.sound250
    CutLabelCertificates.Entropy006.valid126 CutLabelCertificates.Minority006.valid125 CutLabelCertificates.Minority006.sound125 H st hI
theorem probabilityBound125 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch031.certificate375).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate250).dm (WitnessCertificates.Batch012.certificate250).beta) ≤ ((CutFailureCertificates.Budget012.certificate250).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound250 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate250).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch031.certificate375).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch031.certificate376).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch012.certificate250).omega:ℝ) ≤ ((CutFailureCertificates.Budget012.certificate250).bound:ℝ) at hb
  exact (exponentialBound125 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches126 : (MergedCutGroups.Batch031.certificate378).GlobalMatches MergedCutGroups.Batch031.certificate379 CountingCertificates.Batch012.certificate252 CutLabelCertificates.Entropy006.certificate127 CutLabelCertificates.Minority006.certificate126 := by decide +kernel
theorem exponentialBound126 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch031.certificate378).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate252).dm (WitnessCertificates.Batch012.certificate252).beta) ≤ (2*exp (-((CountingCertificates.Batch012.certificate252).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch031.certificate378).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch031.certificate379).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch012.certificate252).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch031.certificate378 MergedCutGroups.Batch031.certificate379 CountingCertificates.Batch012.certificate252 CutLabelCertificates.Entropy006.certificate127 CutLabelCertificates.Minority006.certificate126 matches126 rfl rfl
    MergedCutGroups.Batch031.numericValid378 MergedCutGroups.Batch031.numericValid379 MergedCutGroups.Batch031.cellsSound378 MergedCutGroups.Batch031.cellsSound379
    MergedCutGroups.Batch031.cellsNumeric378 MergedCutGroups.Batch031.cellsNumeric379 MergedCutGroups.Batch031.populationMatches378 MergedCutGroups.Batch031.populationMatches379
    PopulationCertificates.Batch012.valid252 PopulationCertificates.Batch012.sound252 WitnessCertificates.Batch012.valid252 WitnessCertificates.Batch012.sound252 CountingCertificates.Batch012.valid252 CountingCertificates.Batch012.sound252
    CutLabelCertificates.Entropy006.valid127 CutLabelCertificates.Minority006.valid126 CutLabelCertificates.Minority006.sound126 H st hI
theorem probabilityBound126 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch031.certificate378).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate252).dm (WitnessCertificates.Batch012.certificate252).beta) ≤ ((CutFailureCertificates.Budget012.certificate252).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound252 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate252).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch031.certificate378).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch031.certificate379).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch012.certificate252).omega:ℝ) ≤ ((CutFailureCertificates.Budget012.certificate252).bound:ℝ) at hb
  exact (exponentialBound126 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches127 : (MergedCutGroups.Batch031.certificate381).GlobalMatches MergedCutGroups.Batch031.certificate382 CountingCertificates.Batch012.certificate254 CutLabelCertificates.Entropy006.certificate128 CutLabelCertificates.Minority006.certificate127 := by decide +kernel
theorem exponentialBound127 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch031.certificate381).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate254).dm (WitnessCertificates.Batch012.certificate254).beta) ≤ (2*exp (-((CountingCertificates.Batch012.certificate254).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch031.certificate381).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch031.certificate382).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch012.certificate254).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch031.certificate381 MergedCutGroups.Batch031.certificate382 CountingCertificates.Batch012.certificate254 CutLabelCertificates.Entropy006.certificate128 CutLabelCertificates.Minority006.certificate127 matches127 rfl rfl
    MergedCutGroups.Batch031.numericValid381 MergedCutGroups.Batch031.numericValid382 MergedCutGroups.Batch031.cellsSound381 MergedCutGroups.Batch031.cellsSound382
    MergedCutGroups.Batch031.cellsNumeric381 MergedCutGroups.Batch031.cellsNumeric382 MergedCutGroups.Batch031.populationMatches381 MergedCutGroups.Batch031.populationMatches382
    PopulationCertificates.Batch012.valid254 PopulationCertificates.Batch012.sound254 WitnessCertificates.Batch012.valid254 WitnessCertificates.Batch012.sound254 CountingCertificates.Batch012.valid254 CountingCertificates.Batch012.sound254
    CutLabelCertificates.Entropy006.valid128 CutLabelCertificates.Minority006.valid127 CutLabelCertificates.Minority006.sound127 H st hI
theorem probabilityBound127 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch031.certificate381).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate254).dm (WitnessCertificates.Batch012.certificate254).beta) ≤ ((CutFailureCertificates.Budget012.certificate254).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound254 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate254).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch031.certificate381).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch031.certificate382).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch012.certificate254).omega:ℝ) ≤ ((CutFailureCertificates.Budget012.certificate254).bound:ℝ) at hb
  exact (exponentialBound127 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches128 : (MergedCutGroups.Batch032.certificate384).GlobalMatches MergedCutGroups.Batch032.certificate385 CountingCertificates.Batch012.certificate256 CutLabelCertificates.Entropy006.certificate129 CutLabelCertificates.Minority006.certificate128 := by decide +kernel
theorem exponentialBound128 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch032.certificate384).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate256).dm (WitnessCertificates.Batch012.certificate256).beta) ≤ (2*exp (-((CountingCertificates.Batch012.certificate256).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch032.certificate384).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch032.certificate385).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch012.certificate256).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch032.certificate384 MergedCutGroups.Batch032.certificate385 CountingCertificates.Batch012.certificate256 CutLabelCertificates.Entropy006.certificate129 CutLabelCertificates.Minority006.certificate128 matches128 rfl rfl
    MergedCutGroups.Batch032.numericValid384 MergedCutGroups.Batch032.numericValid385 MergedCutGroups.Batch032.cellsSound384 MergedCutGroups.Batch032.cellsSound385
    MergedCutGroups.Batch032.cellsNumeric384 MergedCutGroups.Batch032.cellsNumeric385 MergedCutGroups.Batch032.populationMatches384 MergedCutGroups.Batch032.populationMatches385
    PopulationCertificates.Batch012.valid256 PopulationCertificates.Batch012.sound256 WitnessCertificates.Batch012.valid256 WitnessCertificates.Batch012.sound256 CountingCertificates.Batch012.valid256 CountingCertificates.Batch012.sound256
    CutLabelCertificates.Entropy006.valid129 CutLabelCertificates.Minority006.valid128 CutLabelCertificates.Minority006.sound128 H st hI
theorem probabilityBound128 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch032.certificate384).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate256).dm (WitnessCertificates.Batch012.certificate256).beta) ≤ ((CutFailureCertificates.Budget012.certificate256).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound256 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate256).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch032.certificate384).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch032.certificate385).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch012.certificate256).omega:ℝ) ≤ ((CutFailureCertificates.Budget012.certificate256).bound:ℝ) at hb
  exact (exponentialBound128 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches129 : (MergedCutGroups.Batch032.certificate387).GlobalMatches MergedCutGroups.Batch032.certificate388 CountingCertificates.Batch012.certificate258 CutLabelCertificates.Entropy006.certificate130 CutLabelCertificates.Minority006.certificate129 := by decide +kernel
theorem exponentialBound129 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch032.certificate387).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate258).dm (WitnessCertificates.Batch012.certificate258).beta) ≤ (2*exp (-((CountingCertificates.Batch012.certificate258).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch032.certificate387).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch032.certificate388).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch012.certificate258).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch032.certificate387 MergedCutGroups.Batch032.certificate388 CountingCertificates.Batch012.certificate258 CutLabelCertificates.Entropy006.certificate130 CutLabelCertificates.Minority006.certificate129 matches129 rfl rfl
    MergedCutGroups.Batch032.numericValid387 MergedCutGroups.Batch032.numericValid388 MergedCutGroups.Batch032.cellsSound387 MergedCutGroups.Batch032.cellsSound388
    MergedCutGroups.Batch032.cellsNumeric387 MergedCutGroups.Batch032.cellsNumeric388 MergedCutGroups.Batch032.populationMatches387 MergedCutGroups.Batch032.populationMatches388
    PopulationCertificates.Batch012.valid258 PopulationCertificates.Batch012.sound258 WitnessCertificates.Batch012.valid258 WitnessCertificates.Batch012.sound258 CountingCertificates.Batch012.valid258 CountingCertificates.Batch012.sound258
    CutLabelCertificates.Entropy006.valid130 CutLabelCertificates.Minority006.valid129 CutLabelCertificates.Minority006.sound129 H st hI
theorem probabilityBound129 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch032.certificate387).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch012.certificate258).dm (WitnessCertificates.Batch012.certificate258).beta) ≤ ((CutFailureCertificates.Budget012.certificate258).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound258 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate258).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch032.certificate387).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch032.certificate388).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch012.certificate258).omega:ℝ) ≤ ((CutFailureCertificates.Budget012.certificate258).bound:ℝ) at hb
  exact (exponentialBound129 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches130 : (MergedCutGroups.Batch032.certificate390).GlobalMatches MergedCutGroups.Batch032.certificate391 CountingCertificates.Batch013.certificate260 CutLabelCertificates.Entropy006.certificate131 CutLabelCertificates.Minority006.certificate130 := by decide +kernel
theorem exponentialBound130 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch032.certificate390).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate260).dm (WitnessCertificates.Batch013.certificate260).beta) ≤ (2*exp (-((CountingCertificates.Batch013.certificate260).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch032.certificate390).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch032.certificate391).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch013.certificate260).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch032.certificate390 MergedCutGroups.Batch032.certificate391 CountingCertificates.Batch013.certificate260 CutLabelCertificates.Entropy006.certificate131 CutLabelCertificates.Minority006.certificate130 matches130 rfl rfl
    MergedCutGroups.Batch032.numericValid390 MergedCutGroups.Batch032.numericValid391 MergedCutGroups.Batch032.cellsSound390 MergedCutGroups.Batch032.cellsSound391
    MergedCutGroups.Batch032.cellsNumeric390 MergedCutGroups.Batch032.cellsNumeric391 MergedCutGroups.Batch032.populationMatches390 MergedCutGroups.Batch032.populationMatches391
    PopulationCertificates.Batch013.valid260 PopulationCertificates.Batch013.sound260 WitnessCertificates.Batch013.valid260 WitnessCertificates.Batch013.sound260 CountingCertificates.Batch013.valid260 CountingCertificates.Batch013.sound260
    CutLabelCertificates.Entropy006.valid131 CutLabelCertificates.Minority006.valid130 CutLabelCertificates.Minority006.sound130 H st hI
theorem probabilityBound130 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch032.certificate390).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate260).dm (WitnessCertificates.Batch013.certificate260).beta) ≤ ((CutFailureCertificates.Budget013.certificate260).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound260 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate260).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch032.certificate390).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch032.certificate391).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch013.certificate260).omega:ℝ) ≤ ((CutFailureCertificates.Budget013.certificate260).bound:ℝ) at hb
  exact (exponentialBound130 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches131 : (MergedCutGroups.Batch032.certificate393).GlobalMatches MergedCutGroups.Batch032.certificate394 CountingCertificates.Batch013.certificate262 CutLabelCertificates.Entropy006.certificate132 CutLabelCertificates.Minority006.certificate131 := by decide +kernel
theorem exponentialBound131 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch032.certificate393).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate262).dm (WitnessCertificates.Batch013.certificate262).beta) ≤ (2*exp (-((CountingCertificates.Batch013.certificate262).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch032.certificate393).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch032.certificate394).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch013.certificate262).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch032.certificate393 MergedCutGroups.Batch032.certificate394 CountingCertificates.Batch013.certificate262 CutLabelCertificates.Entropy006.certificate132 CutLabelCertificates.Minority006.certificate131 matches131 rfl rfl
    MergedCutGroups.Batch032.numericValid393 MergedCutGroups.Batch032.numericValid394 MergedCutGroups.Batch032.cellsSound393 MergedCutGroups.Batch032.cellsSound394
    MergedCutGroups.Batch032.cellsNumeric393 MergedCutGroups.Batch032.cellsNumeric394 MergedCutGroups.Batch032.populationMatches393 MergedCutGroups.Batch032.populationMatches394
    PopulationCertificates.Batch013.valid262 PopulationCertificates.Batch013.sound262 WitnessCertificates.Batch013.valid262 WitnessCertificates.Batch013.sound262 CountingCertificates.Batch013.valid262 CountingCertificates.Batch013.sound262
    CutLabelCertificates.Entropy006.valid132 CutLabelCertificates.Minority006.valid131 CutLabelCertificates.Minority006.sound131 H st hI
theorem probabilityBound131 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch032.certificate393).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate262).dm (WitnessCertificates.Batch013.certificate262).beta) ≤ ((CutFailureCertificates.Budget013.certificate262).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound262 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate262).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch032.certificate393).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch032.certificate394).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch013.certificate262).omega:ℝ) ≤ ((CutFailureCertificates.Budget013.certificate262).bound:ℝ) at hb
  exact (exponentialBound131 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches132 : (MergedCutGroups.Batch033.certificate396).GlobalMatches MergedCutGroups.Batch033.certificate397 CountingCertificates.Batch013.certificate264 CutLabelCertificates.Entropy006.certificate133 CutLabelCertificates.Minority006.certificate132 := by decide +kernel
theorem exponentialBound132 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch033.certificate396).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate264).dm (WitnessCertificates.Batch013.certificate264).beta) ≤ (2*exp (-((CountingCertificates.Batch013.certificate264).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch033.certificate396).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch033.certificate397).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch013.certificate264).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch033.certificate396 MergedCutGroups.Batch033.certificate397 CountingCertificates.Batch013.certificate264 CutLabelCertificates.Entropy006.certificate133 CutLabelCertificates.Minority006.certificate132 matches132 rfl rfl
    MergedCutGroups.Batch033.numericValid396 MergedCutGroups.Batch033.numericValid397 MergedCutGroups.Batch033.cellsSound396 MergedCutGroups.Batch033.cellsSound397
    MergedCutGroups.Batch033.cellsNumeric396 MergedCutGroups.Batch033.cellsNumeric397 MergedCutGroups.Batch033.populationMatches396 MergedCutGroups.Batch033.populationMatches397
    PopulationCertificates.Batch013.valid264 PopulationCertificates.Batch013.sound264 WitnessCertificates.Batch013.valid264 WitnessCertificates.Batch013.sound264 CountingCertificates.Batch013.valid264 CountingCertificates.Batch013.sound264
    CutLabelCertificates.Entropy006.valid133 CutLabelCertificates.Minority006.valid132 CutLabelCertificates.Minority006.sound132 H st hI
theorem probabilityBound132 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch033.certificate396).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate264).dm (WitnessCertificates.Batch013.certificate264).beta) ≤ ((CutFailureCertificates.Budget013.certificate264).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound264 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate264).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch033.certificate396).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch033.certificate397).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch013.certificate264).omega:ℝ) ≤ ((CutFailureCertificates.Budget013.certificate264).bound:ℝ) at hb
  exact (exponentialBound132 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches133 : (MergedCutGroups.Batch033.certificate399).GlobalMatches MergedCutGroups.Batch033.certificate400 CountingCertificates.Batch013.certificate266 CutLabelCertificates.Entropy006.certificate134 CutLabelCertificates.Minority006.certificate133 := by decide +kernel
theorem exponentialBound133 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch033.certificate399).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate266).dm (WitnessCertificates.Batch013.certificate266).beta) ≤ (2*exp (-((CountingCertificates.Batch013.certificate266).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch033.certificate399).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch033.certificate400).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch013.certificate266).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch033.certificate399 MergedCutGroups.Batch033.certificate400 CountingCertificates.Batch013.certificate266 CutLabelCertificates.Entropy006.certificate134 CutLabelCertificates.Minority006.certificate133 matches133 rfl rfl
    MergedCutGroups.Batch033.numericValid399 MergedCutGroups.Batch033.numericValid400 MergedCutGroups.Batch033.cellsSound399 MergedCutGroups.Batch033.cellsSound400
    MergedCutGroups.Batch033.cellsNumeric399 MergedCutGroups.Batch033.cellsNumeric400 MergedCutGroups.Batch033.populationMatches399 MergedCutGroups.Batch033.populationMatches400
    PopulationCertificates.Batch013.valid266 PopulationCertificates.Batch013.sound266 WitnessCertificates.Batch013.valid266 WitnessCertificates.Batch013.sound266 CountingCertificates.Batch013.valid266 CountingCertificates.Batch013.sound266
    CutLabelCertificates.Entropy006.valid134 CutLabelCertificates.Minority006.valid133 CutLabelCertificates.Minority006.sound133 H st hI
theorem probabilityBound133 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch033.certificate399).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate266).dm (WitnessCertificates.Batch013.certificate266).beta) ≤ ((CutFailureCertificates.Budget013.certificate266).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound266 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate266).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch033.certificate399).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch033.certificate400).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch013.certificate266).omega:ℝ) ≤ ((CutFailureCertificates.Budget013.certificate266).bound:ℝ) at hb
  exact (exponentialBound133 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches134 : (MergedCutGroups.Batch033.certificate402).GlobalMatches MergedCutGroups.Batch033.certificate403 CountingCertificates.Batch013.certificate268 CutLabelCertificates.Entropy006.certificate135 CutLabelCertificates.Minority006.certificate134 := by decide +kernel
theorem exponentialBound134 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch033.certificate402).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate268).dm (WitnessCertificates.Batch013.certificate268).beta) ≤ (2*exp (-((CountingCertificates.Batch013.certificate268).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch033.certificate402).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch033.certificate403).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch013.certificate268).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch033.certificate402 MergedCutGroups.Batch033.certificate403 CountingCertificates.Batch013.certificate268 CutLabelCertificates.Entropy006.certificate135 CutLabelCertificates.Minority006.certificate134 matches134 rfl rfl
    MergedCutGroups.Batch033.numericValid402 MergedCutGroups.Batch033.numericValid403 MergedCutGroups.Batch033.cellsSound402 MergedCutGroups.Batch033.cellsSound403
    MergedCutGroups.Batch033.cellsNumeric402 MergedCutGroups.Batch033.cellsNumeric403 MergedCutGroups.Batch033.populationMatches402 MergedCutGroups.Batch033.populationMatches403
    PopulationCertificates.Batch013.valid268 PopulationCertificates.Batch013.sound268 WitnessCertificates.Batch013.valid268 WitnessCertificates.Batch013.sound268 CountingCertificates.Batch013.valid268 CountingCertificates.Batch013.sound268
    CutLabelCertificates.Entropy006.valid135 CutLabelCertificates.Minority006.valid134 CutLabelCertificates.Minority006.sound134 H st hI
theorem probabilityBound134 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch033.certificate402).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate268).dm (WitnessCertificates.Batch013.certificate268).beta) ≤ ((CutFailureCertificates.Budget013.certificate268).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound268 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate268).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch033.certificate402).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch033.certificate403).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch013.certificate268).omega:ℝ) ≤ ((CutFailureCertificates.Budget013.certificate268).bound:ℝ) at hb
  exact (exponentialBound134 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches135 : (MergedCutGroups.Batch033.certificate405).GlobalMatches MergedCutGroups.Batch033.certificate406 CountingCertificates.Batch013.certificate270 CutLabelCertificates.Entropy006.certificate136 CutLabelCertificates.Minority006.certificate135 := by decide +kernel
theorem exponentialBound135 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch033.certificate405).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate270).dm (WitnessCertificates.Batch013.certificate270).beta) ≤ (2*exp (-((CountingCertificates.Batch013.certificate270).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch033.certificate405).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch033.certificate406).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch013.certificate270).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch033.certificate405 MergedCutGroups.Batch033.certificate406 CountingCertificates.Batch013.certificate270 CutLabelCertificates.Entropy006.certificate136 CutLabelCertificates.Minority006.certificate135 matches135 rfl rfl
    MergedCutGroups.Batch033.numericValid405 MergedCutGroups.Batch033.numericValid406 MergedCutGroups.Batch033.cellsSound405 MergedCutGroups.Batch033.cellsSound406
    MergedCutGroups.Batch033.cellsNumeric405 MergedCutGroups.Batch033.cellsNumeric406 MergedCutGroups.Batch033.populationMatches405 MergedCutGroups.Batch033.populationMatches406
    PopulationCertificates.Batch013.valid270 PopulationCertificates.Batch013.sound270 WitnessCertificates.Batch013.valid270 WitnessCertificates.Batch013.sound270 CountingCertificates.Batch013.valid270 CountingCertificates.Batch013.sound270
    CutLabelCertificates.Entropy006.valid136 CutLabelCertificates.Minority006.valid135 CutLabelCertificates.Minority006.sound135 H st hI
theorem probabilityBound135 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch033.certificate405).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate270).dm (WitnessCertificates.Batch013.certificate270).beta) ≤ ((CutFailureCertificates.Budget013.certificate270).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound270 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate270).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch033.certificate405).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch033.certificate406).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch013.certificate270).omega:ℝ) ≤ ((CutFailureCertificates.Budget013.certificate270).bound:ℝ) at hb
  exact (exponentialBound135 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches136 : (MergedCutGroups.Batch034.certificate408).GlobalMatches MergedCutGroups.Batch034.certificate409 CountingCertificates.Batch013.certificate272 CutLabelCertificates.Entropy006.certificate137 CutLabelCertificates.Minority006.certificate136 := by decide +kernel
theorem exponentialBound136 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch034.certificate408).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate272).dm (WitnessCertificates.Batch013.certificate272).beta) ≤ (2*exp (-((CountingCertificates.Batch013.certificate272).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch034.certificate408).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch034.certificate409).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch013.certificate272).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch034.certificate408 MergedCutGroups.Batch034.certificate409 CountingCertificates.Batch013.certificate272 CutLabelCertificates.Entropy006.certificate137 CutLabelCertificates.Minority006.certificate136 matches136 rfl rfl
    MergedCutGroups.Batch034.numericValid408 MergedCutGroups.Batch034.numericValid409 MergedCutGroups.Batch034.cellsSound408 MergedCutGroups.Batch034.cellsSound409
    MergedCutGroups.Batch034.cellsNumeric408 MergedCutGroups.Batch034.cellsNumeric409 MergedCutGroups.Batch034.populationMatches408 MergedCutGroups.Batch034.populationMatches409
    PopulationCertificates.Batch013.valid272 PopulationCertificates.Batch013.sound272 WitnessCertificates.Batch013.valid272 WitnessCertificates.Batch013.sound272 CountingCertificates.Batch013.valid272 CountingCertificates.Batch013.sound272
    CutLabelCertificates.Entropy006.valid137 CutLabelCertificates.Minority006.valid136 CutLabelCertificates.Minority006.sound136 H st hI
theorem probabilityBound136 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch034.certificate408).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate272).dm (WitnessCertificates.Batch013.certificate272).beta) ≤ ((CutFailureCertificates.Budget013.certificate272).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound272 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate272).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch034.certificate408).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch034.certificate409).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch013.certificate272).omega:ℝ) ≤ ((CutFailureCertificates.Budget013.certificate272).bound:ℝ) at hb
  exact (exponentialBound136 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches137 : (MergedCutGroups.Batch034.certificate411).GlobalMatches MergedCutGroups.Batch034.certificate412 CountingCertificates.Batch013.certificate274 CutLabelCertificates.Entropy006.certificate138 CutLabelCertificates.Minority006.certificate137 := by decide +kernel
theorem exponentialBound137 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch034.certificate411).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate274).dm (WitnessCertificates.Batch013.certificate274).beta) ≤ (2*exp (-((CountingCertificates.Batch013.certificate274).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch034.certificate411).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch034.certificate412).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch013.certificate274).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch034.certificate411 MergedCutGroups.Batch034.certificate412 CountingCertificates.Batch013.certificate274 CutLabelCertificates.Entropy006.certificate138 CutLabelCertificates.Minority006.certificate137 matches137 rfl rfl
    MergedCutGroups.Batch034.numericValid411 MergedCutGroups.Batch034.numericValid412 MergedCutGroups.Batch034.cellsSound411 MergedCutGroups.Batch034.cellsSound412
    MergedCutGroups.Batch034.cellsNumeric411 MergedCutGroups.Batch034.cellsNumeric412 MergedCutGroups.Batch034.populationMatches411 MergedCutGroups.Batch034.populationMatches412
    PopulationCertificates.Batch013.valid274 PopulationCertificates.Batch013.sound274 WitnessCertificates.Batch013.valid274 WitnessCertificates.Batch013.sound274 CountingCertificates.Batch013.valid274 CountingCertificates.Batch013.sound274
    CutLabelCertificates.Entropy006.valid138 CutLabelCertificates.Minority006.valid137 CutLabelCertificates.Minority006.sound137 H st hI
theorem probabilityBound137 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch034.certificate411).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate274).dm (WitnessCertificates.Batch013.certificate274).beta) ≤ ((CutFailureCertificates.Budget013.certificate274).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound274 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate274).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch034.certificate411).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch034.certificate412).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch013.certificate274).omega:ℝ) ≤ ((CutFailureCertificates.Budget013.certificate274).bound:ℝ) at hb
  exact (exponentialBound137 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches138 : (MergedCutGroups.Batch034.certificate414).GlobalMatches MergedCutGroups.Batch034.certificate415 CountingCertificates.Batch013.certificate276 CutLabelCertificates.Entropy006.certificate139 CutLabelCertificates.Minority006.certificate138 := by decide +kernel
theorem exponentialBound138 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch034.certificate414).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate276).dm (WitnessCertificates.Batch013.certificate276).beta) ≤ (2*exp (-((CountingCertificates.Batch013.certificate276).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch034.certificate414).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch034.certificate415).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch013.certificate276).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch034.certificate414 MergedCutGroups.Batch034.certificate415 CountingCertificates.Batch013.certificate276 CutLabelCertificates.Entropy006.certificate139 CutLabelCertificates.Minority006.certificate138 matches138 rfl rfl
    MergedCutGroups.Batch034.numericValid414 MergedCutGroups.Batch034.numericValid415 MergedCutGroups.Batch034.cellsSound414 MergedCutGroups.Batch034.cellsSound415
    MergedCutGroups.Batch034.cellsNumeric414 MergedCutGroups.Batch034.cellsNumeric415 MergedCutGroups.Batch034.populationMatches414 MergedCutGroups.Batch034.populationMatches415
    PopulationCertificates.Batch013.valid276 PopulationCertificates.Batch013.sound276 WitnessCertificates.Batch013.valid276 WitnessCertificates.Batch013.sound276 CountingCertificates.Batch013.valid276 CountingCertificates.Batch013.sound276
    CutLabelCertificates.Entropy006.valid139 CutLabelCertificates.Minority006.valid138 CutLabelCertificates.Minority006.sound138 H st hI
theorem probabilityBound138 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch034.certificate414).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate276).dm (WitnessCertificates.Batch013.certificate276).beta) ≤ ((CutFailureCertificates.Budget013.certificate276).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound276 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate276).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch034.certificate414).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch034.certificate415).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch013.certificate276).omega:ℝ) ≤ ((CutFailureCertificates.Budget013.certificate276).bound:ℝ) at hb
  exact (exponentialBound138 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches139 : (MergedCutGroups.Batch034.certificate417).GlobalMatches MergedCutGroups.Batch034.certificate418 CountingCertificates.Batch013.certificate278 CutLabelCertificates.Entropy007.certificate140 CutLabelCertificates.Minority006.certificate139 := by decide +kernel
theorem exponentialBound139 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch034.certificate417).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate278).dm (WitnessCertificates.Batch013.certificate278).beta) ≤ (2*exp (-((CountingCertificates.Batch013.certificate278).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch034.certificate417).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch034.certificate418).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch013.certificate278).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch034.certificate417 MergedCutGroups.Batch034.certificate418 CountingCertificates.Batch013.certificate278 CutLabelCertificates.Entropy007.certificate140 CutLabelCertificates.Minority006.certificate139 matches139 rfl rfl
    MergedCutGroups.Batch034.numericValid417 MergedCutGroups.Batch034.numericValid418 MergedCutGroups.Batch034.cellsSound417 MergedCutGroups.Batch034.cellsSound418
    MergedCutGroups.Batch034.cellsNumeric417 MergedCutGroups.Batch034.cellsNumeric418 MergedCutGroups.Batch034.populationMatches417 MergedCutGroups.Batch034.populationMatches418
    PopulationCertificates.Batch013.valid278 PopulationCertificates.Batch013.sound278 WitnessCertificates.Batch013.valid278 WitnessCertificates.Batch013.sound278 CountingCertificates.Batch013.valid278 CountingCertificates.Batch013.sound278
    CutLabelCertificates.Entropy007.valid140 CutLabelCertificates.Minority006.valid139 CutLabelCertificates.Minority006.sound139 H st hI
theorem probabilityBound139 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch034.certificate417).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch013.certificate278).dm (WitnessCertificates.Batch013.certificate278).beta) ≤ ((CutFailureCertificates.Budget013.certificate278).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound278 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate278).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch034.certificate417).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch034.certificate418).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch013.certificate278).omega:ℝ) ≤ ((CutFailureCertificates.Budget013.certificate278).bound:ℝ) at hb
  exact (exponentialBound139 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch006
