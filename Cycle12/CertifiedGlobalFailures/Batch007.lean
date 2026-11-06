import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch014
import Cycle12.CountingCertificates.Batch015
import Cycle12.CutFailureCertificates.Budget014
import Cycle12.CutFailureCertificates.Budget015
import Cycle12.CutLabelCertificates.Entropy007
import Cycle12.CutLabelCertificates.Entropy008
import Cycle12.CutLabelCertificates.Minority007
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

namespace Cycle12.CertifiedGlobalFailures.Batch007
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches140 : (MergedCutGroups.Batch035.certificate420).GlobalMatches MergedCutGroups.Batch035.certificate421 CountingCertificates.Batch014.certificate280 CutLabelCertificates.Entropy007.certificate141 CutLabelCertificates.Minority007.certificate140 := by decide +kernel
theorem exponentialBound140 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch035.certificate420).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate280).dm (WitnessCertificates.Batch014.certificate280).beta) ≤ (2*exp (-((CountingCertificates.Batch014.certificate280).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch035.certificate420).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch035.certificate421).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch014.certificate280).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch035.certificate420 MergedCutGroups.Batch035.certificate421 CountingCertificates.Batch014.certificate280 CutLabelCertificates.Entropy007.certificate141 CutLabelCertificates.Minority007.certificate140 matches140 rfl rfl
    MergedCutGroups.Batch035.numericValid420 MergedCutGroups.Batch035.numericValid421 MergedCutGroups.Batch035.cellsSound420 MergedCutGroups.Batch035.cellsSound421
    MergedCutGroups.Batch035.cellsNumeric420 MergedCutGroups.Batch035.cellsNumeric421 MergedCutGroups.Batch035.populationMatches420 MergedCutGroups.Batch035.populationMatches421
    PopulationCertificates.Batch014.valid280 PopulationCertificates.Batch014.sound280 WitnessCertificates.Batch014.valid280 WitnessCertificates.Batch014.sound280 CountingCertificates.Batch014.valid280 CountingCertificates.Batch014.sound280
    CutLabelCertificates.Entropy007.valid141 CutLabelCertificates.Minority007.valid140 CutLabelCertificates.Minority007.sound140 H st hI
theorem probabilityBound140 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch035.certificate420).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate280).dm (WitnessCertificates.Batch014.certificate280).beta) ≤ ((CutFailureCertificates.Budget014.certificate280).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound280 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate280).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch035.certificate420).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch035.certificate421).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch014.certificate280).omega:ℝ) ≤ ((CutFailureCertificates.Budget014.certificate280).bound:ℝ) at hb
  exact (exponentialBound140 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches141 : (MergedCutGroups.Batch035.certificate423).GlobalMatches MergedCutGroups.Batch035.certificate424 CountingCertificates.Batch014.certificate282 CutLabelCertificates.Entropy007.certificate142 CutLabelCertificates.Minority007.certificate141 := by decide +kernel
theorem exponentialBound141 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch035.certificate423).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate282).dm (WitnessCertificates.Batch014.certificate282).beta) ≤ (2*exp (-((CountingCertificates.Batch014.certificate282).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch035.certificate423).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch035.certificate424).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch014.certificate282).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch035.certificate423 MergedCutGroups.Batch035.certificate424 CountingCertificates.Batch014.certificate282 CutLabelCertificates.Entropy007.certificate142 CutLabelCertificates.Minority007.certificate141 matches141 rfl rfl
    MergedCutGroups.Batch035.numericValid423 MergedCutGroups.Batch035.numericValid424 MergedCutGroups.Batch035.cellsSound423 MergedCutGroups.Batch035.cellsSound424
    MergedCutGroups.Batch035.cellsNumeric423 MergedCutGroups.Batch035.cellsNumeric424 MergedCutGroups.Batch035.populationMatches423 MergedCutGroups.Batch035.populationMatches424
    PopulationCertificates.Batch014.valid282 PopulationCertificates.Batch014.sound282 WitnessCertificates.Batch014.valid282 WitnessCertificates.Batch014.sound282 CountingCertificates.Batch014.valid282 CountingCertificates.Batch014.sound282
    CutLabelCertificates.Entropy007.valid142 CutLabelCertificates.Minority007.valid141 CutLabelCertificates.Minority007.sound141 H st hI
theorem probabilityBound141 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch035.certificate423).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate282).dm (WitnessCertificates.Batch014.certificate282).beta) ≤ ((CutFailureCertificates.Budget014.certificate282).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound282 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate282).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch035.certificate423).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch035.certificate424).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch014.certificate282).omega:ℝ) ≤ ((CutFailureCertificates.Budget014.certificate282).bound:ℝ) at hb
  exact (exponentialBound141 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches142 : (MergedCutGroups.Batch035.certificate426).GlobalMatches MergedCutGroups.Batch035.certificate427 CountingCertificates.Batch014.certificate284 CutLabelCertificates.Entropy007.certificate143 CutLabelCertificates.Minority007.certificate142 := by decide +kernel
theorem exponentialBound142 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch035.certificate426).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate284).dm (WitnessCertificates.Batch014.certificate284).beta) ≤ (2*exp (-((CountingCertificates.Batch014.certificate284).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch035.certificate426).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch035.certificate427).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch014.certificate284).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch035.certificate426 MergedCutGroups.Batch035.certificate427 CountingCertificates.Batch014.certificate284 CutLabelCertificates.Entropy007.certificate143 CutLabelCertificates.Minority007.certificate142 matches142 rfl rfl
    MergedCutGroups.Batch035.numericValid426 MergedCutGroups.Batch035.numericValid427 MergedCutGroups.Batch035.cellsSound426 MergedCutGroups.Batch035.cellsSound427
    MergedCutGroups.Batch035.cellsNumeric426 MergedCutGroups.Batch035.cellsNumeric427 MergedCutGroups.Batch035.populationMatches426 MergedCutGroups.Batch035.populationMatches427
    PopulationCertificates.Batch014.valid284 PopulationCertificates.Batch014.sound284 WitnessCertificates.Batch014.valid284 WitnessCertificates.Batch014.sound284 CountingCertificates.Batch014.valid284 CountingCertificates.Batch014.sound284
    CutLabelCertificates.Entropy007.valid143 CutLabelCertificates.Minority007.valid142 CutLabelCertificates.Minority007.sound142 H st hI
theorem probabilityBound142 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch035.certificate426).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate284).dm (WitnessCertificates.Batch014.certificate284).beta) ≤ ((CutFailureCertificates.Budget014.certificate284).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound284 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate284).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch035.certificate426).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch035.certificate427).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch014.certificate284).omega:ℝ) ≤ ((CutFailureCertificates.Budget014.certificate284).bound:ℝ) at hb
  exact (exponentialBound142 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches143 : (MergedCutGroups.Batch035.certificate429).GlobalMatches MergedCutGroups.Batch035.certificate430 CountingCertificates.Batch014.certificate286 CutLabelCertificates.Entropy007.certificate144 CutLabelCertificates.Minority007.certificate143 := by decide +kernel
theorem exponentialBound143 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch035.certificate429).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate286).dm (WitnessCertificates.Batch014.certificate286).beta) ≤ (2*exp (-((CountingCertificates.Batch014.certificate286).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch035.certificate429).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch035.certificate430).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch014.certificate286).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch035.certificate429 MergedCutGroups.Batch035.certificate430 CountingCertificates.Batch014.certificate286 CutLabelCertificates.Entropy007.certificate144 CutLabelCertificates.Minority007.certificate143 matches143 rfl rfl
    MergedCutGroups.Batch035.numericValid429 MergedCutGroups.Batch035.numericValid430 MergedCutGroups.Batch035.cellsSound429 MergedCutGroups.Batch035.cellsSound430
    MergedCutGroups.Batch035.cellsNumeric429 MergedCutGroups.Batch035.cellsNumeric430 MergedCutGroups.Batch035.populationMatches429 MergedCutGroups.Batch035.populationMatches430
    PopulationCertificates.Batch014.valid286 PopulationCertificates.Batch014.sound286 WitnessCertificates.Batch014.valid286 WitnessCertificates.Batch014.sound286 CountingCertificates.Batch014.valid286 CountingCertificates.Batch014.sound286
    CutLabelCertificates.Entropy007.valid144 CutLabelCertificates.Minority007.valid143 CutLabelCertificates.Minority007.sound143 H st hI
theorem probabilityBound143 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch035.certificate429).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate286).dm (WitnessCertificates.Batch014.certificate286).beta) ≤ ((CutFailureCertificates.Budget014.certificate286).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound286 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate286).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch035.certificate429).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch035.certificate430).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch014.certificate286).omega:ℝ) ≤ ((CutFailureCertificates.Budget014.certificate286).bound:ℝ) at hb
  exact (exponentialBound143 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches144 : (MergedCutGroups.Batch036.certificate432).GlobalMatches MergedCutGroups.Batch036.certificate433 CountingCertificates.Batch014.certificate288 CutLabelCertificates.Entropy007.certificate145 CutLabelCertificates.Minority007.certificate144 := by decide +kernel
theorem exponentialBound144 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch036.certificate432).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate288).dm (WitnessCertificates.Batch014.certificate288).beta) ≤ (2*exp (-((CountingCertificates.Batch014.certificate288).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch036.certificate432).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch036.certificate433).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch014.certificate288).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch036.certificate432 MergedCutGroups.Batch036.certificate433 CountingCertificates.Batch014.certificate288 CutLabelCertificates.Entropy007.certificate145 CutLabelCertificates.Minority007.certificate144 matches144 rfl rfl
    MergedCutGroups.Batch036.numericValid432 MergedCutGroups.Batch036.numericValid433 MergedCutGroups.Batch036.cellsSound432 MergedCutGroups.Batch036.cellsSound433
    MergedCutGroups.Batch036.cellsNumeric432 MergedCutGroups.Batch036.cellsNumeric433 MergedCutGroups.Batch036.populationMatches432 MergedCutGroups.Batch036.populationMatches433
    PopulationCertificates.Batch014.valid288 PopulationCertificates.Batch014.sound288 WitnessCertificates.Batch014.valid288 WitnessCertificates.Batch014.sound288 CountingCertificates.Batch014.valid288 CountingCertificates.Batch014.sound288
    CutLabelCertificates.Entropy007.valid145 CutLabelCertificates.Minority007.valid144 CutLabelCertificates.Minority007.sound144 H st hI
theorem probabilityBound144 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch036.certificate432).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate288).dm (WitnessCertificates.Batch014.certificate288).beta) ≤ ((CutFailureCertificates.Budget014.certificate288).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound288 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate288).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch036.certificate432).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch036.certificate433).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch014.certificate288).omega:ℝ) ≤ ((CutFailureCertificates.Budget014.certificate288).bound:ℝ) at hb
  exact (exponentialBound144 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches145 : (MergedCutGroups.Batch036.certificate435).GlobalMatches MergedCutGroups.Batch036.certificate436 CountingCertificates.Batch014.certificate290 CutLabelCertificates.Entropy007.certificate146 CutLabelCertificates.Minority007.certificate145 := by decide +kernel
theorem exponentialBound145 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch036.certificate435).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate290).dm (WitnessCertificates.Batch014.certificate290).beta) ≤ (2*exp (-((CountingCertificates.Batch014.certificate290).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch036.certificate435).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch036.certificate436).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch014.certificate290).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch036.certificate435 MergedCutGroups.Batch036.certificate436 CountingCertificates.Batch014.certificate290 CutLabelCertificates.Entropy007.certificate146 CutLabelCertificates.Minority007.certificate145 matches145 rfl rfl
    MergedCutGroups.Batch036.numericValid435 MergedCutGroups.Batch036.numericValid436 MergedCutGroups.Batch036.cellsSound435 MergedCutGroups.Batch036.cellsSound436
    MergedCutGroups.Batch036.cellsNumeric435 MergedCutGroups.Batch036.cellsNumeric436 MergedCutGroups.Batch036.populationMatches435 MergedCutGroups.Batch036.populationMatches436
    PopulationCertificates.Batch014.valid290 PopulationCertificates.Batch014.sound290 WitnessCertificates.Batch014.valid290 WitnessCertificates.Batch014.sound290 CountingCertificates.Batch014.valid290 CountingCertificates.Batch014.sound290
    CutLabelCertificates.Entropy007.valid146 CutLabelCertificates.Minority007.valid145 CutLabelCertificates.Minority007.sound145 H st hI
theorem probabilityBound145 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch036.certificate435).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate290).dm (WitnessCertificates.Batch014.certificate290).beta) ≤ ((CutFailureCertificates.Budget014.certificate290).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound290 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate290).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch036.certificate435).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch036.certificate436).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch014.certificate290).omega:ℝ) ≤ ((CutFailureCertificates.Budget014.certificate290).bound:ℝ) at hb
  exact (exponentialBound145 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches146 : (MergedCutGroups.Batch036.certificate438).GlobalMatches MergedCutGroups.Batch036.certificate439 CountingCertificates.Batch014.certificate292 CutLabelCertificates.Entropy007.certificate147 CutLabelCertificates.Minority007.certificate146 := by decide +kernel
theorem exponentialBound146 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch036.certificate438).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate292).dm (WitnessCertificates.Batch014.certificate292).beta) ≤ (2*exp (-((CountingCertificates.Batch014.certificate292).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch036.certificate438).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch036.certificate439).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch014.certificate292).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch036.certificate438 MergedCutGroups.Batch036.certificate439 CountingCertificates.Batch014.certificate292 CutLabelCertificates.Entropy007.certificate147 CutLabelCertificates.Minority007.certificate146 matches146 rfl rfl
    MergedCutGroups.Batch036.numericValid438 MergedCutGroups.Batch036.numericValid439 MergedCutGroups.Batch036.cellsSound438 MergedCutGroups.Batch036.cellsSound439
    MergedCutGroups.Batch036.cellsNumeric438 MergedCutGroups.Batch036.cellsNumeric439 MergedCutGroups.Batch036.populationMatches438 MergedCutGroups.Batch036.populationMatches439
    PopulationCertificates.Batch014.valid292 PopulationCertificates.Batch014.sound292 WitnessCertificates.Batch014.valid292 WitnessCertificates.Batch014.sound292 CountingCertificates.Batch014.valid292 CountingCertificates.Batch014.sound292
    CutLabelCertificates.Entropy007.valid147 CutLabelCertificates.Minority007.valid146 CutLabelCertificates.Minority007.sound146 H st hI
theorem probabilityBound146 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch036.certificate438).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate292).dm (WitnessCertificates.Batch014.certificate292).beta) ≤ ((CutFailureCertificates.Budget014.certificate292).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound292 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate292).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch036.certificate438).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch036.certificate439).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch014.certificate292).omega:ℝ) ≤ ((CutFailureCertificates.Budget014.certificate292).bound:ℝ) at hb
  exact (exponentialBound146 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches147 : (MergedCutGroups.Batch036.certificate441).GlobalMatches MergedCutGroups.Batch036.certificate442 CountingCertificates.Batch014.certificate294 CutLabelCertificates.Entropy007.certificate148 CutLabelCertificates.Minority007.certificate147 := by decide +kernel
theorem exponentialBound147 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch036.certificate441).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate294).dm (WitnessCertificates.Batch014.certificate294).beta) ≤ (2*exp (-((CountingCertificates.Batch014.certificate294).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch036.certificate441).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch036.certificate442).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch014.certificate294).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch036.certificate441 MergedCutGroups.Batch036.certificate442 CountingCertificates.Batch014.certificate294 CutLabelCertificates.Entropy007.certificate148 CutLabelCertificates.Minority007.certificate147 matches147 rfl rfl
    MergedCutGroups.Batch036.numericValid441 MergedCutGroups.Batch036.numericValid442 MergedCutGroups.Batch036.cellsSound441 MergedCutGroups.Batch036.cellsSound442
    MergedCutGroups.Batch036.cellsNumeric441 MergedCutGroups.Batch036.cellsNumeric442 MergedCutGroups.Batch036.populationMatches441 MergedCutGroups.Batch036.populationMatches442
    PopulationCertificates.Batch014.valid294 PopulationCertificates.Batch014.sound294 WitnessCertificates.Batch014.valid294 WitnessCertificates.Batch014.sound294 CountingCertificates.Batch014.valid294 CountingCertificates.Batch014.sound294
    CutLabelCertificates.Entropy007.valid148 CutLabelCertificates.Minority007.valid147 CutLabelCertificates.Minority007.sound147 H st hI
theorem probabilityBound147 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch036.certificate441).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate294).dm (WitnessCertificates.Batch014.certificate294).beta) ≤ ((CutFailureCertificates.Budget014.certificate294).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound294 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate294).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch036.certificate441).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch036.certificate442).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch014.certificate294).omega:ℝ) ≤ ((CutFailureCertificates.Budget014.certificate294).bound:ℝ) at hb
  exact (exponentialBound147 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches148 : (MergedCutGroups.Batch037.certificate444).GlobalMatches MergedCutGroups.Batch037.certificate445 CountingCertificates.Batch014.certificate296 CutLabelCertificates.Entropy007.certificate149 CutLabelCertificates.Minority007.certificate148 := by decide +kernel
theorem exponentialBound148 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch037.certificate444).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate296).dm (WitnessCertificates.Batch014.certificate296).beta) ≤ (2*exp (-((CountingCertificates.Batch014.certificate296).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch037.certificate444).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch037.certificate445).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch014.certificate296).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch037.certificate444 MergedCutGroups.Batch037.certificate445 CountingCertificates.Batch014.certificate296 CutLabelCertificates.Entropy007.certificate149 CutLabelCertificates.Minority007.certificate148 matches148 rfl rfl
    MergedCutGroups.Batch037.numericValid444 MergedCutGroups.Batch037.numericValid445 MergedCutGroups.Batch037.cellsSound444 MergedCutGroups.Batch037.cellsSound445
    MergedCutGroups.Batch037.cellsNumeric444 MergedCutGroups.Batch037.cellsNumeric445 MergedCutGroups.Batch037.populationMatches444 MergedCutGroups.Batch037.populationMatches445
    PopulationCertificates.Batch014.valid296 PopulationCertificates.Batch014.sound296 WitnessCertificates.Batch014.valid296 WitnessCertificates.Batch014.sound296 CountingCertificates.Batch014.valid296 CountingCertificates.Batch014.sound296
    CutLabelCertificates.Entropy007.valid149 CutLabelCertificates.Minority007.valid148 CutLabelCertificates.Minority007.sound148 H st hI
theorem probabilityBound148 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch037.certificate444).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate296).dm (WitnessCertificates.Batch014.certificate296).beta) ≤ ((CutFailureCertificates.Budget014.certificate296).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound296 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate296).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch037.certificate444).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch037.certificate445).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch014.certificate296).omega:ℝ) ≤ ((CutFailureCertificates.Budget014.certificate296).bound:ℝ) at hb
  exact (exponentialBound148 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches149 : (MergedCutGroups.Batch037.certificate447).GlobalMatches MergedCutGroups.Batch037.certificate448 CountingCertificates.Batch014.certificate298 CutLabelCertificates.Entropy007.certificate150 CutLabelCertificates.Minority007.certificate149 := by decide +kernel
theorem exponentialBound149 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch037.certificate447).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate298).dm (WitnessCertificates.Batch014.certificate298).beta) ≤ (2*exp (-((CountingCertificates.Batch014.certificate298).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch037.certificate447).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch037.certificate448).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch014.certificate298).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch037.certificate447 MergedCutGroups.Batch037.certificate448 CountingCertificates.Batch014.certificate298 CutLabelCertificates.Entropy007.certificate150 CutLabelCertificates.Minority007.certificate149 matches149 rfl rfl
    MergedCutGroups.Batch037.numericValid447 MergedCutGroups.Batch037.numericValid448 MergedCutGroups.Batch037.cellsSound447 MergedCutGroups.Batch037.cellsSound448
    MergedCutGroups.Batch037.cellsNumeric447 MergedCutGroups.Batch037.cellsNumeric448 MergedCutGroups.Batch037.populationMatches447 MergedCutGroups.Batch037.populationMatches448
    PopulationCertificates.Batch014.valid298 PopulationCertificates.Batch014.sound298 WitnessCertificates.Batch014.valid298 WitnessCertificates.Batch014.sound298 CountingCertificates.Batch014.valid298 CountingCertificates.Batch014.sound298
    CutLabelCertificates.Entropy007.valid150 CutLabelCertificates.Minority007.valid149 CutLabelCertificates.Minority007.sound149 H st hI
theorem probabilityBound149 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch037.certificate447).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch014.certificate298).dm (WitnessCertificates.Batch014.certificate298).beta) ≤ ((CutFailureCertificates.Budget014.certificate298).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget014.sound298 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch014.certificate298).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch037.certificate447).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch037.certificate448).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch014.certificate298).omega:ℝ) ≤ ((CutFailureCertificates.Budget014.certificate298).bound:ℝ) at hb
  exact (exponentialBound149 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches150 : (MergedCutGroups.Batch037.certificate450).GlobalMatches MergedCutGroups.Batch037.certificate451 CountingCertificates.Batch015.certificate300 CutLabelCertificates.Entropy007.certificate151 CutLabelCertificates.Minority007.certificate150 := by decide +kernel
theorem exponentialBound150 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch037.certificate450).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate300).dm (WitnessCertificates.Batch015.certificate300).beta) ≤ (2*exp (-((CountingCertificates.Batch015.certificate300).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch037.certificate450).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch037.certificate451).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch015.certificate300).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch037.certificate450 MergedCutGroups.Batch037.certificate451 CountingCertificates.Batch015.certificate300 CutLabelCertificates.Entropy007.certificate151 CutLabelCertificates.Minority007.certificate150 matches150 rfl rfl
    MergedCutGroups.Batch037.numericValid450 MergedCutGroups.Batch037.numericValid451 MergedCutGroups.Batch037.cellsSound450 MergedCutGroups.Batch037.cellsSound451
    MergedCutGroups.Batch037.cellsNumeric450 MergedCutGroups.Batch037.cellsNumeric451 MergedCutGroups.Batch037.populationMatches450 MergedCutGroups.Batch037.populationMatches451
    PopulationCertificates.Batch015.valid300 PopulationCertificates.Batch015.sound300 WitnessCertificates.Batch015.valid300 WitnessCertificates.Batch015.sound300 CountingCertificates.Batch015.valid300 CountingCertificates.Batch015.sound300
    CutLabelCertificates.Entropy007.valid151 CutLabelCertificates.Minority007.valid150 CutLabelCertificates.Minority007.sound150 H st hI
theorem probabilityBound150 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch037.certificate450).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate300).dm (WitnessCertificates.Batch015.certificate300).beta) ≤ ((CutFailureCertificates.Budget015.certificate300).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound300 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate300).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch037.certificate450).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch037.certificate451).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch015.certificate300).omega:ℝ) ≤ ((CutFailureCertificates.Budget015.certificate300).bound:ℝ) at hb
  exact (exponentialBound150 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches151 : (MergedCutGroups.Batch037.certificate453).GlobalMatches MergedCutGroups.Batch037.certificate454 CountingCertificates.Batch015.certificate302 CutLabelCertificates.Entropy007.certificate152 CutLabelCertificates.Minority007.certificate151 := by decide +kernel
theorem exponentialBound151 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch037.certificate453).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate302).dm (WitnessCertificates.Batch015.certificate302).beta) ≤ (2*exp (-((CountingCertificates.Batch015.certificate302).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch037.certificate453).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch037.certificate454).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch015.certificate302).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch037.certificate453 MergedCutGroups.Batch037.certificate454 CountingCertificates.Batch015.certificate302 CutLabelCertificates.Entropy007.certificate152 CutLabelCertificates.Minority007.certificate151 matches151 rfl rfl
    MergedCutGroups.Batch037.numericValid453 MergedCutGroups.Batch037.numericValid454 MergedCutGroups.Batch037.cellsSound453 MergedCutGroups.Batch037.cellsSound454
    MergedCutGroups.Batch037.cellsNumeric453 MergedCutGroups.Batch037.cellsNumeric454 MergedCutGroups.Batch037.populationMatches453 MergedCutGroups.Batch037.populationMatches454
    PopulationCertificates.Batch015.valid302 PopulationCertificates.Batch015.sound302 WitnessCertificates.Batch015.valid302 WitnessCertificates.Batch015.sound302 CountingCertificates.Batch015.valid302 CountingCertificates.Batch015.sound302
    CutLabelCertificates.Entropy007.valid152 CutLabelCertificates.Minority007.valid151 CutLabelCertificates.Minority007.sound151 H st hI
theorem probabilityBound151 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch037.certificate453).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate302).dm (WitnessCertificates.Batch015.certificate302).beta) ≤ ((CutFailureCertificates.Budget015.certificate302).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound302 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate302).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch037.certificate453).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch037.certificate454).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch015.certificate302).omega:ℝ) ≤ ((CutFailureCertificates.Budget015.certificate302).bound:ℝ) at hb
  exact (exponentialBound151 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches152 : (MergedCutGroups.Batch038.certificate456).GlobalMatches MergedCutGroups.Batch038.certificate457 CountingCertificates.Batch015.certificate304 CutLabelCertificates.Entropy007.certificate153 CutLabelCertificates.Minority007.certificate152 := by decide +kernel
theorem exponentialBound152 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch038.certificate456).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate304).dm (WitnessCertificates.Batch015.certificate304).beta) ≤ (2*exp (-((CountingCertificates.Batch015.certificate304).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch038.certificate456).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch038.certificate457).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch015.certificate304).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch038.certificate456 MergedCutGroups.Batch038.certificate457 CountingCertificates.Batch015.certificate304 CutLabelCertificates.Entropy007.certificate153 CutLabelCertificates.Minority007.certificate152 matches152 rfl rfl
    MergedCutGroups.Batch038.numericValid456 MergedCutGroups.Batch038.numericValid457 MergedCutGroups.Batch038.cellsSound456 MergedCutGroups.Batch038.cellsSound457
    MergedCutGroups.Batch038.cellsNumeric456 MergedCutGroups.Batch038.cellsNumeric457 MergedCutGroups.Batch038.populationMatches456 MergedCutGroups.Batch038.populationMatches457
    PopulationCertificates.Batch015.valid304 PopulationCertificates.Batch015.sound304 WitnessCertificates.Batch015.valid304 WitnessCertificates.Batch015.sound304 CountingCertificates.Batch015.valid304 CountingCertificates.Batch015.sound304
    CutLabelCertificates.Entropy007.valid153 CutLabelCertificates.Minority007.valid152 CutLabelCertificates.Minority007.sound152 H st hI
theorem probabilityBound152 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch038.certificate456).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate304).dm (WitnessCertificates.Batch015.certificate304).beta) ≤ ((CutFailureCertificates.Budget015.certificate304).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound304 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate304).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch038.certificate456).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch038.certificate457).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch015.certificate304).omega:ℝ) ≤ ((CutFailureCertificates.Budget015.certificate304).bound:ℝ) at hb
  exact (exponentialBound152 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches153 : (MergedCutGroups.Batch038.certificate459).GlobalMatches MergedCutGroups.Batch038.certificate460 CountingCertificates.Batch015.certificate306 CutLabelCertificates.Entropy007.certificate154 CutLabelCertificates.Minority007.certificate153 := by decide +kernel
theorem exponentialBound153 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch038.certificate459).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate306).dm (WitnessCertificates.Batch015.certificate306).beta) ≤ (2*exp (-((CountingCertificates.Batch015.certificate306).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch038.certificate459).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch038.certificate460).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch015.certificate306).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch038.certificate459 MergedCutGroups.Batch038.certificate460 CountingCertificates.Batch015.certificate306 CutLabelCertificates.Entropy007.certificate154 CutLabelCertificates.Minority007.certificate153 matches153 rfl rfl
    MergedCutGroups.Batch038.numericValid459 MergedCutGroups.Batch038.numericValid460 MergedCutGroups.Batch038.cellsSound459 MergedCutGroups.Batch038.cellsSound460
    MergedCutGroups.Batch038.cellsNumeric459 MergedCutGroups.Batch038.cellsNumeric460 MergedCutGroups.Batch038.populationMatches459 MergedCutGroups.Batch038.populationMatches460
    PopulationCertificates.Batch015.valid306 PopulationCertificates.Batch015.sound306 WitnessCertificates.Batch015.valid306 WitnessCertificates.Batch015.sound306 CountingCertificates.Batch015.valid306 CountingCertificates.Batch015.sound306
    CutLabelCertificates.Entropy007.valid154 CutLabelCertificates.Minority007.valid153 CutLabelCertificates.Minority007.sound153 H st hI
theorem probabilityBound153 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch038.certificate459).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate306).dm (WitnessCertificates.Batch015.certificate306).beta) ≤ ((CutFailureCertificates.Budget015.certificate306).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound306 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate306).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch038.certificate459).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch038.certificate460).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch015.certificate306).omega:ℝ) ≤ ((CutFailureCertificates.Budget015.certificate306).bound:ℝ) at hb
  exact (exponentialBound153 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches154 : (MergedCutGroups.Batch038.certificate462).GlobalMatches MergedCutGroups.Batch038.certificate463 CountingCertificates.Batch015.certificate308 CutLabelCertificates.Entropy007.certificate155 CutLabelCertificates.Minority007.certificate154 := by decide +kernel
theorem exponentialBound154 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch038.certificate462).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate308).dm (WitnessCertificates.Batch015.certificate308).beta) ≤ (2*exp (-((CountingCertificates.Batch015.certificate308).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch038.certificate462).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch038.certificate463).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch015.certificate308).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch038.certificate462 MergedCutGroups.Batch038.certificate463 CountingCertificates.Batch015.certificate308 CutLabelCertificates.Entropy007.certificate155 CutLabelCertificates.Minority007.certificate154 matches154 rfl rfl
    MergedCutGroups.Batch038.numericValid462 MergedCutGroups.Batch038.numericValid463 MergedCutGroups.Batch038.cellsSound462 MergedCutGroups.Batch038.cellsSound463
    MergedCutGroups.Batch038.cellsNumeric462 MergedCutGroups.Batch038.cellsNumeric463 MergedCutGroups.Batch038.populationMatches462 MergedCutGroups.Batch038.populationMatches463
    PopulationCertificates.Batch015.valid308 PopulationCertificates.Batch015.sound308 WitnessCertificates.Batch015.valid308 WitnessCertificates.Batch015.sound308 CountingCertificates.Batch015.valid308 CountingCertificates.Batch015.sound308
    CutLabelCertificates.Entropy007.valid155 CutLabelCertificates.Minority007.valid154 CutLabelCertificates.Minority007.sound154 H st hI
theorem probabilityBound154 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch038.certificate462).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate308).dm (WitnessCertificates.Batch015.certificate308).beta) ≤ ((CutFailureCertificates.Budget015.certificate308).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound308 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate308).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch038.certificate462).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch038.certificate463).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch015.certificate308).omega:ℝ) ≤ ((CutFailureCertificates.Budget015.certificate308).bound:ℝ) at hb
  exact (exponentialBound154 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches155 : (MergedCutGroups.Batch038.certificate465).GlobalMatches MergedCutGroups.Batch038.certificate466 CountingCertificates.Batch015.certificate310 CutLabelCertificates.Entropy007.certificate156 CutLabelCertificates.Minority007.certificate155 := by decide +kernel
theorem exponentialBound155 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch038.certificate465).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate310).dm (WitnessCertificates.Batch015.certificate310).beta) ≤ (2*exp (-((CountingCertificates.Batch015.certificate310).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch038.certificate465).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch038.certificate466).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch015.certificate310).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch038.certificate465 MergedCutGroups.Batch038.certificate466 CountingCertificates.Batch015.certificate310 CutLabelCertificates.Entropy007.certificate156 CutLabelCertificates.Minority007.certificate155 matches155 rfl rfl
    MergedCutGroups.Batch038.numericValid465 MergedCutGroups.Batch038.numericValid466 MergedCutGroups.Batch038.cellsSound465 MergedCutGroups.Batch038.cellsSound466
    MergedCutGroups.Batch038.cellsNumeric465 MergedCutGroups.Batch038.cellsNumeric466 MergedCutGroups.Batch038.populationMatches465 MergedCutGroups.Batch038.populationMatches466
    PopulationCertificates.Batch015.valid310 PopulationCertificates.Batch015.sound310 WitnessCertificates.Batch015.valid310 WitnessCertificates.Batch015.sound310 CountingCertificates.Batch015.valid310 CountingCertificates.Batch015.sound310
    CutLabelCertificates.Entropy007.valid156 CutLabelCertificates.Minority007.valid155 CutLabelCertificates.Minority007.sound155 H st hI
theorem probabilityBound155 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch038.certificate465).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate310).dm (WitnessCertificates.Batch015.certificate310).beta) ≤ ((CutFailureCertificates.Budget015.certificate310).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound310 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate310).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch038.certificate465).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch038.certificate466).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch015.certificate310).omega:ℝ) ≤ ((CutFailureCertificates.Budget015.certificate310).bound:ℝ) at hb
  exact (exponentialBound155 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches156 : (MergedCutGroups.Batch039.certificate468).GlobalMatches MergedCutGroups.Batch039.certificate469 CountingCertificates.Batch015.certificate312 CutLabelCertificates.Entropy007.certificate157 CutLabelCertificates.Minority007.certificate156 := by decide +kernel
theorem exponentialBound156 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch039.certificate468).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate312).dm (WitnessCertificates.Batch015.certificate312).beta) ≤ (2*exp (-((CountingCertificates.Batch015.certificate312).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch039.certificate468).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch039.certificate469).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch015.certificate312).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch039.certificate468 MergedCutGroups.Batch039.certificate469 CountingCertificates.Batch015.certificate312 CutLabelCertificates.Entropy007.certificate157 CutLabelCertificates.Minority007.certificate156 matches156 rfl rfl
    MergedCutGroups.Batch039.numericValid468 MergedCutGroups.Batch039.numericValid469 MergedCutGroups.Batch039.cellsSound468 MergedCutGroups.Batch039.cellsSound469
    MergedCutGroups.Batch039.cellsNumeric468 MergedCutGroups.Batch039.cellsNumeric469 MergedCutGroups.Batch039.populationMatches468 MergedCutGroups.Batch039.populationMatches469
    PopulationCertificates.Batch015.valid312 PopulationCertificates.Batch015.sound312 WitnessCertificates.Batch015.valid312 WitnessCertificates.Batch015.sound312 CountingCertificates.Batch015.valid312 CountingCertificates.Batch015.sound312
    CutLabelCertificates.Entropy007.valid157 CutLabelCertificates.Minority007.valid156 CutLabelCertificates.Minority007.sound156 H st hI
theorem probabilityBound156 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch039.certificate468).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate312).dm (WitnessCertificates.Batch015.certificate312).beta) ≤ ((CutFailureCertificates.Budget015.certificate312).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound312 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate312).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch039.certificate468).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch039.certificate469).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch015.certificate312).omega:ℝ) ≤ ((CutFailureCertificates.Budget015.certificate312).bound:ℝ) at hb
  exact (exponentialBound156 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches157 : (MergedCutGroups.Batch039.certificate471).GlobalMatches MergedCutGroups.Batch039.certificate472 CountingCertificates.Batch015.certificate314 CutLabelCertificates.Entropy007.certificate158 CutLabelCertificates.Minority007.certificate157 := by decide +kernel
theorem exponentialBound157 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch039.certificate471).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate314).dm (WitnessCertificates.Batch015.certificate314).beta) ≤ (2*exp (-((CountingCertificates.Batch015.certificate314).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch039.certificate471).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch039.certificate472).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch015.certificate314).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch039.certificate471 MergedCutGroups.Batch039.certificate472 CountingCertificates.Batch015.certificate314 CutLabelCertificates.Entropy007.certificate158 CutLabelCertificates.Minority007.certificate157 matches157 rfl rfl
    MergedCutGroups.Batch039.numericValid471 MergedCutGroups.Batch039.numericValid472 MergedCutGroups.Batch039.cellsSound471 MergedCutGroups.Batch039.cellsSound472
    MergedCutGroups.Batch039.cellsNumeric471 MergedCutGroups.Batch039.cellsNumeric472 MergedCutGroups.Batch039.populationMatches471 MergedCutGroups.Batch039.populationMatches472
    PopulationCertificates.Batch015.valid314 PopulationCertificates.Batch015.sound314 WitnessCertificates.Batch015.valid314 WitnessCertificates.Batch015.sound314 CountingCertificates.Batch015.valid314 CountingCertificates.Batch015.sound314
    CutLabelCertificates.Entropy007.valid158 CutLabelCertificates.Minority007.valid157 CutLabelCertificates.Minority007.sound157 H st hI
theorem probabilityBound157 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch039.certificate471).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate314).dm (WitnessCertificates.Batch015.certificate314).beta) ≤ ((CutFailureCertificates.Budget015.certificate314).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound314 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate314).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch039.certificate471).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch039.certificate472).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch015.certificate314).omega:ℝ) ≤ ((CutFailureCertificates.Budget015.certificate314).bound:ℝ) at hb
  exact (exponentialBound157 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches158 : (MergedCutGroups.Batch039.certificate474).GlobalMatches MergedCutGroups.Batch039.certificate475 CountingCertificates.Batch015.certificate316 CutLabelCertificates.Entropy007.certificate159 CutLabelCertificates.Minority007.certificate158 := by decide +kernel
theorem exponentialBound158 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch039.certificate474).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate316).dm (WitnessCertificates.Batch015.certificate316).beta) ≤ (2*exp (-((CountingCertificates.Batch015.certificate316).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch039.certificate474).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch039.certificate475).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch015.certificate316).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch039.certificate474 MergedCutGroups.Batch039.certificate475 CountingCertificates.Batch015.certificate316 CutLabelCertificates.Entropy007.certificate159 CutLabelCertificates.Minority007.certificate158 matches158 rfl rfl
    MergedCutGroups.Batch039.numericValid474 MergedCutGroups.Batch039.numericValid475 MergedCutGroups.Batch039.cellsSound474 MergedCutGroups.Batch039.cellsSound475
    MergedCutGroups.Batch039.cellsNumeric474 MergedCutGroups.Batch039.cellsNumeric475 MergedCutGroups.Batch039.populationMatches474 MergedCutGroups.Batch039.populationMatches475
    PopulationCertificates.Batch015.valid316 PopulationCertificates.Batch015.sound316 WitnessCertificates.Batch015.valid316 WitnessCertificates.Batch015.sound316 CountingCertificates.Batch015.valid316 CountingCertificates.Batch015.sound316
    CutLabelCertificates.Entropy007.valid159 CutLabelCertificates.Minority007.valid158 CutLabelCertificates.Minority007.sound158 H st hI
theorem probabilityBound158 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch039.certificate474).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate316).dm (WitnessCertificates.Batch015.certificate316).beta) ≤ ((CutFailureCertificates.Budget015.certificate316).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound316 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate316).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch039.certificate474).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch039.certificate475).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch015.certificate316).omega:ℝ) ≤ ((CutFailureCertificates.Budget015.certificate316).bound:ℝ) at hb
  exact (exponentialBound158 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches159 : (MergedCutGroups.Batch039.certificate477).GlobalMatches MergedCutGroups.Batch039.certificate478 CountingCertificates.Batch015.certificate318 CutLabelCertificates.Entropy008.certificate160 CutLabelCertificates.Minority007.certificate159 := by decide +kernel
theorem exponentialBound159 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch039.certificate477).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate318).dm (WitnessCertificates.Batch015.certificate318).beta) ≤ (2*exp (-((CountingCertificates.Batch015.certificate318).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch039.certificate477).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch039.certificate478).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch015.certificate318).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch039.certificate477 MergedCutGroups.Batch039.certificate478 CountingCertificates.Batch015.certificate318 CutLabelCertificates.Entropy008.certificate160 CutLabelCertificates.Minority007.certificate159 matches159 rfl rfl
    MergedCutGroups.Batch039.numericValid477 MergedCutGroups.Batch039.numericValid478 MergedCutGroups.Batch039.cellsSound477 MergedCutGroups.Batch039.cellsSound478
    MergedCutGroups.Batch039.cellsNumeric477 MergedCutGroups.Batch039.cellsNumeric478 MergedCutGroups.Batch039.populationMatches477 MergedCutGroups.Batch039.populationMatches478
    PopulationCertificates.Batch015.valid318 PopulationCertificates.Batch015.sound318 WitnessCertificates.Batch015.valid318 WitnessCertificates.Batch015.sound318 CountingCertificates.Batch015.valid318 CountingCertificates.Batch015.sound318
    CutLabelCertificates.Entropy008.valid160 CutLabelCertificates.Minority007.valid159 CutLabelCertificates.Minority007.sound159 H st hI
theorem probabilityBound159 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch039.certificate477).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch015.certificate318).dm (WitnessCertificates.Batch015.certificate318).beta) ≤ ((CutFailureCertificates.Budget015.certificate318).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget015.sound318 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch015.certificate318).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch039.certificate477).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch039.certificate478).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch015.certificate318).omega:ℝ) ≤ ((CutFailureCertificates.Budget015.certificate318).bound:ℝ) at hb
  exact (exponentialBound159 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch007
