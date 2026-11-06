import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch006
import Cycle12.CountingCertificates.Batch007
import Cycle12.CutFailureCertificates.Budget006
import Cycle12.CutFailureCertificates.Budget007
import Cycle12.CutLabelCertificates.Entropy003
import Cycle12.CutLabelCertificates.Entropy004
import Cycle12.CutLabelCertificates.Minority003
import Cycle12.MergedCutGroups.Batch015
import Cycle12.MergedCutGroups.Batch016
import Cycle12.MergedCutGroups.Batch017
import Cycle12.MergedCutGroups.Batch018
import Cycle12.MergedCutGroups.Batch019
import Cycle12.PopulationCertificates.Batch006
import Cycle12.PopulationCertificates.Batch007
import Cycle12.WitnessCertificates.Batch006
import Cycle12.WitnessCertificates.Batch007

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch003
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches60 : (MergedCutGroups.Batch015.certificate180).GlobalMatches MergedCutGroups.Batch015.certificate181 CountingCertificates.Batch006.certificate120 CutLabelCertificates.Entropy003.certificate61 CutLabelCertificates.Minority003.certificate60 := by decide +kernel
theorem exponentialBound60 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch015.certificate180).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate120).dm (WitnessCertificates.Batch006.certificate120).beta) ≤ (2*exp (-((CountingCertificates.Batch006.certificate120).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch015.certificate180).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch015.certificate181).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch006.certificate120).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch015.certificate180 MergedCutGroups.Batch015.certificate181 CountingCertificates.Batch006.certificate120 CutLabelCertificates.Entropy003.certificate61 CutLabelCertificates.Minority003.certificate60 matches60 rfl rfl
    MergedCutGroups.Batch015.numericValid180 MergedCutGroups.Batch015.numericValid181 MergedCutGroups.Batch015.cellsSound180 MergedCutGroups.Batch015.cellsSound181
    MergedCutGroups.Batch015.cellsNumeric180 MergedCutGroups.Batch015.cellsNumeric181 MergedCutGroups.Batch015.populationMatches180 MergedCutGroups.Batch015.populationMatches181
    PopulationCertificates.Batch006.valid120 PopulationCertificates.Batch006.sound120 WitnessCertificates.Batch006.valid120 WitnessCertificates.Batch006.sound120 CountingCertificates.Batch006.valid120 CountingCertificates.Batch006.sound120
    CutLabelCertificates.Entropy003.valid61 CutLabelCertificates.Minority003.valid60 CutLabelCertificates.Minority003.sound60 H st hI
theorem probabilityBound60 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch015.certificate180).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate120).dm (WitnessCertificates.Batch006.certificate120).beta) ≤ ((CutFailureCertificates.Budget006.certificate120).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound120 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate120).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch015.certificate180).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch015.certificate181).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch006.certificate120).omega:ℝ) ≤ ((CutFailureCertificates.Budget006.certificate120).bound:ℝ) at hb
  exact (exponentialBound60 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches61 : (MergedCutGroups.Batch015.certificate183).GlobalMatches MergedCutGroups.Batch015.certificate184 CountingCertificates.Batch006.certificate122 CutLabelCertificates.Entropy003.certificate62 CutLabelCertificates.Minority003.certificate61 := by decide +kernel
theorem exponentialBound61 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch015.certificate183).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate122).dm (WitnessCertificates.Batch006.certificate122).beta) ≤ (2*exp (-((CountingCertificates.Batch006.certificate122).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch015.certificate183).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch015.certificate184).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch006.certificate122).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch015.certificate183 MergedCutGroups.Batch015.certificate184 CountingCertificates.Batch006.certificate122 CutLabelCertificates.Entropy003.certificate62 CutLabelCertificates.Minority003.certificate61 matches61 rfl rfl
    MergedCutGroups.Batch015.numericValid183 MergedCutGroups.Batch015.numericValid184 MergedCutGroups.Batch015.cellsSound183 MergedCutGroups.Batch015.cellsSound184
    MergedCutGroups.Batch015.cellsNumeric183 MergedCutGroups.Batch015.cellsNumeric184 MergedCutGroups.Batch015.populationMatches183 MergedCutGroups.Batch015.populationMatches184
    PopulationCertificates.Batch006.valid122 PopulationCertificates.Batch006.sound122 WitnessCertificates.Batch006.valid122 WitnessCertificates.Batch006.sound122 CountingCertificates.Batch006.valid122 CountingCertificates.Batch006.sound122
    CutLabelCertificates.Entropy003.valid62 CutLabelCertificates.Minority003.valid61 CutLabelCertificates.Minority003.sound61 H st hI
theorem probabilityBound61 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch015.certificate183).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate122).dm (WitnessCertificates.Batch006.certificate122).beta) ≤ ((CutFailureCertificates.Budget006.certificate122).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound122 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate122).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch015.certificate183).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch015.certificate184).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch006.certificate122).omega:ℝ) ≤ ((CutFailureCertificates.Budget006.certificate122).bound:ℝ) at hb
  exact (exponentialBound61 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches62 : (MergedCutGroups.Batch015.certificate186).GlobalMatches MergedCutGroups.Batch015.certificate187 CountingCertificates.Batch006.certificate124 CutLabelCertificates.Entropy003.certificate63 CutLabelCertificates.Minority003.certificate62 := by decide +kernel
theorem exponentialBound62 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch015.certificate186).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate124).dm (WitnessCertificates.Batch006.certificate124).beta) ≤ (2*exp (-((CountingCertificates.Batch006.certificate124).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch015.certificate186).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch015.certificate187).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch006.certificate124).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch015.certificate186 MergedCutGroups.Batch015.certificate187 CountingCertificates.Batch006.certificate124 CutLabelCertificates.Entropy003.certificate63 CutLabelCertificates.Minority003.certificate62 matches62 rfl rfl
    MergedCutGroups.Batch015.numericValid186 MergedCutGroups.Batch015.numericValid187 MergedCutGroups.Batch015.cellsSound186 MergedCutGroups.Batch015.cellsSound187
    MergedCutGroups.Batch015.cellsNumeric186 MergedCutGroups.Batch015.cellsNumeric187 MergedCutGroups.Batch015.populationMatches186 MergedCutGroups.Batch015.populationMatches187
    PopulationCertificates.Batch006.valid124 PopulationCertificates.Batch006.sound124 WitnessCertificates.Batch006.valid124 WitnessCertificates.Batch006.sound124 CountingCertificates.Batch006.valid124 CountingCertificates.Batch006.sound124
    CutLabelCertificates.Entropy003.valid63 CutLabelCertificates.Minority003.valid62 CutLabelCertificates.Minority003.sound62 H st hI
theorem probabilityBound62 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch015.certificate186).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate124).dm (WitnessCertificates.Batch006.certificate124).beta) ≤ ((CutFailureCertificates.Budget006.certificate124).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound124 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate124).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch015.certificate186).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch015.certificate187).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch006.certificate124).omega:ℝ) ≤ ((CutFailureCertificates.Budget006.certificate124).bound:ℝ) at hb
  exact (exponentialBound62 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches63 : (MergedCutGroups.Batch015.certificate189).GlobalMatches MergedCutGroups.Batch015.certificate190 CountingCertificates.Batch006.certificate126 CutLabelCertificates.Entropy003.certificate64 CutLabelCertificates.Minority003.certificate63 := by decide +kernel
theorem exponentialBound63 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch015.certificate189).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate126).dm (WitnessCertificates.Batch006.certificate126).beta) ≤ (2*exp (-((CountingCertificates.Batch006.certificate126).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch015.certificate189).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch015.certificate190).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch006.certificate126).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch015.certificate189 MergedCutGroups.Batch015.certificate190 CountingCertificates.Batch006.certificate126 CutLabelCertificates.Entropy003.certificate64 CutLabelCertificates.Minority003.certificate63 matches63 rfl rfl
    MergedCutGroups.Batch015.numericValid189 MergedCutGroups.Batch015.numericValid190 MergedCutGroups.Batch015.cellsSound189 MergedCutGroups.Batch015.cellsSound190
    MergedCutGroups.Batch015.cellsNumeric189 MergedCutGroups.Batch015.cellsNumeric190 MergedCutGroups.Batch015.populationMatches189 MergedCutGroups.Batch015.populationMatches190
    PopulationCertificates.Batch006.valid126 PopulationCertificates.Batch006.sound126 WitnessCertificates.Batch006.valid126 WitnessCertificates.Batch006.sound126 CountingCertificates.Batch006.valid126 CountingCertificates.Batch006.sound126
    CutLabelCertificates.Entropy003.valid64 CutLabelCertificates.Minority003.valid63 CutLabelCertificates.Minority003.sound63 H st hI
theorem probabilityBound63 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch015.certificate189).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate126).dm (WitnessCertificates.Batch006.certificate126).beta) ≤ ((CutFailureCertificates.Budget006.certificate126).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound126 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate126).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch015.certificate189).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch015.certificate190).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch006.certificate126).omega:ℝ) ≤ ((CutFailureCertificates.Budget006.certificate126).bound:ℝ) at hb
  exact (exponentialBound63 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches64 : (MergedCutGroups.Batch016.certificate192).GlobalMatches MergedCutGroups.Batch016.certificate193 CountingCertificates.Batch006.certificate128 CutLabelCertificates.Entropy003.certificate65 CutLabelCertificates.Minority003.certificate64 := by decide +kernel
theorem exponentialBound64 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch016.certificate192).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate128).dm (WitnessCertificates.Batch006.certificate128).beta) ≤ (2*exp (-((CountingCertificates.Batch006.certificate128).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch016.certificate192).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch016.certificate193).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch006.certificate128).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch016.certificate192 MergedCutGroups.Batch016.certificate193 CountingCertificates.Batch006.certificate128 CutLabelCertificates.Entropy003.certificate65 CutLabelCertificates.Minority003.certificate64 matches64 rfl rfl
    MergedCutGroups.Batch016.numericValid192 MergedCutGroups.Batch016.numericValid193 MergedCutGroups.Batch016.cellsSound192 MergedCutGroups.Batch016.cellsSound193
    MergedCutGroups.Batch016.cellsNumeric192 MergedCutGroups.Batch016.cellsNumeric193 MergedCutGroups.Batch016.populationMatches192 MergedCutGroups.Batch016.populationMatches193
    PopulationCertificates.Batch006.valid128 PopulationCertificates.Batch006.sound128 WitnessCertificates.Batch006.valid128 WitnessCertificates.Batch006.sound128 CountingCertificates.Batch006.valid128 CountingCertificates.Batch006.sound128
    CutLabelCertificates.Entropy003.valid65 CutLabelCertificates.Minority003.valid64 CutLabelCertificates.Minority003.sound64 H st hI
theorem probabilityBound64 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch016.certificate192).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate128).dm (WitnessCertificates.Batch006.certificate128).beta) ≤ ((CutFailureCertificates.Budget006.certificate128).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound128 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate128).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch016.certificate192).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch016.certificate193).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch006.certificate128).omega:ℝ) ≤ ((CutFailureCertificates.Budget006.certificate128).bound:ℝ) at hb
  exact (exponentialBound64 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches65 : (MergedCutGroups.Batch016.certificate195).GlobalMatches MergedCutGroups.Batch016.certificate196 CountingCertificates.Batch006.certificate130 CutLabelCertificates.Entropy003.certificate66 CutLabelCertificates.Minority003.certificate65 := by decide +kernel
theorem exponentialBound65 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch016.certificate195).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate130).dm (WitnessCertificates.Batch006.certificate130).beta) ≤ (2*exp (-((CountingCertificates.Batch006.certificate130).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch016.certificate195).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch016.certificate196).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch006.certificate130).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch016.certificate195 MergedCutGroups.Batch016.certificate196 CountingCertificates.Batch006.certificate130 CutLabelCertificates.Entropy003.certificate66 CutLabelCertificates.Minority003.certificate65 matches65 rfl rfl
    MergedCutGroups.Batch016.numericValid195 MergedCutGroups.Batch016.numericValid196 MergedCutGroups.Batch016.cellsSound195 MergedCutGroups.Batch016.cellsSound196
    MergedCutGroups.Batch016.cellsNumeric195 MergedCutGroups.Batch016.cellsNumeric196 MergedCutGroups.Batch016.populationMatches195 MergedCutGroups.Batch016.populationMatches196
    PopulationCertificates.Batch006.valid130 PopulationCertificates.Batch006.sound130 WitnessCertificates.Batch006.valid130 WitnessCertificates.Batch006.sound130 CountingCertificates.Batch006.valid130 CountingCertificates.Batch006.sound130
    CutLabelCertificates.Entropy003.valid66 CutLabelCertificates.Minority003.valid65 CutLabelCertificates.Minority003.sound65 H st hI
theorem probabilityBound65 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch016.certificate195).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate130).dm (WitnessCertificates.Batch006.certificate130).beta) ≤ ((CutFailureCertificates.Budget006.certificate130).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound130 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate130).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch016.certificate195).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch016.certificate196).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch006.certificate130).omega:ℝ) ≤ ((CutFailureCertificates.Budget006.certificate130).bound:ℝ) at hb
  exact (exponentialBound65 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches66 : (MergedCutGroups.Batch016.certificate198).GlobalMatches MergedCutGroups.Batch016.certificate199 CountingCertificates.Batch006.certificate132 CutLabelCertificates.Entropy003.certificate67 CutLabelCertificates.Minority003.certificate66 := by decide +kernel
theorem exponentialBound66 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch016.certificate198).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate132).dm (WitnessCertificates.Batch006.certificate132).beta) ≤ (2*exp (-((CountingCertificates.Batch006.certificate132).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch016.certificate198).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch016.certificate199).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch006.certificate132).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch016.certificate198 MergedCutGroups.Batch016.certificate199 CountingCertificates.Batch006.certificate132 CutLabelCertificates.Entropy003.certificate67 CutLabelCertificates.Minority003.certificate66 matches66 rfl rfl
    MergedCutGroups.Batch016.numericValid198 MergedCutGroups.Batch016.numericValid199 MergedCutGroups.Batch016.cellsSound198 MergedCutGroups.Batch016.cellsSound199
    MergedCutGroups.Batch016.cellsNumeric198 MergedCutGroups.Batch016.cellsNumeric199 MergedCutGroups.Batch016.populationMatches198 MergedCutGroups.Batch016.populationMatches199
    PopulationCertificates.Batch006.valid132 PopulationCertificates.Batch006.sound132 WitnessCertificates.Batch006.valid132 WitnessCertificates.Batch006.sound132 CountingCertificates.Batch006.valid132 CountingCertificates.Batch006.sound132
    CutLabelCertificates.Entropy003.valid67 CutLabelCertificates.Minority003.valid66 CutLabelCertificates.Minority003.sound66 H st hI
theorem probabilityBound66 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch016.certificate198).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate132).dm (WitnessCertificates.Batch006.certificate132).beta) ≤ ((CutFailureCertificates.Budget006.certificate132).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound132 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate132).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch016.certificate198).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch016.certificate199).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch006.certificate132).omega:ℝ) ≤ ((CutFailureCertificates.Budget006.certificate132).bound:ℝ) at hb
  exact (exponentialBound66 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches67 : (MergedCutGroups.Batch016.certificate201).GlobalMatches MergedCutGroups.Batch016.certificate202 CountingCertificates.Batch006.certificate134 CutLabelCertificates.Entropy003.certificate68 CutLabelCertificates.Minority003.certificate67 := by decide +kernel
theorem exponentialBound67 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch016.certificate201).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate134).dm (WitnessCertificates.Batch006.certificate134).beta) ≤ (2*exp (-((CountingCertificates.Batch006.certificate134).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch016.certificate201).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch016.certificate202).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch006.certificate134).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch016.certificate201 MergedCutGroups.Batch016.certificate202 CountingCertificates.Batch006.certificate134 CutLabelCertificates.Entropy003.certificate68 CutLabelCertificates.Minority003.certificate67 matches67 rfl rfl
    MergedCutGroups.Batch016.numericValid201 MergedCutGroups.Batch016.numericValid202 MergedCutGroups.Batch016.cellsSound201 MergedCutGroups.Batch016.cellsSound202
    MergedCutGroups.Batch016.cellsNumeric201 MergedCutGroups.Batch016.cellsNumeric202 MergedCutGroups.Batch016.populationMatches201 MergedCutGroups.Batch016.populationMatches202
    PopulationCertificates.Batch006.valid134 PopulationCertificates.Batch006.sound134 WitnessCertificates.Batch006.valid134 WitnessCertificates.Batch006.sound134 CountingCertificates.Batch006.valid134 CountingCertificates.Batch006.sound134
    CutLabelCertificates.Entropy003.valid68 CutLabelCertificates.Minority003.valid67 CutLabelCertificates.Minority003.sound67 H st hI
theorem probabilityBound67 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch016.certificate201).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate134).dm (WitnessCertificates.Batch006.certificate134).beta) ≤ ((CutFailureCertificates.Budget006.certificate134).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound134 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate134).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch016.certificate201).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch016.certificate202).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch006.certificate134).omega:ℝ) ≤ ((CutFailureCertificates.Budget006.certificate134).bound:ℝ) at hb
  exact (exponentialBound67 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches68 : (MergedCutGroups.Batch017.certificate204).GlobalMatches MergedCutGroups.Batch017.certificate205 CountingCertificates.Batch006.certificate136 CutLabelCertificates.Entropy003.certificate69 CutLabelCertificates.Minority003.certificate68 := by decide +kernel
theorem exponentialBound68 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch017.certificate204).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate136).dm (WitnessCertificates.Batch006.certificate136).beta) ≤ (2*exp (-((CountingCertificates.Batch006.certificate136).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch017.certificate204).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch017.certificate205).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch006.certificate136).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch017.certificate204 MergedCutGroups.Batch017.certificate205 CountingCertificates.Batch006.certificate136 CutLabelCertificates.Entropy003.certificate69 CutLabelCertificates.Minority003.certificate68 matches68 rfl rfl
    MergedCutGroups.Batch017.numericValid204 MergedCutGroups.Batch017.numericValid205 MergedCutGroups.Batch017.cellsSound204 MergedCutGroups.Batch017.cellsSound205
    MergedCutGroups.Batch017.cellsNumeric204 MergedCutGroups.Batch017.cellsNumeric205 MergedCutGroups.Batch017.populationMatches204 MergedCutGroups.Batch017.populationMatches205
    PopulationCertificates.Batch006.valid136 PopulationCertificates.Batch006.sound136 WitnessCertificates.Batch006.valid136 WitnessCertificates.Batch006.sound136 CountingCertificates.Batch006.valid136 CountingCertificates.Batch006.sound136
    CutLabelCertificates.Entropy003.valid69 CutLabelCertificates.Minority003.valid68 CutLabelCertificates.Minority003.sound68 H st hI
theorem probabilityBound68 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch017.certificate204).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate136).dm (WitnessCertificates.Batch006.certificate136).beta) ≤ ((CutFailureCertificates.Budget006.certificate136).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound136 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate136).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch017.certificate204).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch017.certificate205).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch006.certificate136).omega:ℝ) ≤ ((CutFailureCertificates.Budget006.certificate136).bound:ℝ) at hb
  exact (exponentialBound68 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches69 : (MergedCutGroups.Batch017.certificate207).GlobalMatches MergedCutGroups.Batch017.certificate208 CountingCertificates.Batch006.certificate138 CutLabelCertificates.Entropy003.certificate70 CutLabelCertificates.Minority003.certificate69 := by decide +kernel
theorem exponentialBound69 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch017.certificate207).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate138).dm (WitnessCertificates.Batch006.certificate138).beta) ≤ (2*exp (-((CountingCertificates.Batch006.certificate138).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch017.certificate207).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch017.certificate208).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch006.certificate138).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch017.certificate207 MergedCutGroups.Batch017.certificate208 CountingCertificates.Batch006.certificate138 CutLabelCertificates.Entropy003.certificate70 CutLabelCertificates.Minority003.certificate69 matches69 rfl rfl
    MergedCutGroups.Batch017.numericValid207 MergedCutGroups.Batch017.numericValid208 MergedCutGroups.Batch017.cellsSound207 MergedCutGroups.Batch017.cellsSound208
    MergedCutGroups.Batch017.cellsNumeric207 MergedCutGroups.Batch017.cellsNumeric208 MergedCutGroups.Batch017.populationMatches207 MergedCutGroups.Batch017.populationMatches208
    PopulationCertificates.Batch006.valid138 PopulationCertificates.Batch006.sound138 WitnessCertificates.Batch006.valid138 WitnessCertificates.Batch006.sound138 CountingCertificates.Batch006.valid138 CountingCertificates.Batch006.sound138
    CutLabelCertificates.Entropy003.valid70 CutLabelCertificates.Minority003.valid69 CutLabelCertificates.Minority003.sound69 H st hI
theorem probabilityBound69 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch017.certificate207).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch006.certificate138).dm (WitnessCertificates.Batch006.certificate138).beta) ≤ ((CutFailureCertificates.Budget006.certificate138).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget006.sound138 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch006.certificate138).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch017.certificate207).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch017.certificate208).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch006.certificate138).omega:ℝ) ≤ ((CutFailureCertificates.Budget006.certificate138).bound:ℝ) at hb
  exact (exponentialBound69 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches70 : (MergedCutGroups.Batch017.certificate210).GlobalMatches MergedCutGroups.Batch017.certificate211 CountingCertificates.Batch007.certificate140 CutLabelCertificates.Entropy003.certificate71 CutLabelCertificates.Minority003.certificate70 := by decide +kernel
theorem exponentialBound70 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch017.certificate210).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate140).dm (WitnessCertificates.Batch007.certificate140).beta) ≤ (2*exp (-((CountingCertificates.Batch007.certificate140).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch017.certificate210).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch017.certificate211).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch007.certificate140).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch017.certificate210 MergedCutGroups.Batch017.certificate211 CountingCertificates.Batch007.certificate140 CutLabelCertificates.Entropy003.certificate71 CutLabelCertificates.Minority003.certificate70 matches70 rfl rfl
    MergedCutGroups.Batch017.numericValid210 MergedCutGroups.Batch017.numericValid211 MergedCutGroups.Batch017.cellsSound210 MergedCutGroups.Batch017.cellsSound211
    MergedCutGroups.Batch017.cellsNumeric210 MergedCutGroups.Batch017.cellsNumeric211 MergedCutGroups.Batch017.populationMatches210 MergedCutGroups.Batch017.populationMatches211
    PopulationCertificates.Batch007.valid140 PopulationCertificates.Batch007.sound140 WitnessCertificates.Batch007.valid140 WitnessCertificates.Batch007.sound140 CountingCertificates.Batch007.valid140 CountingCertificates.Batch007.sound140
    CutLabelCertificates.Entropy003.valid71 CutLabelCertificates.Minority003.valid70 CutLabelCertificates.Minority003.sound70 H st hI
theorem probabilityBound70 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch017.certificate210).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate140).dm (WitnessCertificates.Batch007.certificate140).beta) ≤ ((CutFailureCertificates.Budget007.certificate140).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound140 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate140).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch017.certificate210).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch017.certificate211).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch007.certificate140).omega:ℝ) ≤ ((CutFailureCertificates.Budget007.certificate140).bound:ℝ) at hb
  exact (exponentialBound70 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches71 : (MergedCutGroups.Batch017.certificate213).GlobalMatches MergedCutGroups.Batch017.certificate214 CountingCertificates.Batch007.certificate142 CutLabelCertificates.Entropy003.certificate72 CutLabelCertificates.Minority003.certificate71 := by decide +kernel
theorem exponentialBound71 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch017.certificate213).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate142).dm (WitnessCertificates.Batch007.certificate142).beta) ≤ (2*exp (-((CountingCertificates.Batch007.certificate142).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch017.certificate213).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch017.certificate214).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch007.certificate142).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch017.certificate213 MergedCutGroups.Batch017.certificate214 CountingCertificates.Batch007.certificate142 CutLabelCertificates.Entropy003.certificate72 CutLabelCertificates.Minority003.certificate71 matches71 rfl rfl
    MergedCutGroups.Batch017.numericValid213 MergedCutGroups.Batch017.numericValid214 MergedCutGroups.Batch017.cellsSound213 MergedCutGroups.Batch017.cellsSound214
    MergedCutGroups.Batch017.cellsNumeric213 MergedCutGroups.Batch017.cellsNumeric214 MergedCutGroups.Batch017.populationMatches213 MergedCutGroups.Batch017.populationMatches214
    PopulationCertificates.Batch007.valid142 PopulationCertificates.Batch007.sound142 WitnessCertificates.Batch007.valid142 WitnessCertificates.Batch007.sound142 CountingCertificates.Batch007.valid142 CountingCertificates.Batch007.sound142
    CutLabelCertificates.Entropy003.valid72 CutLabelCertificates.Minority003.valid71 CutLabelCertificates.Minority003.sound71 H st hI
theorem probabilityBound71 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch017.certificate213).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate142).dm (WitnessCertificates.Batch007.certificate142).beta) ≤ ((CutFailureCertificates.Budget007.certificate142).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound142 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate142).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch017.certificate213).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch017.certificate214).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch007.certificate142).omega:ℝ) ≤ ((CutFailureCertificates.Budget007.certificate142).bound:ℝ) at hb
  exact (exponentialBound71 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches72 : (MergedCutGroups.Batch018.certificate216).GlobalMatches MergedCutGroups.Batch018.certificate217 CountingCertificates.Batch007.certificate144 CutLabelCertificates.Entropy003.certificate73 CutLabelCertificates.Minority003.certificate72 := by decide +kernel
theorem exponentialBound72 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch018.certificate216).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate144).dm (WitnessCertificates.Batch007.certificate144).beta) ≤ (2*exp (-((CountingCertificates.Batch007.certificate144).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch018.certificate216).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch018.certificate217).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch007.certificate144).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch018.certificate216 MergedCutGroups.Batch018.certificate217 CountingCertificates.Batch007.certificate144 CutLabelCertificates.Entropy003.certificate73 CutLabelCertificates.Minority003.certificate72 matches72 rfl rfl
    MergedCutGroups.Batch018.numericValid216 MergedCutGroups.Batch018.numericValid217 MergedCutGroups.Batch018.cellsSound216 MergedCutGroups.Batch018.cellsSound217
    MergedCutGroups.Batch018.cellsNumeric216 MergedCutGroups.Batch018.cellsNumeric217 MergedCutGroups.Batch018.populationMatches216 MergedCutGroups.Batch018.populationMatches217
    PopulationCertificates.Batch007.valid144 PopulationCertificates.Batch007.sound144 WitnessCertificates.Batch007.valid144 WitnessCertificates.Batch007.sound144 CountingCertificates.Batch007.valid144 CountingCertificates.Batch007.sound144
    CutLabelCertificates.Entropy003.valid73 CutLabelCertificates.Minority003.valid72 CutLabelCertificates.Minority003.sound72 H st hI
theorem probabilityBound72 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch018.certificate216).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate144).dm (WitnessCertificates.Batch007.certificate144).beta) ≤ ((CutFailureCertificates.Budget007.certificate144).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound144 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate144).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch018.certificate216).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch018.certificate217).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch007.certificate144).omega:ℝ) ≤ ((CutFailureCertificates.Budget007.certificate144).bound:ℝ) at hb
  exact (exponentialBound72 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches73 : (MergedCutGroups.Batch018.certificate219).GlobalMatches MergedCutGroups.Batch018.certificate220 CountingCertificates.Batch007.certificate146 CutLabelCertificates.Entropy003.certificate74 CutLabelCertificates.Minority003.certificate73 := by decide +kernel
theorem exponentialBound73 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch018.certificate219).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate146).dm (WitnessCertificates.Batch007.certificate146).beta) ≤ (2*exp (-((CountingCertificates.Batch007.certificate146).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch018.certificate219).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch018.certificate220).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch007.certificate146).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch018.certificate219 MergedCutGroups.Batch018.certificate220 CountingCertificates.Batch007.certificate146 CutLabelCertificates.Entropy003.certificate74 CutLabelCertificates.Minority003.certificate73 matches73 rfl rfl
    MergedCutGroups.Batch018.numericValid219 MergedCutGroups.Batch018.numericValid220 MergedCutGroups.Batch018.cellsSound219 MergedCutGroups.Batch018.cellsSound220
    MergedCutGroups.Batch018.cellsNumeric219 MergedCutGroups.Batch018.cellsNumeric220 MergedCutGroups.Batch018.populationMatches219 MergedCutGroups.Batch018.populationMatches220
    PopulationCertificates.Batch007.valid146 PopulationCertificates.Batch007.sound146 WitnessCertificates.Batch007.valid146 WitnessCertificates.Batch007.sound146 CountingCertificates.Batch007.valid146 CountingCertificates.Batch007.sound146
    CutLabelCertificates.Entropy003.valid74 CutLabelCertificates.Minority003.valid73 CutLabelCertificates.Minority003.sound73 H st hI
theorem probabilityBound73 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch018.certificate219).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate146).dm (WitnessCertificates.Batch007.certificate146).beta) ≤ ((CutFailureCertificates.Budget007.certificate146).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound146 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate146).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch018.certificate219).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch018.certificate220).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch007.certificate146).omega:ℝ) ≤ ((CutFailureCertificates.Budget007.certificate146).bound:ℝ) at hb
  exact (exponentialBound73 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches74 : (MergedCutGroups.Batch018.certificate222).GlobalMatches MergedCutGroups.Batch018.certificate223 CountingCertificates.Batch007.certificate148 CutLabelCertificates.Entropy003.certificate75 CutLabelCertificates.Minority003.certificate74 := by decide +kernel
theorem exponentialBound74 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch018.certificate222).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate148).dm (WitnessCertificates.Batch007.certificate148).beta) ≤ (2*exp (-((CountingCertificates.Batch007.certificate148).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch018.certificate222).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch018.certificate223).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch007.certificate148).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch018.certificate222 MergedCutGroups.Batch018.certificate223 CountingCertificates.Batch007.certificate148 CutLabelCertificates.Entropy003.certificate75 CutLabelCertificates.Minority003.certificate74 matches74 rfl rfl
    MergedCutGroups.Batch018.numericValid222 MergedCutGroups.Batch018.numericValid223 MergedCutGroups.Batch018.cellsSound222 MergedCutGroups.Batch018.cellsSound223
    MergedCutGroups.Batch018.cellsNumeric222 MergedCutGroups.Batch018.cellsNumeric223 MergedCutGroups.Batch018.populationMatches222 MergedCutGroups.Batch018.populationMatches223
    PopulationCertificates.Batch007.valid148 PopulationCertificates.Batch007.sound148 WitnessCertificates.Batch007.valid148 WitnessCertificates.Batch007.sound148 CountingCertificates.Batch007.valid148 CountingCertificates.Batch007.sound148
    CutLabelCertificates.Entropy003.valid75 CutLabelCertificates.Minority003.valid74 CutLabelCertificates.Minority003.sound74 H st hI
theorem probabilityBound74 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch018.certificate222).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate148).dm (WitnessCertificates.Batch007.certificate148).beta) ≤ ((CutFailureCertificates.Budget007.certificate148).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound148 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate148).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch018.certificate222).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch018.certificate223).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch007.certificate148).omega:ℝ) ≤ ((CutFailureCertificates.Budget007.certificate148).bound:ℝ) at hb
  exact (exponentialBound74 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches75 : (MergedCutGroups.Batch018.certificate225).GlobalMatches MergedCutGroups.Batch018.certificate226 CountingCertificates.Batch007.certificate150 CutLabelCertificates.Entropy003.certificate76 CutLabelCertificates.Minority003.certificate75 := by decide +kernel
theorem exponentialBound75 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch018.certificate225).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate150).dm (WitnessCertificates.Batch007.certificate150).beta) ≤ (2*exp (-((CountingCertificates.Batch007.certificate150).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch018.certificate225).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch018.certificate226).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch007.certificate150).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch018.certificate225 MergedCutGroups.Batch018.certificate226 CountingCertificates.Batch007.certificate150 CutLabelCertificates.Entropy003.certificate76 CutLabelCertificates.Minority003.certificate75 matches75 rfl rfl
    MergedCutGroups.Batch018.numericValid225 MergedCutGroups.Batch018.numericValid226 MergedCutGroups.Batch018.cellsSound225 MergedCutGroups.Batch018.cellsSound226
    MergedCutGroups.Batch018.cellsNumeric225 MergedCutGroups.Batch018.cellsNumeric226 MergedCutGroups.Batch018.populationMatches225 MergedCutGroups.Batch018.populationMatches226
    PopulationCertificates.Batch007.valid150 PopulationCertificates.Batch007.sound150 WitnessCertificates.Batch007.valid150 WitnessCertificates.Batch007.sound150 CountingCertificates.Batch007.valid150 CountingCertificates.Batch007.sound150
    CutLabelCertificates.Entropy003.valid76 CutLabelCertificates.Minority003.valid75 CutLabelCertificates.Minority003.sound75 H st hI
theorem probabilityBound75 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch018.certificate225).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate150).dm (WitnessCertificates.Batch007.certificate150).beta) ≤ ((CutFailureCertificates.Budget007.certificate150).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound150 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate150).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch018.certificate225).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch018.certificate226).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch007.certificate150).omega:ℝ) ≤ ((CutFailureCertificates.Budget007.certificate150).bound:ℝ) at hb
  exact (exponentialBound75 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches76 : (MergedCutGroups.Batch019.certificate228).GlobalMatches MergedCutGroups.Batch019.certificate229 CountingCertificates.Batch007.certificate152 CutLabelCertificates.Entropy003.certificate77 CutLabelCertificates.Minority003.certificate76 := by decide +kernel
theorem exponentialBound76 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch019.certificate228).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate152).dm (WitnessCertificates.Batch007.certificate152).beta) ≤ (2*exp (-((CountingCertificates.Batch007.certificate152).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch019.certificate228).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch019.certificate229).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch007.certificate152).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch019.certificate228 MergedCutGroups.Batch019.certificate229 CountingCertificates.Batch007.certificate152 CutLabelCertificates.Entropy003.certificate77 CutLabelCertificates.Minority003.certificate76 matches76 rfl rfl
    MergedCutGroups.Batch019.numericValid228 MergedCutGroups.Batch019.numericValid229 MergedCutGroups.Batch019.cellsSound228 MergedCutGroups.Batch019.cellsSound229
    MergedCutGroups.Batch019.cellsNumeric228 MergedCutGroups.Batch019.cellsNumeric229 MergedCutGroups.Batch019.populationMatches228 MergedCutGroups.Batch019.populationMatches229
    PopulationCertificates.Batch007.valid152 PopulationCertificates.Batch007.sound152 WitnessCertificates.Batch007.valid152 WitnessCertificates.Batch007.sound152 CountingCertificates.Batch007.valid152 CountingCertificates.Batch007.sound152
    CutLabelCertificates.Entropy003.valid77 CutLabelCertificates.Minority003.valid76 CutLabelCertificates.Minority003.sound76 H st hI
theorem probabilityBound76 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch019.certificate228).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate152).dm (WitnessCertificates.Batch007.certificate152).beta) ≤ ((CutFailureCertificates.Budget007.certificate152).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound152 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate152).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch019.certificate228).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch019.certificate229).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch007.certificate152).omega:ℝ) ≤ ((CutFailureCertificates.Budget007.certificate152).bound:ℝ) at hb
  exact (exponentialBound76 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches77 : (MergedCutGroups.Batch019.certificate231).GlobalMatches MergedCutGroups.Batch019.certificate232 CountingCertificates.Batch007.certificate154 CutLabelCertificates.Entropy003.certificate78 CutLabelCertificates.Minority003.certificate77 := by decide +kernel
theorem exponentialBound77 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch019.certificate231).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate154).dm (WitnessCertificates.Batch007.certificate154).beta) ≤ (2*exp (-((CountingCertificates.Batch007.certificate154).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch019.certificate231).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch019.certificate232).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch007.certificate154).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch019.certificate231 MergedCutGroups.Batch019.certificate232 CountingCertificates.Batch007.certificate154 CutLabelCertificates.Entropy003.certificate78 CutLabelCertificates.Minority003.certificate77 matches77 rfl rfl
    MergedCutGroups.Batch019.numericValid231 MergedCutGroups.Batch019.numericValid232 MergedCutGroups.Batch019.cellsSound231 MergedCutGroups.Batch019.cellsSound232
    MergedCutGroups.Batch019.cellsNumeric231 MergedCutGroups.Batch019.cellsNumeric232 MergedCutGroups.Batch019.populationMatches231 MergedCutGroups.Batch019.populationMatches232
    PopulationCertificates.Batch007.valid154 PopulationCertificates.Batch007.sound154 WitnessCertificates.Batch007.valid154 WitnessCertificates.Batch007.sound154 CountingCertificates.Batch007.valid154 CountingCertificates.Batch007.sound154
    CutLabelCertificates.Entropy003.valid78 CutLabelCertificates.Minority003.valid77 CutLabelCertificates.Minority003.sound77 H st hI
theorem probabilityBound77 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch019.certificate231).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate154).dm (WitnessCertificates.Batch007.certificate154).beta) ≤ ((CutFailureCertificates.Budget007.certificate154).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound154 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate154).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch019.certificate231).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch019.certificate232).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch007.certificate154).omega:ℝ) ≤ ((CutFailureCertificates.Budget007.certificate154).bound:ℝ) at hb
  exact (exponentialBound77 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches78 : (MergedCutGroups.Batch019.certificate234).GlobalMatches MergedCutGroups.Batch019.certificate235 CountingCertificates.Batch007.certificate156 CutLabelCertificates.Entropy003.certificate79 CutLabelCertificates.Minority003.certificate78 := by decide +kernel
theorem exponentialBound78 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch019.certificate234).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate156).dm (WitnessCertificates.Batch007.certificate156).beta) ≤ (2*exp (-((CountingCertificates.Batch007.certificate156).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch019.certificate234).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch019.certificate235).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch007.certificate156).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch019.certificate234 MergedCutGroups.Batch019.certificate235 CountingCertificates.Batch007.certificate156 CutLabelCertificates.Entropy003.certificate79 CutLabelCertificates.Minority003.certificate78 matches78 rfl rfl
    MergedCutGroups.Batch019.numericValid234 MergedCutGroups.Batch019.numericValid235 MergedCutGroups.Batch019.cellsSound234 MergedCutGroups.Batch019.cellsSound235
    MergedCutGroups.Batch019.cellsNumeric234 MergedCutGroups.Batch019.cellsNumeric235 MergedCutGroups.Batch019.populationMatches234 MergedCutGroups.Batch019.populationMatches235
    PopulationCertificates.Batch007.valid156 PopulationCertificates.Batch007.sound156 WitnessCertificates.Batch007.valid156 WitnessCertificates.Batch007.sound156 CountingCertificates.Batch007.valid156 CountingCertificates.Batch007.sound156
    CutLabelCertificates.Entropy003.valid79 CutLabelCertificates.Minority003.valid78 CutLabelCertificates.Minority003.sound78 H st hI
theorem probabilityBound78 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch019.certificate234).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate156).dm (WitnessCertificates.Batch007.certificate156).beta) ≤ ((CutFailureCertificates.Budget007.certificate156).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound156 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate156).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch019.certificate234).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch019.certificate235).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch007.certificate156).omega:ℝ) ≤ ((CutFailureCertificates.Budget007.certificate156).bound:ℝ) at hb
  exact (exponentialBound78 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches79 : (MergedCutGroups.Batch019.certificate237).GlobalMatches MergedCutGroups.Batch019.certificate238 CountingCertificates.Batch007.certificate158 CutLabelCertificates.Entropy004.certificate80 CutLabelCertificates.Minority003.certificate79 := by decide +kernel
theorem exponentialBound79 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch019.certificate237).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate158).dm (WitnessCertificates.Batch007.certificate158).beta) ≤ (2*exp (-((CountingCertificates.Batch007.certificate158).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch019.certificate237).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch019.certificate238).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch007.certificate158).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch019.certificate237 MergedCutGroups.Batch019.certificate238 CountingCertificates.Batch007.certificate158 CutLabelCertificates.Entropy004.certificate80 CutLabelCertificates.Minority003.certificate79 matches79 rfl rfl
    MergedCutGroups.Batch019.numericValid237 MergedCutGroups.Batch019.numericValid238 MergedCutGroups.Batch019.cellsSound237 MergedCutGroups.Batch019.cellsSound238
    MergedCutGroups.Batch019.cellsNumeric237 MergedCutGroups.Batch019.cellsNumeric238 MergedCutGroups.Batch019.populationMatches237 MergedCutGroups.Batch019.populationMatches238
    PopulationCertificates.Batch007.valid158 PopulationCertificates.Batch007.sound158 WitnessCertificates.Batch007.valid158 WitnessCertificates.Batch007.sound158 CountingCertificates.Batch007.valid158 CountingCertificates.Batch007.sound158
    CutLabelCertificates.Entropy004.valid80 CutLabelCertificates.Minority003.valid79 CutLabelCertificates.Minority003.sound79 H st hI
theorem probabilityBound79 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch019.certificate237).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch007.certificate158).dm (WitnessCertificates.Batch007.certificate158).beta) ≤ ((CutFailureCertificates.Budget007.certificate158).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget007.sound158 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch007.certificate158).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch019.certificate237).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch019.certificate238).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch007.certificate158).omega:ℝ) ≤ ((CutFailureCertificates.Budget007.certificate158).bound:ℝ) at hb
  exact (exponentialBound79 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch003
