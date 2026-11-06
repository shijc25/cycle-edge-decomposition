import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch040
import Cycle12.CountingCertificates.Batch041
import Cycle12.CountingCertificates.Batch042
import Cycle12.CutFailureCertificates.Budget040
import Cycle12.CutFailureCertificates.Budget041
import Cycle12.CutFailureCertificates.Budget042
import Cycle12.CutLabelCertificates.Entropy020
import Cycle12.CutLabelCertificates.Entropy021
import Cycle12.CutLabelCertificates.Minority020
import Cycle12.CutLabelCertificates.Minority021
import Cycle12.MergedCutGroups.Batch100
import Cycle12.MergedCutGroups.Batch101
import Cycle12.MergedCutGroups.Batch102
import Cycle12.MergedCutGroups.Batch103
import Cycle12.MergedCutGroups.Batch104
import Cycle12.MergedCutGroups.Batch105
import Cycle12.PopulationCertificates.Batch040
import Cycle12.PopulationCertificates.Batch041
import Cycle12.PopulationCertificates.Batch042
import Cycle12.WitnessCertificates.Batch040
import Cycle12.WitnessCertificates.Batch041
import Cycle12.WitnessCertificates.Batch042

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch020
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches400 : (MergedCutGroups.Batch100.certificate1200).GlobalMatches MergedCutGroups.Batch100.certificate1201 CountingCertificates.Batch040.certificate800 CutLabelCertificates.Entropy020.certificate401 CutLabelCertificates.Minority020.certificate400 := by decide +kernel
theorem exponentialBound400 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch100.certificate1200).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate800).dm (WitnessCertificates.Batch040.certificate800).beta) ≤ (2*exp (-((CountingCertificates.Batch040.certificate800).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch100.certificate1200).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch100.certificate1201).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch040.certificate800).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch100.certificate1200 MergedCutGroups.Batch100.certificate1201 CountingCertificates.Batch040.certificate800 CutLabelCertificates.Entropy020.certificate401 CutLabelCertificates.Minority020.certificate400 matches400 rfl rfl
    MergedCutGroups.Batch100.numericValid1200 MergedCutGroups.Batch100.numericValid1201 MergedCutGroups.Batch100.cellsSound1200 MergedCutGroups.Batch100.cellsSound1201
    MergedCutGroups.Batch100.cellsNumeric1200 MergedCutGroups.Batch100.cellsNumeric1201 MergedCutGroups.Batch100.populationMatches1200 MergedCutGroups.Batch100.populationMatches1201
    PopulationCertificates.Batch040.valid800 PopulationCertificates.Batch040.sound800 WitnessCertificates.Batch040.valid800 WitnessCertificates.Batch040.sound800 CountingCertificates.Batch040.valid800 CountingCertificates.Batch040.sound800
    CutLabelCertificates.Entropy020.valid401 CutLabelCertificates.Minority020.valid400 CutLabelCertificates.Minority020.sound400 H st hI
theorem probabilityBound400 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch100.certificate1200).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate800).dm (WitnessCertificates.Batch040.certificate800).beta) ≤ ((CutFailureCertificates.Budget040.certificate800).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound800 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate800).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch100.certificate1200).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch100.certificate1201).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch040.certificate800).omega:ℝ) ≤ ((CutFailureCertificates.Budget040.certificate800).bound:ℝ) at hb
  exact (exponentialBound400 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches401 : (MergedCutGroups.Batch100.certificate1203).GlobalMatches MergedCutGroups.Batch100.certificate1204 CountingCertificates.Batch040.certificate802 CutLabelCertificates.Entropy020.certificate402 CutLabelCertificates.Minority020.certificate401 := by decide +kernel
theorem exponentialBound401 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch100.certificate1203).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate802).dm (WitnessCertificates.Batch040.certificate802).beta) ≤ (2*exp (-((CountingCertificates.Batch040.certificate802).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch100.certificate1203).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch100.certificate1204).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch040.certificate802).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch100.certificate1203 MergedCutGroups.Batch100.certificate1204 CountingCertificates.Batch040.certificate802 CutLabelCertificates.Entropy020.certificate402 CutLabelCertificates.Minority020.certificate401 matches401 rfl rfl
    MergedCutGroups.Batch100.numericValid1203 MergedCutGroups.Batch100.numericValid1204 MergedCutGroups.Batch100.cellsSound1203 MergedCutGroups.Batch100.cellsSound1204
    MergedCutGroups.Batch100.cellsNumeric1203 MergedCutGroups.Batch100.cellsNumeric1204 MergedCutGroups.Batch100.populationMatches1203 MergedCutGroups.Batch100.populationMatches1204
    PopulationCertificates.Batch040.valid802 PopulationCertificates.Batch040.sound802 WitnessCertificates.Batch040.valid802 WitnessCertificates.Batch040.sound802 CountingCertificates.Batch040.valid802 CountingCertificates.Batch040.sound802
    CutLabelCertificates.Entropy020.valid402 CutLabelCertificates.Minority020.valid401 CutLabelCertificates.Minority020.sound401 H st hI
theorem probabilityBound401 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch100.certificate1203).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate802).dm (WitnessCertificates.Batch040.certificate802).beta) ≤ ((CutFailureCertificates.Budget040.certificate802).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound802 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate802).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch100.certificate1203).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch100.certificate1204).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch040.certificate802).omega:ℝ) ≤ ((CutFailureCertificates.Budget040.certificate802).bound:ℝ) at hb
  exact (exponentialBound401 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches402 : (MergedCutGroups.Batch100.certificate1206).GlobalMatches MergedCutGroups.Batch100.certificate1207 CountingCertificates.Batch040.certificate804 CutLabelCertificates.Entropy020.certificate403 CutLabelCertificates.Minority020.certificate402 := by decide +kernel
theorem exponentialBound402 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch100.certificate1206).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate804).dm (WitnessCertificates.Batch040.certificate804).beta) ≤ (2*exp (-((CountingCertificates.Batch040.certificate804).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch100.certificate1206).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch100.certificate1207).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch040.certificate804).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch100.certificate1206 MergedCutGroups.Batch100.certificate1207 CountingCertificates.Batch040.certificate804 CutLabelCertificates.Entropy020.certificate403 CutLabelCertificates.Minority020.certificate402 matches402 rfl rfl
    MergedCutGroups.Batch100.numericValid1206 MergedCutGroups.Batch100.numericValid1207 MergedCutGroups.Batch100.cellsSound1206 MergedCutGroups.Batch100.cellsSound1207
    MergedCutGroups.Batch100.cellsNumeric1206 MergedCutGroups.Batch100.cellsNumeric1207 MergedCutGroups.Batch100.populationMatches1206 MergedCutGroups.Batch100.populationMatches1207
    PopulationCertificates.Batch040.valid804 PopulationCertificates.Batch040.sound804 WitnessCertificates.Batch040.valid804 WitnessCertificates.Batch040.sound804 CountingCertificates.Batch040.valid804 CountingCertificates.Batch040.sound804
    CutLabelCertificates.Entropy020.valid403 CutLabelCertificates.Minority020.valid402 CutLabelCertificates.Minority020.sound402 H st hI
theorem probabilityBound402 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch100.certificate1206).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate804).dm (WitnessCertificates.Batch040.certificate804).beta) ≤ ((CutFailureCertificates.Budget040.certificate804).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound804 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate804).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch100.certificate1206).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch100.certificate1207).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch040.certificate804).omega:ℝ) ≤ ((CutFailureCertificates.Budget040.certificate804).bound:ℝ) at hb
  exact (exponentialBound402 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches403 : (MergedCutGroups.Batch100.certificate1209).GlobalMatches MergedCutGroups.Batch100.certificate1210 CountingCertificates.Batch040.certificate806 CutLabelCertificates.Entropy020.certificate404 CutLabelCertificates.Minority020.certificate403 := by decide +kernel
theorem exponentialBound403 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch100.certificate1209).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate806).dm (WitnessCertificates.Batch040.certificate806).beta) ≤ (2*exp (-((CountingCertificates.Batch040.certificate806).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch100.certificate1209).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch100.certificate1210).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch040.certificate806).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch100.certificate1209 MergedCutGroups.Batch100.certificate1210 CountingCertificates.Batch040.certificate806 CutLabelCertificates.Entropy020.certificate404 CutLabelCertificates.Minority020.certificate403 matches403 rfl rfl
    MergedCutGroups.Batch100.numericValid1209 MergedCutGroups.Batch100.numericValid1210 MergedCutGroups.Batch100.cellsSound1209 MergedCutGroups.Batch100.cellsSound1210
    MergedCutGroups.Batch100.cellsNumeric1209 MergedCutGroups.Batch100.cellsNumeric1210 MergedCutGroups.Batch100.populationMatches1209 MergedCutGroups.Batch100.populationMatches1210
    PopulationCertificates.Batch040.valid806 PopulationCertificates.Batch040.sound806 WitnessCertificates.Batch040.valid806 WitnessCertificates.Batch040.sound806 CountingCertificates.Batch040.valid806 CountingCertificates.Batch040.sound806
    CutLabelCertificates.Entropy020.valid404 CutLabelCertificates.Minority020.valid403 CutLabelCertificates.Minority020.sound403 H st hI
theorem probabilityBound403 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch100.certificate1209).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate806).dm (WitnessCertificates.Batch040.certificate806).beta) ≤ ((CutFailureCertificates.Budget040.certificate806).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound806 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate806).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch100.certificate1209).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch100.certificate1210).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch040.certificate806).omega:ℝ) ≤ ((CutFailureCertificates.Budget040.certificate806).bound:ℝ) at hb
  exact (exponentialBound403 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches404 : (MergedCutGroups.Batch101.certificate1212).GlobalMatches MergedCutGroups.Batch101.certificate1213 CountingCertificates.Batch040.certificate808 CutLabelCertificates.Entropy020.certificate405 CutLabelCertificates.Minority020.certificate404 := by decide +kernel
theorem exponentialBound404 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch101.certificate1212).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate808).dm (WitnessCertificates.Batch040.certificate808).beta) ≤ (2*exp (-((CountingCertificates.Batch040.certificate808).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch101.certificate1212).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch101.certificate1213).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch040.certificate808).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch101.certificate1212 MergedCutGroups.Batch101.certificate1213 CountingCertificates.Batch040.certificate808 CutLabelCertificates.Entropy020.certificate405 CutLabelCertificates.Minority020.certificate404 matches404 rfl rfl
    MergedCutGroups.Batch101.numericValid1212 MergedCutGroups.Batch101.numericValid1213 MergedCutGroups.Batch101.cellsSound1212 MergedCutGroups.Batch101.cellsSound1213
    MergedCutGroups.Batch101.cellsNumeric1212 MergedCutGroups.Batch101.cellsNumeric1213 MergedCutGroups.Batch101.populationMatches1212 MergedCutGroups.Batch101.populationMatches1213
    PopulationCertificates.Batch040.valid808 PopulationCertificates.Batch040.sound808 WitnessCertificates.Batch040.valid808 WitnessCertificates.Batch040.sound808 CountingCertificates.Batch040.valid808 CountingCertificates.Batch040.sound808
    CutLabelCertificates.Entropy020.valid405 CutLabelCertificates.Minority020.valid404 CutLabelCertificates.Minority020.sound404 H st hI
theorem probabilityBound404 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch101.certificate1212).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate808).dm (WitnessCertificates.Batch040.certificate808).beta) ≤ ((CutFailureCertificates.Budget040.certificate808).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound808 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate808).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch101.certificate1212).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch101.certificate1213).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch040.certificate808).omega:ℝ) ≤ ((CutFailureCertificates.Budget040.certificate808).bound:ℝ) at hb
  exact (exponentialBound404 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches405 : (MergedCutGroups.Batch101.certificate1215).GlobalMatches MergedCutGroups.Batch101.certificate1216 CountingCertificates.Batch040.certificate810 CutLabelCertificates.Entropy020.certificate406 CutLabelCertificates.Minority020.certificate405 := by decide +kernel
theorem exponentialBound405 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch101.certificate1215).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate810).dm (WitnessCertificates.Batch040.certificate810).beta) ≤ (2*exp (-((CountingCertificates.Batch040.certificate810).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch101.certificate1215).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch101.certificate1216).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch040.certificate810).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch101.certificate1215 MergedCutGroups.Batch101.certificate1216 CountingCertificates.Batch040.certificate810 CutLabelCertificates.Entropy020.certificate406 CutLabelCertificates.Minority020.certificate405 matches405 rfl rfl
    MergedCutGroups.Batch101.numericValid1215 MergedCutGroups.Batch101.numericValid1216 MergedCutGroups.Batch101.cellsSound1215 MergedCutGroups.Batch101.cellsSound1216
    MergedCutGroups.Batch101.cellsNumeric1215 MergedCutGroups.Batch101.cellsNumeric1216 MergedCutGroups.Batch101.populationMatches1215 MergedCutGroups.Batch101.populationMatches1216
    PopulationCertificates.Batch040.valid810 PopulationCertificates.Batch040.sound810 WitnessCertificates.Batch040.valid810 WitnessCertificates.Batch040.sound810 CountingCertificates.Batch040.valid810 CountingCertificates.Batch040.sound810
    CutLabelCertificates.Entropy020.valid406 CutLabelCertificates.Minority020.valid405 CutLabelCertificates.Minority020.sound405 H st hI
theorem probabilityBound405 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch101.certificate1215).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate810).dm (WitnessCertificates.Batch040.certificate810).beta) ≤ ((CutFailureCertificates.Budget040.certificate810).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound810 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate810).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch101.certificate1215).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch101.certificate1216).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch040.certificate810).omega:ℝ) ≤ ((CutFailureCertificates.Budget040.certificate810).bound:ℝ) at hb
  exact (exponentialBound405 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches406 : (MergedCutGroups.Batch101.certificate1218).GlobalMatches MergedCutGroups.Batch101.certificate1219 CountingCertificates.Batch040.certificate812 CutLabelCertificates.Entropy020.certificate407 CutLabelCertificates.Minority020.certificate406 := by decide +kernel
theorem exponentialBound406 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch101.certificate1218).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate812).dm (WitnessCertificates.Batch040.certificate812).beta) ≤ (2*exp (-((CountingCertificates.Batch040.certificate812).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch101.certificate1218).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch101.certificate1219).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch040.certificate812).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch101.certificate1218 MergedCutGroups.Batch101.certificate1219 CountingCertificates.Batch040.certificate812 CutLabelCertificates.Entropy020.certificate407 CutLabelCertificates.Minority020.certificate406 matches406 rfl rfl
    MergedCutGroups.Batch101.numericValid1218 MergedCutGroups.Batch101.numericValid1219 MergedCutGroups.Batch101.cellsSound1218 MergedCutGroups.Batch101.cellsSound1219
    MergedCutGroups.Batch101.cellsNumeric1218 MergedCutGroups.Batch101.cellsNumeric1219 MergedCutGroups.Batch101.populationMatches1218 MergedCutGroups.Batch101.populationMatches1219
    PopulationCertificates.Batch040.valid812 PopulationCertificates.Batch040.sound812 WitnessCertificates.Batch040.valid812 WitnessCertificates.Batch040.sound812 CountingCertificates.Batch040.valid812 CountingCertificates.Batch040.sound812
    CutLabelCertificates.Entropy020.valid407 CutLabelCertificates.Minority020.valid406 CutLabelCertificates.Minority020.sound406 H st hI
theorem probabilityBound406 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch101.certificate1218).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate812).dm (WitnessCertificates.Batch040.certificate812).beta) ≤ ((CutFailureCertificates.Budget040.certificate812).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound812 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate812).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch101.certificate1218).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch101.certificate1219).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch040.certificate812).omega:ℝ) ≤ ((CutFailureCertificates.Budget040.certificate812).bound:ℝ) at hb
  exact (exponentialBound406 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches407 : (MergedCutGroups.Batch101.certificate1221).GlobalMatches MergedCutGroups.Batch101.certificate1222 CountingCertificates.Batch040.certificate814 CutLabelCertificates.Entropy020.certificate408 CutLabelCertificates.Minority020.certificate407 := by decide +kernel
theorem exponentialBound407 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch101.certificate1221).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate814).dm (WitnessCertificates.Batch040.certificate814).beta) ≤ (2*exp (-((CountingCertificates.Batch040.certificate814).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch101.certificate1221).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch101.certificate1222).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch040.certificate814).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch101.certificate1221 MergedCutGroups.Batch101.certificate1222 CountingCertificates.Batch040.certificate814 CutLabelCertificates.Entropy020.certificate408 CutLabelCertificates.Minority020.certificate407 matches407 rfl rfl
    MergedCutGroups.Batch101.numericValid1221 MergedCutGroups.Batch101.numericValid1222 MergedCutGroups.Batch101.cellsSound1221 MergedCutGroups.Batch101.cellsSound1222
    MergedCutGroups.Batch101.cellsNumeric1221 MergedCutGroups.Batch101.cellsNumeric1222 MergedCutGroups.Batch101.populationMatches1221 MergedCutGroups.Batch101.populationMatches1222
    PopulationCertificates.Batch040.valid814 PopulationCertificates.Batch040.sound814 WitnessCertificates.Batch040.valid814 WitnessCertificates.Batch040.sound814 CountingCertificates.Batch040.valid814 CountingCertificates.Batch040.sound814
    CutLabelCertificates.Entropy020.valid408 CutLabelCertificates.Minority020.valid407 CutLabelCertificates.Minority020.sound407 H st hI
theorem probabilityBound407 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch101.certificate1221).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate814).dm (WitnessCertificates.Batch040.certificate814).beta) ≤ ((CutFailureCertificates.Budget040.certificate814).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound814 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate814).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch101.certificate1221).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch101.certificate1222).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch040.certificate814).omega:ℝ) ≤ ((CutFailureCertificates.Budget040.certificate814).bound:ℝ) at hb
  exact (exponentialBound407 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches408 : (MergedCutGroups.Batch102.certificate1224).GlobalMatches MergedCutGroups.Batch102.certificate1225 CountingCertificates.Batch040.certificate816 CutLabelCertificates.Entropy020.certificate409 CutLabelCertificates.Minority020.certificate408 := by decide +kernel
theorem exponentialBound408 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch102.certificate1224).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate816).dm (WitnessCertificates.Batch040.certificate816).beta) ≤ (2*exp (-((CountingCertificates.Batch040.certificate816).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch102.certificate1224).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch102.certificate1225).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch040.certificate816).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch102.certificate1224 MergedCutGroups.Batch102.certificate1225 CountingCertificates.Batch040.certificate816 CutLabelCertificates.Entropy020.certificate409 CutLabelCertificates.Minority020.certificate408 matches408 rfl rfl
    MergedCutGroups.Batch102.numericValid1224 MergedCutGroups.Batch102.numericValid1225 MergedCutGroups.Batch102.cellsSound1224 MergedCutGroups.Batch102.cellsSound1225
    MergedCutGroups.Batch102.cellsNumeric1224 MergedCutGroups.Batch102.cellsNumeric1225 MergedCutGroups.Batch102.populationMatches1224 MergedCutGroups.Batch102.populationMatches1225
    PopulationCertificates.Batch040.valid816 PopulationCertificates.Batch040.sound816 WitnessCertificates.Batch040.valid816 WitnessCertificates.Batch040.sound816 CountingCertificates.Batch040.valid816 CountingCertificates.Batch040.sound816
    CutLabelCertificates.Entropy020.valid409 CutLabelCertificates.Minority020.valid408 CutLabelCertificates.Minority020.sound408 H st hI
theorem probabilityBound408 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch102.certificate1224).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate816).dm (WitnessCertificates.Batch040.certificate816).beta) ≤ ((CutFailureCertificates.Budget040.certificate816).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound816 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate816).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch102.certificate1224).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch102.certificate1225).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch040.certificate816).omega:ℝ) ≤ ((CutFailureCertificates.Budget040.certificate816).bound:ℝ) at hb
  exact (exponentialBound408 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches409 : (MergedCutGroups.Batch102.certificate1227).GlobalMatches MergedCutGroups.Batch102.certificate1228 CountingCertificates.Batch040.certificate818 CutLabelCertificates.Entropy020.certificate410 CutLabelCertificates.Minority020.certificate409 := by decide +kernel
theorem exponentialBound409 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch102.certificate1227).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate818).dm (WitnessCertificates.Batch040.certificate818).beta) ≤ (2*exp (-((CountingCertificates.Batch040.certificate818).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch102.certificate1227).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch102.certificate1228).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch040.certificate818).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch102.certificate1227 MergedCutGroups.Batch102.certificate1228 CountingCertificates.Batch040.certificate818 CutLabelCertificates.Entropy020.certificate410 CutLabelCertificates.Minority020.certificate409 matches409 rfl rfl
    MergedCutGroups.Batch102.numericValid1227 MergedCutGroups.Batch102.numericValid1228 MergedCutGroups.Batch102.cellsSound1227 MergedCutGroups.Batch102.cellsSound1228
    MergedCutGroups.Batch102.cellsNumeric1227 MergedCutGroups.Batch102.cellsNumeric1228 MergedCutGroups.Batch102.populationMatches1227 MergedCutGroups.Batch102.populationMatches1228
    PopulationCertificates.Batch040.valid818 PopulationCertificates.Batch040.sound818 WitnessCertificates.Batch040.valid818 WitnessCertificates.Batch040.sound818 CountingCertificates.Batch040.valid818 CountingCertificates.Batch040.sound818
    CutLabelCertificates.Entropy020.valid410 CutLabelCertificates.Minority020.valid409 CutLabelCertificates.Minority020.sound409 H st hI
theorem probabilityBound409 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch102.certificate1227).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch040.certificate818).dm (WitnessCertificates.Batch040.certificate818).beta) ≤ ((CutFailureCertificates.Budget040.certificate818).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound818 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate818).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch102.certificate1227).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch102.certificate1228).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch040.certificate818).omega:ℝ) ≤ ((CutFailureCertificates.Budget040.certificate818).bound:ℝ) at hb
  exact (exponentialBound409 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches410 : (MergedCutGroups.Batch102.certificate1230).GlobalMatches MergedCutGroups.Batch102.certificate1231 CountingCertificates.Batch041.certificate820 CutLabelCertificates.Entropy020.certificate411 CutLabelCertificates.Minority020.certificate410 := by decide +kernel
theorem exponentialBound410 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch102.certificate1230).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate820).dm (WitnessCertificates.Batch041.certificate820).beta) ≤ (2*exp (-((CountingCertificates.Batch041.certificate820).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch102.certificate1230).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch102.certificate1231).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch041.certificate820).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch102.certificate1230 MergedCutGroups.Batch102.certificate1231 CountingCertificates.Batch041.certificate820 CutLabelCertificates.Entropy020.certificate411 CutLabelCertificates.Minority020.certificate410 matches410 rfl rfl
    MergedCutGroups.Batch102.numericValid1230 MergedCutGroups.Batch102.numericValid1231 MergedCutGroups.Batch102.cellsSound1230 MergedCutGroups.Batch102.cellsSound1231
    MergedCutGroups.Batch102.cellsNumeric1230 MergedCutGroups.Batch102.cellsNumeric1231 MergedCutGroups.Batch102.populationMatches1230 MergedCutGroups.Batch102.populationMatches1231
    PopulationCertificates.Batch041.valid820 PopulationCertificates.Batch041.sound820 WitnessCertificates.Batch041.valid820 WitnessCertificates.Batch041.sound820 CountingCertificates.Batch041.valid820 CountingCertificates.Batch041.sound820
    CutLabelCertificates.Entropy020.valid411 CutLabelCertificates.Minority020.valid410 CutLabelCertificates.Minority020.sound410 H st hI
theorem probabilityBound410 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch102.certificate1230).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate820).dm (WitnessCertificates.Batch041.certificate820).beta) ≤ ((CutFailureCertificates.Budget041.certificate820).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound820 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate820).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch102.certificate1230).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch102.certificate1231).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch041.certificate820).omega:ℝ) ≤ ((CutFailureCertificates.Budget041.certificate820).bound:ℝ) at hb
  exact (exponentialBound410 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches411 : (MergedCutGroups.Batch102.certificate1233).GlobalMatches MergedCutGroups.Batch102.certificate1234 CountingCertificates.Batch041.certificate822 CutLabelCertificates.Entropy020.certificate412 CutLabelCertificates.Minority020.certificate411 := by decide +kernel
theorem exponentialBound411 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch102.certificate1233).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate822).dm (WitnessCertificates.Batch041.certificate822).beta) ≤ (2*exp (-((CountingCertificates.Batch041.certificate822).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch102.certificate1233).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch102.certificate1234).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch041.certificate822).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch102.certificate1233 MergedCutGroups.Batch102.certificate1234 CountingCertificates.Batch041.certificate822 CutLabelCertificates.Entropy020.certificate412 CutLabelCertificates.Minority020.certificate411 matches411 rfl rfl
    MergedCutGroups.Batch102.numericValid1233 MergedCutGroups.Batch102.numericValid1234 MergedCutGroups.Batch102.cellsSound1233 MergedCutGroups.Batch102.cellsSound1234
    MergedCutGroups.Batch102.cellsNumeric1233 MergedCutGroups.Batch102.cellsNumeric1234 MergedCutGroups.Batch102.populationMatches1233 MergedCutGroups.Batch102.populationMatches1234
    PopulationCertificates.Batch041.valid822 PopulationCertificates.Batch041.sound822 WitnessCertificates.Batch041.valid822 WitnessCertificates.Batch041.sound822 CountingCertificates.Batch041.valid822 CountingCertificates.Batch041.sound822
    CutLabelCertificates.Entropy020.valid412 CutLabelCertificates.Minority020.valid411 CutLabelCertificates.Minority020.sound411 H st hI
theorem probabilityBound411 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch102.certificate1233).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate822).dm (WitnessCertificates.Batch041.certificate822).beta) ≤ ((CutFailureCertificates.Budget041.certificate822).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound822 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate822).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch102.certificate1233).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch102.certificate1234).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch041.certificate822).omega:ℝ) ≤ ((CutFailureCertificates.Budget041.certificate822).bound:ℝ) at hb
  exact (exponentialBound411 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches412 : (MergedCutGroups.Batch103.certificate1236).GlobalMatches MergedCutGroups.Batch103.certificate1237 CountingCertificates.Batch041.certificate824 CutLabelCertificates.Entropy020.certificate413 CutLabelCertificates.Minority020.certificate412 := by decide +kernel
theorem exponentialBound412 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch103.certificate1236).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate824).dm (WitnessCertificates.Batch041.certificate824).beta) ≤ (2*exp (-((CountingCertificates.Batch041.certificate824).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch103.certificate1236).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch103.certificate1237).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch041.certificate824).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch103.certificate1236 MergedCutGroups.Batch103.certificate1237 CountingCertificates.Batch041.certificate824 CutLabelCertificates.Entropy020.certificate413 CutLabelCertificates.Minority020.certificate412 matches412 rfl rfl
    MergedCutGroups.Batch103.numericValid1236 MergedCutGroups.Batch103.numericValid1237 MergedCutGroups.Batch103.cellsSound1236 MergedCutGroups.Batch103.cellsSound1237
    MergedCutGroups.Batch103.cellsNumeric1236 MergedCutGroups.Batch103.cellsNumeric1237 MergedCutGroups.Batch103.populationMatches1236 MergedCutGroups.Batch103.populationMatches1237
    PopulationCertificates.Batch041.valid824 PopulationCertificates.Batch041.sound824 WitnessCertificates.Batch041.valid824 WitnessCertificates.Batch041.sound824 CountingCertificates.Batch041.valid824 CountingCertificates.Batch041.sound824
    CutLabelCertificates.Entropy020.valid413 CutLabelCertificates.Minority020.valid412 CutLabelCertificates.Minority020.sound412 H st hI
theorem probabilityBound412 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch103.certificate1236).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate824).dm (WitnessCertificates.Batch041.certificate824).beta) ≤ ((CutFailureCertificates.Budget041.certificate824).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound824 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate824).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch103.certificate1236).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch103.certificate1237).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch041.certificate824).omega:ℝ) ≤ ((CutFailureCertificates.Budget041.certificate824).bound:ℝ) at hb
  exact (exponentialBound412 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches413 : (MergedCutGroups.Batch103.certificate1239).GlobalMatches MergedCutGroups.Batch103.certificate1240 CountingCertificates.Batch041.certificate826 CutLabelCertificates.Entropy020.certificate414 CutLabelCertificates.Minority020.certificate413 := by decide +kernel
theorem exponentialBound413 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch103.certificate1239).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate826).dm (WitnessCertificates.Batch041.certificate826).beta) ≤ (2*exp (-((CountingCertificates.Batch041.certificate826).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch103.certificate1239).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch103.certificate1240).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch041.certificate826).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch103.certificate1239 MergedCutGroups.Batch103.certificate1240 CountingCertificates.Batch041.certificate826 CutLabelCertificates.Entropy020.certificate414 CutLabelCertificates.Minority020.certificate413 matches413 rfl rfl
    MergedCutGroups.Batch103.numericValid1239 MergedCutGroups.Batch103.numericValid1240 MergedCutGroups.Batch103.cellsSound1239 MergedCutGroups.Batch103.cellsSound1240
    MergedCutGroups.Batch103.cellsNumeric1239 MergedCutGroups.Batch103.cellsNumeric1240 MergedCutGroups.Batch103.populationMatches1239 MergedCutGroups.Batch103.populationMatches1240
    PopulationCertificates.Batch041.valid826 PopulationCertificates.Batch041.sound826 WitnessCertificates.Batch041.valid826 WitnessCertificates.Batch041.sound826 CountingCertificates.Batch041.valid826 CountingCertificates.Batch041.sound826
    CutLabelCertificates.Entropy020.valid414 CutLabelCertificates.Minority020.valid413 CutLabelCertificates.Minority020.sound413 H st hI
theorem probabilityBound413 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch103.certificate1239).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate826).dm (WitnessCertificates.Batch041.certificate826).beta) ≤ ((CutFailureCertificates.Budget041.certificate826).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound826 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate826).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch103.certificate1239).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch103.certificate1240).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch041.certificate826).omega:ℝ) ≤ ((CutFailureCertificates.Budget041.certificate826).bound:ℝ) at hb
  exact (exponentialBound413 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches414 : (MergedCutGroups.Batch103.certificate1242).GlobalMatches MergedCutGroups.Batch103.certificate1243 CountingCertificates.Batch041.certificate828 CutLabelCertificates.Entropy020.certificate415 CutLabelCertificates.Minority020.certificate414 := by decide +kernel
theorem exponentialBound414 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch103.certificate1242).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate828).dm (WitnessCertificates.Batch041.certificate828).beta) ≤ (2*exp (-((CountingCertificates.Batch041.certificate828).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch103.certificate1242).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch103.certificate1243).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch041.certificate828).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch103.certificate1242 MergedCutGroups.Batch103.certificate1243 CountingCertificates.Batch041.certificate828 CutLabelCertificates.Entropy020.certificate415 CutLabelCertificates.Minority020.certificate414 matches414 rfl rfl
    MergedCutGroups.Batch103.numericValid1242 MergedCutGroups.Batch103.numericValid1243 MergedCutGroups.Batch103.cellsSound1242 MergedCutGroups.Batch103.cellsSound1243
    MergedCutGroups.Batch103.cellsNumeric1242 MergedCutGroups.Batch103.cellsNumeric1243 MergedCutGroups.Batch103.populationMatches1242 MergedCutGroups.Batch103.populationMatches1243
    PopulationCertificates.Batch041.valid828 PopulationCertificates.Batch041.sound828 WitnessCertificates.Batch041.valid828 WitnessCertificates.Batch041.sound828 CountingCertificates.Batch041.valid828 CountingCertificates.Batch041.sound828
    CutLabelCertificates.Entropy020.valid415 CutLabelCertificates.Minority020.valid414 CutLabelCertificates.Minority020.sound414 H st hI
theorem probabilityBound414 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch103.certificate1242).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate828).dm (WitnessCertificates.Batch041.certificate828).beta) ≤ ((CutFailureCertificates.Budget041.certificate828).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound828 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate828).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch103.certificate1242).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch103.certificate1243).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch041.certificate828).omega:ℝ) ≤ ((CutFailureCertificates.Budget041.certificate828).bound:ℝ) at hb
  exact (exponentialBound414 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches415 : (MergedCutGroups.Batch103.certificate1245).GlobalMatches MergedCutGroups.Batch103.certificate1246 CountingCertificates.Batch041.certificate830 CutLabelCertificates.Entropy020.certificate416 CutLabelCertificates.Minority020.certificate415 := by decide +kernel
theorem exponentialBound415 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch103.certificate1245).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate830).dm (WitnessCertificates.Batch041.certificate830).beta) ≤ (2*exp (-((CountingCertificates.Batch041.certificate830).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch103.certificate1245).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch103.certificate1246).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch041.certificate830).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch103.certificate1245 MergedCutGroups.Batch103.certificate1246 CountingCertificates.Batch041.certificate830 CutLabelCertificates.Entropy020.certificate416 CutLabelCertificates.Minority020.certificate415 matches415 rfl rfl
    MergedCutGroups.Batch103.numericValid1245 MergedCutGroups.Batch103.numericValid1246 MergedCutGroups.Batch103.cellsSound1245 MergedCutGroups.Batch103.cellsSound1246
    MergedCutGroups.Batch103.cellsNumeric1245 MergedCutGroups.Batch103.cellsNumeric1246 MergedCutGroups.Batch103.populationMatches1245 MergedCutGroups.Batch103.populationMatches1246
    PopulationCertificates.Batch041.valid830 PopulationCertificates.Batch041.sound830 WitnessCertificates.Batch041.valid830 WitnessCertificates.Batch041.sound830 CountingCertificates.Batch041.valid830 CountingCertificates.Batch041.sound830
    CutLabelCertificates.Entropy020.valid416 CutLabelCertificates.Minority020.valid415 CutLabelCertificates.Minority020.sound415 H st hI
theorem probabilityBound415 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch103.certificate1245).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate830).dm (WitnessCertificates.Batch041.certificate830).beta) ≤ ((CutFailureCertificates.Budget041.certificate830).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound830 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate830).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch103.certificate1245).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch103.certificate1246).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch041.certificate830).omega:ℝ) ≤ ((CutFailureCertificates.Budget041.certificate830).bound:ℝ) at hb
  exact (exponentialBound415 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches416 : (MergedCutGroups.Batch104.certificate1249).GlobalMatches MergedCutGroups.Batch104.certificate1250 CountingCertificates.Batch041.certificate833 CutLabelCertificates.Entropy021.certificate420 CutLabelCertificates.Minority020.certificate419 := by decide +kernel
theorem exponentialBound416 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch104.certificate1249).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate833).dm (WitnessCertificates.Batch041.certificate833).beta) ≤ (2*exp (-((CountingCertificates.Batch041.certificate833).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch104.certificate1249).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch104.certificate1250).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch041.certificate833).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch104.certificate1249 MergedCutGroups.Batch104.certificate1250 CountingCertificates.Batch041.certificate833 CutLabelCertificates.Entropy021.certificate420 CutLabelCertificates.Minority020.certificate419 matches416 rfl rfl
    MergedCutGroups.Batch104.numericValid1249 MergedCutGroups.Batch104.numericValid1250 MergedCutGroups.Batch104.cellsSound1249 MergedCutGroups.Batch104.cellsSound1250
    MergedCutGroups.Batch104.cellsNumeric1249 MergedCutGroups.Batch104.cellsNumeric1250 MergedCutGroups.Batch104.populationMatches1249 MergedCutGroups.Batch104.populationMatches1250
    PopulationCertificates.Batch041.valid833 PopulationCertificates.Batch041.sound833 WitnessCertificates.Batch041.valid833 WitnessCertificates.Batch041.sound833 CountingCertificates.Batch041.valid833 CountingCertificates.Batch041.sound833
    CutLabelCertificates.Entropy021.valid420 CutLabelCertificates.Minority020.valid419 CutLabelCertificates.Minority020.sound419 H st hI
theorem probabilityBound416 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch104.certificate1249).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate833).dm (WitnessCertificates.Batch041.certificate833).beta) ≤ ((CutFailureCertificates.Budget041.certificate833).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound833 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate833).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch104.certificate1249).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch104.certificate1250).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch041.certificate833).omega:ℝ) ≤ ((CutFailureCertificates.Budget041.certificate833).bound:ℝ) at hb
  exact (exponentialBound416 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches417 : (MergedCutGroups.Batch104.certificate1253).GlobalMatches MergedCutGroups.Batch104.certificate1254 CountingCertificates.Batch041.certificate836 CutLabelCertificates.Entropy021.certificate424 CutLabelCertificates.Minority021.certificate423 := by decide +kernel
theorem exponentialBound417 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch104.certificate1253).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate836).dm (WitnessCertificates.Batch041.certificate836).beta) ≤ (2*exp (-((CountingCertificates.Batch041.certificate836).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch104.certificate1253).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch104.certificate1254).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch041.certificate836).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch104.certificate1253 MergedCutGroups.Batch104.certificate1254 CountingCertificates.Batch041.certificate836 CutLabelCertificates.Entropy021.certificate424 CutLabelCertificates.Minority021.certificate423 matches417 rfl rfl
    MergedCutGroups.Batch104.numericValid1253 MergedCutGroups.Batch104.numericValid1254 MergedCutGroups.Batch104.cellsSound1253 MergedCutGroups.Batch104.cellsSound1254
    MergedCutGroups.Batch104.cellsNumeric1253 MergedCutGroups.Batch104.cellsNumeric1254 MergedCutGroups.Batch104.populationMatches1253 MergedCutGroups.Batch104.populationMatches1254
    PopulationCertificates.Batch041.valid836 PopulationCertificates.Batch041.sound836 WitnessCertificates.Batch041.valid836 WitnessCertificates.Batch041.sound836 CountingCertificates.Batch041.valid836 CountingCertificates.Batch041.sound836
    CutLabelCertificates.Entropy021.valid424 CutLabelCertificates.Minority021.valid423 CutLabelCertificates.Minority021.sound423 H st hI
theorem probabilityBound417 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch104.certificate1253).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate836).dm (WitnessCertificates.Batch041.certificate836).beta) ≤ ((CutFailureCertificates.Budget041.certificate836).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound836 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate836).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch104.certificate1253).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch104.certificate1254).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch041.certificate836).omega:ℝ) ≤ ((CutFailureCertificates.Budget041.certificate836).bound:ℝ) at hb
  exact (exponentialBound417 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches418 : (MergedCutGroups.Batch104.certificate1257).GlobalMatches MergedCutGroups.Batch104.certificate1258 CountingCertificates.Batch041.certificate839 CutLabelCertificates.Entropy021.certificate428 CutLabelCertificates.Minority021.certificate427 := by decide +kernel
theorem exponentialBound418 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch104.certificate1257).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate839).dm (WitnessCertificates.Batch041.certificate839).beta) ≤ (2*exp (-((CountingCertificates.Batch041.certificate839).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch104.certificate1257).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch104.certificate1258).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch041.certificate839).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch104.certificate1257 MergedCutGroups.Batch104.certificate1258 CountingCertificates.Batch041.certificate839 CutLabelCertificates.Entropy021.certificate428 CutLabelCertificates.Minority021.certificate427 matches418 rfl rfl
    MergedCutGroups.Batch104.numericValid1257 MergedCutGroups.Batch104.numericValid1258 MergedCutGroups.Batch104.cellsSound1257 MergedCutGroups.Batch104.cellsSound1258
    MergedCutGroups.Batch104.cellsNumeric1257 MergedCutGroups.Batch104.cellsNumeric1258 MergedCutGroups.Batch104.populationMatches1257 MergedCutGroups.Batch104.populationMatches1258
    PopulationCertificates.Batch041.valid839 PopulationCertificates.Batch041.sound839 WitnessCertificates.Batch041.valid839 WitnessCertificates.Batch041.sound839 CountingCertificates.Batch041.valid839 CountingCertificates.Batch041.sound839
    CutLabelCertificates.Entropy021.valid428 CutLabelCertificates.Minority021.valid427 CutLabelCertificates.Minority021.sound427 H st hI
theorem probabilityBound418 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch104.certificate1257).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate839).dm (WitnessCertificates.Batch041.certificate839).beta) ≤ ((CutFailureCertificates.Budget041.certificate839).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound839 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate839).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch104.certificate1257).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch104.certificate1258).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch041.certificate839).omega:ℝ) ≤ ((CutFailureCertificates.Budget041.certificate839).bound:ℝ) at hb
  exact (exponentialBound418 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches419 : (MergedCutGroups.Batch105.certificate1261).GlobalMatches MergedCutGroups.Batch105.certificate1262 CountingCertificates.Batch042.certificate842 CutLabelCertificates.Entropy021.certificate432 CutLabelCertificates.Minority021.certificate431 := by decide +kernel
theorem exponentialBound419 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch105.certificate1261).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate842).dm (WitnessCertificates.Batch042.certificate842).beta) ≤ (2*exp (-((CountingCertificates.Batch042.certificate842).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch105.certificate1261).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch105.certificate1262).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch042.certificate842).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch105.certificate1261 MergedCutGroups.Batch105.certificate1262 CountingCertificates.Batch042.certificate842 CutLabelCertificates.Entropy021.certificate432 CutLabelCertificates.Minority021.certificate431 matches419 rfl rfl
    MergedCutGroups.Batch105.numericValid1261 MergedCutGroups.Batch105.numericValid1262 MergedCutGroups.Batch105.cellsSound1261 MergedCutGroups.Batch105.cellsSound1262
    MergedCutGroups.Batch105.cellsNumeric1261 MergedCutGroups.Batch105.cellsNumeric1262 MergedCutGroups.Batch105.populationMatches1261 MergedCutGroups.Batch105.populationMatches1262
    PopulationCertificates.Batch042.valid842 PopulationCertificates.Batch042.sound842 WitnessCertificates.Batch042.valid842 WitnessCertificates.Batch042.sound842 CountingCertificates.Batch042.valid842 CountingCertificates.Batch042.sound842
    CutLabelCertificates.Entropy021.valid432 CutLabelCertificates.Minority021.valid431 CutLabelCertificates.Minority021.sound431 H st hI
theorem probabilityBound419 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch105.certificate1261).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate842).dm (WitnessCertificates.Batch042.certificate842).beta) ≤ ((CutFailureCertificates.Budget042.certificate842).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound842 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate842).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch105.certificate1261).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch105.certificate1262).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch042.certificate842).omega:ℝ) ≤ ((CutFailureCertificates.Budget042.certificate842).bound:ℝ) at hb
  exact (exponentialBound419 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch020
