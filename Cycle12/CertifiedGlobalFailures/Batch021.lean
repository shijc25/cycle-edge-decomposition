import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch042
import Cycle12.CountingCertificates.Batch043
import Cycle12.CountingCertificates.Batch044
import Cycle12.CountingCertificates.Batch045
import Cycle12.CutFailureCertificates.Budget042
import Cycle12.CutFailureCertificates.Budget043
import Cycle12.CutFailureCertificates.Budget044
import Cycle12.CutFailureCertificates.Budget045
import Cycle12.CutLabelCertificates.Entropy021
import Cycle12.CutLabelCertificates.Entropy022
import Cycle12.CutLabelCertificates.Entropy023
import Cycle12.CutLabelCertificates.Entropy024
import Cycle12.CutLabelCertificates.Entropy025
import Cycle12.CutLabelCertificates.Entropy026
import Cycle12.CutLabelCertificates.Minority021
import Cycle12.CutLabelCertificates.Minority022
import Cycle12.CutLabelCertificates.Minority023
import Cycle12.CutLabelCertificates.Minority024
import Cycle12.CutLabelCertificates.Minority025
import Cycle12.CutLabelCertificates.Minority026
import Cycle12.MergedCutGroups.Batch105
import Cycle12.MergedCutGroups.Batch106
import Cycle12.MergedCutGroups.Batch107
import Cycle12.MergedCutGroups.Batch108
import Cycle12.MergedCutGroups.Batch109
import Cycle12.MergedCutGroups.Batch110
import Cycle12.MergedCutGroups.Batch111
import Cycle12.PopulationCertificates.Batch042
import Cycle12.PopulationCertificates.Batch043
import Cycle12.PopulationCertificates.Batch044
import Cycle12.PopulationCertificates.Batch045
import Cycle12.WitnessCertificates.Batch042
import Cycle12.WitnessCertificates.Batch043
import Cycle12.WitnessCertificates.Batch044
import Cycle12.WitnessCertificates.Batch045

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch021
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches420 : (MergedCutGroups.Batch105.certificate1265).GlobalMatches MergedCutGroups.Batch105.certificate1266 CountingCertificates.Batch042.certificate845 CutLabelCertificates.Entropy021.certificate436 CutLabelCertificates.Minority021.certificate435 := by decide +kernel
theorem exponentialBound420 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch105.certificate1265).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate845).dm (WitnessCertificates.Batch042.certificate845).beta) ≤ (2*exp (-((CountingCertificates.Batch042.certificate845).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch105.certificate1265).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch105.certificate1266).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch042.certificate845).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch105.certificate1265 MergedCutGroups.Batch105.certificate1266 CountingCertificates.Batch042.certificate845 CutLabelCertificates.Entropy021.certificate436 CutLabelCertificates.Minority021.certificate435 matches420 rfl rfl
    MergedCutGroups.Batch105.numericValid1265 MergedCutGroups.Batch105.numericValid1266 MergedCutGroups.Batch105.cellsSound1265 MergedCutGroups.Batch105.cellsSound1266
    MergedCutGroups.Batch105.cellsNumeric1265 MergedCutGroups.Batch105.cellsNumeric1266 MergedCutGroups.Batch105.populationMatches1265 MergedCutGroups.Batch105.populationMatches1266
    PopulationCertificates.Batch042.valid845 PopulationCertificates.Batch042.sound845 WitnessCertificates.Batch042.valid845 WitnessCertificates.Batch042.sound845 CountingCertificates.Batch042.valid845 CountingCertificates.Batch042.sound845
    CutLabelCertificates.Entropy021.valid436 CutLabelCertificates.Minority021.valid435 CutLabelCertificates.Minority021.sound435 H st hI
theorem probabilityBound420 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch105.certificate1265).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate845).dm (WitnessCertificates.Batch042.certificate845).beta) ≤ ((CutFailureCertificates.Budget042.certificate845).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound845 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate845).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch105.certificate1265).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch105.certificate1266).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch042.certificate845).omega:ℝ) ≤ ((CutFailureCertificates.Budget042.certificate845).bound:ℝ) at hb
  exact (exponentialBound420 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches421 : (MergedCutGroups.Batch105.certificate1269).GlobalMatches MergedCutGroups.Batch105.certificate1270 CountingCertificates.Batch042.certificate848 CutLabelCertificates.Entropy022.certificate440 CutLabelCertificates.Minority021.certificate439 := by decide +kernel
theorem exponentialBound421 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch105.certificate1269).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate848).dm (WitnessCertificates.Batch042.certificate848).beta) ≤ (2*exp (-((CountingCertificates.Batch042.certificate848).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch105.certificate1269).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch105.certificate1270).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch042.certificate848).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch105.certificate1269 MergedCutGroups.Batch105.certificate1270 CountingCertificates.Batch042.certificate848 CutLabelCertificates.Entropy022.certificate440 CutLabelCertificates.Minority021.certificate439 matches421 rfl rfl
    MergedCutGroups.Batch105.numericValid1269 MergedCutGroups.Batch105.numericValid1270 MergedCutGroups.Batch105.cellsSound1269 MergedCutGroups.Batch105.cellsSound1270
    MergedCutGroups.Batch105.cellsNumeric1269 MergedCutGroups.Batch105.cellsNumeric1270 MergedCutGroups.Batch105.populationMatches1269 MergedCutGroups.Batch105.populationMatches1270
    PopulationCertificates.Batch042.valid848 PopulationCertificates.Batch042.sound848 WitnessCertificates.Batch042.valid848 WitnessCertificates.Batch042.sound848 CountingCertificates.Batch042.valid848 CountingCertificates.Batch042.sound848
    CutLabelCertificates.Entropy022.valid440 CutLabelCertificates.Minority021.valid439 CutLabelCertificates.Minority021.sound439 H st hI
theorem probabilityBound421 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch105.certificate1269).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate848).dm (WitnessCertificates.Batch042.certificate848).beta) ≤ ((CutFailureCertificates.Budget042.certificate848).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound848 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate848).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch105.certificate1269).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch105.certificate1270).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch042.certificate848).omega:ℝ) ≤ ((CutFailureCertificates.Budget042.certificate848).bound:ℝ) at hb
  exact (exponentialBound421 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches422 : (MergedCutGroups.Batch106.certificate1273).GlobalMatches MergedCutGroups.Batch106.certificate1274 CountingCertificates.Batch042.certificate851 CutLabelCertificates.Entropy022.certificate444 CutLabelCertificates.Minority022.certificate443 := by decide +kernel
theorem exponentialBound422 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch106.certificate1273).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate851).dm (WitnessCertificates.Batch042.certificate851).beta) ≤ (2*exp (-((CountingCertificates.Batch042.certificate851).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch106.certificate1273).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch106.certificate1274).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch042.certificate851).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch106.certificate1273 MergedCutGroups.Batch106.certificate1274 CountingCertificates.Batch042.certificate851 CutLabelCertificates.Entropy022.certificate444 CutLabelCertificates.Minority022.certificate443 matches422 rfl rfl
    MergedCutGroups.Batch106.numericValid1273 MergedCutGroups.Batch106.numericValid1274 MergedCutGroups.Batch106.cellsSound1273 MergedCutGroups.Batch106.cellsSound1274
    MergedCutGroups.Batch106.cellsNumeric1273 MergedCutGroups.Batch106.cellsNumeric1274 MergedCutGroups.Batch106.populationMatches1273 MergedCutGroups.Batch106.populationMatches1274
    PopulationCertificates.Batch042.valid851 PopulationCertificates.Batch042.sound851 WitnessCertificates.Batch042.valid851 WitnessCertificates.Batch042.sound851 CountingCertificates.Batch042.valid851 CountingCertificates.Batch042.sound851
    CutLabelCertificates.Entropy022.valid444 CutLabelCertificates.Minority022.valid443 CutLabelCertificates.Minority022.sound443 H st hI
theorem probabilityBound422 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch106.certificate1273).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate851).dm (WitnessCertificates.Batch042.certificate851).beta) ≤ ((CutFailureCertificates.Budget042.certificate851).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound851 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate851).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch106.certificate1273).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch106.certificate1274).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch042.certificate851).omega:ℝ) ≤ ((CutFailureCertificates.Budget042.certificate851).bound:ℝ) at hb
  exact (exponentialBound422 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches423 : (MergedCutGroups.Batch106.certificate1277).GlobalMatches MergedCutGroups.Batch106.certificate1278 CountingCertificates.Batch042.certificate854 CutLabelCertificates.Entropy022.certificate448 CutLabelCertificates.Minority022.certificate447 := by decide +kernel
theorem exponentialBound423 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch106.certificate1277).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate854).dm (WitnessCertificates.Batch042.certificate854).beta) ≤ (2*exp (-((CountingCertificates.Batch042.certificate854).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch106.certificate1277).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch106.certificate1278).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch042.certificate854).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch106.certificate1277 MergedCutGroups.Batch106.certificate1278 CountingCertificates.Batch042.certificate854 CutLabelCertificates.Entropy022.certificate448 CutLabelCertificates.Minority022.certificate447 matches423 rfl rfl
    MergedCutGroups.Batch106.numericValid1277 MergedCutGroups.Batch106.numericValid1278 MergedCutGroups.Batch106.cellsSound1277 MergedCutGroups.Batch106.cellsSound1278
    MergedCutGroups.Batch106.cellsNumeric1277 MergedCutGroups.Batch106.cellsNumeric1278 MergedCutGroups.Batch106.populationMatches1277 MergedCutGroups.Batch106.populationMatches1278
    PopulationCertificates.Batch042.valid854 PopulationCertificates.Batch042.sound854 WitnessCertificates.Batch042.valid854 WitnessCertificates.Batch042.sound854 CountingCertificates.Batch042.valid854 CountingCertificates.Batch042.sound854
    CutLabelCertificates.Entropy022.valid448 CutLabelCertificates.Minority022.valid447 CutLabelCertificates.Minority022.sound447 H st hI
theorem probabilityBound423 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch106.certificate1277).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate854).dm (WitnessCertificates.Batch042.certificate854).beta) ≤ ((CutFailureCertificates.Budget042.certificate854).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound854 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate854).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch106.certificate1277).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch106.certificate1278).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch042.certificate854).omega:ℝ) ≤ ((CutFailureCertificates.Budget042.certificate854).bound:ℝ) at hb
  exact (exponentialBound423 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches424 : (MergedCutGroups.Batch106.certificate1281).GlobalMatches MergedCutGroups.Batch106.certificate1282 CountingCertificates.Batch042.certificate857 CutLabelCertificates.Entropy022.certificate452 CutLabelCertificates.Minority022.certificate451 := by decide +kernel
theorem exponentialBound424 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch106.certificate1281).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate857).dm (WitnessCertificates.Batch042.certificate857).beta) ≤ (2*exp (-((CountingCertificates.Batch042.certificate857).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch106.certificate1281).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch106.certificate1282).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch042.certificate857).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch106.certificate1281 MergedCutGroups.Batch106.certificate1282 CountingCertificates.Batch042.certificate857 CutLabelCertificates.Entropy022.certificate452 CutLabelCertificates.Minority022.certificate451 matches424 rfl rfl
    MergedCutGroups.Batch106.numericValid1281 MergedCutGroups.Batch106.numericValid1282 MergedCutGroups.Batch106.cellsSound1281 MergedCutGroups.Batch106.cellsSound1282
    MergedCutGroups.Batch106.cellsNumeric1281 MergedCutGroups.Batch106.cellsNumeric1282 MergedCutGroups.Batch106.populationMatches1281 MergedCutGroups.Batch106.populationMatches1282
    PopulationCertificates.Batch042.valid857 PopulationCertificates.Batch042.sound857 WitnessCertificates.Batch042.valid857 WitnessCertificates.Batch042.sound857 CountingCertificates.Batch042.valid857 CountingCertificates.Batch042.sound857
    CutLabelCertificates.Entropy022.valid452 CutLabelCertificates.Minority022.valid451 CutLabelCertificates.Minority022.sound451 H st hI
theorem probabilityBound424 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch106.certificate1281).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate857).dm (WitnessCertificates.Batch042.certificate857).beta) ≤ ((CutFailureCertificates.Budget042.certificate857).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound857 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate857).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch106.certificate1281).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch106.certificate1282).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch042.certificate857).omega:ℝ) ≤ ((CutFailureCertificates.Budget042.certificate857).bound:ℝ) at hb
  exact (exponentialBound424 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches425 : (MergedCutGroups.Batch107.certificate1285).GlobalMatches MergedCutGroups.Batch107.certificate1286 CountingCertificates.Batch043.certificate860 CutLabelCertificates.Entropy022.certificate457 CutLabelCertificates.Minority022.certificate456 := by decide +kernel
theorem exponentialBound425 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch107.certificate1285).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate860).dm (WitnessCertificates.Batch043.certificate860).beta) ≤ (2*exp (-((CountingCertificates.Batch043.certificate860).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch107.certificate1285).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch107.certificate1286).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch043.certificate860).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch107.certificate1285 MergedCutGroups.Batch107.certificate1286 CountingCertificates.Batch043.certificate860 CutLabelCertificates.Entropy022.certificate457 CutLabelCertificates.Minority022.certificate456 matches425 rfl rfl
    MergedCutGroups.Batch107.numericValid1285 MergedCutGroups.Batch107.numericValid1286 MergedCutGroups.Batch107.cellsSound1285 MergedCutGroups.Batch107.cellsSound1286
    MergedCutGroups.Batch107.cellsNumeric1285 MergedCutGroups.Batch107.cellsNumeric1286 MergedCutGroups.Batch107.populationMatches1285 MergedCutGroups.Batch107.populationMatches1286
    PopulationCertificates.Batch043.valid860 PopulationCertificates.Batch043.sound860 WitnessCertificates.Batch043.valid860 WitnessCertificates.Batch043.sound860 CountingCertificates.Batch043.valid860 CountingCertificates.Batch043.sound860
    CutLabelCertificates.Entropy022.valid457 CutLabelCertificates.Minority022.valid456 CutLabelCertificates.Minority022.sound456 H st hI
theorem probabilityBound425 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch107.certificate1285).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate860).dm (WitnessCertificates.Batch043.certificate860).beta) ≤ ((CutFailureCertificates.Budget043.certificate860).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound860 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate860).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch107.certificate1285).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch107.certificate1286).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch043.certificate860).omega:ℝ) ≤ ((CutFailureCertificates.Budget043.certificate860).bound:ℝ) at hb
  exact (exponentialBound425 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches426 : (MergedCutGroups.Batch107.certificate1289).GlobalMatches MergedCutGroups.Batch107.certificate1290 CountingCertificates.Batch043.certificate863 CutLabelCertificates.Entropy023.certificate462 CutLabelCertificates.Minority023.certificate461 := by decide +kernel
theorem exponentialBound426 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch107.certificate1289).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate863).dm (WitnessCertificates.Batch043.certificate863).beta) ≤ (2*exp (-((CountingCertificates.Batch043.certificate863).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch107.certificate1289).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch107.certificate1290).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch043.certificate863).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch107.certificate1289 MergedCutGroups.Batch107.certificate1290 CountingCertificates.Batch043.certificate863 CutLabelCertificates.Entropy023.certificate462 CutLabelCertificates.Minority023.certificate461 matches426 rfl rfl
    MergedCutGroups.Batch107.numericValid1289 MergedCutGroups.Batch107.numericValid1290 MergedCutGroups.Batch107.cellsSound1289 MergedCutGroups.Batch107.cellsSound1290
    MergedCutGroups.Batch107.cellsNumeric1289 MergedCutGroups.Batch107.cellsNumeric1290 MergedCutGroups.Batch107.populationMatches1289 MergedCutGroups.Batch107.populationMatches1290
    PopulationCertificates.Batch043.valid863 PopulationCertificates.Batch043.sound863 WitnessCertificates.Batch043.valid863 WitnessCertificates.Batch043.sound863 CountingCertificates.Batch043.valid863 CountingCertificates.Batch043.sound863
    CutLabelCertificates.Entropy023.valid462 CutLabelCertificates.Minority023.valid461 CutLabelCertificates.Minority023.sound461 H st hI
theorem probabilityBound426 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch107.certificate1289).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate863).dm (WitnessCertificates.Batch043.certificate863).beta) ≤ ((CutFailureCertificates.Budget043.certificate863).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound863 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate863).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch107.certificate1289).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch107.certificate1290).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch043.certificate863).omega:ℝ) ≤ ((CutFailureCertificates.Budget043.certificate863).bound:ℝ) at hb
  exact (exponentialBound426 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches427 : (MergedCutGroups.Batch107.certificate1293).GlobalMatches MergedCutGroups.Batch107.certificate1294 CountingCertificates.Batch043.certificate866 CutLabelCertificates.Entropy023.certificate467 CutLabelCertificates.Minority023.certificate466 := by decide +kernel
theorem exponentialBound427 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch107.certificate1293).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate866).dm (WitnessCertificates.Batch043.certificate866).beta) ≤ (2*exp (-((CountingCertificates.Batch043.certificate866).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch107.certificate1293).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch107.certificate1294).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch043.certificate866).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch107.certificate1293 MergedCutGroups.Batch107.certificate1294 CountingCertificates.Batch043.certificate866 CutLabelCertificates.Entropy023.certificate467 CutLabelCertificates.Minority023.certificate466 matches427 rfl rfl
    MergedCutGroups.Batch107.numericValid1293 MergedCutGroups.Batch107.numericValid1294 MergedCutGroups.Batch107.cellsSound1293 MergedCutGroups.Batch107.cellsSound1294
    MergedCutGroups.Batch107.cellsNumeric1293 MergedCutGroups.Batch107.cellsNumeric1294 MergedCutGroups.Batch107.populationMatches1293 MergedCutGroups.Batch107.populationMatches1294
    PopulationCertificates.Batch043.valid866 PopulationCertificates.Batch043.sound866 WitnessCertificates.Batch043.valid866 WitnessCertificates.Batch043.sound866 CountingCertificates.Batch043.valid866 CountingCertificates.Batch043.sound866
    CutLabelCertificates.Entropy023.valid467 CutLabelCertificates.Minority023.valid466 CutLabelCertificates.Minority023.sound466 H st hI
theorem probabilityBound427 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch107.certificate1293).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate866).dm (WitnessCertificates.Batch043.certificate866).beta) ≤ ((CutFailureCertificates.Budget043.certificate866).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound866 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate866).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch107.certificate1293).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch107.certificate1294).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch043.certificate866).omega:ℝ) ≤ ((CutFailureCertificates.Budget043.certificate866).bound:ℝ) at hb
  exact (exponentialBound427 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches428 : (MergedCutGroups.Batch108.certificate1297).GlobalMatches MergedCutGroups.Batch108.certificate1298 CountingCertificates.Batch043.certificate869 CutLabelCertificates.Entropy023.certificate472 CutLabelCertificates.Minority023.certificate471 := by decide +kernel
theorem exponentialBound428 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch108.certificate1297).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate869).dm (WitnessCertificates.Batch043.certificate869).beta) ≤ (2*exp (-((CountingCertificates.Batch043.certificate869).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch108.certificate1297).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch108.certificate1298).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch043.certificate869).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch108.certificate1297 MergedCutGroups.Batch108.certificate1298 CountingCertificates.Batch043.certificate869 CutLabelCertificates.Entropy023.certificate472 CutLabelCertificates.Minority023.certificate471 matches428 rfl rfl
    MergedCutGroups.Batch108.numericValid1297 MergedCutGroups.Batch108.numericValid1298 MergedCutGroups.Batch108.cellsSound1297 MergedCutGroups.Batch108.cellsSound1298
    MergedCutGroups.Batch108.cellsNumeric1297 MergedCutGroups.Batch108.cellsNumeric1298 MergedCutGroups.Batch108.populationMatches1297 MergedCutGroups.Batch108.populationMatches1298
    PopulationCertificates.Batch043.valid869 PopulationCertificates.Batch043.sound869 WitnessCertificates.Batch043.valid869 WitnessCertificates.Batch043.sound869 CountingCertificates.Batch043.valid869 CountingCertificates.Batch043.sound869
    CutLabelCertificates.Entropy023.valid472 CutLabelCertificates.Minority023.valid471 CutLabelCertificates.Minority023.sound471 H st hI
theorem probabilityBound428 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch108.certificate1297).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate869).dm (WitnessCertificates.Batch043.certificate869).beta) ≤ ((CutFailureCertificates.Budget043.certificate869).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound869 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate869).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch108.certificate1297).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch108.certificate1298).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch043.certificate869).omega:ℝ) ≤ ((CutFailureCertificates.Budget043.certificate869).bound:ℝ) at hb
  exact (exponentialBound428 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches429 : (MergedCutGroups.Batch108.certificate1301).GlobalMatches MergedCutGroups.Batch108.certificate1302 CountingCertificates.Batch043.certificate872 CutLabelCertificates.Entropy023.certificate477 CutLabelCertificates.Minority023.certificate476 := by decide +kernel
theorem exponentialBound429 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch108.certificate1301).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate872).dm (WitnessCertificates.Batch043.certificate872).beta) ≤ (2*exp (-((CountingCertificates.Batch043.certificate872).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch108.certificate1301).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch108.certificate1302).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch043.certificate872).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch108.certificate1301 MergedCutGroups.Batch108.certificate1302 CountingCertificates.Batch043.certificate872 CutLabelCertificates.Entropy023.certificate477 CutLabelCertificates.Minority023.certificate476 matches429 rfl rfl
    MergedCutGroups.Batch108.numericValid1301 MergedCutGroups.Batch108.numericValid1302 MergedCutGroups.Batch108.cellsSound1301 MergedCutGroups.Batch108.cellsSound1302
    MergedCutGroups.Batch108.cellsNumeric1301 MergedCutGroups.Batch108.cellsNumeric1302 MergedCutGroups.Batch108.populationMatches1301 MergedCutGroups.Batch108.populationMatches1302
    PopulationCertificates.Batch043.valid872 PopulationCertificates.Batch043.sound872 WitnessCertificates.Batch043.valid872 WitnessCertificates.Batch043.sound872 CountingCertificates.Batch043.valid872 CountingCertificates.Batch043.sound872
    CutLabelCertificates.Entropy023.valid477 CutLabelCertificates.Minority023.valid476 CutLabelCertificates.Minority023.sound476 H st hI
theorem probabilityBound429 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch108.certificate1301).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate872).dm (WitnessCertificates.Batch043.certificate872).beta) ≤ ((CutFailureCertificates.Budget043.certificate872).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound872 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate872).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch108.certificate1301).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch108.certificate1302).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch043.certificate872).omega:ℝ) ≤ ((CutFailureCertificates.Budget043.certificate872).bound:ℝ) at hb
  exact (exponentialBound429 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches430 : (MergedCutGroups.Batch108.certificate1305).GlobalMatches MergedCutGroups.Batch108.certificate1306 CountingCertificates.Batch043.certificate875 CutLabelCertificates.Entropy024.certificate482 CutLabelCertificates.Minority024.certificate481 := by decide +kernel
theorem exponentialBound430 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch108.certificate1305).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate875).dm (WitnessCertificates.Batch043.certificate875).beta) ≤ (2*exp (-((CountingCertificates.Batch043.certificate875).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch108.certificate1305).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch108.certificate1306).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch043.certificate875).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch108.certificate1305 MergedCutGroups.Batch108.certificate1306 CountingCertificates.Batch043.certificate875 CutLabelCertificates.Entropy024.certificate482 CutLabelCertificates.Minority024.certificate481 matches430 rfl rfl
    MergedCutGroups.Batch108.numericValid1305 MergedCutGroups.Batch108.numericValid1306 MergedCutGroups.Batch108.cellsSound1305 MergedCutGroups.Batch108.cellsSound1306
    MergedCutGroups.Batch108.cellsNumeric1305 MergedCutGroups.Batch108.cellsNumeric1306 MergedCutGroups.Batch108.populationMatches1305 MergedCutGroups.Batch108.populationMatches1306
    PopulationCertificates.Batch043.valid875 PopulationCertificates.Batch043.sound875 WitnessCertificates.Batch043.valid875 WitnessCertificates.Batch043.sound875 CountingCertificates.Batch043.valid875 CountingCertificates.Batch043.sound875
    CutLabelCertificates.Entropy024.valid482 CutLabelCertificates.Minority024.valid481 CutLabelCertificates.Minority024.sound481 H st hI
theorem probabilityBound430 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch108.certificate1305).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate875).dm (WitnessCertificates.Batch043.certificate875).beta) ≤ ((CutFailureCertificates.Budget043.certificate875).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound875 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate875).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch108.certificate1305).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch108.certificate1306).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch043.certificate875).omega:ℝ) ≤ ((CutFailureCertificates.Budget043.certificate875).bound:ℝ) at hb
  exact (exponentialBound430 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches431 : (MergedCutGroups.Batch109.certificate1309).GlobalMatches MergedCutGroups.Batch109.certificate1310 CountingCertificates.Batch043.certificate878 CutLabelCertificates.Entropy024.certificate487 CutLabelCertificates.Minority024.certificate486 := by decide +kernel
theorem exponentialBound431 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch109.certificate1309).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate878).dm (WitnessCertificates.Batch043.certificate878).beta) ≤ (2*exp (-((CountingCertificates.Batch043.certificate878).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch109.certificate1309).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch109.certificate1310).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch043.certificate878).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch109.certificate1309 MergedCutGroups.Batch109.certificate1310 CountingCertificates.Batch043.certificate878 CutLabelCertificates.Entropy024.certificate487 CutLabelCertificates.Minority024.certificate486 matches431 rfl rfl
    MergedCutGroups.Batch109.numericValid1309 MergedCutGroups.Batch109.numericValid1310 MergedCutGroups.Batch109.cellsSound1309 MergedCutGroups.Batch109.cellsSound1310
    MergedCutGroups.Batch109.cellsNumeric1309 MergedCutGroups.Batch109.cellsNumeric1310 MergedCutGroups.Batch109.populationMatches1309 MergedCutGroups.Batch109.populationMatches1310
    PopulationCertificates.Batch043.valid878 PopulationCertificates.Batch043.sound878 WitnessCertificates.Batch043.valid878 WitnessCertificates.Batch043.sound878 CountingCertificates.Batch043.valid878 CountingCertificates.Batch043.sound878
    CutLabelCertificates.Entropy024.valid487 CutLabelCertificates.Minority024.valid486 CutLabelCertificates.Minority024.sound486 H st hI
theorem probabilityBound431 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch109.certificate1309).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate878).dm (WitnessCertificates.Batch043.certificate878).beta) ≤ ((CutFailureCertificates.Budget043.certificate878).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound878 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate878).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch109.certificate1309).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch109.certificate1310).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch043.certificate878).omega:ℝ) ≤ ((CutFailureCertificates.Budget043.certificate878).bound:ℝ) at hb
  exact (exponentialBound431 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches432 : (MergedCutGroups.Batch109.certificate1313).GlobalMatches MergedCutGroups.Batch109.certificate1314 CountingCertificates.Batch044.certificate881 CutLabelCertificates.Entropy024.certificate492 CutLabelCertificates.Minority024.certificate491 := by decide +kernel
theorem exponentialBound432 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch109.certificate1313).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate881).dm (WitnessCertificates.Batch044.certificate881).beta) ≤ (2*exp (-((CountingCertificates.Batch044.certificate881).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch109.certificate1313).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch109.certificate1314).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch044.certificate881).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch109.certificate1313 MergedCutGroups.Batch109.certificate1314 CountingCertificates.Batch044.certificate881 CutLabelCertificates.Entropy024.certificate492 CutLabelCertificates.Minority024.certificate491 matches432 rfl rfl
    MergedCutGroups.Batch109.numericValid1313 MergedCutGroups.Batch109.numericValid1314 MergedCutGroups.Batch109.cellsSound1313 MergedCutGroups.Batch109.cellsSound1314
    MergedCutGroups.Batch109.cellsNumeric1313 MergedCutGroups.Batch109.cellsNumeric1314 MergedCutGroups.Batch109.populationMatches1313 MergedCutGroups.Batch109.populationMatches1314
    PopulationCertificates.Batch044.valid881 PopulationCertificates.Batch044.sound881 WitnessCertificates.Batch044.valid881 WitnessCertificates.Batch044.sound881 CountingCertificates.Batch044.valid881 CountingCertificates.Batch044.sound881
    CutLabelCertificates.Entropy024.valid492 CutLabelCertificates.Minority024.valid491 CutLabelCertificates.Minority024.sound491 H st hI
theorem probabilityBound432 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch109.certificate1313).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate881).dm (WitnessCertificates.Batch044.certificate881).beta) ≤ ((CutFailureCertificates.Budget044.certificate881).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound881 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate881).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch109.certificate1313).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch109.certificate1314).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch044.certificate881).omega:ℝ) ≤ ((CutFailureCertificates.Budget044.certificate881).bound:ℝ) at hb
  exact (exponentialBound432 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches433 : (MergedCutGroups.Batch109.certificate1317).GlobalMatches MergedCutGroups.Batch109.certificate1318 CountingCertificates.Batch044.certificate884 CutLabelCertificates.Entropy024.certificate497 CutLabelCertificates.Minority024.certificate496 := by decide +kernel
theorem exponentialBound433 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch109.certificate1317).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate884).dm (WitnessCertificates.Batch044.certificate884).beta) ≤ (2*exp (-((CountingCertificates.Batch044.certificate884).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch109.certificate1317).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch109.certificate1318).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch044.certificate884).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch109.certificate1317 MergedCutGroups.Batch109.certificate1318 CountingCertificates.Batch044.certificate884 CutLabelCertificates.Entropy024.certificate497 CutLabelCertificates.Minority024.certificate496 matches433 rfl rfl
    MergedCutGroups.Batch109.numericValid1317 MergedCutGroups.Batch109.numericValid1318 MergedCutGroups.Batch109.cellsSound1317 MergedCutGroups.Batch109.cellsSound1318
    MergedCutGroups.Batch109.cellsNumeric1317 MergedCutGroups.Batch109.cellsNumeric1318 MergedCutGroups.Batch109.populationMatches1317 MergedCutGroups.Batch109.populationMatches1318
    PopulationCertificates.Batch044.valid884 PopulationCertificates.Batch044.sound884 WitnessCertificates.Batch044.valid884 WitnessCertificates.Batch044.sound884 CountingCertificates.Batch044.valid884 CountingCertificates.Batch044.sound884
    CutLabelCertificates.Entropy024.valid497 CutLabelCertificates.Minority024.valid496 CutLabelCertificates.Minority024.sound496 H st hI
theorem probabilityBound433 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch109.certificate1317).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate884).dm (WitnessCertificates.Batch044.certificate884).beta) ≤ ((CutFailureCertificates.Budget044.certificate884).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound884 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate884).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch109.certificate1317).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch109.certificate1318).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch044.certificate884).omega:ℝ) ≤ ((CutFailureCertificates.Budget044.certificate884).bound:ℝ) at hb
  exact (exponentialBound433 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches434 : (MergedCutGroups.Batch110.certificate1321).GlobalMatches MergedCutGroups.Batch110.certificate1322 CountingCertificates.Batch044.certificate887 CutLabelCertificates.Entropy025.certificate502 CutLabelCertificates.Minority025.certificate501 := by decide +kernel
theorem exponentialBound434 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch110.certificate1321).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate887).dm (WitnessCertificates.Batch044.certificate887).beta) ≤ (2*exp (-((CountingCertificates.Batch044.certificate887).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch110.certificate1321).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch110.certificate1322).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch044.certificate887).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch110.certificate1321 MergedCutGroups.Batch110.certificate1322 CountingCertificates.Batch044.certificate887 CutLabelCertificates.Entropy025.certificate502 CutLabelCertificates.Minority025.certificate501 matches434 rfl rfl
    MergedCutGroups.Batch110.numericValid1321 MergedCutGroups.Batch110.numericValid1322 MergedCutGroups.Batch110.cellsSound1321 MergedCutGroups.Batch110.cellsSound1322
    MergedCutGroups.Batch110.cellsNumeric1321 MergedCutGroups.Batch110.cellsNumeric1322 MergedCutGroups.Batch110.populationMatches1321 MergedCutGroups.Batch110.populationMatches1322
    PopulationCertificates.Batch044.valid887 PopulationCertificates.Batch044.sound887 WitnessCertificates.Batch044.valid887 WitnessCertificates.Batch044.sound887 CountingCertificates.Batch044.valid887 CountingCertificates.Batch044.sound887
    CutLabelCertificates.Entropy025.valid502 CutLabelCertificates.Minority025.valid501 CutLabelCertificates.Minority025.sound501 H st hI
theorem probabilityBound434 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch110.certificate1321).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate887).dm (WitnessCertificates.Batch044.certificate887).beta) ≤ ((CutFailureCertificates.Budget044.certificate887).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound887 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate887).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch110.certificate1321).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch110.certificate1322).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch044.certificate887).omega:ℝ) ≤ ((CutFailureCertificates.Budget044.certificate887).bound:ℝ) at hb
  exact (exponentialBound434 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches435 : (MergedCutGroups.Batch110.certificate1325).GlobalMatches MergedCutGroups.Batch110.certificate1326 CountingCertificates.Batch044.certificate890 CutLabelCertificates.Entropy025.certificate507 CutLabelCertificates.Minority025.certificate506 := by decide +kernel
theorem exponentialBound435 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch110.certificate1325).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate890).dm (WitnessCertificates.Batch044.certificate890).beta) ≤ (2*exp (-((CountingCertificates.Batch044.certificate890).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch110.certificate1325).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch110.certificate1326).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch044.certificate890).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch110.certificate1325 MergedCutGroups.Batch110.certificate1326 CountingCertificates.Batch044.certificate890 CutLabelCertificates.Entropy025.certificate507 CutLabelCertificates.Minority025.certificate506 matches435 rfl rfl
    MergedCutGroups.Batch110.numericValid1325 MergedCutGroups.Batch110.numericValid1326 MergedCutGroups.Batch110.cellsSound1325 MergedCutGroups.Batch110.cellsSound1326
    MergedCutGroups.Batch110.cellsNumeric1325 MergedCutGroups.Batch110.cellsNumeric1326 MergedCutGroups.Batch110.populationMatches1325 MergedCutGroups.Batch110.populationMatches1326
    PopulationCertificates.Batch044.valid890 PopulationCertificates.Batch044.sound890 WitnessCertificates.Batch044.valid890 WitnessCertificates.Batch044.sound890 CountingCertificates.Batch044.valid890 CountingCertificates.Batch044.sound890
    CutLabelCertificates.Entropy025.valid507 CutLabelCertificates.Minority025.valid506 CutLabelCertificates.Minority025.sound506 H st hI
theorem probabilityBound435 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch110.certificate1325).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate890).dm (WitnessCertificates.Batch044.certificate890).beta) ≤ ((CutFailureCertificates.Budget044.certificate890).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound890 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate890).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch110.certificate1325).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch110.certificate1326).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch044.certificate890).omega:ℝ) ≤ ((CutFailureCertificates.Budget044.certificate890).bound:ℝ) at hb
  exact (exponentialBound435 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches436 : (MergedCutGroups.Batch110.certificate1329).GlobalMatches MergedCutGroups.Batch110.certificate1330 CountingCertificates.Batch044.certificate893 CutLabelCertificates.Entropy025.certificate512 CutLabelCertificates.Minority025.certificate511 := by decide +kernel
theorem exponentialBound436 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch110.certificate1329).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate893).dm (WitnessCertificates.Batch044.certificate893).beta) ≤ (2*exp (-((CountingCertificates.Batch044.certificate893).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch110.certificate1329).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch110.certificate1330).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch044.certificate893).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch110.certificate1329 MergedCutGroups.Batch110.certificate1330 CountingCertificates.Batch044.certificate893 CutLabelCertificates.Entropy025.certificate512 CutLabelCertificates.Minority025.certificate511 matches436 rfl rfl
    MergedCutGroups.Batch110.numericValid1329 MergedCutGroups.Batch110.numericValid1330 MergedCutGroups.Batch110.cellsSound1329 MergedCutGroups.Batch110.cellsSound1330
    MergedCutGroups.Batch110.cellsNumeric1329 MergedCutGroups.Batch110.cellsNumeric1330 MergedCutGroups.Batch110.populationMatches1329 MergedCutGroups.Batch110.populationMatches1330
    PopulationCertificates.Batch044.valid893 PopulationCertificates.Batch044.sound893 WitnessCertificates.Batch044.valid893 WitnessCertificates.Batch044.sound893 CountingCertificates.Batch044.valid893 CountingCertificates.Batch044.sound893
    CutLabelCertificates.Entropy025.valid512 CutLabelCertificates.Minority025.valid511 CutLabelCertificates.Minority025.sound511 H st hI
theorem probabilityBound436 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch110.certificate1329).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate893).dm (WitnessCertificates.Batch044.certificate893).beta) ≤ ((CutFailureCertificates.Budget044.certificate893).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound893 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate893).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch110.certificate1329).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch110.certificate1330).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch044.certificate893).omega:ℝ) ≤ ((CutFailureCertificates.Budget044.certificate893).bound:ℝ) at hb
  exact (exponentialBound436 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches437 : (MergedCutGroups.Batch111.certificate1333).GlobalMatches MergedCutGroups.Batch111.certificate1334 CountingCertificates.Batch044.certificate896 CutLabelCertificates.Entropy025.certificate517 CutLabelCertificates.Minority025.certificate516 := by decide +kernel
theorem exponentialBound437 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch111.certificate1333).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate896).dm (WitnessCertificates.Batch044.certificate896).beta) ≤ (2*exp (-((CountingCertificates.Batch044.certificate896).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch111.certificate1333).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch111.certificate1334).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch044.certificate896).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch111.certificate1333 MergedCutGroups.Batch111.certificate1334 CountingCertificates.Batch044.certificate896 CutLabelCertificates.Entropy025.certificate517 CutLabelCertificates.Minority025.certificate516 matches437 rfl rfl
    MergedCutGroups.Batch111.numericValid1333 MergedCutGroups.Batch111.numericValid1334 MergedCutGroups.Batch111.cellsSound1333 MergedCutGroups.Batch111.cellsSound1334
    MergedCutGroups.Batch111.cellsNumeric1333 MergedCutGroups.Batch111.cellsNumeric1334 MergedCutGroups.Batch111.populationMatches1333 MergedCutGroups.Batch111.populationMatches1334
    PopulationCertificates.Batch044.valid896 PopulationCertificates.Batch044.sound896 WitnessCertificates.Batch044.valid896 WitnessCertificates.Batch044.sound896 CountingCertificates.Batch044.valid896 CountingCertificates.Batch044.sound896
    CutLabelCertificates.Entropy025.valid517 CutLabelCertificates.Minority025.valid516 CutLabelCertificates.Minority025.sound516 H st hI
theorem probabilityBound437 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch111.certificate1333).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate896).dm (WitnessCertificates.Batch044.certificate896).beta) ≤ ((CutFailureCertificates.Budget044.certificate896).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound896 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate896).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch111.certificate1333).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch111.certificate1334).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch044.certificate896).omega:ℝ) ≤ ((CutFailureCertificates.Budget044.certificate896).bound:ℝ) at hb
  exact (exponentialBound437 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches438 : (MergedCutGroups.Batch111.certificate1337).GlobalMatches MergedCutGroups.Batch111.certificate1338 CountingCertificates.Batch044.certificate899 CutLabelCertificates.Entropy026.certificate522 CutLabelCertificates.Minority026.certificate521 := by decide +kernel
theorem exponentialBound438 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch111.certificate1337).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate899).dm (WitnessCertificates.Batch044.certificate899).beta) ≤ (2*exp (-((CountingCertificates.Batch044.certificate899).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch111.certificate1337).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch111.certificate1338).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch044.certificate899).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch111.certificate1337 MergedCutGroups.Batch111.certificate1338 CountingCertificates.Batch044.certificate899 CutLabelCertificates.Entropy026.certificate522 CutLabelCertificates.Minority026.certificate521 matches438 rfl rfl
    MergedCutGroups.Batch111.numericValid1337 MergedCutGroups.Batch111.numericValid1338 MergedCutGroups.Batch111.cellsSound1337 MergedCutGroups.Batch111.cellsSound1338
    MergedCutGroups.Batch111.cellsNumeric1337 MergedCutGroups.Batch111.cellsNumeric1338 MergedCutGroups.Batch111.populationMatches1337 MergedCutGroups.Batch111.populationMatches1338
    PopulationCertificates.Batch044.valid899 PopulationCertificates.Batch044.sound899 WitnessCertificates.Batch044.valid899 WitnessCertificates.Batch044.sound899 CountingCertificates.Batch044.valid899 CountingCertificates.Batch044.sound899
    CutLabelCertificates.Entropy026.valid522 CutLabelCertificates.Minority026.valid521 CutLabelCertificates.Minority026.sound521 H st hI
theorem probabilityBound438 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch111.certificate1337).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate899).dm (WitnessCertificates.Batch044.certificate899).beta) ≤ ((CutFailureCertificates.Budget044.certificate899).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound899 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate899).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch111.certificate1337).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch111.certificate1338).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch044.certificate899).omega:ℝ) ≤ ((CutFailureCertificates.Budget044.certificate899).bound:ℝ) at hb
  exact (exponentialBound438 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches439 : (MergedCutGroups.Batch111.certificate1341).GlobalMatches MergedCutGroups.Batch111.certificate1342 CountingCertificates.Batch045.certificate902 CutLabelCertificates.Entropy026.certificate527 CutLabelCertificates.Minority026.certificate526 := by decide +kernel
theorem exponentialBound439 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch111.certificate1341).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate902).dm (WitnessCertificates.Batch045.certificate902).beta) ≤ (2*exp (-((CountingCertificates.Batch045.certificate902).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch111.certificate1341).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch111.certificate1342).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch045.certificate902).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch111.certificate1341 MergedCutGroups.Batch111.certificate1342 CountingCertificates.Batch045.certificate902 CutLabelCertificates.Entropy026.certificate527 CutLabelCertificates.Minority026.certificate526 matches439 rfl rfl
    MergedCutGroups.Batch111.numericValid1341 MergedCutGroups.Batch111.numericValid1342 MergedCutGroups.Batch111.cellsSound1341 MergedCutGroups.Batch111.cellsSound1342
    MergedCutGroups.Batch111.cellsNumeric1341 MergedCutGroups.Batch111.cellsNumeric1342 MergedCutGroups.Batch111.populationMatches1341 MergedCutGroups.Batch111.populationMatches1342
    PopulationCertificates.Batch045.valid902 PopulationCertificates.Batch045.sound902 WitnessCertificates.Batch045.valid902 WitnessCertificates.Batch045.sound902 CountingCertificates.Batch045.valid902 CountingCertificates.Batch045.sound902
    CutLabelCertificates.Entropy026.valid527 CutLabelCertificates.Minority026.valid526 CutLabelCertificates.Minority026.sound526 H st hI
theorem probabilityBound439 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch111.certificate1341).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate902).dm (WitnessCertificates.Batch045.certificate902).beta) ≤ ((CutFailureCertificates.Budget045.certificate902).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound902 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate902).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch111.certificate1341).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch111.certificate1342).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch045.certificate902).omega:ℝ) ≤ ((CutFailureCertificates.Budget045.certificate902).bound:ℝ) at hb
  exact (exponentialBound439 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch021
