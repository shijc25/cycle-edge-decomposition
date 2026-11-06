import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch042
import Cycle12.CountingCertificates.Batch043
import Cycle12.CountingCertificates.Batch044
import Cycle12.CountingCertificates.Batch045
import Cycle12.CutFailureCertificates.Budget042
import Cycle12.CutFailureCertificates.Budget043
import Cycle12.CutFailureCertificates.Budget044
import Cycle12.CutFailureCertificates.Budget045
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

namespace Cycle12.CertifiedAnchorFailures.Batch021
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches420 : (MergedCutGroups.Batch105.certificate1267).AnchorMatches CountingCertificates.Batch042.certificate846 := by decide +kernel
theorem exponentialBound420 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch105.certificate1267).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch042.certificate846).dm (WitnessCertificates.Batch042.certificate846).beta (WitnessCertificates.Batch042.certificate846).L) ≤ (2*exp (-((CountingCertificates.Batch042.certificate846).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch105.certificate1267).exponent:ℝ)*st.R))/((WitnessCertificates.Batch042.certificate846).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch105.certificate1267 CountingCertificates.Batch042.certificate846 matches420 MergedCutGroups.Batch105.numericValid1267 MergedCutGroups.Batch105.cellsSound1267 MergedCutGroups.Batch105.cellsNumeric1267 MergedCutGroups.Batch105.populationMatches1267
    PopulationCertificates.Batch042.valid846 PopulationCertificates.Batch042.sound846 WitnessCertificates.Batch042.valid846 WitnessCertificates.Batch042.sound846 CountingCertificates.Batch042.valid846 CountingCertificates.Batch042.sound846 H st hI
theorem probabilityBound420 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch105.certificate1267).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch042.certificate846).dm (WitnessCertificates.Batch042.certificate846).beta (WitnessCertificates.Batch042.certificate846).L) ≤ ((CutFailureCertificates.Budget042.certificate846).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound846 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate846).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch105.certificate1267).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch042.certificate846).omega:ℝ)) ≤ ((CutFailureCertificates.Budget042.certificate846).bound:ℝ) at hb
  exact (exponentialBound420 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches421 : (MergedCutGroups.Batch105.certificate1271).AnchorMatches CountingCertificates.Batch042.certificate849 := by decide +kernel
theorem exponentialBound421 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch105.certificate1271).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch042.certificate849).dm (WitnessCertificates.Batch042.certificate849).beta (WitnessCertificates.Batch042.certificate849).L) ≤ (2*exp (-((CountingCertificates.Batch042.certificate849).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch105.certificate1271).exponent:ℝ)*st.R))/((WitnessCertificates.Batch042.certificate849).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch105.certificate1271 CountingCertificates.Batch042.certificate849 matches421 MergedCutGroups.Batch105.numericValid1271 MergedCutGroups.Batch105.cellsSound1271 MergedCutGroups.Batch105.cellsNumeric1271 MergedCutGroups.Batch105.populationMatches1271
    PopulationCertificates.Batch042.valid849 PopulationCertificates.Batch042.sound849 WitnessCertificates.Batch042.valid849 WitnessCertificates.Batch042.sound849 CountingCertificates.Batch042.valid849 CountingCertificates.Batch042.sound849 H st hI
theorem probabilityBound421 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch105.certificate1271).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch042.certificate849).dm (WitnessCertificates.Batch042.certificate849).beta (WitnessCertificates.Batch042.certificate849).L) ≤ ((CutFailureCertificates.Budget042.certificate849).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound849 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate849).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch105.certificate1271).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch042.certificate849).omega:ℝ)) ≤ ((CutFailureCertificates.Budget042.certificate849).bound:ℝ) at hb
  exact (exponentialBound421 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches422 : (MergedCutGroups.Batch106.certificate1275).AnchorMatches CountingCertificates.Batch042.certificate852 := by decide +kernel
theorem exponentialBound422 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch106.certificate1275).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch042.certificate852).dm (WitnessCertificates.Batch042.certificate852).beta (WitnessCertificates.Batch042.certificate852).L) ≤ (2*exp (-((CountingCertificates.Batch042.certificate852).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch106.certificate1275).exponent:ℝ)*st.R))/((WitnessCertificates.Batch042.certificate852).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch106.certificate1275 CountingCertificates.Batch042.certificate852 matches422 MergedCutGroups.Batch106.numericValid1275 MergedCutGroups.Batch106.cellsSound1275 MergedCutGroups.Batch106.cellsNumeric1275 MergedCutGroups.Batch106.populationMatches1275
    PopulationCertificates.Batch042.valid852 PopulationCertificates.Batch042.sound852 WitnessCertificates.Batch042.valid852 WitnessCertificates.Batch042.sound852 CountingCertificates.Batch042.valid852 CountingCertificates.Batch042.sound852 H st hI
theorem probabilityBound422 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch106.certificate1275).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch042.certificate852).dm (WitnessCertificates.Batch042.certificate852).beta (WitnessCertificates.Batch042.certificate852).L) ≤ ((CutFailureCertificates.Budget042.certificate852).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound852 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate852).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch106.certificate1275).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch042.certificate852).omega:ℝ)) ≤ ((CutFailureCertificates.Budget042.certificate852).bound:ℝ) at hb
  exact (exponentialBound422 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches423 : (MergedCutGroups.Batch106.certificate1279).AnchorMatches CountingCertificates.Batch042.certificate855 := by decide +kernel
theorem exponentialBound423 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch106.certificate1279).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch042.certificate855).dm (WitnessCertificates.Batch042.certificate855).beta (WitnessCertificates.Batch042.certificate855).L) ≤ (2*exp (-((CountingCertificates.Batch042.certificate855).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch106.certificate1279).exponent:ℝ)*st.R))/((WitnessCertificates.Batch042.certificate855).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch106.certificate1279 CountingCertificates.Batch042.certificate855 matches423 MergedCutGroups.Batch106.numericValid1279 MergedCutGroups.Batch106.cellsSound1279 MergedCutGroups.Batch106.cellsNumeric1279 MergedCutGroups.Batch106.populationMatches1279
    PopulationCertificates.Batch042.valid855 PopulationCertificates.Batch042.sound855 WitnessCertificates.Batch042.valid855 WitnessCertificates.Batch042.sound855 CountingCertificates.Batch042.valid855 CountingCertificates.Batch042.sound855 H st hI
theorem probabilityBound423 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch106.certificate1279).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch042.certificate855).dm (WitnessCertificates.Batch042.certificate855).beta (WitnessCertificates.Batch042.certificate855).L) ≤ ((CutFailureCertificates.Budget042.certificate855).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound855 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate855).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch106.certificate1279).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch042.certificate855).omega:ℝ)) ≤ ((CutFailureCertificates.Budget042.certificate855).bound:ℝ) at hb
  exact (exponentialBound423 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches424 : (MergedCutGroups.Batch106.certificate1283).AnchorMatches CountingCertificates.Batch042.certificate858 := by decide +kernel
theorem exponentialBound424 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch106.certificate1283).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch042.certificate858).dm (WitnessCertificates.Batch042.certificate858).beta (WitnessCertificates.Batch042.certificate858).L) ≤ (2*exp (-((CountingCertificates.Batch042.certificate858).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch106.certificate1283).exponent:ℝ)*st.R))/((WitnessCertificates.Batch042.certificate858).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch106.certificate1283 CountingCertificates.Batch042.certificate858 matches424 MergedCutGroups.Batch106.numericValid1283 MergedCutGroups.Batch106.cellsSound1283 MergedCutGroups.Batch106.cellsNumeric1283 MergedCutGroups.Batch106.populationMatches1283
    PopulationCertificates.Batch042.valid858 PopulationCertificates.Batch042.sound858 WitnessCertificates.Batch042.valid858 WitnessCertificates.Batch042.sound858 CountingCertificates.Batch042.valid858 CountingCertificates.Batch042.sound858 H st hI
theorem probabilityBound424 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch106.certificate1283).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch042.certificate858).dm (WitnessCertificates.Batch042.certificate858).beta (WitnessCertificates.Batch042.certificate858).L) ≤ ((CutFailureCertificates.Budget042.certificate858).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound858 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate858).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch106.certificate1283).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch042.certificate858).omega:ℝ)) ≤ ((CutFailureCertificates.Budget042.certificate858).bound:ℝ) at hb
  exact (exponentialBound424 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches425 : (MergedCutGroups.Batch107.certificate1287).AnchorMatches CountingCertificates.Batch043.certificate861 := by decide +kernel
theorem exponentialBound425 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch107.certificate1287).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch043.certificate861).dm (WitnessCertificates.Batch043.certificate861).beta (WitnessCertificates.Batch043.certificate861).L) ≤ (2*exp (-((CountingCertificates.Batch043.certificate861).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch107.certificate1287).exponent:ℝ)*st.R))/((WitnessCertificates.Batch043.certificate861).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch107.certificate1287 CountingCertificates.Batch043.certificate861 matches425 MergedCutGroups.Batch107.numericValid1287 MergedCutGroups.Batch107.cellsSound1287 MergedCutGroups.Batch107.cellsNumeric1287 MergedCutGroups.Batch107.populationMatches1287
    PopulationCertificates.Batch043.valid861 PopulationCertificates.Batch043.sound861 WitnessCertificates.Batch043.valid861 WitnessCertificates.Batch043.sound861 CountingCertificates.Batch043.valid861 CountingCertificates.Batch043.sound861 H st hI
theorem probabilityBound425 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch107.certificate1287).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch043.certificate861).dm (WitnessCertificates.Batch043.certificate861).beta (WitnessCertificates.Batch043.certificate861).L) ≤ ((CutFailureCertificates.Budget043.certificate861).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound861 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate861).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch107.certificate1287).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch043.certificate861).omega:ℝ)) ≤ ((CutFailureCertificates.Budget043.certificate861).bound:ℝ) at hb
  exact (exponentialBound425 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches426 : (MergedCutGroups.Batch107.certificate1291).AnchorMatches CountingCertificates.Batch043.certificate864 := by decide +kernel
theorem exponentialBound426 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch107.certificate1291).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch043.certificate864).dm (WitnessCertificates.Batch043.certificate864).beta (WitnessCertificates.Batch043.certificate864).L) ≤ (2*exp (-((CountingCertificates.Batch043.certificate864).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch107.certificate1291).exponent:ℝ)*st.R))/((WitnessCertificates.Batch043.certificate864).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch107.certificate1291 CountingCertificates.Batch043.certificate864 matches426 MergedCutGroups.Batch107.numericValid1291 MergedCutGroups.Batch107.cellsSound1291 MergedCutGroups.Batch107.cellsNumeric1291 MergedCutGroups.Batch107.populationMatches1291
    PopulationCertificates.Batch043.valid864 PopulationCertificates.Batch043.sound864 WitnessCertificates.Batch043.valid864 WitnessCertificates.Batch043.sound864 CountingCertificates.Batch043.valid864 CountingCertificates.Batch043.sound864 H st hI
theorem probabilityBound426 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch107.certificate1291).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch043.certificate864).dm (WitnessCertificates.Batch043.certificate864).beta (WitnessCertificates.Batch043.certificate864).L) ≤ ((CutFailureCertificates.Budget043.certificate864).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound864 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate864).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch107.certificate1291).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch043.certificate864).omega:ℝ)) ≤ ((CutFailureCertificates.Budget043.certificate864).bound:ℝ) at hb
  exact (exponentialBound426 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches427 : (MergedCutGroups.Batch107.certificate1295).AnchorMatches CountingCertificates.Batch043.certificate867 := by decide +kernel
theorem exponentialBound427 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch107.certificate1295).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch043.certificate867).dm (WitnessCertificates.Batch043.certificate867).beta (WitnessCertificates.Batch043.certificate867).L) ≤ (2*exp (-((CountingCertificates.Batch043.certificate867).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch107.certificate1295).exponent:ℝ)*st.R))/((WitnessCertificates.Batch043.certificate867).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch107.certificate1295 CountingCertificates.Batch043.certificate867 matches427 MergedCutGroups.Batch107.numericValid1295 MergedCutGroups.Batch107.cellsSound1295 MergedCutGroups.Batch107.cellsNumeric1295 MergedCutGroups.Batch107.populationMatches1295
    PopulationCertificates.Batch043.valid867 PopulationCertificates.Batch043.sound867 WitnessCertificates.Batch043.valid867 WitnessCertificates.Batch043.sound867 CountingCertificates.Batch043.valid867 CountingCertificates.Batch043.sound867 H st hI
theorem probabilityBound427 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch107.certificate1295).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch043.certificate867).dm (WitnessCertificates.Batch043.certificate867).beta (WitnessCertificates.Batch043.certificate867).L) ≤ ((CutFailureCertificates.Budget043.certificate867).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound867 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate867).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch107.certificate1295).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch043.certificate867).omega:ℝ)) ≤ ((CutFailureCertificates.Budget043.certificate867).bound:ℝ) at hb
  exact (exponentialBound427 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches428 : (MergedCutGroups.Batch108.certificate1299).AnchorMatches CountingCertificates.Batch043.certificate870 := by decide +kernel
theorem exponentialBound428 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch108.certificate1299).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch043.certificate870).dm (WitnessCertificates.Batch043.certificate870).beta (WitnessCertificates.Batch043.certificate870).L) ≤ (2*exp (-((CountingCertificates.Batch043.certificate870).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch108.certificate1299).exponent:ℝ)*st.R))/((WitnessCertificates.Batch043.certificate870).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch108.certificate1299 CountingCertificates.Batch043.certificate870 matches428 MergedCutGroups.Batch108.numericValid1299 MergedCutGroups.Batch108.cellsSound1299 MergedCutGroups.Batch108.cellsNumeric1299 MergedCutGroups.Batch108.populationMatches1299
    PopulationCertificates.Batch043.valid870 PopulationCertificates.Batch043.sound870 WitnessCertificates.Batch043.valid870 WitnessCertificates.Batch043.sound870 CountingCertificates.Batch043.valid870 CountingCertificates.Batch043.sound870 H st hI
theorem probabilityBound428 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch108.certificate1299).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch043.certificate870).dm (WitnessCertificates.Batch043.certificate870).beta (WitnessCertificates.Batch043.certificate870).L) ≤ ((CutFailureCertificates.Budget043.certificate870).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound870 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate870).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch108.certificate1299).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch043.certificate870).omega:ℝ)) ≤ ((CutFailureCertificates.Budget043.certificate870).bound:ℝ) at hb
  exact (exponentialBound428 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches429 : (MergedCutGroups.Batch108.certificate1303).AnchorMatches CountingCertificates.Batch043.certificate873 := by decide +kernel
theorem exponentialBound429 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch108.certificate1303).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch043.certificate873).dm (WitnessCertificates.Batch043.certificate873).beta (WitnessCertificates.Batch043.certificate873).L) ≤ (2*exp (-((CountingCertificates.Batch043.certificate873).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch108.certificate1303).exponent:ℝ)*st.R))/((WitnessCertificates.Batch043.certificate873).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch108.certificate1303 CountingCertificates.Batch043.certificate873 matches429 MergedCutGroups.Batch108.numericValid1303 MergedCutGroups.Batch108.cellsSound1303 MergedCutGroups.Batch108.cellsNumeric1303 MergedCutGroups.Batch108.populationMatches1303
    PopulationCertificates.Batch043.valid873 PopulationCertificates.Batch043.sound873 WitnessCertificates.Batch043.valid873 WitnessCertificates.Batch043.sound873 CountingCertificates.Batch043.valid873 CountingCertificates.Batch043.sound873 H st hI
theorem probabilityBound429 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch108.certificate1303).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch043.certificate873).dm (WitnessCertificates.Batch043.certificate873).beta (WitnessCertificates.Batch043.certificate873).L) ≤ ((CutFailureCertificates.Budget043.certificate873).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound873 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate873).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch108.certificate1303).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch043.certificate873).omega:ℝ)) ≤ ((CutFailureCertificates.Budget043.certificate873).bound:ℝ) at hb
  exact (exponentialBound429 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches430 : (MergedCutGroups.Batch108.certificate1307).AnchorMatches CountingCertificates.Batch043.certificate876 := by decide +kernel
theorem exponentialBound430 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch108.certificate1307).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch043.certificate876).dm (WitnessCertificates.Batch043.certificate876).beta (WitnessCertificates.Batch043.certificate876).L) ≤ (2*exp (-((CountingCertificates.Batch043.certificate876).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch108.certificate1307).exponent:ℝ)*st.R))/((WitnessCertificates.Batch043.certificate876).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch108.certificate1307 CountingCertificates.Batch043.certificate876 matches430 MergedCutGroups.Batch108.numericValid1307 MergedCutGroups.Batch108.cellsSound1307 MergedCutGroups.Batch108.cellsNumeric1307 MergedCutGroups.Batch108.populationMatches1307
    PopulationCertificates.Batch043.valid876 PopulationCertificates.Batch043.sound876 WitnessCertificates.Batch043.valid876 WitnessCertificates.Batch043.sound876 CountingCertificates.Batch043.valid876 CountingCertificates.Batch043.sound876 H st hI
theorem probabilityBound430 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch108.certificate1307).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch043.certificate876).dm (WitnessCertificates.Batch043.certificate876).beta (WitnessCertificates.Batch043.certificate876).L) ≤ ((CutFailureCertificates.Budget043.certificate876).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound876 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate876).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch108.certificate1307).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch043.certificate876).omega:ℝ)) ≤ ((CutFailureCertificates.Budget043.certificate876).bound:ℝ) at hb
  exact (exponentialBound430 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches431 : (MergedCutGroups.Batch109.certificate1311).AnchorMatches CountingCertificates.Batch043.certificate879 := by decide +kernel
theorem exponentialBound431 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch109.certificate1311).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch043.certificate879).dm (WitnessCertificates.Batch043.certificate879).beta (WitnessCertificates.Batch043.certificate879).L) ≤ (2*exp (-((CountingCertificates.Batch043.certificate879).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch109.certificate1311).exponent:ℝ)*st.R))/((WitnessCertificates.Batch043.certificate879).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch109.certificate1311 CountingCertificates.Batch043.certificate879 matches431 MergedCutGroups.Batch109.numericValid1311 MergedCutGroups.Batch109.cellsSound1311 MergedCutGroups.Batch109.cellsNumeric1311 MergedCutGroups.Batch109.populationMatches1311
    PopulationCertificates.Batch043.valid879 PopulationCertificates.Batch043.sound879 WitnessCertificates.Batch043.valid879 WitnessCertificates.Batch043.sound879 CountingCertificates.Batch043.valid879 CountingCertificates.Batch043.sound879 H st hI
theorem probabilityBound431 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch109.certificate1311).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch043.certificate879).dm (WitnessCertificates.Batch043.certificate879).beta (WitnessCertificates.Batch043.certificate879).L) ≤ ((CutFailureCertificates.Budget043.certificate879).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound879 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate879).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch109.certificate1311).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch043.certificate879).omega:ℝ)) ≤ ((CutFailureCertificates.Budget043.certificate879).bound:ℝ) at hb
  exact (exponentialBound431 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches432 : (MergedCutGroups.Batch109.certificate1315).AnchorMatches CountingCertificates.Batch044.certificate882 := by decide +kernel
theorem exponentialBound432 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch109.certificate1315).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch044.certificate882).dm (WitnessCertificates.Batch044.certificate882).beta (WitnessCertificates.Batch044.certificate882).L) ≤ (2*exp (-((CountingCertificates.Batch044.certificate882).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch109.certificate1315).exponent:ℝ)*st.R))/((WitnessCertificates.Batch044.certificate882).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch109.certificate1315 CountingCertificates.Batch044.certificate882 matches432 MergedCutGroups.Batch109.numericValid1315 MergedCutGroups.Batch109.cellsSound1315 MergedCutGroups.Batch109.cellsNumeric1315 MergedCutGroups.Batch109.populationMatches1315
    PopulationCertificates.Batch044.valid882 PopulationCertificates.Batch044.sound882 WitnessCertificates.Batch044.valid882 WitnessCertificates.Batch044.sound882 CountingCertificates.Batch044.valid882 CountingCertificates.Batch044.sound882 H st hI
theorem probabilityBound432 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch109.certificate1315).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch044.certificate882).dm (WitnessCertificates.Batch044.certificate882).beta (WitnessCertificates.Batch044.certificate882).L) ≤ ((CutFailureCertificates.Budget044.certificate882).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound882 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate882).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch109.certificate1315).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch044.certificate882).omega:ℝ)) ≤ ((CutFailureCertificates.Budget044.certificate882).bound:ℝ) at hb
  exact (exponentialBound432 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches433 : (MergedCutGroups.Batch109.certificate1319).AnchorMatches CountingCertificates.Batch044.certificate885 := by decide +kernel
theorem exponentialBound433 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch109.certificate1319).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch044.certificate885).dm (WitnessCertificates.Batch044.certificate885).beta (WitnessCertificates.Batch044.certificate885).L) ≤ (2*exp (-((CountingCertificates.Batch044.certificate885).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch109.certificate1319).exponent:ℝ)*st.R))/((WitnessCertificates.Batch044.certificate885).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch109.certificate1319 CountingCertificates.Batch044.certificate885 matches433 MergedCutGroups.Batch109.numericValid1319 MergedCutGroups.Batch109.cellsSound1319 MergedCutGroups.Batch109.cellsNumeric1319 MergedCutGroups.Batch109.populationMatches1319
    PopulationCertificates.Batch044.valid885 PopulationCertificates.Batch044.sound885 WitnessCertificates.Batch044.valid885 WitnessCertificates.Batch044.sound885 CountingCertificates.Batch044.valid885 CountingCertificates.Batch044.sound885 H st hI
theorem probabilityBound433 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch109.certificate1319).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch044.certificate885).dm (WitnessCertificates.Batch044.certificate885).beta (WitnessCertificates.Batch044.certificate885).L) ≤ ((CutFailureCertificates.Budget044.certificate885).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound885 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate885).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch109.certificate1319).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch044.certificate885).omega:ℝ)) ≤ ((CutFailureCertificates.Budget044.certificate885).bound:ℝ) at hb
  exact (exponentialBound433 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches434 : (MergedCutGroups.Batch110.certificate1323).AnchorMatches CountingCertificates.Batch044.certificate888 := by decide +kernel
theorem exponentialBound434 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch110.certificate1323).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch044.certificate888).dm (WitnessCertificates.Batch044.certificate888).beta (WitnessCertificates.Batch044.certificate888).L) ≤ (2*exp (-((CountingCertificates.Batch044.certificate888).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch110.certificate1323).exponent:ℝ)*st.R))/((WitnessCertificates.Batch044.certificate888).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch110.certificate1323 CountingCertificates.Batch044.certificate888 matches434 MergedCutGroups.Batch110.numericValid1323 MergedCutGroups.Batch110.cellsSound1323 MergedCutGroups.Batch110.cellsNumeric1323 MergedCutGroups.Batch110.populationMatches1323
    PopulationCertificates.Batch044.valid888 PopulationCertificates.Batch044.sound888 WitnessCertificates.Batch044.valid888 WitnessCertificates.Batch044.sound888 CountingCertificates.Batch044.valid888 CountingCertificates.Batch044.sound888 H st hI
theorem probabilityBound434 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch110.certificate1323).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch044.certificate888).dm (WitnessCertificates.Batch044.certificate888).beta (WitnessCertificates.Batch044.certificate888).L) ≤ ((CutFailureCertificates.Budget044.certificate888).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound888 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate888).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch110.certificate1323).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch044.certificate888).omega:ℝ)) ≤ ((CutFailureCertificates.Budget044.certificate888).bound:ℝ) at hb
  exact (exponentialBound434 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches435 : (MergedCutGroups.Batch110.certificate1327).AnchorMatches CountingCertificates.Batch044.certificate891 := by decide +kernel
theorem exponentialBound435 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch110.certificate1327).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch044.certificate891).dm (WitnessCertificates.Batch044.certificate891).beta (WitnessCertificates.Batch044.certificate891).L) ≤ (2*exp (-((CountingCertificates.Batch044.certificate891).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch110.certificate1327).exponent:ℝ)*st.R))/((WitnessCertificates.Batch044.certificate891).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch110.certificate1327 CountingCertificates.Batch044.certificate891 matches435 MergedCutGroups.Batch110.numericValid1327 MergedCutGroups.Batch110.cellsSound1327 MergedCutGroups.Batch110.cellsNumeric1327 MergedCutGroups.Batch110.populationMatches1327
    PopulationCertificates.Batch044.valid891 PopulationCertificates.Batch044.sound891 WitnessCertificates.Batch044.valid891 WitnessCertificates.Batch044.sound891 CountingCertificates.Batch044.valid891 CountingCertificates.Batch044.sound891 H st hI
theorem probabilityBound435 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch110.certificate1327).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch044.certificate891).dm (WitnessCertificates.Batch044.certificate891).beta (WitnessCertificates.Batch044.certificate891).L) ≤ ((CutFailureCertificates.Budget044.certificate891).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound891 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate891).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch110.certificate1327).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch044.certificate891).omega:ℝ)) ≤ ((CutFailureCertificates.Budget044.certificate891).bound:ℝ) at hb
  exact (exponentialBound435 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches436 : (MergedCutGroups.Batch110.certificate1331).AnchorMatches CountingCertificates.Batch044.certificate894 := by decide +kernel
theorem exponentialBound436 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch110.certificate1331).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch044.certificate894).dm (WitnessCertificates.Batch044.certificate894).beta (WitnessCertificates.Batch044.certificate894).L) ≤ (2*exp (-((CountingCertificates.Batch044.certificate894).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch110.certificate1331).exponent:ℝ)*st.R))/((WitnessCertificates.Batch044.certificate894).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch110.certificate1331 CountingCertificates.Batch044.certificate894 matches436 MergedCutGroups.Batch110.numericValid1331 MergedCutGroups.Batch110.cellsSound1331 MergedCutGroups.Batch110.cellsNumeric1331 MergedCutGroups.Batch110.populationMatches1331
    PopulationCertificates.Batch044.valid894 PopulationCertificates.Batch044.sound894 WitnessCertificates.Batch044.valid894 WitnessCertificates.Batch044.sound894 CountingCertificates.Batch044.valid894 CountingCertificates.Batch044.sound894 H st hI
theorem probabilityBound436 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch110.certificate1331).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch044.certificate894).dm (WitnessCertificates.Batch044.certificate894).beta (WitnessCertificates.Batch044.certificate894).L) ≤ ((CutFailureCertificates.Budget044.certificate894).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound894 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate894).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch110.certificate1331).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch044.certificate894).omega:ℝ)) ≤ ((CutFailureCertificates.Budget044.certificate894).bound:ℝ) at hb
  exact (exponentialBound436 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches437 : (MergedCutGroups.Batch111.certificate1335).AnchorMatches CountingCertificates.Batch044.certificate897 := by decide +kernel
theorem exponentialBound437 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch111.certificate1335).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch044.certificate897).dm (WitnessCertificates.Batch044.certificate897).beta (WitnessCertificates.Batch044.certificate897).L) ≤ (2*exp (-((CountingCertificates.Batch044.certificate897).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch111.certificate1335).exponent:ℝ)*st.R))/((WitnessCertificates.Batch044.certificate897).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch111.certificate1335 CountingCertificates.Batch044.certificate897 matches437 MergedCutGroups.Batch111.numericValid1335 MergedCutGroups.Batch111.cellsSound1335 MergedCutGroups.Batch111.cellsNumeric1335 MergedCutGroups.Batch111.populationMatches1335
    PopulationCertificates.Batch044.valid897 PopulationCertificates.Batch044.sound897 WitnessCertificates.Batch044.valid897 WitnessCertificates.Batch044.sound897 CountingCertificates.Batch044.valid897 CountingCertificates.Batch044.sound897 H st hI
theorem probabilityBound437 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch111.certificate1335).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch044.certificate897).dm (WitnessCertificates.Batch044.certificate897).beta (WitnessCertificates.Batch044.certificate897).L) ≤ ((CutFailureCertificates.Budget044.certificate897).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound897 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate897).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch111.certificate1335).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch044.certificate897).omega:ℝ)) ≤ ((CutFailureCertificates.Budget044.certificate897).bound:ℝ) at hb
  exact (exponentialBound437 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches438 : (MergedCutGroups.Batch111.certificate1339).AnchorMatches CountingCertificates.Batch045.certificate900 := by decide +kernel
theorem exponentialBound438 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch111.certificate1339).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch045.certificate900).dm (WitnessCertificates.Batch045.certificate900).beta (WitnessCertificates.Batch045.certificate900).L) ≤ (2*exp (-((CountingCertificates.Batch045.certificate900).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch111.certificate1339).exponent:ℝ)*st.R))/((WitnessCertificates.Batch045.certificate900).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch111.certificate1339 CountingCertificates.Batch045.certificate900 matches438 MergedCutGroups.Batch111.numericValid1339 MergedCutGroups.Batch111.cellsSound1339 MergedCutGroups.Batch111.cellsNumeric1339 MergedCutGroups.Batch111.populationMatches1339
    PopulationCertificates.Batch045.valid900 PopulationCertificates.Batch045.sound900 WitnessCertificates.Batch045.valid900 WitnessCertificates.Batch045.sound900 CountingCertificates.Batch045.valid900 CountingCertificates.Batch045.sound900 H st hI
theorem probabilityBound438 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch111.certificate1339).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch045.certificate900).dm (WitnessCertificates.Batch045.certificate900).beta (WitnessCertificates.Batch045.certificate900).L) ≤ ((CutFailureCertificates.Budget045.certificate900).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound900 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate900).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch111.certificate1339).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch045.certificate900).omega:ℝ)) ≤ ((CutFailureCertificates.Budget045.certificate900).bound:ℝ) at hb
  exact (exponentialBound438 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches439 : (MergedCutGroups.Batch111.certificate1343).AnchorMatches CountingCertificates.Batch045.certificate903 := by decide +kernel
theorem exponentialBound439 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch111.certificate1343).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch045.certificate903).dm (WitnessCertificates.Batch045.certificate903).beta (WitnessCertificates.Batch045.certificate903).L) ≤ (2*exp (-((CountingCertificates.Batch045.certificate903).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch111.certificate1343).exponent:ℝ)*st.R))/((WitnessCertificates.Batch045.certificate903).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch111.certificate1343 CountingCertificates.Batch045.certificate903 matches439 MergedCutGroups.Batch111.numericValid1343 MergedCutGroups.Batch111.cellsSound1343 MergedCutGroups.Batch111.cellsNumeric1343 MergedCutGroups.Batch111.populationMatches1343
    PopulationCertificates.Batch045.valid903 PopulationCertificates.Batch045.sound903 WitnessCertificates.Batch045.valid903 WitnessCertificates.Batch045.sound903 CountingCertificates.Batch045.valid903 CountingCertificates.Batch045.sound903 H st hI
theorem probabilityBound439 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch111.certificate1343).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch045.certificate903).dm (WitnessCertificates.Batch045.certificate903).beta (WitnessCertificates.Batch045.certificate903).L) ≤ ((CutFailureCertificates.Budget045.certificate903).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound903 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate903).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch111.certificate1343).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch045.certificate903).omega:ℝ)) ≤ ((CutFailureCertificates.Budget045.certificate903).bound:ℝ) at hb
  exact (exponentialBound439 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch021
