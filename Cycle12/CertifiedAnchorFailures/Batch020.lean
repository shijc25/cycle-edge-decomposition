import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch040
import Cycle12.CountingCertificates.Batch041
import Cycle12.CountingCertificates.Batch042
import Cycle12.CutFailureCertificates.Budget040
import Cycle12.CutFailureCertificates.Budget041
import Cycle12.CutFailureCertificates.Budget042
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

namespace Cycle12.CertifiedAnchorFailures.Batch020
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches400 : (MergedCutGroups.Batch100.certificate1202).AnchorMatches CountingCertificates.Batch040.certificate801 := by decide +kernel
theorem exponentialBound400 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch100.certificate1202).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate801).dm (WitnessCertificates.Batch040.certificate801).beta (WitnessCertificates.Batch040.certificate801).L) ≤ (2*exp (-((CountingCertificates.Batch040.certificate801).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch100.certificate1202).exponent:ℝ)*st.R))/((WitnessCertificates.Batch040.certificate801).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch100.certificate1202 CountingCertificates.Batch040.certificate801 matches400 MergedCutGroups.Batch100.numericValid1202 MergedCutGroups.Batch100.cellsSound1202 MergedCutGroups.Batch100.cellsNumeric1202 MergedCutGroups.Batch100.populationMatches1202
    PopulationCertificates.Batch040.valid801 PopulationCertificates.Batch040.sound801 WitnessCertificates.Batch040.valid801 WitnessCertificates.Batch040.sound801 CountingCertificates.Batch040.valid801 CountingCertificates.Batch040.sound801 H st hI
theorem probabilityBound400 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch100.certificate1202).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate801).dm (WitnessCertificates.Batch040.certificate801).beta (WitnessCertificates.Batch040.certificate801).L) ≤ ((CutFailureCertificates.Budget040.certificate801).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound801 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate801).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch100.certificate1202).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch040.certificate801).omega:ℝ)) ≤ ((CutFailureCertificates.Budget040.certificate801).bound:ℝ) at hb
  exact (exponentialBound400 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches401 : (MergedCutGroups.Batch100.certificate1205).AnchorMatches CountingCertificates.Batch040.certificate803 := by decide +kernel
theorem exponentialBound401 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch100.certificate1205).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate803).dm (WitnessCertificates.Batch040.certificate803).beta (WitnessCertificates.Batch040.certificate803).L) ≤ (2*exp (-((CountingCertificates.Batch040.certificate803).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch100.certificate1205).exponent:ℝ)*st.R))/((WitnessCertificates.Batch040.certificate803).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch100.certificate1205 CountingCertificates.Batch040.certificate803 matches401 MergedCutGroups.Batch100.numericValid1205 MergedCutGroups.Batch100.cellsSound1205 MergedCutGroups.Batch100.cellsNumeric1205 MergedCutGroups.Batch100.populationMatches1205
    PopulationCertificates.Batch040.valid803 PopulationCertificates.Batch040.sound803 WitnessCertificates.Batch040.valid803 WitnessCertificates.Batch040.sound803 CountingCertificates.Batch040.valid803 CountingCertificates.Batch040.sound803 H st hI
theorem probabilityBound401 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch100.certificate1205).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate803).dm (WitnessCertificates.Batch040.certificate803).beta (WitnessCertificates.Batch040.certificate803).L) ≤ ((CutFailureCertificates.Budget040.certificate803).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound803 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate803).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch100.certificate1205).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch040.certificate803).omega:ℝ)) ≤ ((CutFailureCertificates.Budget040.certificate803).bound:ℝ) at hb
  exact (exponentialBound401 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches402 : (MergedCutGroups.Batch100.certificate1208).AnchorMatches CountingCertificates.Batch040.certificate805 := by decide +kernel
theorem exponentialBound402 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch100.certificate1208).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate805).dm (WitnessCertificates.Batch040.certificate805).beta (WitnessCertificates.Batch040.certificate805).L) ≤ (2*exp (-((CountingCertificates.Batch040.certificate805).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch100.certificate1208).exponent:ℝ)*st.R))/((WitnessCertificates.Batch040.certificate805).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch100.certificate1208 CountingCertificates.Batch040.certificate805 matches402 MergedCutGroups.Batch100.numericValid1208 MergedCutGroups.Batch100.cellsSound1208 MergedCutGroups.Batch100.cellsNumeric1208 MergedCutGroups.Batch100.populationMatches1208
    PopulationCertificates.Batch040.valid805 PopulationCertificates.Batch040.sound805 WitnessCertificates.Batch040.valid805 WitnessCertificates.Batch040.sound805 CountingCertificates.Batch040.valid805 CountingCertificates.Batch040.sound805 H st hI
theorem probabilityBound402 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch100.certificate1208).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate805).dm (WitnessCertificates.Batch040.certificate805).beta (WitnessCertificates.Batch040.certificate805).L) ≤ ((CutFailureCertificates.Budget040.certificate805).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound805 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate805).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch100.certificate1208).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch040.certificate805).omega:ℝ)) ≤ ((CutFailureCertificates.Budget040.certificate805).bound:ℝ) at hb
  exact (exponentialBound402 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches403 : (MergedCutGroups.Batch100.certificate1211).AnchorMatches CountingCertificates.Batch040.certificate807 := by decide +kernel
theorem exponentialBound403 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch100.certificate1211).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate807).dm (WitnessCertificates.Batch040.certificate807).beta (WitnessCertificates.Batch040.certificate807).L) ≤ (2*exp (-((CountingCertificates.Batch040.certificate807).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch100.certificate1211).exponent:ℝ)*st.R))/((WitnessCertificates.Batch040.certificate807).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch100.certificate1211 CountingCertificates.Batch040.certificate807 matches403 MergedCutGroups.Batch100.numericValid1211 MergedCutGroups.Batch100.cellsSound1211 MergedCutGroups.Batch100.cellsNumeric1211 MergedCutGroups.Batch100.populationMatches1211
    PopulationCertificates.Batch040.valid807 PopulationCertificates.Batch040.sound807 WitnessCertificates.Batch040.valid807 WitnessCertificates.Batch040.sound807 CountingCertificates.Batch040.valid807 CountingCertificates.Batch040.sound807 H st hI
theorem probabilityBound403 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch100.certificate1211).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate807).dm (WitnessCertificates.Batch040.certificate807).beta (WitnessCertificates.Batch040.certificate807).L) ≤ ((CutFailureCertificates.Budget040.certificate807).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound807 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate807).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch100.certificate1211).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch040.certificate807).omega:ℝ)) ≤ ((CutFailureCertificates.Budget040.certificate807).bound:ℝ) at hb
  exact (exponentialBound403 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches404 : (MergedCutGroups.Batch101.certificate1214).AnchorMatches CountingCertificates.Batch040.certificate809 := by decide +kernel
theorem exponentialBound404 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch101.certificate1214).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate809).dm (WitnessCertificates.Batch040.certificate809).beta (WitnessCertificates.Batch040.certificate809).L) ≤ (2*exp (-((CountingCertificates.Batch040.certificate809).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch101.certificate1214).exponent:ℝ)*st.R))/((WitnessCertificates.Batch040.certificate809).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch101.certificate1214 CountingCertificates.Batch040.certificate809 matches404 MergedCutGroups.Batch101.numericValid1214 MergedCutGroups.Batch101.cellsSound1214 MergedCutGroups.Batch101.cellsNumeric1214 MergedCutGroups.Batch101.populationMatches1214
    PopulationCertificates.Batch040.valid809 PopulationCertificates.Batch040.sound809 WitnessCertificates.Batch040.valid809 WitnessCertificates.Batch040.sound809 CountingCertificates.Batch040.valid809 CountingCertificates.Batch040.sound809 H st hI
theorem probabilityBound404 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch101.certificate1214).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate809).dm (WitnessCertificates.Batch040.certificate809).beta (WitnessCertificates.Batch040.certificate809).L) ≤ ((CutFailureCertificates.Budget040.certificate809).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound809 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate809).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch101.certificate1214).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch040.certificate809).omega:ℝ)) ≤ ((CutFailureCertificates.Budget040.certificate809).bound:ℝ) at hb
  exact (exponentialBound404 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches405 : (MergedCutGroups.Batch101.certificate1217).AnchorMatches CountingCertificates.Batch040.certificate811 := by decide +kernel
theorem exponentialBound405 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch101.certificate1217).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate811).dm (WitnessCertificates.Batch040.certificate811).beta (WitnessCertificates.Batch040.certificate811).L) ≤ (2*exp (-((CountingCertificates.Batch040.certificate811).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch101.certificate1217).exponent:ℝ)*st.R))/((WitnessCertificates.Batch040.certificate811).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch101.certificate1217 CountingCertificates.Batch040.certificate811 matches405 MergedCutGroups.Batch101.numericValid1217 MergedCutGroups.Batch101.cellsSound1217 MergedCutGroups.Batch101.cellsNumeric1217 MergedCutGroups.Batch101.populationMatches1217
    PopulationCertificates.Batch040.valid811 PopulationCertificates.Batch040.sound811 WitnessCertificates.Batch040.valid811 WitnessCertificates.Batch040.sound811 CountingCertificates.Batch040.valid811 CountingCertificates.Batch040.sound811 H st hI
theorem probabilityBound405 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch101.certificate1217).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate811).dm (WitnessCertificates.Batch040.certificate811).beta (WitnessCertificates.Batch040.certificate811).L) ≤ ((CutFailureCertificates.Budget040.certificate811).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound811 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate811).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch101.certificate1217).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch040.certificate811).omega:ℝ)) ≤ ((CutFailureCertificates.Budget040.certificate811).bound:ℝ) at hb
  exact (exponentialBound405 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches406 : (MergedCutGroups.Batch101.certificate1220).AnchorMatches CountingCertificates.Batch040.certificate813 := by decide +kernel
theorem exponentialBound406 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch101.certificate1220).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate813).dm (WitnessCertificates.Batch040.certificate813).beta (WitnessCertificates.Batch040.certificate813).L) ≤ (2*exp (-((CountingCertificates.Batch040.certificate813).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch101.certificate1220).exponent:ℝ)*st.R))/((WitnessCertificates.Batch040.certificate813).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch101.certificate1220 CountingCertificates.Batch040.certificate813 matches406 MergedCutGroups.Batch101.numericValid1220 MergedCutGroups.Batch101.cellsSound1220 MergedCutGroups.Batch101.cellsNumeric1220 MergedCutGroups.Batch101.populationMatches1220
    PopulationCertificates.Batch040.valid813 PopulationCertificates.Batch040.sound813 WitnessCertificates.Batch040.valid813 WitnessCertificates.Batch040.sound813 CountingCertificates.Batch040.valid813 CountingCertificates.Batch040.sound813 H st hI
theorem probabilityBound406 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch101.certificate1220).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate813).dm (WitnessCertificates.Batch040.certificate813).beta (WitnessCertificates.Batch040.certificate813).L) ≤ ((CutFailureCertificates.Budget040.certificate813).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound813 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate813).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch101.certificate1220).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch040.certificate813).omega:ℝ)) ≤ ((CutFailureCertificates.Budget040.certificate813).bound:ℝ) at hb
  exact (exponentialBound406 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches407 : (MergedCutGroups.Batch101.certificate1223).AnchorMatches CountingCertificates.Batch040.certificate815 := by decide +kernel
theorem exponentialBound407 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch101.certificate1223).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate815).dm (WitnessCertificates.Batch040.certificate815).beta (WitnessCertificates.Batch040.certificate815).L) ≤ (2*exp (-((CountingCertificates.Batch040.certificate815).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch101.certificate1223).exponent:ℝ)*st.R))/((WitnessCertificates.Batch040.certificate815).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch101.certificate1223 CountingCertificates.Batch040.certificate815 matches407 MergedCutGroups.Batch101.numericValid1223 MergedCutGroups.Batch101.cellsSound1223 MergedCutGroups.Batch101.cellsNumeric1223 MergedCutGroups.Batch101.populationMatches1223
    PopulationCertificates.Batch040.valid815 PopulationCertificates.Batch040.sound815 WitnessCertificates.Batch040.valid815 WitnessCertificates.Batch040.sound815 CountingCertificates.Batch040.valid815 CountingCertificates.Batch040.sound815 H st hI
theorem probabilityBound407 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch101.certificate1223).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate815).dm (WitnessCertificates.Batch040.certificate815).beta (WitnessCertificates.Batch040.certificate815).L) ≤ ((CutFailureCertificates.Budget040.certificate815).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound815 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate815).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch101.certificate1223).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch040.certificate815).omega:ℝ)) ≤ ((CutFailureCertificates.Budget040.certificate815).bound:ℝ) at hb
  exact (exponentialBound407 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches408 : (MergedCutGroups.Batch102.certificate1226).AnchorMatches CountingCertificates.Batch040.certificate817 := by decide +kernel
theorem exponentialBound408 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch102.certificate1226).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate817).dm (WitnessCertificates.Batch040.certificate817).beta (WitnessCertificates.Batch040.certificate817).L) ≤ (2*exp (-((CountingCertificates.Batch040.certificate817).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch102.certificate1226).exponent:ℝ)*st.R))/((WitnessCertificates.Batch040.certificate817).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch102.certificate1226 CountingCertificates.Batch040.certificate817 matches408 MergedCutGroups.Batch102.numericValid1226 MergedCutGroups.Batch102.cellsSound1226 MergedCutGroups.Batch102.cellsNumeric1226 MergedCutGroups.Batch102.populationMatches1226
    PopulationCertificates.Batch040.valid817 PopulationCertificates.Batch040.sound817 WitnessCertificates.Batch040.valid817 WitnessCertificates.Batch040.sound817 CountingCertificates.Batch040.valid817 CountingCertificates.Batch040.sound817 H st hI
theorem probabilityBound408 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch102.certificate1226).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate817).dm (WitnessCertificates.Batch040.certificate817).beta (WitnessCertificates.Batch040.certificate817).L) ≤ ((CutFailureCertificates.Budget040.certificate817).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound817 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate817).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch102.certificate1226).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch040.certificate817).omega:ℝ)) ≤ ((CutFailureCertificates.Budget040.certificate817).bound:ℝ) at hb
  exact (exponentialBound408 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches409 : (MergedCutGroups.Batch102.certificate1229).AnchorMatches CountingCertificates.Batch040.certificate819 := by decide +kernel
theorem exponentialBound409 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch102.certificate1229).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate819).dm (WitnessCertificates.Batch040.certificate819).beta (WitnessCertificates.Batch040.certificate819).L) ≤ (2*exp (-((CountingCertificates.Batch040.certificate819).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch102.certificate1229).exponent:ℝ)*st.R))/((WitnessCertificates.Batch040.certificate819).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch102.certificate1229 CountingCertificates.Batch040.certificate819 matches409 MergedCutGroups.Batch102.numericValid1229 MergedCutGroups.Batch102.cellsSound1229 MergedCutGroups.Batch102.cellsNumeric1229 MergedCutGroups.Batch102.populationMatches1229
    PopulationCertificates.Batch040.valid819 PopulationCertificates.Batch040.sound819 WitnessCertificates.Batch040.valid819 WitnessCertificates.Batch040.sound819 CountingCertificates.Batch040.valid819 CountingCertificates.Batch040.sound819 H st hI
theorem probabilityBound409 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch102.certificate1229).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch040.certificate819).dm (WitnessCertificates.Batch040.certificate819).beta (WitnessCertificates.Batch040.certificate819).L) ≤ ((CutFailureCertificates.Budget040.certificate819).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget040.sound819 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch040.certificate819).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch102.certificate1229).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch040.certificate819).omega:ℝ)) ≤ ((CutFailureCertificates.Budget040.certificate819).bound:ℝ) at hb
  exact (exponentialBound409 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches410 : (MergedCutGroups.Batch102.certificate1232).AnchorMatches CountingCertificates.Batch041.certificate821 := by decide +kernel
theorem exponentialBound410 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch102.certificate1232).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch041.certificate821).dm (WitnessCertificates.Batch041.certificate821).beta (WitnessCertificates.Batch041.certificate821).L) ≤ (2*exp (-((CountingCertificates.Batch041.certificate821).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch102.certificate1232).exponent:ℝ)*st.R))/((WitnessCertificates.Batch041.certificate821).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch102.certificate1232 CountingCertificates.Batch041.certificate821 matches410 MergedCutGroups.Batch102.numericValid1232 MergedCutGroups.Batch102.cellsSound1232 MergedCutGroups.Batch102.cellsNumeric1232 MergedCutGroups.Batch102.populationMatches1232
    PopulationCertificates.Batch041.valid821 PopulationCertificates.Batch041.sound821 WitnessCertificates.Batch041.valid821 WitnessCertificates.Batch041.sound821 CountingCertificates.Batch041.valid821 CountingCertificates.Batch041.sound821 H st hI
theorem probabilityBound410 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch102.certificate1232).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch041.certificate821).dm (WitnessCertificates.Batch041.certificate821).beta (WitnessCertificates.Batch041.certificate821).L) ≤ ((CutFailureCertificates.Budget041.certificate821).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound821 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate821).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch102.certificate1232).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch041.certificate821).omega:ℝ)) ≤ ((CutFailureCertificates.Budget041.certificate821).bound:ℝ) at hb
  exact (exponentialBound410 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches411 : (MergedCutGroups.Batch102.certificate1235).AnchorMatches CountingCertificates.Batch041.certificate823 := by decide +kernel
theorem exponentialBound411 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch102.certificate1235).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch041.certificate823).dm (WitnessCertificates.Batch041.certificate823).beta (WitnessCertificates.Batch041.certificate823).L) ≤ (2*exp (-((CountingCertificates.Batch041.certificate823).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch102.certificate1235).exponent:ℝ)*st.R))/((WitnessCertificates.Batch041.certificate823).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch102.certificate1235 CountingCertificates.Batch041.certificate823 matches411 MergedCutGroups.Batch102.numericValid1235 MergedCutGroups.Batch102.cellsSound1235 MergedCutGroups.Batch102.cellsNumeric1235 MergedCutGroups.Batch102.populationMatches1235
    PopulationCertificates.Batch041.valid823 PopulationCertificates.Batch041.sound823 WitnessCertificates.Batch041.valid823 WitnessCertificates.Batch041.sound823 CountingCertificates.Batch041.valid823 CountingCertificates.Batch041.sound823 H st hI
theorem probabilityBound411 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch102.certificate1235).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch041.certificate823).dm (WitnessCertificates.Batch041.certificate823).beta (WitnessCertificates.Batch041.certificate823).L) ≤ ((CutFailureCertificates.Budget041.certificate823).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound823 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate823).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch102.certificate1235).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch041.certificate823).omega:ℝ)) ≤ ((CutFailureCertificates.Budget041.certificate823).bound:ℝ) at hb
  exact (exponentialBound411 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches412 : (MergedCutGroups.Batch103.certificate1238).AnchorMatches CountingCertificates.Batch041.certificate825 := by decide +kernel
theorem exponentialBound412 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch103.certificate1238).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch041.certificate825).dm (WitnessCertificates.Batch041.certificate825).beta (WitnessCertificates.Batch041.certificate825).L) ≤ (2*exp (-((CountingCertificates.Batch041.certificate825).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch103.certificate1238).exponent:ℝ)*st.R))/((WitnessCertificates.Batch041.certificate825).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch103.certificate1238 CountingCertificates.Batch041.certificate825 matches412 MergedCutGroups.Batch103.numericValid1238 MergedCutGroups.Batch103.cellsSound1238 MergedCutGroups.Batch103.cellsNumeric1238 MergedCutGroups.Batch103.populationMatches1238
    PopulationCertificates.Batch041.valid825 PopulationCertificates.Batch041.sound825 WitnessCertificates.Batch041.valid825 WitnessCertificates.Batch041.sound825 CountingCertificates.Batch041.valid825 CountingCertificates.Batch041.sound825 H st hI
theorem probabilityBound412 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch103.certificate1238).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch041.certificate825).dm (WitnessCertificates.Batch041.certificate825).beta (WitnessCertificates.Batch041.certificate825).L) ≤ ((CutFailureCertificates.Budget041.certificate825).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound825 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate825).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch103.certificate1238).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch041.certificate825).omega:ℝ)) ≤ ((CutFailureCertificates.Budget041.certificate825).bound:ℝ) at hb
  exact (exponentialBound412 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches413 : (MergedCutGroups.Batch103.certificate1241).AnchorMatches CountingCertificates.Batch041.certificate827 := by decide +kernel
theorem exponentialBound413 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch103.certificate1241).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch041.certificate827).dm (WitnessCertificates.Batch041.certificate827).beta (WitnessCertificates.Batch041.certificate827).L) ≤ (2*exp (-((CountingCertificates.Batch041.certificate827).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch103.certificate1241).exponent:ℝ)*st.R))/((WitnessCertificates.Batch041.certificate827).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch103.certificate1241 CountingCertificates.Batch041.certificate827 matches413 MergedCutGroups.Batch103.numericValid1241 MergedCutGroups.Batch103.cellsSound1241 MergedCutGroups.Batch103.cellsNumeric1241 MergedCutGroups.Batch103.populationMatches1241
    PopulationCertificates.Batch041.valid827 PopulationCertificates.Batch041.sound827 WitnessCertificates.Batch041.valid827 WitnessCertificates.Batch041.sound827 CountingCertificates.Batch041.valid827 CountingCertificates.Batch041.sound827 H st hI
theorem probabilityBound413 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch103.certificate1241).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch041.certificate827).dm (WitnessCertificates.Batch041.certificate827).beta (WitnessCertificates.Batch041.certificate827).L) ≤ ((CutFailureCertificates.Budget041.certificate827).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound827 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate827).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch103.certificate1241).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch041.certificate827).omega:ℝ)) ≤ ((CutFailureCertificates.Budget041.certificate827).bound:ℝ) at hb
  exact (exponentialBound413 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches414 : (MergedCutGroups.Batch103.certificate1244).AnchorMatches CountingCertificates.Batch041.certificate829 := by decide +kernel
theorem exponentialBound414 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch103.certificate1244).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch041.certificate829).dm (WitnessCertificates.Batch041.certificate829).beta (WitnessCertificates.Batch041.certificate829).L) ≤ (2*exp (-((CountingCertificates.Batch041.certificate829).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch103.certificate1244).exponent:ℝ)*st.R))/((WitnessCertificates.Batch041.certificate829).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch103.certificate1244 CountingCertificates.Batch041.certificate829 matches414 MergedCutGroups.Batch103.numericValid1244 MergedCutGroups.Batch103.cellsSound1244 MergedCutGroups.Batch103.cellsNumeric1244 MergedCutGroups.Batch103.populationMatches1244
    PopulationCertificates.Batch041.valid829 PopulationCertificates.Batch041.sound829 WitnessCertificates.Batch041.valid829 WitnessCertificates.Batch041.sound829 CountingCertificates.Batch041.valid829 CountingCertificates.Batch041.sound829 H st hI
theorem probabilityBound414 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch103.certificate1244).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch041.certificate829).dm (WitnessCertificates.Batch041.certificate829).beta (WitnessCertificates.Batch041.certificate829).L) ≤ ((CutFailureCertificates.Budget041.certificate829).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound829 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate829).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch103.certificate1244).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch041.certificate829).omega:ℝ)) ≤ ((CutFailureCertificates.Budget041.certificate829).bound:ℝ) at hb
  exact (exponentialBound414 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches415 : (MergedCutGroups.Batch103.certificate1247).AnchorMatches CountingCertificates.Batch041.certificate831 := by decide +kernel
theorem exponentialBound415 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch103.certificate1247).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch041.certificate831).dm (WitnessCertificates.Batch041.certificate831).beta (WitnessCertificates.Batch041.certificate831).L) ≤ (2*exp (-((CountingCertificates.Batch041.certificate831).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch103.certificate1247).exponent:ℝ)*st.R))/((WitnessCertificates.Batch041.certificate831).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch103.certificate1247 CountingCertificates.Batch041.certificate831 matches415 MergedCutGroups.Batch103.numericValid1247 MergedCutGroups.Batch103.cellsSound1247 MergedCutGroups.Batch103.cellsNumeric1247 MergedCutGroups.Batch103.populationMatches1247
    PopulationCertificates.Batch041.valid831 PopulationCertificates.Batch041.sound831 WitnessCertificates.Batch041.valid831 WitnessCertificates.Batch041.sound831 CountingCertificates.Batch041.valid831 CountingCertificates.Batch041.sound831 H st hI
theorem probabilityBound415 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch103.certificate1247).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch041.certificate831).dm (WitnessCertificates.Batch041.certificate831).beta (WitnessCertificates.Batch041.certificate831).L) ≤ ((CutFailureCertificates.Budget041.certificate831).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound831 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate831).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch103.certificate1247).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch041.certificate831).omega:ℝ)) ≤ ((CutFailureCertificates.Budget041.certificate831).bound:ℝ) at hb
  exact (exponentialBound415 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches416 : (MergedCutGroups.Batch104.certificate1251).AnchorMatches CountingCertificates.Batch041.certificate834 := by decide +kernel
theorem exponentialBound416 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch104.certificate1251).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch041.certificate834).dm (WitnessCertificates.Batch041.certificate834).beta (WitnessCertificates.Batch041.certificate834).L) ≤ (2*exp (-((CountingCertificates.Batch041.certificate834).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch104.certificate1251).exponent:ℝ)*st.R))/((WitnessCertificates.Batch041.certificate834).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch104.certificate1251 CountingCertificates.Batch041.certificate834 matches416 MergedCutGroups.Batch104.numericValid1251 MergedCutGroups.Batch104.cellsSound1251 MergedCutGroups.Batch104.cellsNumeric1251 MergedCutGroups.Batch104.populationMatches1251
    PopulationCertificates.Batch041.valid834 PopulationCertificates.Batch041.sound834 WitnessCertificates.Batch041.valid834 WitnessCertificates.Batch041.sound834 CountingCertificates.Batch041.valid834 CountingCertificates.Batch041.sound834 H st hI
theorem probabilityBound416 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch104.certificate1251).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch041.certificate834).dm (WitnessCertificates.Batch041.certificate834).beta (WitnessCertificates.Batch041.certificate834).L) ≤ ((CutFailureCertificates.Budget041.certificate834).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound834 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate834).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch104.certificate1251).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch041.certificate834).omega:ℝ)) ≤ ((CutFailureCertificates.Budget041.certificate834).bound:ℝ) at hb
  exact (exponentialBound416 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches417 : (MergedCutGroups.Batch104.certificate1255).AnchorMatches CountingCertificates.Batch041.certificate837 := by decide +kernel
theorem exponentialBound417 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch104.certificate1255).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch041.certificate837).dm (WitnessCertificates.Batch041.certificate837).beta (WitnessCertificates.Batch041.certificate837).L) ≤ (2*exp (-((CountingCertificates.Batch041.certificate837).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch104.certificate1255).exponent:ℝ)*st.R))/((WitnessCertificates.Batch041.certificate837).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch104.certificate1255 CountingCertificates.Batch041.certificate837 matches417 MergedCutGroups.Batch104.numericValid1255 MergedCutGroups.Batch104.cellsSound1255 MergedCutGroups.Batch104.cellsNumeric1255 MergedCutGroups.Batch104.populationMatches1255
    PopulationCertificates.Batch041.valid837 PopulationCertificates.Batch041.sound837 WitnessCertificates.Batch041.valid837 WitnessCertificates.Batch041.sound837 CountingCertificates.Batch041.valid837 CountingCertificates.Batch041.sound837 H st hI
theorem probabilityBound417 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch104.certificate1255).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch041.certificate837).dm (WitnessCertificates.Batch041.certificate837).beta (WitnessCertificates.Batch041.certificate837).L) ≤ ((CutFailureCertificates.Budget041.certificate837).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound837 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate837).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch104.certificate1255).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch041.certificate837).omega:ℝ)) ≤ ((CutFailureCertificates.Budget041.certificate837).bound:ℝ) at hb
  exact (exponentialBound417 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches418 : (MergedCutGroups.Batch104.certificate1259).AnchorMatches CountingCertificates.Batch042.certificate840 := by decide +kernel
theorem exponentialBound418 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch104.certificate1259).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch042.certificate840).dm (WitnessCertificates.Batch042.certificate840).beta (WitnessCertificates.Batch042.certificate840).L) ≤ (2*exp (-((CountingCertificates.Batch042.certificate840).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch104.certificate1259).exponent:ℝ)*st.R))/((WitnessCertificates.Batch042.certificate840).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch104.certificate1259 CountingCertificates.Batch042.certificate840 matches418 MergedCutGroups.Batch104.numericValid1259 MergedCutGroups.Batch104.cellsSound1259 MergedCutGroups.Batch104.cellsNumeric1259 MergedCutGroups.Batch104.populationMatches1259
    PopulationCertificates.Batch042.valid840 PopulationCertificates.Batch042.sound840 WitnessCertificates.Batch042.valid840 WitnessCertificates.Batch042.sound840 CountingCertificates.Batch042.valid840 CountingCertificates.Batch042.sound840 H st hI
theorem probabilityBound418 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch104.certificate1259).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch042.certificate840).dm (WitnessCertificates.Batch042.certificate840).beta (WitnessCertificates.Batch042.certificate840).L) ≤ ((CutFailureCertificates.Budget042.certificate840).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound840 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate840).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch104.certificate1259).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch042.certificate840).omega:ℝ)) ≤ ((CutFailureCertificates.Budget042.certificate840).bound:ℝ) at hb
  exact (exponentialBound418 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches419 : (MergedCutGroups.Batch105.certificate1263).AnchorMatches CountingCertificates.Batch042.certificate843 := by decide +kernel
theorem exponentialBound419 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch105.certificate1263).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch042.certificate843).dm (WitnessCertificates.Batch042.certificate843).beta (WitnessCertificates.Batch042.certificate843).L) ≤ (2*exp (-((CountingCertificates.Batch042.certificate843).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch105.certificate1263).exponent:ℝ)*st.R))/((WitnessCertificates.Batch042.certificate843).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch105.certificate1263 CountingCertificates.Batch042.certificate843 matches419 MergedCutGroups.Batch105.numericValid1263 MergedCutGroups.Batch105.cellsSound1263 MergedCutGroups.Batch105.cellsNumeric1263 MergedCutGroups.Batch105.populationMatches1263
    PopulationCertificates.Batch042.valid843 PopulationCertificates.Batch042.sound843 WitnessCertificates.Batch042.valid843 WitnessCertificates.Batch042.sound843 CountingCertificates.Batch042.valid843 CountingCertificates.Batch042.sound843 H st hI
theorem probabilityBound419 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch105.certificate1263).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch042.certificate843).dm (WitnessCertificates.Batch042.certificate843).beta (WitnessCertificates.Batch042.certificate843).L) ≤ ((CutFailureCertificates.Budget042.certificate843).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound843 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate843).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch105.certificate1263).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch042.certificate843).omega:ℝ)) ≤ ((CutFailureCertificates.Budget042.certificate843).bound:ℝ) at hb
  exact (exponentialBound419 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch020
