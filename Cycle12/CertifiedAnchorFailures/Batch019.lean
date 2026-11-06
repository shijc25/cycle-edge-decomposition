import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch038
import Cycle12.CountingCertificates.Batch039
import Cycle12.CutFailureCertificates.Budget038
import Cycle12.CutFailureCertificates.Budget039
import Cycle12.MergedCutGroups.Batch095
import Cycle12.MergedCutGroups.Batch096
import Cycle12.MergedCutGroups.Batch097
import Cycle12.MergedCutGroups.Batch098
import Cycle12.MergedCutGroups.Batch099
import Cycle12.PopulationCertificates.Batch038
import Cycle12.PopulationCertificates.Batch039
import Cycle12.WitnessCertificates.Batch038
import Cycle12.WitnessCertificates.Batch039

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedAnchorFailures.Batch019
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches380 : (MergedCutGroups.Batch095.certificate1142).AnchorMatches CountingCertificates.Batch038.certificate761 := by decide +kernel
theorem exponentialBound380 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch095.certificate1142).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate761).dm (WitnessCertificates.Batch038.certificate761).beta (WitnessCertificates.Batch038.certificate761).L) ≤ (2*exp (-((CountingCertificates.Batch038.certificate761).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch095.certificate1142).exponent:ℝ)*st.R))/((WitnessCertificates.Batch038.certificate761).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch095.certificate1142 CountingCertificates.Batch038.certificate761 matches380 MergedCutGroups.Batch095.numericValid1142 MergedCutGroups.Batch095.cellsSound1142 MergedCutGroups.Batch095.cellsNumeric1142 MergedCutGroups.Batch095.populationMatches1142
    PopulationCertificates.Batch038.valid761 PopulationCertificates.Batch038.sound761 WitnessCertificates.Batch038.valid761 WitnessCertificates.Batch038.sound761 CountingCertificates.Batch038.valid761 CountingCertificates.Batch038.sound761 H st hI
theorem probabilityBound380 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch095.certificate1142).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate761).dm (WitnessCertificates.Batch038.certificate761).beta (WitnessCertificates.Batch038.certificate761).L) ≤ ((CutFailureCertificates.Budget038.certificate761).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound761 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate761).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch095.certificate1142).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch038.certificate761).omega:ℝ)) ≤ ((CutFailureCertificates.Budget038.certificate761).bound:ℝ) at hb
  exact (exponentialBound380 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches381 : (MergedCutGroups.Batch095.certificate1145).AnchorMatches CountingCertificates.Batch038.certificate763 := by decide +kernel
theorem exponentialBound381 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch095.certificate1145).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate763).dm (WitnessCertificates.Batch038.certificate763).beta (WitnessCertificates.Batch038.certificate763).L) ≤ (2*exp (-((CountingCertificates.Batch038.certificate763).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch095.certificate1145).exponent:ℝ)*st.R))/((WitnessCertificates.Batch038.certificate763).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch095.certificate1145 CountingCertificates.Batch038.certificate763 matches381 MergedCutGroups.Batch095.numericValid1145 MergedCutGroups.Batch095.cellsSound1145 MergedCutGroups.Batch095.cellsNumeric1145 MergedCutGroups.Batch095.populationMatches1145
    PopulationCertificates.Batch038.valid763 PopulationCertificates.Batch038.sound763 WitnessCertificates.Batch038.valid763 WitnessCertificates.Batch038.sound763 CountingCertificates.Batch038.valid763 CountingCertificates.Batch038.sound763 H st hI
theorem probabilityBound381 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch095.certificate1145).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate763).dm (WitnessCertificates.Batch038.certificate763).beta (WitnessCertificates.Batch038.certificate763).L) ≤ ((CutFailureCertificates.Budget038.certificate763).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound763 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate763).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch095.certificate1145).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch038.certificate763).omega:ℝ)) ≤ ((CutFailureCertificates.Budget038.certificate763).bound:ℝ) at hb
  exact (exponentialBound381 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches382 : (MergedCutGroups.Batch095.certificate1148).AnchorMatches CountingCertificates.Batch038.certificate765 := by decide +kernel
theorem exponentialBound382 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch095.certificate1148).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate765).dm (WitnessCertificates.Batch038.certificate765).beta (WitnessCertificates.Batch038.certificate765).L) ≤ (2*exp (-((CountingCertificates.Batch038.certificate765).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch095.certificate1148).exponent:ℝ)*st.R))/((WitnessCertificates.Batch038.certificate765).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch095.certificate1148 CountingCertificates.Batch038.certificate765 matches382 MergedCutGroups.Batch095.numericValid1148 MergedCutGroups.Batch095.cellsSound1148 MergedCutGroups.Batch095.cellsNumeric1148 MergedCutGroups.Batch095.populationMatches1148
    PopulationCertificates.Batch038.valid765 PopulationCertificates.Batch038.sound765 WitnessCertificates.Batch038.valid765 WitnessCertificates.Batch038.sound765 CountingCertificates.Batch038.valid765 CountingCertificates.Batch038.sound765 H st hI
theorem probabilityBound382 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch095.certificate1148).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate765).dm (WitnessCertificates.Batch038.certificate765).beta (WitnessCertificates.Batch038.certificate765).L) ≤ ((CutFailureCertificates.Budget038.certificate765).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound765 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate765).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch095.certificate1148).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch038.certificate765).omega:ℝ)) ≤ ((CutFailureCertificates.Budget038.certificate765).bound:ℝ) at hb
  exact (exponentialBound382 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches383 : (MergedCutGroups.Batch095.certificate1151).AnchorMatches CountingCertificates.Batch038.certificate767 := by decide +kernel
theorem exponentialBound383 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch095.certificate1151).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate767).dm (WitnessCertificates.Batch038.certificate767).beta (WitnessCertificates.Batch038.certificate767).L) ≤ (2*exp (-((CountingCertificates.Batch038.certificate767).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch095.certificate1151).exponent:ℝ)*st.R))/((WitnessCertificates.Batch038.certificate767).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch095.certificate1151 CountingCertificates.Batch038.certificate767 matches383 MergedCutGroups.Batch095.numericValid1151 MergedCutGroups.Batch095.cellsSound1151 MergedCutGroups.Batch095.cellsNumeric1151 MergedCutGroups.Batch095.populationMatches1151
    PopulationCertificates.Batch038.valid767 PopulationCertificates.Batch038.sound767 WitnessCertificates.Batch038.valid767 WitnessCertificates.Batch038.sound767 CountingCertificates.Batch038.valid767 CountingCertificates.Batch038.sound767 H st hI
theorem probabilityBound383 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch095.certificate1151).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate767).dm (WitnessCertificates.Batch038.certificate767).beta (WitnessCertificates.Batch038.certificate767).L) ≤ ((CutFailureCertificates.Budget038.certificate767).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound767 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate767).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch095.certificate1151).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch038.certificate767).omega:ℝ)) ≤ ((CutFailureCertificates.Budget038.certificate767).bound:ℝ) at hb
  exact (exponentialBound383 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches384 : (MergedCutGroups.Batch096.certificate1154).AnchorMatches CountingCertificates.Batch038.certificate769 := by decide +kernel
theorem exponentialBound384 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch096.certificate1154).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate769).dm (WitnessCertificates.Batch038.certificate769).beta (WitnessCertificates.Batch038.certificate769).L) ≤ (2*exp (-((CountingCertificates.Batch038.certificate769).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch096.certificate1154).exponent:ℝ)*st.R))/((WitnessCertificates.Batch038.certificate769).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch096.certificate1154 CountingCertificates.Batch038.certificate769 matches384 MergedCutGroups.Batch096.numericValid1154 MergedCutGroups.Batch096.cellsSound1154 MergedCutGroups.Batch096.cellsNumeric1154 MergedCutGroups.Batch096.populationMatches1154
    PopulationCertificates.Batch038.valid769 PopulationCertificates.Batch038.sound769 WitnessCertificates.Batch038.valid769 WitnessCertificates.Batch038.sound769 CountingCertificates.Batch038.valid769 CountingCertificates.Batch038.sound769 H st hI
theorem probabilityBound384 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch096.certificate1154).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate769).dm (WitnessCertificates.Batch038.certificate769).beta (WitnessCertificates.Batch038.certificate769).L) ≤ ((CutFailureCertificates.Budget038.certificate769).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound769 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate769).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch096.certificate1154).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch038.certificate769).omega:ℝ)) ≤ ((CutFailureCertificates.Budget038.certificate769).bound:ℝ) at hb
  exact (exponentialBound384 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches385 : (MergedCutGroups.Batch096.certificate1157).AnchorMatches CountingCertificates.Batch038.certificate771 := by decide +kernel
theorem exponentialBound385 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch096.certificate1157).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate771).dm (WitnessCertificates.Batch038.certificate771).beta (WitnessCertificates.Batch038.certificate771).L) ≤ (2*exp (-((CountingCertificates.Batch038.certificate771).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch096.certificate1157).exponent:ℝ)*st.R))/((WitnessCertificates.Batch038.certificate771).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch096.certificate1157 CountingCertificates.Batch038.certificate771 matches385 MergedCutGroups.Batch096.numericValid1157 MergedCutGroups.Batch096.cellsSound1157 MergedCutGroups.Batch096.cellsNumeric1157 MergedCutGroups.Batch096.populationMatches1157
    PopulationCertificates.Batch038.valid771 PopulationCertificates.Batch038.sound771 WitnessCertificates.Batch038.valid771 WitnessCertificates.Batch038.sound771 CountingCertificates.Batch038.valid771 CountingCertificates.Batch038.sound771 H st hI
theorem probabilityBound385 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch096.certificate1157).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate771).dm (WitnessCertificates.Batch038.certificate771).beta (WitnessCertificates.Batch038.certificate771).L) ≤ ((CutFailureCertificates.Budget038.certificate771).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound771 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate771).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch096.certificate1157).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch038.certificate771).omega:ℝ)) ≤ ((CutFailureCertificates.Budget038.certificate771).bound:ℝ) at hb
  exact (exponentialBound385 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches386 : (MergedCutGroups.Batch096.certificate1160).AnchorMatches CountingCertificates.Batch038.certificate773 := by decide +kernel
theorem exponentialBound386 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch096.certificate1160).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate773).dm (WitnessCertificates.Batch038.certificate773).beta (WitnessCertificates.Batch038.certificate773).L) ≤ (2*exp (-((CountingCertificates.Batch038.certificate773).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch096.certificate1160).exponent:ℝ)*st.R))/((WitnessCertificates.Batch038.certificate773).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch096.certificate1160 CountingCertificates.Batch038.certificate773 matches386 MergedCutGroups.Batch096.numericValid1160 MergedCutGroups.Batch096.cellsSound1160 MergedCutGroups.Batch096.cellsNumeric1160 MergedCutGroups.Batch096.populationMatches1160
    PopulationCertificates.Batch038.valid773 PopulationCertificates.Batch038.sound773 WitnessCertificates.Batch038.valid773 WitnessCertificates.Batch038.sound773 CountingCertificates.Batch038.valid773 CountingCertificates.Batch038.sound773 H st hI
theorem probabilityBound386 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch096.certificate1160).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate773).dm (WitnessCertificates.Batch038.certificate773).beta (WitnessCertificates.Batch038.certificate773).L) ≤ ((CutFailureCertificates.Budget038.certificate773).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound773 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate773).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch096.certificate1160).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch038.certificate773).omega:ℝ)) ≤ ((CutFailureCertificates.Budget038.certificate773).bound:ℝ) at hb
  exact (exponentialBound386 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches387 : (MergedCutGroups.Batch096.certificate1163).AnchorMatches CountingCertificates.Batch038.certificate775 := by decide +kernel
theorem exponentialBound387 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch096.certificate1163).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate775).dm (WitnessCertificates.Batch038.certificate775).beta (WitnessCertificates.Batch038.certificate775).L) ≤ (2*exp (-((CountingCertificates.Batch038.certificate775).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch096.certificate1163).exponent:ℝ)*st.R))/((WitnessCertificates.Batch038.certificate775).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch096.certificate1163 CountingCertificates.Batch038.certificate775 matches387 MergedCutGroups.Batch096.numericValid1163 MergedCutGroups.Batch096.cellsSound1163 MergedCutGroups.Batch096.cellsNumeric1163 MergedCutGroups.Batch096.populationMatches1163
    PopulationCertificates.Batch038.valid775 PopulationCertificates.Batch038.sound775 WitnessCertificates.Batch038.valid775 WitnessCertificates.Batch038.sound775 CountingCertificates.Batch038.valid775 CountingCertificates.Batch038.sound775 H st hI
theorem probabilityBound387 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch096.certificate1163).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate775).dm (WitnessCertificates.Batch038.certificate775).beta (WitnessCertificates.Batch038.certificate775).L) ≤ ((CutFailureCertificates.Budget038.certificate775).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound775 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate775).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch096.certificate1163).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch038.certificate775).omega:ℝ)) ≤ ((CutFailureCertificates.Budget038.certificate775).bound:ℝ) at hb
  exact (exponentialBound387 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches388 : (MergedCutGroups.Batch097.certificate1166).AnchorMatches CountingCertificates.Batch038.certificate777 := by decide +kernel
theorem exponentialBound388 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch097.certificate1166).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate777).dm (WitnessCertificates.Batch038.certificate777).beta (WitnessCertificates.Batch038.certificate777).L) ≤ (2*exp (-((CountingCertificates.Batch038.certificate777).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch097.certificate1166).exponent:ℝ)*st.R))/((WitnessCertificates.Batch038.certificate777).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch097.certificate1166 CountingCertificates.Batch038.certificate777 matches388 MergedCutGroups.Batch097.numericValid1166 MergedCutGroups.Batch097.cellsSound1166 MergedCutGroups.Batch097.cellsNumeric1166 MergedCutGroups.Batch097.populationMatches1166
    PopulationCertificates.Batch038.valid777 PopulationCertificates.Batch038.sound777 WitnessCertificates.Batch038.valid777 WitnessCertificates.Batch038.sound777 CountingCertificates.Batch038.valid777 CountingCertificates.Batch038.sound777 H st hI
theorem probabilityBound388 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch097.certificate1166).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate777).dm (WitnessCertificates.Batch038.certificate777).beta (WitnessCertificates.Batch038.certificate777).L) ≤ ((CutFailureCertificates.Budget038.certificate777).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound777 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate777).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch097.certificate1166).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch038.certificate777).omega:ℝ)) ≤ ((CutFailureCertificates.Budget038.certificate777).bound:ℝ) at hb
  exact (exponentialBound388 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches389 : (MergedCutGroups.Batch097.certificate1169).AnchorMatches CountingCertificates.Batch038.certificate779 := by decide +kernel
theorem exponentialBound389 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch097.certificate1169).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate779).dm (WitnessCertificates.Batch038.certificate779).beta (WitnessCertificates.Batch038.certificate779).L) ≤ (2*exp (-((CountingCertificates.Batch038.certificate779).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch097.certificate1169).exponent:ℝ)*st.R))/((WitnessCertificates.Batch038.certificate779).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch097.certificate1169 CountingCertificates.Batch038.certificate779 matches389 MergedCutGroups.Batch097.numericValid1169 MergedCutGroups.Batch097.cellsSound1169 MergedCutGroups.Batch097.cellsNumeric1169 MergedCutGroups.Batch097.populationMatches1169
    PopulationCertificates.Batch038.valid779 PopulationCertificates.Batch038.sound779 WitnessCertificates.Batch038.valid779 WitnessCertificates.Batch038.sound779 CountingCertificates.Batch038.valid779 CountingCertificates.Batch038.sound779 H st hI
theorem probabilityBound389 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch097.certificate1169).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch038.certificate779).dm (WitnessCertificates.Batch038.certificate779).beta (WitnessCertificates.Batch038.certificate779).L) ≤ ((CutFailureCertificates.Budget038.certificate779).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound779 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate779).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch097.certificate1169).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch038.certificate779).omega:ℝ)) ≤ ((CutFailureCertificates.Budget038.certificate779).bound:ℝ) at hb
  exact (exponentialBound389 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches390 : (MergedCutGroups.Batch097.certificate1172).AnchorMatches CountingCertificates.Batch039.certificate781 := by decide +kernel
theorem exponentialBound390 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch097.certificate1172).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate781).dm (WitnessCertificates.Batch039.certificate781).beta (WitnessCertificates.Batch039.certificate781).L) ≤ (2*exp (-((CountingCertificates.Batch039.certificate781).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch097.certificate1172).exponent:ℝ)*st.R))/((WitnessCertificates.Batch039.certificate781).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch097.certificate1172 CountingCertificates.Batch039.certificate781 matches390 MergedCutGroups.Batch097.numericValid1172 MergedCutGroups.Batch097.cellsSound1172 MergedCutGroups.Batch097.cellsNumeric1172 MergedCutGroups.Batch097.populationMatches1172
    PopulationCertificates.Batch039.valid781 PopulationCertificates.Batch039.sound781 WitnessCertificates.Batch039.valid781 WitnessCertificates.Batch039.sound781 CountingCertificates.Batch039.valid781 CountingCertificates.Batch039.sound781 H st hI
theorem probabilityBound390 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch097.certificate1172).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate781).dm (WitnessCertificates.Batch039.certificate781).beta (WitnessCertificates.Batch039.certificate781).L) ≤ ((CutFailureCertificates.Budget039.certificate781).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound781 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate781).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch097.certificate1172).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch039.certificate781).omega:ℝ)) ≤ ((CutFailureCertificates.Budget039.certificate781).bound:ℝ) at hb
  exact (exponentialBound390 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches391 : (MergedCutGroups.Batch097.certificate1175).AnchorMatches CountingCertificates.Batch039.certificate783 := by decide +kernel
theorem exponentialBound391 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch097.certificate1175).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate783).dm (WitnessCertificates.Batch039.certificate783).beta (WitnessCertificates.Batch039.certificate783).L) ≤ (2*exp (-((CountingCertificates.Batch039.certificate783).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch097.certificate1175).exponent:ℝ)*st.R))/((WitnessCertificates.Batch039.certificate783).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch097.certificate1175 CountingCertificates.Batch039.certificate783 matches391 MergedCutGroups.Batch097.numericValid1175 MergedCutGroups.Batch097.cellsSound1175 MergedCutGroups.Batch097.cellsNumeric1175 MergedCutGroups.Batch097.populationMatches1175
    PopulationCertificates.Batch039.valid783 PopulationCertificates.Batch039.sound783 WitnessCertificates.Batch039.valid783 WitnessCertificates.Batch039.sound783 CountingCertificates.Batch039.valid783 CountingCertificates.Batch039.sound783 H st hI
theorem probabilityBound391 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch097.certificate1175).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate783).dm (WitnessCertificates.Batch039.certificate783).beta (WitnessCertificates.Batch039.certificate783).L) ≤ ((CutFailureCertificates.Budget039.certificate783).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound783 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate783).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch097.certificate1175).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch039.certificate783).omega:ℝ)) ≤ ((CutFailureCertificates.Budget039.certificate783).bound:ℝ) at hb
  exact (exponentialBound391 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches392 : (MergedCutGroups.Batch098.certificate1178).AnchorMatches CountingCertificates.Batch039.certificate785 := by decide +kernel
theorem exponentialBound392 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch098.certificate1178).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate785).dm (WitnessCertificates.Batch039.certificate785).beta (WitnessCertificates.Batch039.certificate785).L) ≤ (2*exp (-((CountingCertificates.Batch039.certificate785).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch098.certificate1178).exponent:ℝ)*st.R))/((WitnessCertificates.Batch039.certificate785).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch098.certificate1178 CountingCertificates.Batch039.certificate785 matches392 MergedCutGroups.Batch098.numericValid1178 MergedCutGroups.Batch098.cellsSound1178 MergedCutGroups.Batch098.cellsNumeric1178 MergedCutGroups.Batch098.populationMatches1178
    PopulationCertificates.Batch039.valid785 PopulationCertificates.Batch039.sound785 WitnessCertificates.Batch039.valid785 WitnessCertificates.Batch039.sound785 CountingCertificates.Batch039.valid785 CountingCertificates.Batch039.sound785 H st hI
theorem probabilityBound392 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch098.certificate1178).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate785).dm (WitnessCertificates.Batch039.certificate785).beta (WitnessCertificates.Batch039.certificate785).L) ≤ ((CutFailureCertificates.Budget039.certificate785).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound785 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate785).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch098.certificate1178).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch039.certificate785).omega:ℝ)) ≤ ((CutFailureCertificates.Budget039.certificate785).bound:ℝ) at hb
  exact (exponentialBound392 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches393 : (MergedCutGroups.Batch098.certificate1181).AnchorMatches CountingCertificates.Batch039.certificate787 := by decide +kernel
theorem exponentialBound393 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch098.certificate1181).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate787).dm (WitnessCertificates.Batch039.certificate787).beta (WitnessCertificates.Batch039.certificate787).L) ≤ (2*exp (-((CountingCertificates.Batch039.certificate787).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch098.certificate1181).exponent:ℝ)*st.R))/((WitnessCertificates.Batch039.certificate787).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch098.certificate1181 CountingCertificates.Batch039.certificate787 matches393 MergedCutGroups.Batch098.numericValid1181 MergedCutGroups.Batch098.cellsSound1181 MergedCutGroups.Batch098.cellsNumeric1181 MergedCutGroups.Batch098.populationMatches1181
    PopulationCertificates.Batch039.valid787 PopulationCertificates.Batch039.sound787 WitnessCertificates.Batch039.valid787 WitnessCertificates.Batch039.sound787 CountingCertificates.Batch039.valid787 CountingCertificates.Batch039.sound787 H st hI
theorem probabilityBound393 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch098.certificate1181).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate787).dm (WitnessCertificates.Batch039.certificate787).beta (WitnessCertificates.Batch039.certificate787).L) ≤ ((CutFailureCertificates.Budget039.certificate787).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound787 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate787).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch098.certificate1181).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch039.certificate787).omega:ℝ)) ≤ ((CutFailureCertificates.Budget039.certificate787).bound:ℝ) at hb
  exact (exponentialBound393 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches394 : (MergedCutGroups.Batch098.certificate1184).AnchorMatches CountingCertificates.Batch039.certificate789 := by decide +kernel
theorem exponentialBound394 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch098.certificate1184).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate789).dm (WitnessCertificates.Batch039.certificate789).beta (WitnessCertificates.Batch039.certificate789).L) ≤ (2*exp (-((CountingCertificates.Batch039.certificate789).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch098.certificate1184).exponent:ℝ)*st.R))/((WitnessCertificates.Batch039.certificate789).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch098.certificate1184 CountingCertificates.Batch039.certificate789 matches394 MergedCutGroups.Batch098.numericValid1184 MergedCutGroups.Batch098.cellsSound1184 MergedCutGroups.Batch098.cellsNumeric1184 MergedCutGroups.Batch098.populationMatches1184
    PopulationCertificates.Batch039.valid789 PopulationCertificates.Batch039.sound789 WitnessCertificates.Batch039.valid789 WitnessCertificates.Batch039.sound789 CountingCertificates.Batch039.valid789 CountingCertificates.Batch039.sound789 H st hI
theorem probabilityBound394 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch098.certificate1184).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate789).dm (WitnessCertificates.Batch039.certificate789).beta (WitnessCertificates.Batch039.certificate789).L) ≤ ((CutFailureCertificates.Budget039.certificate789).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound789 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate789).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch098.certificate1184).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch039.certificate789).omega:ℝ)) ≤ ((CutFailureCertificates.Budget039.certificate789).bound:ℝ) at hb
  exact (exponentialBound394 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches395 : (MergedCutGroups.Batch098.certificate1187).AnchorMatches CountingCertificates.Batch039.certificate791 := by decide +kernel
theorem exponentialBound395 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch098.certificate1187).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate791).dm (WitnessCertificates.Batch039.certificate791).beta (WitnessCertificates.Batch039.certificate791).L) ≤ (2*exp (-((CountingCertificates.Batch039.certificate791).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch098.certificate1187).exponent:ℝ)*st.R))/((WitnessCertificates.Batch039.certificate791).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch098.certificate1187 CountingCertificates.Batch039.certificate791 matches395 MergedCutGroups.Batch098.numericValid1187 MergedCutGroups.Batch098.cellsSound1187 MergedCutGroups.Batch098.cellsNumeric1187 MergedCutGroups.Batch098.populationMatches1187
    PopulationCertificates.Batch039.valid791 PopulationCertificates.Batch039.sound791 WitnessCertificates.Batch039.valid791 WitnessCertificates.Batch039.sound791 CountingCertificates.Batch039.valid791 CountingCertificates.Batch039.sound791 H st hI
theorem probabilityBound395 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch098.certificate1187).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate791).dm (WitnessCertificates.Batch039.certificate791).beta (WitnessCertificates.Batch039.certificate791).L) ≤ ((CutFailureCertificates.Budget039.certificate791).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound791 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate791).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch098.certificate1187).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch039.certificate791).omega:ℝ)) ≤ ((CutFailureCertificates.Budget039.certificate791).bound:ℝ) at hb
  exact (exponentialBound395 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches396 : (MergedCutGroups.Batch099.certificate1190).AnchorMatches CountingCertificates.Batch039.certificate793 := by decide +kernel
theorem exponentialBound396 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch099.certificate1190).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate793).dm (WitnessCertificates.Batch039.certificate793).beta (WitnessCertificates.Batch039.certificate793).L) ≤ (2*exp (-((CountingCertificates.Batch039.certificate793).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch099.certificate1190).exponent:ℝ)*st.R))/((WitnessCertificates.Batch039.certificate793).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch099.certificate1190 CountingCertificates.Batch039.certificate793 matches396 MergedCutGroups.Batch099.numericValid1190 MergedCutGroups.Batch099.cellsSound1190 MergedCutGroups.Batch099.cellsNumeric1190 MergedCutGroups.Batch099.populationMatches1190
    PopulationCertificates.Batch039.valid793 PopulationCertificates.Batch039.sound793 WitnessCertificates.Batch039.valid793 WitnessCertificates.Batch039.sound793 CountingCertificates.Batch039.valid793 CountingCertificates.Batch039.sound793 H st hI
theorem probabilityBound396 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch099.certificate1190).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate793).dm (WitnessCertificates.Batch039.certificate793).beta (WitnessCertificates.Batch039.certificate793).L) ≤ ((CutFailureCertificates.Budget039.certificate793).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound793 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate793).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch099.certificate1190).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch039.certificate793).omega:ℝ)) ≤ ((CutFailureCertificates.Budget039.certificate793).bound:ℝ) at hb
  exact (exponentialBound396 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches397 : (MergedCutGroups.Batch099.certificate1193).AnchorMatches CountingCertificates.Batch039.certificate795 := by decide +kernel
theorem exponentialBound397 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch099.certificate1193).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate795).dm (WitnessCertificates.Batch039.certificate795).beta (WitnessCertificates.Batch039.certificate795).L) ≤ (2*exp (-((CountingCertificates.Batch039.certificate795).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch099.certificate1193).exponent:ℝ)*st.R))/((WitnessCertificates.Batch039.certificate795).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch099.certificate1193 CountingCertificates.Batch039.certificate795 matches397 MergedCutGroups.Batch099.numericValid1193 MergedCutGroups.Batch099.cellsSound1193 MergedCutGroups.Batch099.cellsNumeric1193 MergedCutGroups.Batch099.populationMatches1193
    PopulationCertificates.Batch039.valid795 PopulationCertificates.Batch039.sound795 WitnessCertificates.Batch039.valid795 WitnessCertificates.Batch039.sound795 CountingCertificates.Batch039.valid795 CountingCertificates.Batch039.sound795 H st hI
theorem probabilityBound397 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch099.certificate1193).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate795).dm (WitnessCertificates.Batch039.certificate795).beta (WitnessCertificates.Batch039.certificate795).L) ≤ ((CutFailureCertificates.Budget039.certificate795).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound795 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate795).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch099.certificate1193).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch039.certificate795).omega:ℝ)) ≤ ((CutFailureCertificates.Budget039.certificate795).bound:ℝ) at hb
  exact (exponentialBound397 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches398 : (MergedCutGroups.Batch099.certificate1196).AnchorMatches CountingCertificates.Batch039.certificate797 := by decide +kernel
theorem exponentialBound398 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch099.certificate1196).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate797).dm (WitnessCertificates.Batch039.certificate797).beta (WitnessCertificates.Batch039.certificate797).L) ≤ (2*exp (-((CountingCertificates.Batch039.certificate797).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch099.certificate1196).exponent:ℝ)*st.R))/((WitnessCertificates.Batch039.certificate797).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch099.certificate1196 CountingCertificates.Batch039.certificate797 matches398 MergedCutGroups.Batch099.numericValid1196 MergedCutGroups.Batch099.cellsSound1196 MergedCutGroups.Batch099.cellsNumeric1196 MergedCutGroups.Batch099.populationMatches1196
    PopulationCertificates.Batch039.valid797 PopulationCertificates.Batch039.sound797 WitnessCertificates.Batch039.valid797 WitnessCertificates.Batch039.sound797 CountingCertificates.Batch039.valid797 CountingCertificates.Batch039.sound797 H st hI
theorem probabilityBound398 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch099.certificate1196).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate797).dm (WitnessCertificates.Batch039.certificate797).beta (WitnessCertificates.Batch039.certificate797).L) ≤ ((CutFailureCertificates.Budget039.certificate797).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound797 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate797).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch099.certificate1196).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch039.certificate797).omega:ℝ)) ≤ ((CutFailureCertificates.Budget039.certificate797).bound:ℝ) at hb
  exact (exponentialBound398 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches399 : (MergedCutGroups.Batch099.certificate1199).AnchorMatches CountingCertificates.Batch039.certificate799 := by decide +kernel
theorem exponentialBound399 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch099.certificate1199).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate799).dm (WitnessCertificates.Batch039.certificate799).beta (WitnessCertificates.Batch039.certificate799).L) ≤ (2*exp (-((CountingCertificates.Batch039.certificate799).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch099.certificate1199).exponent:ℝ)*st.R))/((WitnessCertificates.Batch039.certificate799).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch099.certificate1199 CountingCertificates.Batch039.certificate799 matches399 MergedCutGroups.Batch099.numericValid1199 MergedCutGroups.Batch099.cellsSound1199 MergedCutGroups.Batch099.cellsNumeric1199 MergedCutGroups.Batch099.populationMatches1199
    PopulationCertificates.Batch039.valid799 PopulationCertificates.Batch039.sound799 WitnessCertificates.Batch039.valid799 WitnessCertificates.Batch039.sound799 CountingCertificates.Batch039.valid799 CountingCertificates.Batch039.sound799 H st hI
theorem probabilityBound399 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch099.certificate1199).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch039.certificate799).dm (WitnessCertificates.Batch039.certificate799).beta (WitnessCertificates.Batch039.certificate799).L) ≤ ((CutFailureCertificates.Budget039.certificate799).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound799 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate799).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch099.certificate1199).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch039.certificate799).omega:ℝ)) ≤ ((CutFailureCertificates.Budget039.certificate799).bound:ℝ) at hb
  exact (exponentialBound399 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch019
