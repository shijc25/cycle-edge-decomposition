import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch038
import Cycle12.CountingCertificates.Batch039
import Cycle12.CutFailureCertificates.Budget038
import Cycle12.CutFailureCertificates.Budget039
import Cycle12.CutLabelCertificates.Entropy019
import Cycle12.CutLabelCertificates.Entropy020
import Cycle12.CutLabelCertificates.Minority019
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

namespace Cycle12.CertifiedGlobalFailures.Batch019
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches380 : (MergedCutGroups.Batch095.certificate1140).GlobalMatches MergedCutGroups.Batch095.certificate1141 CountingCertificates.Batch038.certificate760 CutLabelCertificates.Entropy019.certificate381 CutLabelCertificates.Minority019.certificate380 := by decide +kernel
theorem exponentialBound380 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch095.certificate1140).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate760).dm (WitnessCertificates.Batch038.certificate760).beta) ≤ (2*exp (-((CountingCertificates.Batch038.certificate760).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch095.certificate1140).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch095.certificate1141).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch038.certificate760).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch095.certificate1140 MergedCutGroups.Batch095.certificate1141 CountingCertificates.Batch038.certificate760 CutLabelCertificates.Entropy019.certificate381 CutLabelCertificates.Minority019.certificate380 matches380 rfl rfl
    MergedCutGroups.Batch095.numericValid1140 MergedCutGroups.Batch095.numericValid1141 MergedCutGroups.Batch095.cellsSound1140 MergedCutGroups.Batch095.cellsSound1141
    MergedCutGroups.Batch095.cellsNumeric1140 MergedCutGroups.Batch095.cellsNumeric1141 MergedCutGroups.Batch095.populationMatches1140 MergedCutGroups.Batch095.populationMatches1141
    PopulationCertificates.Batch038.valid760 PopulationCertificates.Batch038.sound760 WitnessCertificates.Batch038.valid760 WitnessCertificates.Batch038.sound760 CountingCertificates.Batch038.valid760 CountingCertificates.Batch038.sound760
    CutLabelCertificates.Entropy019.valid381 CutLabelCertificates.Minority019.valid380 CutLabelCertificates.Minority019.sound380 H st hI
theorem probabilityBound380 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch095.certificate1140).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate760).dm (WitnessCertificates.Batch038.certificate760).beta) ≤ ((CutFailureCertificates.Budget038.certificate760).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound760 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate760).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch095.certificate1140).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch095.certificate1141).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch038.certificate760).omega:ℝ) ≤ ((CutFailureCertificates.Budget038.certificate760).bound:ℝ) at hb
  exact (exponentialBound380 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches381 : (MergedCutGroups.Batch095.certificate1143).GlobalMatches MergedCutGroups.Batch095.certificate1144 CountingCertificates.Batch038.certificate762 CutLabelCertificates.Entropy019.certificate382 CutLabelCertificates.Minority019.certificate381 := by decide +kernel
theorem exponentialBound381 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch095.certificate1143).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate762).dm (WitnessCertificates.Batch038.certificate762).beta) ≤ (2*exp (-((CountingCertificates.Batch038.certificate762).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch095.certificate1143).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch095.certificate1144).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch038.certificate762).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch095.certificate1143 MergedCutGroups.Batch095.certificate1144 CountingCertificates.Batch038.certificate762 CutLabelCertificates.Entropy019.certificate382 CutLabelCertificates.Minority019.certificate381 matches381 rfl rfl
    MergedCutGroups.Batch095.numericValid1143 MergedCutGroups.Batch095.numericValid1144 MergedCutGroups.Batch095.cellsSound1143 MergedCutGroups.Batch095.cellsSound1144
    MergedCutGroups.Batch095.cellsNumeric1143 MergedCutGroups.Batch095.cellsNumeric1144 MergedCutGroups.Batch095.populationMatches1143 MergedCutGroups.Batch095.populationMatches1144
    PopulationCertificates.Batch038.valid762 PopulationCertificates.Batch038.sound762 WitnessCertificates.Batch038.valid762 WitnessCertificates.Batch038.sound762 CountingCertificates.Batch038.valid762 CountingCertificates.Batch038.sound762
    CutLabelCertificates.Entropy019.valid382 CutLabelCertificates.Minority019.valid381 CutLabelCertificates.Minority019.sound381 H st hI
theorem probabilityBound381 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch095.certificate1143).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate762).dm (WitnessCertificates.Batch038.certificate762).beta) ≤ ((CutFailureCertificates.Budget038.certificate762).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound762 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate762).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch095.certificate1143).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch095.certificate1144).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch038.certificate762).omega:ℝ) ≤ ((CutFailureCertificates.Budget038.certificate762).bound:ℝ) at hb
  exact (exponentialBound381 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches382 : (MergedCutGroups.Batch095.certificate1146).GlobalMatches MergedCutGroups.Batch095.certificate1147 CountingCertificates.Batch038.certificate764 CutLabelCertificates.Entropy019.certificate383 CutLabelCertificates.Minority019.certificate382 := by decide +kernel
theorem exponentialBound382 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch095.certificate1146).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate764).dm (WitnessCertificates.Batch038.certificate764).beta) ≤ (2*exp (-((CountingCertificates.Batch038.certificate764).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch095.certificate1146).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch095.certificate1147).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch038.certificate764).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch095.certificate1146 MergedCutGroups.Batch095.certificate1147 CountingCertificates.Batch038.certificate764 CutLabelCertificates.Entropy019.certificate383 CutLabelCertificates.Minority019.certificate382 matches382 rfl rfl
    MergedCutGroups.Batch095.numericValid1146 MergedCutGroups.Batch095.numericValid1147 MergedCutGroups.Batch095.cellsSound1146 MergedCutGroups.Batch095.cellsSound1147
    MergedCutGroups.Batch095.cellsNumeric1146 MergedCutGroups.Batch095.cellsNumeric1147 MergedCutGroups.Batch095.populationMatches1146 MergedCutGroups.Batch095.populationMatches1147
    PopulationCertificates.Batch038.valid764 PopulationCertificates.Batch038.sound764 WitnessCertificates.Batch038.valid764 WitnessCertificates.Batch038.sound764 CountingCertificates.Batch038.valid764 CountingCertificates.Batch038.sound764
    CutLabelCertificates.Entropy019.valid383 CutLabelCertificates.Minority019.valid382 CutLabelCertificates.Minority019.sound382 H st hI
theorem probabilityBound382 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch095.certificate1146).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate764).dm (WitnessCertificates.Batch038.certificate764).beta) ≤ ((CutFailureCertificates.Budget038.certificate764).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound764 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate764).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch095.certificate1146).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch095.certificate1147).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch038.certificate764).omega:ℝ) ≤ ((CutFailureCertificates.Budget038.certificate764).bound:ℝ) at hb
  exact (exponentialBound382 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches383 : (MergedCutGroups.Batch095.certificate1149).GlobalMatches MergedCutGroups.Batch095.certificate1150 CountingCertificates.Batch038.certificate766 CutLabelCertificates.Entropy019.certificate384 CutLabelCertificates.Minority019.certificate383 := by decide +kernel
theorem exponentialBound383 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch095.certificate1149).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate766).dm (WitnessCertificates.Batch038.certificate766).beta) ≤ (2*exp (-((CountingCertificates.Batch038.certificate766).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch095.certificate1149).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch095.certificate1150).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch038.certificate766).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch095.certificate1149 MergedCutGroups.Batch095.certificate1150 CountingCertificates.Batch038.certificate766 CutLabelCertificates.Entropy019.certificate384 CutLabelCertificates.Minority019.certificate383 matches383 rfl rfl
    MergedCutGroups.Batch095.numericValid1149 MergedCutGroups.Batch095.numericValid1150 MergedCutGroups.Batch095.cellsSound1149 MergedCutGroups.Batch095.cellsSound1150
    MergedCutGroups.Batch095.cellsNumeric1149 MergedCutGroups.Batch095.cellsNumeric1150 MergedCutGroups.Batch095.populationMatches1149 MergedCutGroups.Batch095.populationMatches1150
    PopulationCertificates.Batch038.valid766 PopulationCertificates.Batch038.sound766 WitnessCertificates.Batch038.valid766 WitnessCertificates.Batch038.sound766 CountingCertificates.Batch038.valid766 CountingCertificates.Batch038.sound766
    CutLabelCertificates.Entropy019.valid384 CutLabelCertificates.Minority019.valid383 CutLabelCertificates.Minority019.sound383 H st hI
theorem probabilityBound383 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch095.certificate1149).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate766).dm (WitnessCertificates.Batch038.certificate766).beta) ≤ ((CutFailureCertificates.Budget038.certificate766).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound766 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate766).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch095.certificate1149).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch095.certificate1150).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch038.certificate766).omega:ℝ) ≤ ((CutFailureCertificates.Budget038.certificate766).bound:ℝ) at hb
  exact (exponentialBound383 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches384 : (MergedCutGroups.Batch096.certificate1152).GlobalMatches MergedCutGroups.Batch096.certificate1153 CountingCertificates.Batch038.certificate768 CutLabelCertificates.Entropy019.certificate385 CutLabelCertificates.Minority019.certificate384 := by decide +kernel
theorem exponentialBound384 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch096.certificate1152).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate768).dm (WitnessCertificates.Batch038.certificate768).beta) ≤ (2*exp (-((CountingCertificates.Batch038.certificate768).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch096.certificate1152).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch096.certificate1153).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch038.certificate768).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch096.certificate1152 MergedCutGroups.Batch096.certificate1153 CountingCertificates.Batch038.certificate768 CutLabelCertificates.Entropy019.certificate385 CutLabelCertificates.Minority019.certificate384 matches384 rfl rfl
    MergedCutGroups.Batch096.numericValid1152 MergedCutGroups.Batch096.numericValid1153 MergedCutGroups.Batch096.cellsSound1152 MergedCutGroups.Batch096.cellsSound1153
    MergedCutGroups.Batch096.cellsNumeric1152 MergedCutGroups.Batch096.cellsNumeric1153 MergedCutGroups.Batch096.populationMatches1152 MergedCutGroups.Batch096.populationMatches1153
    PopulationCertificates.Batch038.valid768 PopulationCertificates.Batch038.sound768 WitnessCertificates.Batch038.valid768 WitnessCertificates.Batch038.sound768 CountingCertificates.Batch038.valid768 CountingCertificates.Batch038.sound768
    CutLabelCertificates.Entropy019.valid385 CutLabelCertificates.Minority019.valid384 CutLabelCertificates.Minority019.sound384 H st hI
theorem probabilityBound384 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch096.certificate1152).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate768).dm (WitnessCertificates.Batch038.certificate768).beta) ≤ ((CutFailureCertificates.Budget038.certificate768).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound768 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate768).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch096.certificate1152).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch096.certificate1153).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch038.certificate768).omega:ℝ) ≤ ((CutFailureCertificates.Budget038.certificate768).bound:ℝ) at hb
  exact (exponentialBound384 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches385 : (MergedCutGroups.Batch096.certificate1155).GlobalMatches MergedCutGroups.Batch096.certificate1156 CountingCertificates.Batch038.certificate770 CutLabelCertificates.Entropy019.certificate386 CutLabelCertificates.Minority019.certificate385 := by decide +kernel
theorem exponentialBound385 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch096.certificate1155).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate770).dm (WitnessCertificates.Batch038.certificate770).beta) ≤ (2*exp (-((CountingCertificates.Batch038.certificate770).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch096.certificate1155).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch096.certificate1156).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch038.certificate770).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch096.certificate1155 MergedCutGroups.Batch096.certificate1156 CountingCertificates.Batch038.certificate770 CutLabelCertificates.Entropy019.certificate386 CutLabelCertificates.Minority019.certificate385 matches385 rfl rfl
    MergedCutGroups.Batch096.numericValid1155 MergedCutGroups.Batch096.numericValid1156 MergedCutGroups.Batch096.cellsSound1155 MergedCutGroups.Batch096.cellsSound1156
    MergedCutGroups.Batch096.cellsNumeric1155 MergedCutGroups.Batch096.cellsNumeric1156 MergedCutGroups.Batch096.populationMatches1155 MergedCutGroups.Batch096.populationMatches1156
    PopulationCertificates.Batch038.valid770 PopulationCertificates.Batch038.sound770 WitnessCertificates.Batch038.valid770 WitnessCertificates.Batch038.sound770 CountingCertificates.Batch038.valid770 CountingCertificates.Batch038.sound770
    CutLabelCertificates.Entropy019.valid386 CutLabelCertificates.Minority019.valid385 CutLabelCertificates.Minority019.sound385 H st hI
theorem probabilityBound385 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch096.certificate1155).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate770).dm (WitnessCertificates.Batch038.certificate770).beta) ≤ ((CutFailureCertificates.Budget038.certificate770).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound770 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate770).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch096.certificate1155).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch096.certificate1156).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch038.certificate770).omega:ℝ) ≤ ((CutFailureCertificates.Budget038.certificate770).bound:ℝ) at hb
  exact (exponentialBound385 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches386 : (MergedCutGroups.Batch096.certificate1158).GlobalMatches MergedCutGroups.Batch096.certificate1159 CountingCertificates.Batch038.certificate772 CutLabelCertificates.Entropy019.certificate387 CutLabelCertificates.Minority019.certificate386 := by decide +kernel
theorem exponentialBound386 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch096.certificate1158).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate772).dm (WitnessCertificates.Batch038.certificate772).beta) ≤ (2*exp (-((CountingCertificates.Batch038.certificate772).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch096.certificate1158).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch096.certificate1159).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch038.certificate772).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch096.certificate1158 MergedCutGroups.Batch096.certificate1159 CountingCertificates.Batch038.certificate772 CutLabelCertificates.Entropy019.certificate387 CutLabelCertificates.Minority019.certificate386 matches386 rfl rfl
    MergedCutGroups.Batch096.numericValid1158 MergedCutGroups.Batch096.numericValid1159 MergedCutGroups.Batch096.cellsSound1158 MergedCutGroups.Batch096.cellsSound1159
    MergedCutGroups.Batch096.cellsNumeric1158 MergedCutGroups.Batch096.cellsNumeric1159 MergedCutGroups.Batch096.populationMatches1158 MergedCutGroups.Batch096.populationMatches1159
    PopulationCertificates.Batch038.valid772 PopulationCertificates.Batch038.sound772 WitnessCertificates.Batch038.valid772 WitnessCertificates.Batch038.sound772 CountingCertificates.Batch038.valid772 CountingCertificates.Batch038.sound772
    CutLabelCertificates.Entropy019.valid387 CutLabelCertificates.Minority019.valid386 CutLabelCertificates.Minority019.sound386 H st hI
theorem probabilityBound386 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch096.certificate1158).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate772).dm (WitnessCertificates.Batch038.certificate772).beta) ≤ ((CutFailureCertificates.Budget038.certificate772).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound772 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate772).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch096.certificate1158).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch096.certificate1159).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch038.certificate772).omega:ℝ) ≤ ((CutFailureCertificates.Budget038.certificate772).bound:ℝ) at hb
  exact (exponentialBound386 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches387 : (MergedCutGroups.Batch096.certificate1161).GlobalMatches MergedCutGroups.Batch096.certificate1162 CountingCertificates.Batch038.certificate774 CutLabelCertificates.Entropy019.certificate388 CutLabelCertificates.Minority019.certificate387 := by decide +kernel
theorem exponentialBound387 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch096.certificate1161).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate774).dm (WitnessCertificates.Batch038.certificate774).beta) ≤ (2*exp (-((CountingCertificates.Batch038.certificate774).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch096.certificate1161).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch096.certificate1162).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch038.certificate774).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch096.certificate1161 MergedCutGroups.Batch096.certificate1162 CountingCertificates.Batch038.certificate774 CutLabelCertificates.Entropy019.certificate388 CutLabelCertificates.Minority019.certificate387 matches387 rfl rfl
    MergedCutGroups.Batch096.numericValid1161 MergedCutGroups.Batch096.numericValid1162 MergedCutGroups.Batch096.cellsSound1161 MergedCutGroups.Batch096.cellsSound1162
    MergedCutGroups.Batch096.cellsNumeric1161 MergedCutGroups.Batch096.cellsNumeric1162 MergedCutGroups.Batch096.populationMatches1161 MergedCutGroups.Batch096.populationMatches1162
    PopulationCertificates.Batch038.valid774 PopulationCertificates.Batch038.sound774 WitnessCertificates.Batch038.valid774 WitnessCertificates.Batch038.sound774 CountingCertificates.Batch038.valid774 CountingCertificates.Batch038.sound774
    CutLabelCertificates.Entropy019.valid388 CutLabelCertificates.Minority019.valid387 CutLabelCertificates.Minority019.sound387 H st hI
theorem probabilityBound387 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch096.certificate1161).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate774).dm (WitnessCertificates.Batch038.certificate774).beta) ≤ ((CutFailureCertificates.Budget038.certificate774).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound774 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate774).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch096.certificate1161).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch096.certificate1162).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch038.certificate774).omega:ℝ) ≤ ((CutFailureCertificates.Budget038.certificate774).bound:ℝ) at hb
  exact (exponentialBound387 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches388 : (MergedCutGroups.Batch097.certificate1164).GlobalMatches MergedCutGroups.Batch097.certificate1165 CountingCertificates.Batch038.certificate776 CutLabelCertificates.Entropy019.certificate389 CutLabelCertificates.Minority019.certificate388 := by decide +kernel
theorem exponentialBound388 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch097.certificate1164).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate776).dm (WitnessCertificates.Batch038.certificate776).beta) ≤ (2*exp (-((CountingCertificates.Batch038.certificate776).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch097.certificate1164).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch097.certificate1165).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch038.certificate776).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch097.certificate1164 MergedCutGroups.Batch097.certificate1165 CountingCertificates.Batch038.certificate776 CutLabelCertificates.Entropy019.certificate389 CutLabelCertificates.Minority019.certificate388 matches388 rfl rfl
    MergedCutGroups.Batch097.numericValid1164 MergedCutGroups.Batch097.numericValid1165 MergedCutGroups.Batch097.cellsSound1164 MergedCutGroups.Batch097.cellsSound1165
    MergedCutGroups.Batch097.cellsNumeric1164 MergedCutGroups.Batch097.cellsNumeric1165 MergedCutGroups.Batch097.populationMatches1164 MergedCutGroups.Batch097.populationMatches1165
    PopulationCertificates.Batch038.valid776 PopulationCertificates.Batch038.sound776 WitnessCertificates.Batch038.valid776 WitnessCertificates.Batch038.sound776 CountingCertificates.Batch038.valid776 CountingCertificates.Batch038.sound776
    CutLabelCertificates.Entropy019.valid389 CutLabelCertificates.Minority019.valid388 CutLabelCertificates.Minority019.sound388 H st hI
theorem probabilityBound388 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch097.certificate1164).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate776).dm (WitnessCertificates.Batch038.certificate776).beta) ≤ ((CutFailureCertificates.Budget038.certificate776).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound776 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate776).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch097.certificate1164).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch097.certificate1165).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch038.certificate776).omega:ℝ) ≤ ((CutFailureCertificates.Budget038.certificate776).bound:ℝ) at hb
  exact (exponentialBound388 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches389 : (MergedCutGroups.Batch097.certificate1167).GlobalMatches MergedCutGroups.Batch097.certificate1168 CountingCertificates.Batch038.certificate778 CutLabelCertificates.Entropy019.certificate390 CutLabelCertificates.Minority019.certificate389 := by decide +kernel
theorem exponentialBound389 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch097.certificate1167).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate778).dm (WitnessCertificates.Batch038.certificate778).beta) ≤ (2*exp (-((CountingCertificates.Batch038.certificate778).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch097.certificate1167).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch097.certificate1168).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch038.certificate778).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch097.certificate1167 MergedCutGroups.Batch097.certificate1168 CountingCertificates.Batch038.certificate778 CutLabelCertificates.Entropy019.certificate390 CutLabelCertificates.Minority019.certificate389 matches389 rfl rfl
    MergedCutGroups.Batch097.numericValid1167 MergedCutGroups.Batch097.numericValid1168 MergedCutGroups.Batch097.cellsSound1167 MergedCutGroups.Batch097.cellsSound1168
    MergedCutGroups.Batch097.cellsNumeric1167 MergedCutGroups.Batch097.cellsNumeric1168 MergedCutGroups.Batch097.populationMatches1167 MergedCutGroups.Batch097.populationMatches1168
    PopulationCertificates.Batch038.valid778 PopulationCertificates.Batch038.sound778 WitnessCertificates.Batch038.valid778 WitnessCertificates.Batch038.sound778 CountingCertificates.Batch038.valid778 CountingCertificates.Batch038.sound778
    CutLabelCertificates.Entropy019.valid390 CutLabelCertificates.Minority019.valid389 CutLabelCertificates.Minority019.sound389 H st hI
theorem probabilityBound389 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch097.certificate1167).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch038.certificate778).dm (WitnessCertificates.Batch038.certificate778).beta) ≤ ((CutFailureCertificates.Budget038.certificate778).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget038.sound778 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch038.certificate778).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch097.certificate1167).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch097.certificate1168).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch038.certificate778).omega:ℝ) ≤ ((CutFailureCertificates.Budget038.certificate778).bound:ℝ) at hb
  exact (exponentialBound389 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches390 : (MergedCutGroups.Batch097.certificate1170).GlobalMatches MergedCutGroups.Batch097.certificate1171 CountingCertificates.Batch039.certificate780 CutLabelCertificates.Entropy019.certificate391 CutLabelCertificates.Minority019.certificate390 := by decide +kernel
theorem exponentialBound390 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch097.certificate1170).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate780).dm (WitnessCertificates.Batch039.certificate780).beta) ≤ (2*exp (-((CountingCertificates.Batch039.certificate780).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch097.certificate1170).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch097.certificate1171).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch039.certificate780).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch097.certificate1170 MergedCutGroups.Batch097.certificate1171 CountingCertificates.Batch039.certificate780 CutLabelCertificates.Entropy019.certificate391 CutLabelCertificates.Minority019.certificate390 matches390 rfl rfl
    MergedCutGroups.Batch097.numericValid1170 MergedCutGroups.Batch097.numericValid1171 MergedCutGroups.Batch097.cellsSound1170 MergedCutGroups.Batch097.cellsSound1171
    MergedCutGroups.Batch097.cellsNumeric1170 MergedCutGroups.Batch097.cellsNumeric1171 MergedCutGroups.Batch097.populationMatches1170 MergedCutGroups.Batch097.populationMatches1171
    PopulationCertificates.Batch039.valid780 PopulationCertificates.Batch039.sound780 WitnessCertificates.Batch039.valid780 WitnessCertificates.Batch039.sound780 CountingCertificates.Batch039.valid780 CountingCertificates.Batch039.sound780
    CutLabelCertificates.Entropy019.valid391 CutLabelCertificates.Minority019.valid390 CutLabelCertificates.Minority019.sound390 H st hI
theorem probabilityBound390 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch097.certificate1170).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate780).dm (WitnessCertificates.Batch039.certificate780).beta) ≤ ((CutFailureCertificates.Budget039.certificate780).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound780 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate780).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch097.certificate1170).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch097.certificate1171).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch039.certificate780).omega:ℝ) ≤ ((CutFailureCertificates.Budget039.certificate780).bound:ℝ) at hb
  exact (exponentialBound390 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches391 : (MergedCutGroups.Batch097.certificate1173).GlobalMatches MergedCutGroups.Batch097.certificate1174 CountingCertificates.Batch039.certificate782 CutLabelCertificates.Entropy019.certificate392 CutLabelCertificates.Minority019.certificate391 := by decide +kernel
theorem exponentialBound391 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch097.certificate1173).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate782).dm (WitnessCertificates.Batch039.certificate782).beta) ≤ (2*exp (-((CountingCertificates.Batch039.certificate782).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch097.certificate1173).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch097.certificate1174).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch039.certificate782).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch097.certificate1173 MergedCutGroups.Batch097.certificate1174 CountingCertificates.Batch039.certificate782 CutLabelCertificates.Entropy019.certificate392 CutLabelCertificates.Minority019.certificate391 matches391 rfl rfl
    MergedCutGroups.Batch097.numericValid1173 MergedCutGroups.Batch097.numericValid1174 MergedCutGroups.Batch097.cellsSound1173 MergedCutGroups.Batch097.cellsSound1174
    MergedCutGroups.Batch097.cellsNumeric1173 MergedCutGroups.Batch097.cellsNumeric1174 MergedCutGroups.Batch097.populationMatches1173 MergedCutGroups.Batch097.populationMatches1174
    PopulationCertificates.Batch039.valid782 PopulationCertificates.Batch039.sound782 WitnessCertificates.Batch039.valid782 WitnessCertificates.Batch039.sound782 CountingCertificates.Batch039.valid782 CountingCertificates.Batch039.sound782
    CutLabelCertificates.Entropy019.valid392 CutLabelCertificates.Minority019.valid391 CutLabelCertificates.Minority019.sound391 H st hI
theorem probabilityBound391 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch097.certificate1173).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate782).dm (WitnessCertificates.Batch039.certificate782).beta) ≤ ((CutFailureCertificates.Budget039.certificate782).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound782 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate782).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch097.certificate1173).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch097.certificate1174).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch039.certificate782).omega:ℝ) ≤ ((CutFailureCertificates.Budget039.certificate782).bound:ℝ) at hb
  exact (exponentialBound391 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches392 : (MergedCutGroups.Batch098.certificate1176).GlobalMatches MergedCutGroups.Batch098.certificate1177 CountingCertificates.Batch039.certificate784 CutLabelCertificates.Entropy019.certificate393 CutLabelCertificates.Minority019.certificate392 := by decide +kernel
theorem exponentialBound392 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch098.certificate1176).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate784).dm (WitnessCertificates.Batch039.certificate784).beta) ≤ (2*exp (-((CountingCertificates.Batch039.certificate784).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch098.certificate1176).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch098.certificate1177).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch039.certificate784).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch098.certificate1176 MergedCutGroups.Batch098.certificate1177 CountingCertificates.Batch039.certificate784 CutLabelCertificates.Entropy019.certificate393 CutLabelCertificates.Minority019.certificate392 matches392 rfl rfl
    MergedCutGroups.Batch098.numericValid1176 MergedCutGroups.Batch098.numericValid1177 MergedCutGroups.Batch098.cellsSound1176 MergedCutGroups.Batch098.cellsSound1177
    MergedCutGroups.Batch098.cellsNumeric1176 MergedCutGroups.Batch098.cellsNumeric1177 MergedCutGroups.Batch098.populationMatches1176 MergedCutGroups.Batch098.populationMatches1177
    PopulationCertificates.Batch039.valid784 PopulationCertificates.Batch039.sound784 WitnessCertificates.Batch039.valid784 WitnessCertificates.Batch039.sound784 CountingCertificates.Batch039.valid784 CountingCertificates.Batch039.sound784
    CutLabelCertificates.Entropy019.valid393 CutLabelCertificates.Minority019.valid392 CutLabelCertificates.Minority019.sound392 H st hI
theorem probabilityBound392 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch098.certificate1176).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate784).dm (WitnessCertificates.Batch039.certificate784).beta) ≤ ((CutFailureCertificates.Budget039.certificate784).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound784 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate784).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch098.certificate1176).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch098.certificate1177).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch039.certificate784).omega:ℝ) ≤ ((CutFailureCertificates.Budget039.certificate784).bound:ℝ) at hb
  exact (exponentialBound392 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches393 : (MergedCutGroups.Batch098.certificate1179).GlobalMatches MergedCutGroups.Batch098.certificate1180 CountingCertificates.Batch039.certificate786 CutLabelCertificates.Entropy019.certificate394 CutLabelCertificates.Minority019.certificate393 := by decide +kernel
theorem exponentialBound393 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch098.certificate1179).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate786).dm (WitnessCertificates.Batch039.certificate786).beta) ≤ (2*exp (-((CountingCertificates.Batch039.certificate786).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch098.certificate1179).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch098.certificate1180).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch039.certificate786).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch098.certificate1179 MergedCutGroups.Batch098.certificate1180 CountingCertificates.Batch039.certificate786 CutLabelCertificates.Entropy019.certificate394 CutLabelCertificates.Minority019.certificate393 matches393 rfl rfl
    MergedCutGroups.Batch098.numericValid1179 MergedCutGroups.Batch098.numericValid1180 MergedCutGroups.Batch098.cellsSound1179 MergedCutGroups.Batch098.cellsSound1180
    MergedCutGroups.Batch098.cellsNumeric1179 MergedCutGroups.Batch098.cellsNumeric1180 MergedCutGroups.Batch098.populationMatches1179 MergedCutGroups.Batch098.populationMatches1180
    PopulationCertificates.Batch039.valid786 PopulationCertificates.Batch039.sound786 WitnessCertificates.Batch039.valid786 WitnessCertificates.Batch039.sound786 CountingCertificates.Batch039.valid786 CountingCertificates.Batch039.sound786
    CutLabelCertificates.Entropy019.valid394 CutLabelCertificates.Minority019.valid393 CutLabelCertificates.Minority019.sound393 H st hI
theorem probabilityBound393 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch098.certificate1179).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate786).dm (WitnessCertificates.Batch039.certificate786).beta) ≤ ((CutFailureCertificates.Budget039.certificate786).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound786 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate786).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch098.certificate1179).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch098.certificate1180).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch039.certificate786).omega:ℝ) ≤ ((CutFailureCertificates.Budget039.certificate786).bound:ℝ) at hb
  exact (exponentialBound393 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches394 : (MergedCutGroups.Batch098.certificate1182).GlobalMatches MergedCutGroups.Batch098.certificate1183 CountingCertificates.Batch039.certificate788 CutLabelCertificates.Entropy019.certificate395 CutLabelCertificates.Minority019.certificate394 := by decide +kernel
theorem exponentialBound394 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch098.certificate1182).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate788).dm (WitnessCertificates.Batch039.certificate788).beta) ≤ (2*exp (-((CountingCertificates.Batch039.certificate788).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch098.certificate1182).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch098.certificate1183).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch039.certificate788).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch098.certificate1182 MergedCutGroups.Batch098.certificate1183 CountingCertificates.Batch039.certificate788 CutLabelCertificates.Entropy019.certificate395 CutLabelCertificates.Minority019.certificate394 matches394 rfl rfl
    MergedCutGroups.Batch098.numericValid1182 MergedCutGroups.Batch098.numericValid1183 MergedCutGroups.Batch098.cellsSound1182 MergedCutGroups.Batch098.cellsSound1183
    MergedCutGroups.Batch098.cellsNumeric1182 MergedCutGroups.Batch098.cellsNumeric1183 MergedCutGroups.Batch098.populationMatches1182 MergedCutGroups.Batch098.populationMatches1183
    PopulationCertificates.Batch039.valid788 PopulationCertificates.Batch039.sound788 WitnessCertificates.Batch039.valid788 WitnessCertificates.Batch039.sound788 CountingCertificates.Batch039.valid788 CountingCertificates.Batch039.sound788
    CutLabelCertificates.Entropy019.valid395 CutLabelCertificates.Minority019.valid394 CutLabelCertificates.Minority019.sound394 H st hI
theorem probabilityBound394 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch098.certificate1182).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate788).dm (WitnessCertificates.Batch039.certificate788).beta) ≤ ((CutFailureCertificates.Budget039.certificate788).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound788 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate788).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch098.certificate1182).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch098.certificate1183).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch039.certificate788).omega:ℝ) ≤ ((CutFailureCertificates.Budget039.certificate788).bound:ℝ) at hb
  exact (exponentialBound394 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches395 : (MergedCutGroups.Batch098.certificate1185).GlobalMatches MergedCutGroups.Batch098.certificate1186 CountingCertificates.Batch039.certificate790 CutLabelCertificates.Entropy019.certificate396 CutLabelCertificates.Minority019.certificate395 := by decide +kernel
theorem exponentialBound395 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch098.certificate1185).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate790).dm (WitnessCertificates.Batch039.certificate790).beta) ≤ (2*exp (-((CountingCertificates.Batch039.certificate790).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch098.certificate1185).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch098.certificate1186).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch039.certificate790).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch098.certificate1185 MergedCutGroups.Batch098.certificate1186 CountingCertificates.Batch039.certificate790 CutLabelCertificates.Entropy019.certificate396 CutLabelCertificates.Minority019.certificate395 matches395 rfl rfl
    MergedCutGroups.Batch098.numericValid1185 MergedCutGroups.Batch098.numericValid1186 MergedCutGroups.Batch098.cellsSound1185 MergedCutGroups.Batch098.cellsSound1186
    MergedCutGroups.Batch098.cellsNumeric1185 MergedCutGroups.Batch098.cellsNumeric1186 MergedCutGroups.Batch098.populationMatches1185 MergedCutGroups.Batch098.populationMatches1186
    PopulationCertificates.Batch039.valid790 PopulationCertificates.Batch039.sound790 WitnessCertificates.Batch039.valid790 WitnessCertificates.Batch039.sound790 CountingCertificates.Batch039.valid790 CountingCertificates.Batch039.sound790
    CutLabelCertificates.Entropy019.valid396 CutLabelCertificates.Minority019.valid395 CutLabelCertificates.Minority019.sound395 H st hI
theorem probabilityBound395 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch098.certificate1185).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate790).dm (WitnessCertificates.Batch039.certificate790).beta) ≤ ((CutFailureCertificates.Budget039.certificate790).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound790 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate790).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch098.certificate1185).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch098.certificate1186).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch039.certificate790).omega:ℝ) ≤ ((CutFailureCertificates.Budget039.certificate790).bound:ℝ) at hb
  exact (exponentialBound395 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches396 : (MergedCutGroups.Batch099.certificate1188).GlobalMatches MergedCutGroups.Batch099.certificate1189 CountingCertificates.Batch039.certificate792 CutLabelCertificates.Entropy019.certificate397 CutLabelCertificates.Minority019.certificate396 := by decide +kernel
theorem exponentialBound396 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch099.certificate1188).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate792).dm (WitnessCertificates.Batch039.certificate792).beta) ≤ (2*exp (-((CountingCertificates.Batch039.certificate792).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch099.certificate1188).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch099.certificate1189).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch039.certificate792).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch099.certificate1188 MergedCutGroups.Batch099.certificate1189 CountingCertificates.Batch039.certificate792 CutLabelCertificates.Entropy019.certificate397 CutLabelCertificates.Minority019.certificate396 matches396 rfl rfl
    MergedCutGroups.Batch099.numericValid1188 MergedCutGroups.Batch099.numericValid1189 MergedCutGroups.Batch099.cellsSound1188 MergedCutGroups.Batch099.cellsSound1189
    MergedCutGroups.Batch099.cellsNumeric1188 MergedCutGroups.Batch099.cellsNumeric1189 MergedCutGroups.Batch099.populationMatches1188 MergedCutGroups.Batch099.populationMatches1189
    PopulationCertificates.Batch039.valid792 PopulationCertificates.Batch039.sound792 WitnessCertificates.Batch039.valid792 WitnessCertificates.Batch039.sound792 CountingCertificates.Batch039.valid792 CountingCertificates.Batch039.sound792
    CutLabelCertificates.Entropy019.valid397 CutLabelCertificates.Minority019.valid396 CutLabelCertificates.Minority019.sound396 H st hI
theorem probabilityBound396 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch099.certificate1188).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate792).dm (WitnessCertificates.Batch039.certificate792).beta) ≤ ((CutFailureCertificates.Budget039.certificate792).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound792 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate792).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch099.certificate1188).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch099.certificate1189).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch039.certificate792).omega:ℝ) ≤ ((CutFailureCertificates.Budget039.certificate792).bound:ℝ) at hb
  exact (exponentialBound396 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches397 : (MergedCutGroups.Batch099.certificate1191).GlobalMatches MergedCutGroups.Batch099.certificate1192 CountingCertificates.Batch039.certificate794 CutLabelCertificates.Entropy019.certificate398 CutLabelCertificates.Minority019.certificate397 := by decide +kernel
theorem exponentialBound397 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch099.certificate1191).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate794).dm (WitnessCertificates.Batch039.certificate794).beta) ≤ (2*exp (-((CountingCertificates.Batch039.certificate794).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch099.certificate1191).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch099.certificate1192).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch039.certificate794).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch099.certificate1191 MergedCutGroups.Batch099.certificate1192 CountingCertificates.Batch039.certificate794 CutLabelCertificates.Entropy019.certificate398 CutLabelCertificates.Minority019.certificate397 matches397 rfl rfl
    MergedCutGroups.Batch099.numericValid1191 MergedCutGroups.Batch099.numericValid1192 MergedCutGroups.Batch099.cellsSound1191 MergedCutGroups.Batch099.cellsSound1192
    MergedCutGroups.Batch099.cellsNumeric1191 MergedCutGroups.Batch099.cellsNumeric1192 MergedCutGroups.Batch099.populationMatches1191 MergedCutGroups.Batch099.populationMatches1192
    PopulationCertificates.Batch039.valid794 PopulationCertificates.Batch039.sound794 WitnessCertificates.Batch039.valid794 WitnessCertificates.Batch039.sound794 CountingCertificates.Batch039.valid794 CountingCertificates.Batch039.sound794
    CutLabelCertificates.Entropy019.valid398 CutLabelCertificates.Minority019.valid397 CutLabelCertificates.Minority019.sound397 H st hI
theorem probabilityBound397 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch099.certificate1191).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate794).dm (WitnessCertificates.Batch039.certificate794).beta) ≤ ((CutFailureCertificates.Budget039.certificate794).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound794 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate794).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch099.certificate1191).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch099.certificate1192).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch039.certificate794).omega:ℝ) ≤ ((CutFailureCertificates.Budget039.certificate794).bound:ℝ) at hb
  exact (exponentialBound397 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches398 : (MergedCutGroups.Batch099.certificate1194).GlobalMatches MergedCutGroups.Batch099.certificate1195 CountingCertificates.Batch039.certificate796 CutLabelCertificates.Entropy019.certificate399 CutLabelCertificates.Minority019.certificate398 := by decide +kernel
theorem exponentialBound398 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch099.certificate1194).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate796).dm (WitnessCertificates.Batch039.certificate796).beta) ≤ (2*exp (-((CountingCertificates.Batch039.certificate796).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch099.certificate1194).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch099.certificate1195).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch039.certificate796).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch099.certificate1194 MergedCutGroups.Batch099.certificate1195 CountingCertificates.Batch039.certificate796 CutLabelCertificates.Entropy019.certificate399 CutLabelCertificates.Minority019.certificate398 matches398 rfl rfl
    MergedCutGroups.Batch099.numericValid1194 MergedCutGroups.Batch099.numericValid1195 MergedCutGroups.Batch099.cellsSound1194 MergedCutGroups.Batch099.cellsSound1195
    MergedCutGroups.Batch099.cellsNumeric1194 MergedCutGroups.Batch099.cellsNumeric1195 MergedCutGroups.Batch099.populationMatches1194 MergedCutGroups.Batch099.populationMatches1195
    PopulationCertificates.Batch039.valid796 PopulationCertificates.Batch039.sound796 WitnessCertificates.Batch039.valid796 WitnessCertificates.Batch039.sound796 CountingCertificates.Batch039.valid796 CountingCertificates.Batch039.sound796
    CutLabelCertificates.Entropy019.valid399 CutLabelCertificates.Minority019.valid398 CutLabelCertificates.Minority019.sound398 H st hI
theorem probabilityBound398 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch099.certificate1194).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate796).dm (WitnessCertificates.Batch039.certificate796).beta) ≤ ((CutFailureCertificates.Budget039.certificate796).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound796 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate796).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch099.certificate1194).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch099.certificate1195).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch039.certificate796).omega:ℝ) ≤ ((CutFailureCertificates.Budget039.certificate796).bound:ℝ) at hb
  exact (exponentialBound398 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches399 : (MergedCutGroups.Batch099.certificate1197).GlobalMatches MergedCutGroups.Batch099.certificate1198 CountingCertificates.Batch039.certificate798 CutLabelCertificates.Entropy020.certificate400 CutLabelCertificates.Minority019.certificate399 := by decide +kernel
theorem exponentialBound399 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch099.certificate1197).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate798).dm (WitnessCertificates.Batch039.certificate798).beta) ≤ (2*exp (-((CountingCertificates.Batch039.certificate798).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch099.certificate1197).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch099.certificate1198).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch039.certificate798).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch099.certificate1197 MergedCutGroups.Batch099.certificate1198 CountingCertificates.Batch039.certificate798 CutLabelCertificates.Entropy020.certificate400 CutLabelCertificates.Minority019.certificate399 matches399 rfl rfl
    MergedCutGroups.Batch099.numericValid1197 MergedCutGroups.Batch099.numericValid1198 MergedCutGroups.Batch099.cellsSound1197 MergedCutGroups.Batch099.cellsSound1198
    MergedCutGroups.Batch099.cellsNumeric1197 MergedCutGroups.Batch099.cellsNumeric1198 MergedCutGroups.Batch099.populationMatches1197 MergedCutGroups.Batch099.populationMatches1198
    PopulationCertificates.Batch039.valid798 PopulationCertificates.Batch039.sound798 WitnessCertificates.Batch039.valid798 WitnessCertificates.Batch039.sound798 CountingCertificates.Batch039.valid798 CountingCertificates.Batch039.sound798
    CutLabelCertificates.Entropy020.valid400 CutLabelCertificates.Minority019.valid399 CutLabelCertificates.Minority019.sound399 H st hI
theorem probabilityBound399 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch099.certificate1197).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch039.certificate798).dm (WitnessCertificates.Batch039.certificate798).beta) ≤ ((CutFailureCertificates.Budget039.certificate798).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget039.sound798 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch039.certificate798).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch099.certificate1197).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch099.certificate1198).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch039.certificate798).omega:ℝ) ≤ ((CutFailureCertificates.Budget039.certificate798).bound:ℝ) at hb
  exact (exponentialBound399 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch019
