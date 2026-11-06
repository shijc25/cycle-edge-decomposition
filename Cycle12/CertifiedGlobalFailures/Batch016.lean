import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch032
import Cycle12.CountingCertificates.Batch033
import Cycle12.CutFailureCertificates.Budget032
import Cycle12.CutFailureCertificates.Budget033
import Cycle12.CutLabelCertificates.Entropy016
import Cycle12.CutLabelCertificates.Entropy017
import Cycle12.CutLabelCertificates.Minority016
import Cycle12.MergedCutGroups.Batch080
import Cycle12.MergedCutGroups.Batch081
import Cycle12.MergedCutGroups.Batch082
import Cycle12.MergedCutGroups.Batch083
import Cycle12.MergedCutGroups.Batch084
import Cycle12.PopulationCertificates.Batch032
import Cycle12.PopulationCertificates.Batch033
import Cycle12.WitnessCertificates.Batch032
import Cycle12.WitnessCertificates.Batch033

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch016
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches320 : (MergedCutGroups.Batch080.certificate960).GlobalMatches MergedCutGroups.Batch080.certificate961 CountingCertificates.Batch032.certificate640 CutLabelCertificates.Entropy016.certificate321 CutLabelCertificates.Minority016.certificate320 := by decide +kernel
theorem exponentialBound320 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch080.certificate960).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate640).dm (WitnessCertificates.Batch032.certificate640).beta) ≤ (2*exp (-((CountingCertificates.Batch032.certificate640).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch080.certificate960).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch080.certificate961).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch032.certificate640).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch080.certificate960 MergedCutGroups.Batch080.certificate961 CountingCertificates.Batch032.certificate640 CutLabelCertificates.Entropy016.certificate321 CutLabelCertificates.Minority016.certificate320 matches320 rfl rfl
    MergedCutGroups.Batch080.numericValid960 MergedCutGroups.Batch080.numericValid961 MergedCutGroups.Batch080.cellsSound960 MergedCutGroups.Batch080.cellsSound961
    MergedCutGroups.Batch080.cellsNumeric960 MergedCutGroups.Batch080.cellsNumeric961 MergedCutGroups.Batch080.populationMatches960 MergedCutGroups.Batch080.populationMatches961
    PopulationCertificates.Batch032.valid640 PopulationCertificates.Batch032.sound640 WitnessCertificates.Batch032.valid640 WitnessCertificates.Batch032.sound640 CountingCertificates.Batch032.valid640 CountingCertificates.Batch032.sound640
    CutLabelCertificates.Entropy016.valid321 CutLabelCertificates.Minority016.valid320 CutLabelCertificates.Minority016.sound320 H st hI
theorem probabilityBound320 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch080.certificate960).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate640).dm (WitnessCertificates.Batch032.certificate640).beta) ≤ ((CutFailureCertificates.Budget032.certificate640).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound640 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate640).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch080.certificate960).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch080.certificate961).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch032.certificate640).omega:ℝ) ≤ ((CutFailureCertificates.Budget032.certificate640).bound:ℝ) at hb
  exact (exponentialBound320 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches321 : (MergedCutGroups.Batch080.certificate963).GlobalMatches MergedCutGroups.Batch080.certificate964 CountingCertificates.Batch032.certificate642 CutLabelCertificates.Entropy016.certificate322 CutLabelCertificates.Minority016.certificate321 := by decide +kernel
theorem exponentialBound321 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch080.certificate963).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate642).dm (WitnessCertificates.Batch032.certificate642).beta) ≤ (2*exp (-((CountingCertificates.Batch032.certificate642).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch080.certificate963).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch080.certificate964).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch032.certificate642).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch080.certificate963 MergedCutGroups.Batch080.certificate964 CountingCertificates.Batch032.certificate642 CutLabelCertificates.Entropy016.certificate322 CutLabelCertificates.Minority016.certificate321 matches321 rfl rfl
    MergedCutGroups.Batch080.numericValid963 MergedCutGroups.Batch080.numericValid964 MergedCutGroups.Batch080.cellsSound963 MergedCutGroups.Batch080.cellsSound964
    MergedCutGroups.Batch080.cellsNumeric963 MergedCutGroups.Batch080.cellsNumeric964 MergedCutGroups.Batch080.populationMatches963 MergedCutGroups.Batch080.populationMatches964
    PopulationCertificates.Batch032.valid642 PopulationCertificates.Batch032.sound642 WitnessCertificates.Batch032.valid642 WitnessCertificates.Batch032.sound642 CountingCertificates.Batch032.valid642 CountingCertificates.Batch032.sound642
    CutLabelCertificates.Entropy016.valid322 CutLabelCertificates.Minority016.valid321 CutLabelCertificates.Minority016.sound321 H st hI
theorem probabilityBound321 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch080.certificate963).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate642).dm (WitnessCertificates.Batch032.certificate642).beta) ≤ ((CutFailureCertificates.Budget032.certificate642).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound642 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate642).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch080.certificate963).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch080.certificate964).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch032.certificate642).omega:ℝ) ≤ ((CutFailureCertificates.Budget032.certificate642).bound:ℝ) at hb
  exact (exponentialBound321 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches322 : (MergedCutGroups.Batch080.certificate966).GlobalMatches MergedCutGroups.Batch080.certificate967 CountingCertificates.Batch032.certificate644 CutLabelCertificates.Entropy016.certificate323 CutLabelCertificates.Minority016.certificate322 := by decide +kernel
theorem exponentialBound322 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch080.certificate966).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate644).dm (WitnessCertificates.Batch032.certificate644).beta) ≤ (2*exp (-((CountingCertificates.Batch032.certificate644).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch080.certificate966).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch080.certificate967).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch032.certificate644).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch080.certificate966 MergedCutGroups.Batch080.certificate967 CountingCertificates.Batch032.certificate644 CutLabelCertificates.Entropy016.certificate323 CutLabelCertificates.Minority016.certificate322 matches322 rfl rfl
    MergedCutGroups.Batch080.numericValid966 MergedCutGroups.Batch080.numericValid967 MergedCutGroups.Batch080.cellsSound966 MergedCutGroups.Batch080.cellsSound967
    MergedCutGroups.Batch080.cellsNumeric966 MergedCutGroups.Batch080.cellsNumeric967 MergedCutGroups.Batch080.populationMatches966 MergedCutGroups.Batch080.populationMatches967
    PopulationCertificates.Batch032.valid644 PopulationCertificates.Batch032.sound644 WitnessCertificates.Batch032.valid644 WitnessCertificates.Batch032.sound644 CountingCertificates.Batch032.valid644 CountingCertificates.Batch032.sound644
    CutLabelCertificates.Entropy016.valid323 CutLabelCertificates.Minority016.valid322 CutLabelCertificates.Minority016.sound322 H st hI
theorem probabilityBound322 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch080.certificate966).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate644).dm (WitnessCertificates.Batch032.certificate644).beta) ≤ ((CutFailureCertificates.Budget032.certificate644).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound644 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate644).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch080.certificate966).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch080.certificate967).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch032.certificate644).omega:ℝ) ≤ ((CutFailureCertificates.Budget032.certificate644).bound:ℝ) at hb
  exact (exponentialBound322 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches323 : (MergedCutGroups.Batch080.certificate969).GlobalMatches MergedCutGroups.Batch080.certificate970 CountingCertificates.Batch032.certificate646 CutLabelCertificates.Entropy016.certificate324 CutLabelCertificates.Minority016.certificate323 := by decide +kernel
theorem exponentialBound323 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch080.certificate969).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate646).dm (WitnessCertificates.Batch032.certificate646).beta) ≤ (2*exp (-((CountingCertificates.Batch032.certificate646).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch080.certificate969).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch080.certificate970).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch032.certificate646).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch080.certificate969 MergedCutGroups.Batch080.certificate970 CountingCertificates.Batch032.certificate646 CutLabelCertificates.Entropy016.certificate324 CutLabelCertificates.Minority016.certificate323 matches323 rfl rfl
    MergedCutGroups.Batch080.numericValid969 MergedCutGroups.Batch080.numericValid970 MergedCutGroups.Batch080.cellsSound969 MergedCutGroups.Batch080.cellsSound970
    MergedCutGroups.Batch080.cellsNumeric969 MergedCutGroups.Batch080.cellsNumeric970 MergedCutGroups.Batch080.populationMatches969 MergedCutGroups.Batch080.populationMatches970
    PopulationCertificates.Batch032.valid646 PopulationCertificates.Batch032.sound646 WitnessCertificates.Batch032.valid646 WitnessCertificates.Batch032.sound646 CountingCertificates.Batch032.valid646 CountingCertificates.Batch032.sound646
    CutLabelCertificates.Entropy016.valid324 CutLabelCertificates.Minority016.valid323 CutLabelCertificates.Minority016.sound323 H st hI
theorem probabilityBound323 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch080.certificate969).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate646).dm (WitnessCertificates.Batch032.certificate646).beta) ≤ ((CutFailureCertificates.Budget032.certificate646).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound646 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate646).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch080.certificate969).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch080.certificate970).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch032.certificate646).omega:ℝ) ≤ ((CutFailureCertificates.Budget032.certificate646).bound:ℝ) at hb
  exact (exponentialBound323 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches324 : (MergedCutGroups.Batch081.certificate972).GlobalMatches MergedCutGroups.Batch081.certificate973 CountingCertificates.Batch032.certificate648 CutLabelCertificates.Entropy016.certificate325 CutLabelCertificates.Minority016.certificate324 := by decide +kernel
theorem exponentialBound324 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch081.certificate972).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate648).dm (WitnessCertificates.Batch032.certificate648).beta) ≤ (2*exp (-((CountingCertificates.Batch032.certificate648).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch081.certificate972).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch081.certificate973).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch032.certificate648).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch081.certificate972 MergedCutGroups.Batch081.certificate973 CountingCertificates.Batch032.certificate648 CutLabelCertificates.Entropy016.certificate325 CutLabelCertificates.Minority016.certificate324 matches324 rfl rfl
    MergedCutGroups.Batch081.numericValid972 MergedCutGroups.Batch081.numericValid973 MergedCutGroups.Batch081.cellsSound972 MergedCutGroups.Batch081.cellsSound973
    MergedCutGroups.Batch081.cellsNumeric972 MergedCutGroups.Batch081.cellsNumeric973 MergedCutGroups.Batch081.populationMatches972 MergedCutGroups.Batch081.populationMatches973
    PopulationCertificates.Batch032.valid648 PopulationCertificates.Batch032.sound648 WitnessCertificates.Batch032.valid648 WitnessCertificates.Batch032.sound648 CountingCertificates.Batch032.valid648 CountingCertificates.Batch032.sound648
    CutLabelCertificates.Entropy016.valid325 CutLabelCertificates.Minority016.valid324 CutLabelCertificates.Minority016.sound324 H st hI
theorem probabilityBound324 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch081.certificate972).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate648).dm (WitnessCertificates.Batch032.certificate648).beta) ≤ ((CutFailureCertificates.Budget032.certificate648).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound648 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate648).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch081.certificate972).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch081.certificate973).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch032.certificate648).omega:ℝ) ≤ ((CutFailureCertificates.Budget032.certificate648).bound:ℝ) at hb
  exact (exponentialBound324 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches325 : (MergedCutGroups.Batch081.certificate975).GlobalMatches MergedCutGroups.Batch081.certificate976 CountingCertificates.Batch032.certificate650 CutLabelCertificates.Entropy016.certificate326 CutLabelCertificates.Minority016.certificate325 := by decide +kernel
theorem exponentialBound325 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch081.certificate975).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate650).dm (WitnessCertificates.Batch032.certificate650).beta) ≤ (2*exp (-((CountingCertificates.Batch032.certificate650).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch081.certificate975).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch081.certificate976).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch032.certificate650).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch081.certificate975 MergedCutGroups.Batch081.certificate976 CountingCertificates.Batch032.certificate650 CutLabelCertificates.Entropy016.certificate326 CutLabelCertificates.Minority016.certificate325 matches325 rfl rfl
    MergedCutGroups.Batch081.numericValid975 MergedCutGroups.Batch081.numericValid976 MergedCutGroups.Batch081.cellsSound975 MergedCutGroups.Batch081.cellsSound976
    MergedCutGroups.Batch081.cellsNumeric975 MergedCutGroups.Batch081.cellsNumeric976 MergedCutGroups.Batch081.populationMatches975 MergedCutGroups.Batch081.populationMatches976
    PopulationCertificates.Batch032.valid650 PopulationCertificates.Batch032.sound650 WitnessCertificates.Batch032.valid650 WitnessCertificates.Batch032.sound650 CountingCertificates.Batch032.valid650 CountingCertificates.Batch032.sound650
    CutLabelCertificates.Entropy016.valid326 CutLabelCertificates.Minority016.valid325 CutLabelCertificates.Minority016.sound325 H st hI
theorem probabilityBound325 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch081.certificate975).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate650).dm (WitnessCertificates.Batch032.certificate650).beta) ≤ ((CutFailureCertificates.Budget032.certificate650).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound650 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate650).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch081.certificate975).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch081.certificate976).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch032.certificate650).omega:ℝ) ≤ ((CutFailureCertificates.Budget032.certificate650).bound:ℝ) at hb
  exact (exponentialBound325 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches326 : (MergedCutGroups.Batch081.certificate978).GlobalMatches MergedCutGroups.Batch081.certificate979 CountingCertificates.Batch032.certificate652 CutLabelCertificates.Entropy016.certificate327 CutLabelCertificates.Minority016.certificate326 := by decide +kernel
theorem exponentialBound326 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch081.certificate978).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate652).dm (WitnessCertificates.Batch032.certificate652).beta) ≤ (2*exp (-((CountingCertificates.Batch032.certificate652).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch081.certificate978).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch081.certificate979).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch032.certificate652).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch081.certificate978 MergedCutGroups.Batch081.certificate979 CountingCertificates.Batch032.certificate652 CutLabelCertificates.Entropy016.certificate327 CutLabelCertificates.Minority016.certificate326 matches326 rfl rfl
    MergedCutGroups.Batch081.numericValid978 MergedCutGroups.Batch081.numericValid979 MergedCutGroups.Batch081.cellsSound978 MergedCutGroups.Batch081.cellsSound979
    MergedCutGroups.Batch081.cellsNumeric978 MergedCutGroups.Batch081.cellsNumeric979 MergedCutGroups.Batch081.populationMatches978 MergedCutGroups.Batch081.populationMatches979
    PopulationCertificates.Batch032.valid652 PopulationCertificates.Batch032.sound652 WitnessCertificates.Batch032.valid652 WitnessCertificates.Batch032.sound652 CountingCertificates.Batch032.valid652 CountingCertificates.Batch032.sound652
    CutLabelCertificates.Entropy016.valid327 CutLabelCertificates.Minority016.valid326 CutLabelCertificates.Minority016.sound326 H st hI
theorem probabilityBound326 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch081.certificate978).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate652).dm (WitnessCertificates.Batch032.certificate652).beta) ≤ ((CutFailureCertificates.Budget032.certificate652).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound652 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate652).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch081.certificate978).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch081.certificate979).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch032.certificate652).omega:ℝ) ≤ ((CutFailureCertificates.Budget032.certificate652).bound:ℝ) at hb
  exact (exponentialBound326 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches327 : (MergedCutGroups.Batch081.certificate981).GlobalMatches MergedCutGroups.Batch081.certificate982 CountingCertificates.Batch032.certificate654 CutLabelCertificates.Entropy016.certificate328 CutLabelCertificates.Minority016.certificate327 := by decide +kernel
theorem exponentialBound327 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch081.certificate981).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate654).dm (WitnessCertificates.Batch032.certificate654).beta) ≤ (2*exp (-((CountingCertificates.Batch032.certificate654).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch081.certificate981).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch081.certificate982).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch032.certificate654).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch081.certificate981 MergedCutGroups.Batch081.certificate982 CountingCertificates.Batch032.certificate654 CutLabelCertificates.Entropy016.certificate328 CutLabelCertificates.Minority016.certificate327 matches327 rfl rfl
    MergedCutGroups.Batch081.numericValid981 MergedCutGroups.Batch081.numericValid982 MergedCutGroups.Batch081.cellsSound981 MergedCutGroups.Batch081.cellsSound982
    MergedCutGroups.Batch081.cellsNumeric981 MergedCutGroups.Batch081.cellsNumeric982 MergedCutGroups.Batch081.populationMatches981 MergedCutGroups.Batch081.populationMatches982
    PopulationCertificates.Batch032.valid654 PopulationCertificates.Batch032.sound654 WitnessCertificates.Batch032.valid654 WitnessCertificates.Batch032.sound654 CountingCertificates.Batch032.valid654 CountingCertificates.Batch032.sound654
    CutLabelCertificates.Entropy016.valid328 CutLabelCertificates.Minority016.valid327 CutLabelCertificates.Minority016.sound327 H st hI
theorem probabilityBound327 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch081.certificate981).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate654).dm (WitnessCertificates.Batch032.certificate654).beta) ≤ ((CutFailureCertificates.Budget032.certificate654).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound654 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate654).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch081.certificate981).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch081.certificate982).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch032.certificate654).omega:ℝ) ≤ ((CutFailureCertificates.Budget032.certificate654).bound:ℝ) at hb
  exact (exponentialBound327 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches328 : (MergedCutGroups.Batch082.certificate984).GlobalMatches MergedCutGroups.Batch082.certificate985 CountingCertificates.Batch032.certificate656 CutLabelCertificates.Entropy016.certificate329 CutLabelCertificates.Minority016.certificate328 := by decide +kernel
theorem exponentialBound328 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch082.certificate984).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate656).dm (WitnessCertificates.Batch032.certificate656).beta) ≤ (2*exp (-((CountingCertificates.Batch032.certificate656).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch082.certificate984).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch082.certificate985).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch032.certificate656).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch082.certificate984 MergedCutGroups.Batch082.certificate985 CountingCertificates.Batch032.certificate656 CutLabelCertificates.Entropy016.certificate329 CutLabelCertificates.Minority016.certificate328 matches328 rfl rfl
    MergedCutGroups.Batch082.numericValid984 MergedCutGroups.Batch082.numericValid985 MergedCutGroups.Batch082.cellsSound984 MergedCutGroups.Batch082.cellsSound985
    MergedCutGroups.Batch082.cellsNumeric984 MergedCutGroups.Batch082.cellsNumeric985 MergedCutGroups.Batch082.populationMatches984 MergedCutGroups.Batch082.populationMatches985
    PopulationCertificates.Batch032.valid656 PopulationCertificates.Batch032.sound656 WitnessCertificates.Batch032.valid656 WitnessCertificates.Batch032.sound656 CountingCertificates.Batch032.valid656 CountingCertificates.Batch032.sound656
    CutLabelCertificates.Entropy016.valid329 CutLabelCertificates.Minority016.valid328 CutLabelCertificates.Minority016.sound328 H st hI
theorem probabilityBound328 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch082.certificate984).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate656).dm (WitnessCertificates.Batch032.certificate656).beta) ≤ ((CutFailureCertificates.Budget032.certificate656).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound656 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate656).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch082.certificate984).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch082.certificate985).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch032.certificate656).omega:ℝ) ≤ ((CutFailureCertificates.Budget032.certificate656).bound:ℝ) at hb
  exact (exponentialBound328 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches329 : (MergedCutGroups.Batch082.certificate987).GlobalMatches MergedCutGroups.Batch082.certificate988 CountingCertificates.Batch032.certificate658 CutLabelCertificates.Entropy016.certificate330 CutLabelCertificates.Minority016.certificate329 := by decide +kernel
theorem exponentialBound329 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch082.certificate987).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate658).dm (WitnessCertificates.Batch032.certificate658).beta) ≤ (2*exp (-((CountingCertificates.Batch032.certificate658).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch082.certificate987).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch082.certificate988).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch032.certificate658).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch082.certificate987 MergedCutGroups.Batch082.certificate988 CountingCertificates.Batch032.certificate658 CutLabelCertificates.Entropy016.certificate330 CutLabelCertificates.Minority016.certificate329 matches329 rfl rfl
    MergedCutGroups.Batch082.numericValid987 MergedCutGroups.Batch082.numericValid988 MergedCutGroups.Batch082.cellsSound987 MergedCutGroups.Batch082.cellsSound988
    MergedCutGroups.Batch082.cellsNumeric987 MergedCutGroups.Batch082.cellsNumeric988 MergedCutGroups.Batch082.populationMatches987 MergedCutGroups.Batch082.populationMatches988
    PopulationCertificates.Batch032.valid658 PopulationCertificates.Batch032.sound658 WitnessCertificates.Batch032.valid658 WitnessCertificates.Batch032.sound658 CountingCertificates.Batch032.valid658 CountingCertificates.Batch032.sound658
    CutLabelCertificates.Entropy016.valid330 CutLabelCertificates.Minority016.valid329 CutLabelCertificates.Minority016.sound329 H st hI
theorem probabilityBound329 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch082.certificate987).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch032.certificate658).dm (WitnessCertificates.Batch032.certificate658).beta) ≤ ((CutFailureCertificates.Budget032.certificate658).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget032.sound658 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch032.certificate658).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch082.certificate987).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch082.certificate988).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch032.certificate658).omega:ℝ) ≤ ((CutFailureCertificates.Budget032.certificate658).bound:ℝ) at hb
  exact (exponentialBound329 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches330 : (MergedCutGroups.Batch082.certificate990).GlobalMatches MergedCutGroups.Batch082.certificate991 CountingCertificates.Batch033.certificate660 CutLabelCertificates.Entropy016.certificate331 CutLabelCertificates.Minority016.certificate330 := by decide +kernel
theorem exponentialBound330 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch082.certificate990).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate660).dm (WitnessCertificates.Batch033.certificate660).beta) ≤ (2*exp (-((CountingCertificates.Batch033.certificate660).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch082.certificate990).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch082.certificate991).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch033.certificate660).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch082.certificate990 MergedCutGroups.Batch082.certificate991 CountingCertificates.Batch033.certificate660 CutLabelCertificates.Entropy016.certificate331 CutLabelCertificates.Minority016.certificate330 matches330 rfl rfl
    MergedCutGroups.Batch082.numericValid990 MergedCutGroups.Batch082.numericValid991 MergedCutGroups.Batch082.cellsSound990 MergedCutGroups.Batch082.cellsSound991
    MergedCutGroups.Batch082.cellsNumeric990 MergedCutGroups.Batch082.cellsNumeric991 MergedCutGroups.Batch082.populationMatches990 MergedCutGroups.Batch082.populationMatches991
    PopulationCertificates.Batch033.valid660 PopulationCertificates.Batch033.sound660 WitnessCertificates.Batch033.valid660 WitnessCertificates.Batch033.sound660 CountingCertificates.Batch033.valid660 CountingCertificates.Batch033.sound660
    CutLabelCertificates.Entropy016.valid331 CutLabelCertificates.Minority016.valid330 CutLabelCertificates.Minority016.sound330 H st hI
theorem probabilityBound330 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch082.certificate990).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate660).dm (WitnessCertificates.Batch033.certificate660).beta) ≤ ((CutFailureCertificates.Budget033.certificate660).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound660 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate660).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch082.certificate990).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch082.certificate991).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch033.certificate660).omega:ℝ) ≤ ((CutFailureCertificates.Budget033.certificate660).bound:ℝ) at hb
  exact (exponentialBound330 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches331 : (MergedCutGroups.Batch082.certificate993).GlobalMatches MergedCutGroups.Batch082.certificate994 CountingCertificates.Batch033.certificate662 CutLabelCertificates.Entropy016.certificate332 CutLabelCertificates.Minority016.certificate331 := by decide +kernel
theorem exponentialBound331 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch082.certificate993).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate662).dm (WitnessCertificates.Batch033.certificate662).beta) ≤ (2*exp (-((CountingCertificates.Batch033.certificate662).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch082.certificate993).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch082.certificate994).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch033.certificate662).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch082.certificate993 MergedCutGroups.Batch082.certificate994 CountingCertificates.Batch033.certificate662 CutLabelCertificates.Entropy016.certificate332 CutLabelCertificates.Minority016.certificate331 matches331 rfl rfl
    MergedCutGroups.Batch082.numericValid993 MergedCutGroups.Batch082.numericValid994 MergedCutGroups.Batch082.cellsSound993 MergedCutGroups.Batch082.cellsSound994
    MergedCutGroups.Batch082.cellsNumeric993 MergedCutGroups.Batch082.cellsNumeric994 MergedCutGroups.Batch082.populationMatches993 MergedCutGroups.Batch082.populationMatches994
    PopulationCertificates.Batch033.valid662 PopulationCertificates.Batch033.sound662 WitnessCertificates.Batch033.valid662 WitnessCertificates.Batch033.sound662 CountingCertificates.Batch033.valid662 CountingCertificates.Batch033.sound662
    CutLabelCertificates.Entropy016.valid332 CutLabelCertificates.Minority016.valid331 CutLabelCertificates.Minority016.sound331 H st hI
theorem probabilityBound331 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch082.certificate993).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate662).dm (WitnessCertificates.Batch033.certificate662).beta) ≤ ((CutFailureCertificates.Budget033.certificate662).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound662 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate662).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch082.certificate993).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch082.certificate994).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch033.certificate662).omega:ℝ) ≤ ((CutFailureCertificates.Budget033.certificate662).bound:ℝ) at hb
  exact (exponentialBound331 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches332 : (MergedCutGroups.Batch083.certificate996).GlobalMatches MergedCutGroups.Batch083.certificate997 CountingCertificates.Batch033.certificate664 CutLabelCertificates.Entropy016.certificate333 CutLabelCertificates.Minority016.certificate332 := by decide +kernel
theorem exponentialBound332 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch083.certificate996).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate664).dm (WitnessCertificates.Batch033.certificate664).beta) ≤ (2*exp (-((CountingCertificates.Batch033.certificate664).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch083.certificate996).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch083.certificate997).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch033.certificate664).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch083.certificate996 MergedCutGroups.Batch083.certificate997 CountingCertificates.Batch033.certificate664 CutLabelCertificates.Entropy016.certificate333 CutLabelCertificates.Minority016.certificate332 matches332 rfl rfl
    MergedCutGroups.Batch083.numericValid996 MergedCutGroups.Batch083.numericValid997 MergedCutGroups.Batch083.cellsSound996 MergedCutGroups.Batch083.cellsSound997
    MergedCutGroups.Batch083.cellsNumeric996 MergedCutGroups.Batch083.cellsNumeric997 MergedCutGroups.Batch083.populationMatches996 MergedCutGroups.Batch083.populationMatches997
    PopulationCertificates.Batch033.valid664 PopulationCertificates.Batch033.sound664 WitnessCertificates.Batch033.valid664 WitnessCertificates.Batch033.sound664 CountingCertificates.Batch033.valid664 CountingCertificates.Batch033.sound664
    CutLabelCertificates.Entropy016.valid333 CutLabelCertificates.Minority016.valid332 CutLabelCertificates.Minority016.sound332 H st hI
theorem probabilityBound332 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch083.certificate996).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate664).dm (WitnessCertificates.Batch033.certificate664).beta) ≤ ((CutFailureCertificates.Budget033.certificate664).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound664 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate664).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch083.certificate996).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch083.certificate997).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch033.certificate664).omega:ℝ) ≤ ((CutFailureCertificates.Budget033.certificate664).bound:ℝ) at hb
  exact (exponentialBound332 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches333 : (MergedCutGroups.Batch083.certificate999).GlobalMatches MergedCutGroups.Batch083.certificate1000 CountingCertificates.Batch033.certificate666 CutLabelCertificates.Entropy016.certificate334 CutLabelCertificates.Minority016.certificate333 := by decide +kernel
theorem exponentialBound333 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch083.certificate999).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate666).dm (WitnessCertificates.Batch033.certificate666).beta) ≤ (2*exp (-((CountingCertificates.Batch033.certificate666).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch083.certificate999).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch083.certificate1000).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch033.certificate666).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch083.certificate999 MergedCutGroups.Batch083.certificate1000 CountingCertificates.Batch033.certificate666 CutLabelCertificates.Entropy016.certificate334 CutLabelCertificates.Minority016.certificate333 matches333 rfl rfl
    MergedCutGroups.Batch083.numericValid999 MergedCutGroups.Batch083.numericValid1000 MergedCutGroups.Batch083.cellsSound999 MergedCutGroups.Batch083.cellsSound1000
    MergedCutGroups.Batch083.cellsNumeric999 MergedCutGroups.Batch083.cellsNumeric1000 MergedCutGroups.Batch083.populationMatches999 MergedCutGroups.Batch083.populationMatches1000
    PopulationCertificates.Batch033.valid666 PopulationCertificates.Batch033.sound666 WitnessCertificates.Batch033.valid666 WitnessCertificates.Batch033.sound666 CountingCertificates.Batch033.valid666 CountingCertificates.Batch033.sound666
    CutLabelCertificates.Entropy016.valid334 CutLabelCertificates.Minority016.valid333 CutLabelCertificates.Minority016.sound333 H st hI
theorem probabilityBound333 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch083.certificate999).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate666).dm (WitnessCertificates.Batch033.certificate666).beta) ≤ ((CutFailureCertificates.Budget033.certificate666).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound666 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate666).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch083.certificate999).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch083.certificate1000).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch033.certificate666).omega:ℝ) ≤ ((CutFailureCertificates.Budget033.certificate666).bound:ℝ) at hb
  exact (exponentialBound333 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches334 : (MergedCutGroups.Batch083.certificate1002).GlobalMatches MergedCutGroups.Batch083.certificate1003 CountingCertificates.Batch033.certificate668 CutLabelCertificates.Entropy016.certificate335 CutLabelCertificates.Minority016.certificate334 := by decide +kernel
theorem exponentialBound334 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch083.certificate1002).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate668).dm (WitnessCertificates.Batch033.certificate668).beta) ≤ (2*exp (-((CountingCertificates.Batch033.certificate668).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch083.certificate1002).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch083.certificate1003).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch033.certificate668).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch083.certificate1002 MergedCutGroups.Batch083.certificate1003 CountingCertificates.Batch033.certificate668 CutLabelCertificates.Entropy016.certificate335 CutLabelCertificates.Minority016.certificate334 matches334 rfl rfl
    MergedCutGroups.Batch083.numericValid1002 MergedCutGroups.Batch083.numericValid1003 MergedCutGroups.Batch083.cellsSound1002 MergedCutGroups.Batch083.cellsSound1003
    MergedCutGroups.Batch083.cellsNumeric1002 MergedCutGroups.Batch083.cellsNumeric1003 MergedCutGroups.Batch083.populationMatches1002 MergedCutGroups.Batch083.populationMatches1003
    PopulationCertificates.Batch033.valid668 PopulationCertificates.Batch033.sound668 WitnessCertificates.Batch033.valid668 WitnessCertificates.Batch033.sound668 CountingCertificates.Batch033.valid668 CountingCertificates.Batch033.sound668
    CutLabelCertificates.Entropy016.valid335 CutLabelCertificates.Minority016.valid334 CutLabelCertificates.Minority016.sound334 H st hI
theorem probabilityBound334 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch083.certificate1002).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate668).dm (WitnessCertificates.Batch033.certificate668).beta) ≤ ((CutFailureCertificates.Budget033.certificate668).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound668 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate668).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch083.certificate1002).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch083.certificate1003).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch033.certificate668).omega:ℝ) ≤ ((CutFailureCertificates.Budget033.certificate668).bound:ℝ) at hb
  exact (exponentialBound334 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches335 : (MergedCutGroups.Batch083.certificate1005).GlobalMatches MergedCutGroups.Batch083.certificate1006 CountingCertificates.Batch033.certificate670 CutLabelCertificates.Entropy016.certificate336 CutLabelCertificates.Minority016.certificate335 := by decide +kernel
theorem exponentialBound335 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch083.certificate1005).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate670).dm (WitnessCertificates.Batch033.certificate670).beta) ≤ (2*exp (-((CountingCertificates.Batch033.certificate670).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch083.certificate1005).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch083.certificate1006).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch033.certificate670).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch083.certificate1005 MergedCutGroups.Batch083.certificate1006 CountingCertificates.Batch033.certificate670 CutLabelCertificates.Entropy016.certificate336 CutLabelCertificates.Minority016.certificate335 matches335 rfl rfl
    MergedCutGroups.Batch083.numericValid1005 MergedCutGroups.Batch083.numericValid1006 MergedCutGroups.Batch083.cellsSound1005 MergedCutGroups.Batch083.cellsSound1006
    MergedCutGroups.Batch083.cellsNumeric1005 MergedCutGroups.Batch083.cellsNumeric1006 MergedCutGroups.Batch083.populationMatches1005 MergedCutGroups.Batch083.populationMatches1006
    PopulationCertificates.Batch033.valid670 PopulationCertificates.Batch033.sound670 WitnessCertificates.Batch033.valid670 WitnessCertificates.Batch033.sound670 CountingCertificates.Batch033.valid670 CountingCertificates.Batch033.sound670
    CutLabelCertificates.Entropy016.valid336 CutLabelCertificates.Minority016.valid335 CutLabelCertificates.Minority016.sound335 H st hI
theorem probabilityBound335 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch083.certificate1005).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate670).dm (WitnessCertificates.Batch033.certificate670).beta) ≤ ((CutFailureCertificates.Budget033.certificate670).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound670 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate670).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch083.certificate1005).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch083.certificate1006).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch033.certificate670).omega:ℝ) ≤ ((CutFailureCertificates.Budget033.certificate670).bound:ℝ) at hb
  exact (exponentialBound335 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches336 : (MergedCutGroups.Batch084.certificate1008).GlobalMatches MergedCutGroups.Batch084.certificate1009 CountingCertificates.Batch033.certificate672 CutLabelCertificates.Entropy016.certificate337 CutLabelCertificates.Minority016.certificate336 := by decide +kernel
theorem exponentialBound336 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch084.certificate1008).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate672).dm (WitnessCertificates.Batch033.certificate672).beta) ≤ (2*exp (-((CountingCertificates.Batch033.certificate672).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch084.certificate1008).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch084.certificate1009).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch033.certificate672).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch084.certificate1008 MergedCutGroups.Batch084.certificate1009 CountingCertificates.Batch033.certificate672 CutLabelCertificates.Entropy016.certificate337 CutLabelCertificates.Minority016.certificate336 matches336 rfl rfl
    MergedCutGroups.Batch084.numericValid1008 MergedCutGroups.Batch084.numericValid1009 MergedCutGroups.Batch084.cellsSound1008 MergedCutGroups.Batch084.cellsSound1009
    MergedCutGroups.Batch084.cellsNumeric1008 MergedCutGroups.Batch084.cellsNumeric1009 MergedCutGroups.Batch084.populationMatches1008 MergedCutGroups.Batch084.populationMatches1009
    PopulationCertificates.Batch033.valid672 PopulationCertificates.Batch033.sound672 WitnessCertificates.Batch033.valid672 WitnessCertificates.Batch033.sound672 CountingCertificates.Batch033.valid672 CountingCertificates.Batch033.sound672
    CutLabelCertificates.Entropy016.valid337 CutLabelCertificates.Minority016.valid336 CutLabelCertificates.Minority016.sound336 H st hI
theorem probabilityBound336 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch084.certificate1008).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate672).dm (WitnessCertificates.Batch033.certificate672).beta) ≤ ((CutFailureCertificates.Budget033.certificate672).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound672 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate672).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch084.certificate1008).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch084.certificate1009).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch033.certificate672).omega:ℝ) ≤ ((CutFailureCertificates.Budget033.certificate672).bound:ℝ) at hb
  exact (exponentialBound336 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches337 : (MergedCutGroups.Batch084.certificate1011).GlobalMatches MergedCutGroups.Batch084.certificate1012 CountingCertificates.Batch033.certificate674 CutLabelCertificates.Entropy016.certificate338 CutLabelCertificates.Minority016.certificate337 := by decide +kernel
theorem exponentialBound337 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch084.certificate1011).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate674).dm (WitnessCertificates.Batch033.certificate674).beta) ≤ (2*exp (-((CountingCertificates.Batch033.certificate674).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch084.certificate1011).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch084.certificate1012).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch033.certificate674).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch084.certificate1011 MergedCutGroups.Batch084.certificate1012 CountingCertificates.Batch033.certificate674 CutLabelCertificates.Entropy016.certificate338 CutLabelCertificates.Minority016.certificate337 matches337 rfl rfl
    MergedCutGroups.Batch084.numericValid1011 MergedCutGroups.Batch084.numericValid1012 MergedCutGroups.Batch084.cellsSound1011 MergedCutGroups.Batch084.cellsSound1012
    MergedCutGroups.Batch084.cellsNumeric1011 MergedCutGroups.Batch084.cellsNumeric1012 MergedCutGroups.Batch084.populationMatches1011 MergedCutGroups.Batch084.populationMatches1012
    PopulationCertificates.Batch033.valid674 PopulationCertificates.Batch033.sound674 WitnessCertificates.Batch033.valid674 WitnessCertificates.Batch033.sound674 CountingCertificates.Batch033.valid674 CountingCertificates.Batch033.sound674
    CutLabelCertificates.Entropy016.valid338 CutLabelCertificates.Minority016.valid337 CutLabelCertificates.Minority016.sound337 H st hI
theorem probabilityBound337 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch084.certificate1011).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate674).dm (WitnessCertificates.Batch033.certificate674).beta) ≤ ((CutFailureCertificates.Budget033.certificate674).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound674 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate674).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch084.certificate1011).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch084.certificate1012).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch033.certificate674).omega:ℝ) ≤ ((CutFailureCertificates.Budget033.certificate674).bound:ℝ) at hb
  exact (exponentialBound337 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches338 : (MergedCutGroups.Batch084.certificate1014).GlobalMatches MergedCutGroups.Batch084.certificate1015 CountingCertificates.Batch033.certificate676 CutLabelCertificates.Entropy016.certificate339 CutLabelCertificates.Minority016.certificate338 := by decide +kernel
theorem exponentialBound338 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch084.certificate1014).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate676).dm (WitnessCertificates.Batch033.certificate676).beta) ≤ (2*exp (-((CountingCertificates.Batch033.certificate676).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch084.certificate1014).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch084.certificate1015).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch033.certificate676).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch084.certificate1014 MergedCutGroups.Batch084.certificate1015 CountingCertificates.Batch033.certificate676 CutLabelCertificates.Entropy016.certificate339 CutLabelCertificates.Minority016.certificate338 matches338 rfl rfl
    MergedCutGroups.Batch084.numericValid1014 MergedCutGroups.Batch084.numericValid1015 MergedCutGroups.Batch084.cellsSound1014 MergedCutGroups.Batch084.cellsSound1015
    MergedCutGroups.Batch084.cellsNumeric1014 MergedCutGroups.Batch084.cellsNumeric1015 MergedCutGroups.Batch084.populationMatches1014 MergedCutGroups.Batch084.populationMatches1015
    PopulationCertificates.Batch033.valid676 PopulationCertificates.Batch033.sound676 WitnessCertificates.Batch033.valid676 WitnessCertificates.Batch033.sound676 CountingCertificates.Batch033.valid676 CountingCertificates.Batch033.sound676
    CutLabelCertificates.Entropy016.valid339 CutLabelCertificates.Minority016.valid338 CutLabelCertificates.Minority016.sound338 H st hI
theorem probabilityBound338 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch084.certificate1014).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate676).dm (WitnessCertificates.Batch033.certificate676).beta) ≤ ((CutFailureCertificates.Budget033.certificate676).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound676 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate676).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch084.certificate1014).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch084.certificate1015).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch033.certificate676).omega:ℝ) ≤ ((CutFailureCertificates.Budget033.certificate676).bound:ℝ) at hb
  exact (exponentialBound338 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches339 : (MergedCutGroups.Batch084.certificate1017).GlobalMatches MergedCutGroups.Batch084.certificate1018 CountingCertificates.Batch033.certificate678 CutLabelCertificates.Entropy017.certificate340 CutLabelCertificates.Minority016.certificate339 := by decide +kernel
theorem exponentialBound339 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch084.certificate1017).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate678).dm (WitnessCertificates.Batch033.certificate678).beta) ≤ (2*exp (-((CountingCertificates.Batch033.certificate678).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch084.certificate1017).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch084.certificate1018).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch033.certificate678).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch084.certificate1017 MergedCutGroups.Batch084.certificate1018 CountingCertificates.Batch033.certificate678 CutLabelCertificates.Entropy017.certificate340 CutLabelCertificates.Minority016.certificate339 matches339 rfl rfl
    MergedCutGroups.Batch084.numericValid1017 MergedCutGroups.Batch084.numericValid1018 MergedCutGroups.Batch084.cellsSound1017 MergedCutGroups.Batch084.cellsSound1018
    MergedCutGroups.Batch084.cellsNumeric1017 MergedCutGroups.Batch084.cellsNumeric1018 MergedCutGroups.Batch084.populationMatches1017 MergedCutGroups.Batch084.populationMatches1018
    PopulationCertificates.Batch033.valid678 PopulationCertificates.Batch033.sound678 WitnessCertificates.Batch033.valid678 WitnessCertificates.Batch033.sound678 CountingCertificates.Batch033.valid678 CountingCertificates.Batch033.sound678
    CutLabelCertificates.Entropy017.valid340 CutLabelCertificates.Minority016.valid339 CutLabelCertificates.Minority016.sound339 H st hI
theorem probabilityBound339 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch084.certificate1017).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch033.certificate678).dm (WitnessCertificates.Batch033.certificate678).beta) ≤ ((CutFailureCertificates.Budget033.certificate678).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget033.sound678 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch033.certificate678).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch084.certificate1017).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch084.certificate1018).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch033.certificate678).omega:ℝ) ≤ ((CutFailureCertificates.Budget033.certificate678).bound:ℝ) at hb
  exact (exponentialBound339 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch016
