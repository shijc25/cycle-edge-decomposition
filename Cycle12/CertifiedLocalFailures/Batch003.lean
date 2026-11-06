import Cycle12.CertifiedLocalFailure
import Cycle12.CountingCertificates.Batch050
import Cycle12.CountingCertificates.Batch051
import Cycle12.CountingCertificates.Batch052
import Cycle12.CountingCertificates.Batch053
import Cycle12.CutFailureCertificates.Budget050
import Cycle12.CutFailureCertificates.Budget051
import Cycle12.CutFailureCertificates.Budget052
import Cycle12.CutFailureCertificates.Budget053
import Cycle12.CutFailureCertificates.Reverse003
import Cycle12.CutLabelCertificates.Minority035
import Cycle12.CutLabelCertificates.Minority036
import Cycle12.CutLabelCertificates.Minority037
import Cycle12.CutLabelCertificates.Minority038
import Cycle12.CutLabelCertificates.Minority039
import Cycle12.CutLabelCertificates.Minority040
import Cycle12.CutLabelCertificates.Minority041
import Cycle12.MergedCutGroups.Batch124
import Cycle12.MergedCutGroups.Batch125
import Cycle12.MergedCutGroups.Batch126
import Cycle12.MergedCutGroups.Batch127
import Cycle12.MergedCutGroups.Batch128
import Cycle12.MergedCutGroups.Batch129
import Cycle12.MergedCutGroups.Batch130
import Cycle12.PopulationCertificates.Batch050
import Cycle12.PopulationCertificates.Batch051
import Cycle12.PopulationCertificates.Batch052
import Cycle12.PopulationCertificates.Batch053
import Cycle12.WitnessCertificates.Batch050
import Cycle12.WitnessCertificates.Batch051
import Cycle12.WitnessCertificates.Batch052
import Cycle12.WitnessCertificates.Batch053

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedLocalFailures.Batch003
open Finset SimpleGraph Cycle13 Real

def budgets60 : Fin (MergedCutGroups.Batch124.certificate1488).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority035.certificate715,CutLabelCertificates.Minority035.certificate716,CutLabelCertificates.Minority035.certificate717,CutLabelCertificates.Minority035.certificate718,CutLabelCertificates.Minority035.certificate719]
theorem matches60 : (MergedCutGroups.Batch124.certificate1488).LocalMatches CountingCertificates.Batch050.certificate1012 budgets60 := by decide +kernel
theorem budgetsSound60 : ∀ l, (budgets60 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority035.sound715
  · exact CutLabelCertificates.Minority035.sound716
  · exact CutLabelCertificates.Minority035.sound717
  · exact CutLabelCertificates.Minority035.sound718
  · exact CutLabelCertificates.Minority035.sound719
theorem multiplicity60 : (MergedCutGroups.Batch124.certificate1488).cells.length ≤ 454 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound60 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch124.certificate1488).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1012).dm (WitnessCertificates.Batch050.certificate1012).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1012).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate60).exponent:ℝ)*st.R)+((MergedCutGroups.Batch124.certificate1488).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch124.certificate1488).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch050.certificate1012).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch124.certificate1488 CountingCertificates.Batch050.certificate1012 budgets60 CutFailureCertificates.Reverse003.certificate60 matches60 rfl rfl
    MergedCutGroups.Batch124.numericValid1488 MergedCutGroups.Batch124.cellsSound1488 MergedCutGroups.Batch124.cellsEntropyValid1488 MergedCutGroups.Batch124.populationMatches1488
    PopulationCertificates.Batch050.valid1012 PopulationCertificates.Batch050.sound1012 WitnessCertificates.Batch050.valid1012 WitnessCertificates.Batch050.sound1012 CountingCertificates.Batch050.valid1012 CountingCertificates.Batch050.sound1012
    budgetsSound60 CutFailureCertificates.Reverse003.sound60 H st hI
theorem probabilityBound60 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch124.certificate1488).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1012).dm (WitnessCertificates.Batch050.certificate1012).beta (1/125)) ≤ ((CutFailureCertificates.Budget050.certificate1012).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1012 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1012).aa:ℝ)*st.R)+(((908:ℚ):ℝ)*exp (-((MergedCutGroups.Batch124.certificate1488).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate60).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch050.certificate1012).omega:ℝ) ≤ ((CutFailureCertificates.Budget050.certificate1012).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch124.certificate1488).cells.length:ℝ) ≤ (454:ℝ) := by exact_mod_cast multiplicity60
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch124.certificate1488).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound60 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch050.certificate1012).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate60).exponent:ℝ)*st.R)+((MergedCutGroups.Batch124.certificate1488).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch124.certificate1488).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch050.certificate1012).aa:ℝ)*st.R)+((908:ℝ)*exp (-((MergedCutGroups.Batch124.certificate1488).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate60).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch050.sound1012.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets61 : Fin (MergedCutGroups.Batch124.certificate1492).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority036.certificate721,CutLabelCertificates.Minority036.certificate722,CutLabelCertificates.Minority036.certificate723,CutLabelCertificates.Minority036.certificate724,CutLabelCertificates.Minority036.certificate725]
theorem matches61 : (MergedCutGroups.Batch124.certificate1492).LocalMatches CountingCertificates.Batch050.certificate1015 budgets61 := by decide +kernel
theorem budgetsSound61 : ∀ l, (budgets61 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority036.sound721
  · exact CutLabelCertificates.Minority036.sound722
  · exact CutLabelCertificates.Minority036.sound723
  · exact CutLabelCertificates.Minority036.sound724
  · exact CutLabelCertificates.Minority036.sound725
theorem multiplicity61 : (MergedCutGroups.Batch124.certificate1492).cells.length ≤ 453 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound61 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch124.certificate1492).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1015).dm (WitnessCertificates.Batch050.certificate1015).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1015).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate61).exponent:ℝ)*st.R)+((MergedCutGroups.Batch124.certificate1492).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch124.certificate1492).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch050.certificate1015).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch124.certificate1492 CountingCertificates.Batch050.certificate1015 budgets61 CutFailureCertificates.Reverse003.certificate61 matches61 rfl rfl
    MergedCutGroups.Batch124.numericValid1492 MergedCutGroups.Batch124.cellsSound1492 MergedCutGroups.Batch124.cellsEntropyValid1492 MergedCutGroups.Batch124.populationMatches1492
    PopulationCertificates.Batch050.valid1015 PopulationCertificates.Batch050.sound1015 WitnessCertificates.Batch050.valid1015 WitnessCertificates.Batch050.sound1015 CountingCertificates.Batch050.valid1015 CountingCertificates.Batch050.sound1015
    budgetsSound61 CutFailureCertificates.Reverse003.sound61 H st hI
theorem probabilityBound61 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch124.certificate1492).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1015).dm (WitnessCertificates.Batch050.certificate1015).beta (1/125)) ≤ ((CutFailureCertificates.Budget050.certificate1015).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1015 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1015).aa:ℝ)*st.R)+(((906:ℚ):ℝ)*exp (-((MergedCutGroups.Batch124.certificate1492).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate61).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch050.certificate1015).omega:ℝ) ≤ ((CutFailureCertificates.Budget050.certificate1015).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch124.certificate1492).cells.length:ℝ) ≤ (453:ℝ) := by exact_mod_cast multiplicity61
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch124.certificate1492).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound61 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch050.certificate1015).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate61).exponent:ℝ)*st.R)+((MergedCutGroups.Batch124.certificate1492).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch124.certificate1492).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch050.certificate1015).aa:ℝ)*st.R)+((906:ℝ)*exp (-((MergedCutGroups.Batch124.certificate1492).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate61).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch050.sound1015.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets62 : Fin (MergedCutGroups.Batch124.certificate1496).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority036.certificate727,CutLabelCertificates.Minority036.certificate728,CutLabelCertificates.Minority036.certificate729,CutLabelCertificates.Minority036.certificate730,CutLabelCertificates.Minority036.certificate731]
theorem matches62 : (MergedCutGroups.Batch124.certificate1496).LocalMatches CountingCertificates.Batch050.certificate1018 budgets62 := by decide +kernel
theorem budgetsSound62 : ∀ l, (budgets62 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority036.sound727
  · exact CutLabelCertificates.Minority036.sound728
  · exact CutLabelCertificates.Minority036.sound729
  · exact CutLabelCertificates.Minority036.sound730
  · exact CutLabelCertificates.Minority036.sound731
theorem multiplicity62 : (MergedCutGroups.Batch124.certificate1496).cells.length ≤ 453 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound62 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch124.certificate1496).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1018).dm (WitnessCertificates.Batch050.certificate1018).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1018).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate62).exponent:ℝ)*st.R)+((MergedCutGroups.Batch124.certificate1496).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch124.certificate1496).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch050.certificate1018).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch124.certificate1496 CountingCertificates.Batch050.certificate1018 budgets62 CutFailureCertificates.Reverse003.certificate62 matches62 rfl rfl
    MergedCutGroups.Batch124.numericValid1496 MergedCutGroups.Batch124.cellsSound1496 MergedCutGroups.Batch124.cellsEntropyValid1496 MergedCutGroups.Batch124.populationMatches1496
    PopulationCertificates.Batch050.valid1018 PopulationCertificates.Batch050.sound1018 WitnessCertificates.Batch050.valid1018 WitnessCertificates.Batch050.sound1018 CountingCertificates.Batch050.valid1018 CountingCertificates.Batch050.sound1018
    budgetsSound62 CutFailureCertificates.Reverse003.sound62 H st hI
theorem probabilityBound62 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch124.certificate1496).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1018).dm (WitnessCertificates.Batch050.certificate1018).beta (1/125)) ≤ ((CutFailureCertificates.Budget050.certificate1018).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1018 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1018).aa:ℝ)*st.R)+(((906:ℚ):ℝ)*exp (-((MergedCutGroups.Batch124.certificate1496).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate62).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch050.certificate1018).omega:ℝ) ≤ ((CutFailureCertificates.Budget050.certificate1018).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch124.certificate1496).cells.length:ℝ) ≤ (453:ℝ) := by exact_mod_cast multiplicity62
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch124.certificate1496).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound62 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch050.certificate1018).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate62).exponent:ℝ)*st.R)+((MergedCutGroups.Batch124.certificate1496).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch124.certificate1496).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch050.certificate1018).aa:ℝ)*st.R)+((906:ℝ)*exp (-((MergedCutGroups.Batch124.certificate1496).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate62).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch050.sound1018.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets63 : Fin (MergedCutGroups.Batch125.certificate1500).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority036.certificate733,CutLabelCertificates.Minority036.certificate734,CutLabelCertificates.Minority036.certificate735,CutLabelCertificates.Minority036.certificate736,CutLabelCertificates.Minority036.certificate737]
theorem matches63 : (MergedCutGroups.Batch125.certificate1500).LocalMatches CountingCertificates.Batch051.certificate1021 budgets63 := by decide +kernel
theorem budgetsSound63 : ∀ l, (budgets63 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority036.sound733
  · exact CutLabelCertificates.Minority036.sound734
  · exact CutLabelCertificates.Minority036.sound735
  · exact CutLabelCertificates.Minority036.sound736
  · exact CutLabelCertificates.Minority036.sound737
theorem multiplicity63 : (MergedCutGroups.Batch125.certificate1500).cells.length ≤ 452 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound63 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch125.certificate1500).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1021).dm (WitnessCertificates.Batch051.certificate1021).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1021).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate63).exponent:ℝ)*st.R)+((MergedCutGroups.Batch125.certificate1500).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch125.certificate1500).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch051.certificate1021).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch125.certificate1500 CountingCertificates.Batch051.certificate1021 budgets63 CutFailureCertificates.Reverse003.certificate63 matches63 rfl rfl
    MergedCutGroups.Batch125.numericValid1500 MergedCutGroups.Batch125.cellsSound1500 MergedCutGroups.Batch125.cellsEntropyValid1500 MergedCutGroups.Batch125.populationMatches1500
    PopulationCertificates.Batch051.valid1021 PopulationCertificates.Batch051.sound1021 WitnessCertificates.Batch051.valid1021 WitnessCertificates.Batch051.sound1021 CountingCertificates.Batch051.valid1021 CountingCertificates.Batch051.sound1021
    budgetsSound63 CutFailureCertificates.Reverse003.sound63 H st hI
theorem probabilityBound63 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch125.certificate1500).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1021).dm (WitnessCertificates.Batch051.certificate1021).beta (1/125)) ≤ ((CutFailureCertificates.Budget051.certificate1021).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1021 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1021).aa:ℝ)*st.R)+(((904:ℚ):ℝ)*exp (-((MergedCutGroups.Batch125.certificate1500).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate63).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch051.certificate1021).omega:ℝ) ≤ ((CutFailureCertificates.Budget051.certificate1021).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch125.certificate1500).cells.length:ℝ) ≤ (452:ℝ) := by exact_mod_cast multiplicity63
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch125.certificate1500).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound63 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch051.certificate1021).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate63).exponent:ℝ)*st.R)+((MergedCutGroups.Batch125.certificate1500).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch125.certificate1500).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch051.certificate1021).aa:ℝ)*st.R)+((904:ℝ)*exp (-((MergedCutGroups.Batch125.certificate1500).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate63).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch051.sound1021.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets64 : Fin (MergedCutGroups.Batch125.certificate1504).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority036.certificate739,CutLabelCertificates.Minority037.certificate740,CutLabelCertificates.Minority037.certificate741,CutLabelCertificates.Minority037.certificate742,CutLabelCertificates.Minority037.certificate743]
theorem matches64 : (MergedCutGroups.Batch125.certificate1504).LocalMatches CountingCertificates.Batch051.certificate1024 budgets64 := by decide +kernel
theorem budgetsSound64 : ∀ l, (budgets64 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority036.sound739
  · exact CutLabelCertificates.Minority037.sound740
  · exact CutLabelCertificates.Minority037.sound741
  · exact CutLabelCertificates.Minority037.sound742
  · exact CutLabelCertificates.Minority037.sound743
theorem multiplicity64 : (MergedCutGroups.Batch125.certificate1504).cells.length ≤ 451 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound64 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch125.certificate1504).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1024).dm (WitnessCertificates.Batch051.certificate1024).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1024).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate64).exponent:ℝ)*st.R)+((MergedCutGroups.Batch125.certificate1504).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch125.certificate1504).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch051.certificate1024).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch125.certificate1504 CountingCertificates.Batch051.certificate1024 budgets64 CutFailureCertificates.Reverse003.certificate64 matches64 rfl rfl
    MergedCutGroups.Batch125.numericValid1504 MergedCutGroups.Batch125.cellsSound1504 MergedCutGroups.Batch125.cellsEntropyValid1504 MergedCutGroups.Batch125.populationMatches1504
    PopulationCertificates.Batch051.valid1024 PopulationCertificates.Batch051.sound1024 WitnessCertificates.Batch051.valid1024 WitnessCertificates.Batch051.sound1024 CountingCertificates.Batch051.valid1024 CountingCertificates.Batch051.sound1024
    budgetsSound64 CutFailureCertificates.Reverse003.sound64 H st hI
theorem probabilityBound64 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch125.certificate1504).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1024).dm (WitnessCertificates.Batch051.certificate1024).beta (1/125)) ≤ ((CutFailureCertificates.Budget051.certificate1024).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1024 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1024).aa:ℝ)*st.R)+(((902:ℚ):ℝ)*exp (-((MergedCutGroups.Batch125.certificate1504).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate64).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch051.certificate1024).omega:ℝ) ≤ ((CutFailureCertificates.Budget051.certificate1024).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch125.certificate1504).cells.length:ℝ) ≤ (451:ℝ) := by exact_mod_cast multiplicity64
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch125.certificate1504).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound64 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch051.certificate1024).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate64).exponent:ℝ)*st.R)+((MergedCutGroups.Batch125.certificate1504).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch125.certificate1504).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch051.certificate1024).aa:ℝ)*st.R)+((902:ℝ)*exp (-((MergedCutGroups.Batch125.certificate1504).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate64).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch051.sound1024.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets65 : Fin (MergedCutGroups.Batch125.certificate1508).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority037.certificate745,CutLabelCertificates.Minority037.certificate746,CutLabelCertificates.Minority037.certificate747,CutLabelCertificates.Minority037.certificate748,CutLabelCertificates.Minority037.certificate749]
theorem matches65 : (MergedCutGroups.Batch125.certificate1508).LocalMatches CountingCertificates.Batch051.certificate1027 budgets65 := by decide +kernel
theorem budgetsSound65 : ∀ l, (budgets65 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority037.sound745
  · exact CutLabelCertificates.Minority037.sound746
  · exact CutLabelCertificates.Minority037.sound747
  · exact CutLabelCertificates.Minority037.sound748
  · exact CutLabelCertificates.Minority037.sound749
theorem multiplicity65 : (MergedCutGroups.Batch125.certificate1508).cells.length ≤ 451 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound65 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch125.certificate1508).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1027).dm (WitnessCertificates.Batch051.certificate1027).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1027).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate65).exponent:ℝ)*st.R)+((MergedCutGroups.Batch125.certificate1508).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch125.certificate1508).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch051.certificate1027).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch125.certificate1508 CountingCertificates.Batch051.certificate1027 budgets65 CutFailureCertificates.Reverse003.certificate65 matches65 rfl rfl
    MergedCutGroups.Batch125.numericValid1508 MergedCutGroups.Batch125.cellsSound1508 MergedCutGroups.Batch125.cellsEntropyValid1508 MergedCutGroups.Batch125.populationMatches1508
    PopulationCertificates.Batch051.valid1027 PopulationCertificates.Batch051.sound1027 WitnessCertificates.Batch051.valid1027 WitnessCertificates.Batch051.sound1027 CountingCertificates.Batch051.valid1027 CountingCertificates.Batch051.sound1027
    budgetsSound65 CutFailureCertificates.Reverse003.sound65 H st hI
theorem probabilityBound65 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch125.certificate1508).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1027).dm (WitnessCertificates.Batch051.certificate1027).beta (1/125)) ≤ ((CutFailureCertificates.Budget051.certificate1027).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1027 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1027).aa:ℝ)*st.R)+(((902:ℚ):ℝ)*exp (-((MergedCutGroups.Batch125.certificate1508).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate65).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch051.certificate1027).omega:ℝ) ≤ ((CutFailureCertificates.Budget051.certificate1027).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch125.certificate1508).cells.length:ℝ) ≤ (451:ℝ) := by exact_mod_cast multiplicity65
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch125.certificate1508).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound65 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch051.certificate1027).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate65).exponent:ℝ)*st.R)+((MergedCutGroups.Batch125.certificate1508).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch125.certificate1508).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch051.certificate1027).aa:ℝ)*st.R)+((902:ℝ)*exp (-((MergedCutGroups.Batch125.certificate1508).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate65).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch051.sound1027.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets66 : Fin (MergedCutGroups.Batch126.certificate1512).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority037.certificate751,CutLabelCertificates.Minority037.certificate752,CutLabelCertificates.Minority037.certificate753,CutLabelCertificates.Minority037.certificate754,CutLabelCertificates.Minority037.certificate755]
theorem matches66 : (MergedCutGroups.Batch126.certificate1512).LocalMatches CountingCertificates.Batch051.certificate1030 budgets66 := by decide +kernel
theorem budgetsSound66 : ∀ l, (budgets66 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority037.sound751
  · exact CutLabelCertificates.Minority037.sound752
  · exact CutLabelCertificates.Minority037.sound753
  · exact CutLabelCertificates.Minority037.sound754
  · exact CutLabelCertificates.Minority037.sound755
theorem multiplicity66 : (MergedCutGroups.Batch126.certificate1512).cells.length ≤ 450 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound66 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch126.certificate1512).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1030).dm (WitnessCertificates.Batch051.certificate1030).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1030).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate66).exponent:ℝ)*st.R)+((MergedCutGroups.Batch126.certificate1512).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch126.certificate1512).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch051.certificate1030).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch126.certificate1512 CountingCertificates.Batch051.certificate1030 budgets66 CutFailureCertificates.Reverse003.certificate66 matches66 rfl rfl
    MergedCutGroups.Batch126.numericValid1512 MergedCutGroups.Batch126.cellsSound1512 MergedCutGroups.Batch126.cellsEntropyValid1512 MergedCutGroups.Batch126.populationMatches1512
    PopulationCertificates.Batch051.valid1030 PopulationCertificates.Batch051.sound1030 WitnessCertificates.Batch051.valid1030 WitnessCertificates.Batch051.sound1030 CountingCertificates.Batch051.valid1030 CountingCertificates.Batch051.sound1030
    budgetsSound66 CutFailureCertificates.Reverse003.sound66 H st hI
theorem probabilityBound66 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch126.certificate1512).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1030).dm (WitnessCertificates.Batch051.certificate1030).beta (1/125)) ≤ ((CutFailureCertificates.Budget051.certificate1030).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1030 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1030).aa:ℝ)*st.R)+(((900:ℚ):ℝ)*exp (-((MergedCutGroups.Batch126.certificate1512).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate66).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch051.certificate1030).omega:ℝ) ≤ ((CutFailureCertificates.Budget051.certificate1030).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch126.certificate1512).cells.length:ℝ) ≤ (450:ℝ) := by exact_mod_cast multiplicity66
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch126.certificate1512).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound66 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch051.certificate1030).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate66).exponent:ℝ)*st.R)+((MergedCutGroups.Batch126.certificate1512).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch126.certificate1512).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch051.certificate1030).aa:ℝ)*st.R)+((900:ℝ)*exp (-((MergedCutGroups.Batch126.certificate1512).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate66).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch051.sound1030.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets67 : Fin (MergedCutGroups.Batch126.certificate1516).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority037.certificate757,CutLabelCertificates.Minority037.certificate758,CutLabelCertificates.Minority037.certificate759,CutLabelCertificates.Minority038.certificate760,CutLabelCertificates.Minority038.certificate761]
theorem matches67 : (MergedCutGroups.Batch126.certificate1516).LocalMatches CountingCertificates.Batch051.certificate1033 budgets67 := by decide +kernel
theorem budgetsSound67 : ∀ l, (budgets67 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority037.sound757
  · exact CutLabelCertificates.Minority037.sound758
  · exact CutLabelCertificates.Minority037.sound759
  · exact CutLabelCertificates.Minority038.sound760
  · exact CutLabelCertificates.Minority038.sound761
theorem multiplicity67 : (MergedCutGroups.Batch126.certificate1516).cells.length ≤ 450 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound67 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch126.certificate1516).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1033).dm (WitnessCertificates.Batch051.certificate1033).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1033).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate67).exponent:ℝ)*st.R)+((MergedCutGroups.Batch126.certificate1516).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch126.certificate1516).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch051.certificate1033).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch126.certificate1516 CountingCertificates.Batch051.certificate1033 budgets67 CutFailureCertificates.Reverse003.certificate67 matches67 rfl rfl
    MergedCutGroups.Batch126.numericValid1516 MergedCutGroups.Batch126.cellsSound1516 MergedCutGroups.Batch126.cellsEntropyValid1516 MergedCutGroups.Batch126.populationMatches1516
    PopulationCertificates.Batch051.valid1033 PopulationCertificates.Batch051.sound1033 WitnessCertificates.Batch051.valid1033 WitnessCertificates.Batch051.sound1033 CountingCertificates.Batch051.valid1033 CountingCertificates.Batch051.sound1033
    budgetsSound67 CutFailureCertificates.Reverse003.sound67 H st hI
theorem probabilityBound67 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch126.certificate1516).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1033).dm (WitnessCertificates.Batch051.certificate1033).beta (1/125)) ≤ ((CutFailureCertificates.Budget051.certificate1033).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1033 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1033).aa:ℝ)*st.R)+(((900:ℚ):ℝ)*exp (-((MergedCutGroups.Batch126.certificate1516).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate67).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch051.certificate1033).omega:ℝ) ≤ ((CutFailureCertificates.Budget051.certificate1033).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch126.certificate1516).cells.length:ℝ) ≤ (450:ℝ) := by exact_mod_cast multiplicity67
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch126.certificate1516).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound67 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch051.certificate1033).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate67).exponent:ℝ)*st.R)+((MergedCutGroups.Batch126.certificate1516).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch126.certificate1516).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch051.certificate1033).aa:ℝ)*st.R)+((900:ℝ)*exp (-((MergedCutGroups.Batch126.certificate1516).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate67).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch051.sound1033.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets68 : Fin (MergedCutGroups.Batch126.certificate1520).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority038.certificate763,CutLabelCertificates.Minority038.certificate764,CutLabelCertificates.Minority038.certificate765,CutLabelCertificates.Minority038.certificate766,CutLabelCertificates.Minority038.certificate767]
theorem matches68 : (MergedCutGroups.Batch126.certificate1520).LocalMatches CountingCertificates.Batch051.certificate1036 budgets68 := by decide +kernel
theorem budgetsSound68 : ∀ l, (budgets68 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority038.sound763
  · exact CutLabelCertificates.Minority038.sound764
  · exact CutLabelCertificates.Minority038.sound765
  · exact CutLabelCertificates.Minority038.sound766
  · exact CutLabelCertificates.Minority038.sound767
theorem multiplicity68 : (MergedCutGroups.Batch126.certificate1520).cells.length ≤ 449 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound68 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch126.certificate1520).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1036).dm (WitnessCertificates.Batch051.certificate1036).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1036).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate68).exponent:ℝ)*st.R)+((MergedCutGroups.Batch126.certificate1520).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch126.certificate1520).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch051.certificate1036).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch126.certificate1520 CountingCertificates.Batch051.certificate1036 budgets68 CutFailureCertificates.Reverse003.certificate68 matches68 rfl rfl
    MergedCutGroups.Batch126.numericValid1520 MergedCutGroups.Batch126.cellsSound1520 MergedCutGroups.Batch126.cellsEntropyValid1520 MergedCutGroups.Batch126.populationMatches1520
    PopulationCertificates.Batch051.valid1036 PopulationCertificates.Batch051.sound1036 WitnessCertificates.Batch051.valid1036 WitnessCertificates.Batch051.sound1036 CountingCertificates.Batch051.valid1036 CountingCertificates.Batch051.sound1036
    budgetsSound68 CutFailureCertificates.Reverse003.sound68 H st hI
theorem probabilityBound68 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch126.certificate1520).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1036).dm (WitnessCertificates.Batch051.certificate1036).beta (1/125)) ≤ ((CutFailureCertificates.Budget051.certificate1036).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1036 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1036).aa:ℝ)*st.R)+(((898:ℚ):ℝ)*exp (-((MergedCutGroups.Batch126.certificate1520).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate68).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch051.certificate1036).omega:ℝ) ≤ ((CutFailureCertificates.Budget051.certificate1036).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch126.certificate1520).cells.length:ℝ) ≤ (449:ℝ) := by exact_mod_cast multiplicity68
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch126.certificate1520).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound68 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch051.certificate1036).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate68).exponent:ℝ)*st.R)+((MergedCutGroups.Batch126.certificate1520).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch126.certificate1520).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch051.certificate1036).aa:ℝ)*st.R)+((898:ℝ)*exp (-((MergedCutGroups.Batch126.certificate1520).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate68).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch051.sound1036.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets69 : Fin (MergedCutGroups.Batch127.certificate1524).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority038.certificate769,CutLabelCertificates.Minority038.certificate770,CutLabelCertificates.Minority038.certificate771,CutLabelCertificates.Minority038.certificate772,CutLabelCertificates.Minority038.certificate773]
theorem matches69 : (MergedCutGroups.Batch127.certificate1524).LocalMatches CountingCertificates.Batch051.certificate1039 budgets69 := by decide +kernel
theorem budgetsSound69 : ∀ l, (budgets69 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority038.sound769
  · exact CutLabelCertificates.Minority038.sound770
  · exact CutLabelCertificates.Minority038.sound771
  · exact CutLabelCertificates.Minority038.sound772
  · exact CutLabelCertificates.Minority038.sound773
theorem multiplicity69 : (MergedCutGroups.Batch127.certificate1524).cells.length ≤ 449 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound69 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch127.certificate1524).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1039).dm (WitnessCertificates.Batch051.certificate1039).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1039).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate69).exponent:ℝ)*st.R)+((MergedCutGroups.Batch127.certificate1524).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch127.certificate1524).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch051.certificate1039).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch127.certificate1524 CountingCertificates.Batch051.certificate1039 budgets69 CutFailureCertificates.Reverse003.certificate69 matches69 rfl rfl
    MergedCutGroups.Batch127.numericValid1524 MergedCutGroups.Batch127.cellsSound1524 MergedCutGroups.Batch127.cellsEntropyValid1524 MergedCutGroups.Batch127.populationMatches1524
    PopulationCertificates.Batch051.valid1039 PopulationCertificates.Batch051.sound1039 WitnessCertificates.Batch051.valid1039 WitnessCertificates.Batch051.sound1039 CountingCertificates.Batch051.valid1039 CountingCertificates.Batch051.sound1039
    budgetsSound69 CutFailureCertificates.Reverse003.sound69 H st hI
theorem probabilityBound69 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch127.certificate1524).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1039).dm (WitnessCertificates.Batch051.certificate1039).beta (1/125)) ≤ ((CutFailureCertificates.Budget051.certificate1039).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1039 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1039).aa:ℝ)*st.R)+(((898:ℚ):ℝ)*exp (-((MergedCutGroups.Batch127.certificate1524).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate69).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch051.certificate1039).omega:ℝ) ≤ ((CutFailureCertificates.Budget051.certificate1039).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch127.certificate1524).cells.length:ℝ) ≤ (449:ℝ) := by exact_mod_cast multiplicity69
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch127.certificate1524).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound69 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch051.certificate1039).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate69).exponent:ℝ)*st.R)+((MergedCutGroups.Batch127.certificate1524).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch127.certificate1524).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch051.certificate1039).aa:ℝ)*st.R)+((898:ℝ)*exp (-((MergedCutGroups.Batch127.certificate1524).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate69).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch051.sound1039.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets70 : Fin (MergedCutGroups.Batch127.certificate1528).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority038.certificate775,CutLabelCertificates.Minority038.certificate776,CutLabelCertificates.Minority038.certificate777,CutLabelCertificates.Minority038.certificate778,CutLabelCertificates.Minority038.certificate779]
theorem matches70 : (MergedCutGroups.Batch127.certificate1528).LocalMatches CountingCertificates.Batch052.certificate1042 budgets70 := by decide +kernel
theorem budgetsSound70 : ∀ l, (budgets70 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority038.sound775
  · exact CutLabelCertificates.Minority038.sound776
  · exact CutLabelCertificates.Minority038.sound777
  · exact CutLabelCertificates.Minority038.sound778
  · exact CutLabelCertificates.Minority038.sound779
theorem multiplicity70 : (MergedCutGroups.Batch127.certificate1528).cells.length ≤ 448 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound70 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch127.certificate1528).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1042).dm (WitnessCertificates.Batch052.certificate1042).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1042).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate70).exponent:ℝ)*st.R)+((MergedCutGroups.Batch127.certificate1528).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch127.certificate1528).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch052.certificate1042).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch127.certificate1528 CountingCertificates.Batch052.certificate1042 budgets70 CutFailureCertificates.Reverse003.certificate70 matches70 rfl rfl
    MergedCutGroups.Batch127.numericValid1528 MergedCutGroups.Batch127.cellsSound1528 MergedCutGroups.Batch127.cellsEntropyValid1528 MergedCutGroups.Batch127.populationMatches1528
    PopulationCertificates.Batch052.valid1042 PopulationCertificates.Batch052.sound1042 WitnessCertificates.Batch052.valid1042 WitnessCertificates.Batch052.sound1042 CountingCertificates.Batch052.valid1042 CountingCertificates.Batch052.sound1042
    budgetsSound70 CutFailureCertificates.Reverse003.sound70 H st hI
theorem probabilityBound70 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch127.certificate1528).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1042).dm (WitnessCertificates.Batch052.certificate1042).beta (1/125)) ≤ ((CutFailureCertificates.Budget052.certificate1042).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1042 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1042).aa:ℝ)*st.R)+(((896:ℚ):ℝ)*exp (-((MergedCutGroups.Batch127.certificate1528).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate70).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch052.certificate1042).omega:ℝ) ≤ ((CutFailureCertificates.Budget052.certificate1042).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch127.certificate1528).cells.length:ℝ) ≤ (448:ℝ) := by exact_mod_cast multiplicity70
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch127.certificate1528).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound70 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch052.certificate1042).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate70).exponent:ℝ)*st.R)+((MergedCutGroups.Batch127.certificate1528).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch127.certificate1528).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch052.certificate1042).aa:ℝ)*st.R)+((896:ℝ)*exp (-((MergedCutGroups.Batch127.certificate1528).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate70).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch052.sound1042.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets71 : Fin (MergedCutGroups.Batch127.certificate1532).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority039.certificate781,CutLabelCertificates.Minority039.certificate782,CutLabelCertificates.Minority039.certificate783,CutLabelCertificates.Minority039.certificate784,CutLabelCertificates.Minority039.certificate785]
theorem matches71 : (MergedCutGroups.Batch127.certificate1532).LocalMatches CountingCertificates.Batch052.certificate1045 budgets71 := by decide +kernel
theorem budgetsSound71 : ∀ l, (budgets71 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority039.sound781
  · exact CutLabelCertificates.Minority039.sound782
  · exact CutLabelCertificates.Minority039.sound783
  · exact CutLabelCertificates.Minority039.sound784
  · exact CutLabelCertificates.Minority039.sound785
theorem multiplicity71 : (MergedCutGroups.Batch127.certificate1532).cells.length ≤ 448 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound71 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch127.certificate1532).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1045).dm (WitnessCertificates.Batch052.certificate1045).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1045).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate71).exponent:ℝ)*st.R)+((MergedCutGroups.Batch127.certificate1532).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch127.certificate1532).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch052.certificate1045).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch127.certificate1532 CountingCertificates.Batch052.certificate1045 budgets71 CutFailureCertificates.Reverse003.certificate71 matches71 rfl rfl
    MergedCutGroups.Batch127.numericValid1532 MergedCutGroups.Batch127.cellsSound1532 MergedCutGroups.Batch127.cellsEntropyValid1532 MergedCutGroups.Batch127.populationMatches1532
    PopulationCertificates.Batch052.valid1045 PopulationCertificates.Batch052.sound1045 WitnessCertificates.Batch052.valid1045 WitnessCertificates.Batch052.sound1045 CountingCertificates.Batch052.valid1045 CountingCertificates.Batch052.sound1045
    budgetsSound71 CutFailureCertificates.Reverse003.sound71 H st hI
theorem probabilityBound71 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch127.certificate1532).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1045).dm (WitnessCertificates.Batch052.certificate1045).beta (1/125)) ≤ ((CutFailureCertificates.Budget052.certificate1045).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1045 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1045).aa:ℝ)*st.R)+(((896:ℚ):ℝ)*exp (-((MergedCutGroups.Batch127.certificate1532).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate71).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch052.certificate1045).omega:ℝ) ≤ ((CutFailureCertificates.Budget052.certificate1045).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch127.certificate1532).cells.length:ℝ) ≤ (448:ℝ) := by exact_mod_cast multiplicity71
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch127.certificate1532).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound71 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch052.certificate1045).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate71).exponent:ℝ)*st.R)+((MergedCutGroups.Batch127.certificate1532).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch127.certificate1532).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch052.certificate1045).aa:ℝ)*st.R)+((896:ℝ)*exp (-((MergedCutGroups.Batch127.certificate1532).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate71).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch052.sound1045.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets72 : Fin (MergedCutGroups.Batch128.certificate1536).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority039.certificate787,CutLabelCertificates.Minority039.certificate788,CutLabelCertificates.Minority039.certificate789,CutLabelCertificates.Minority039.certificate790,CutLabelCertificates.Minority039.certificate791]
theorem matches72 : (MergedCutGroups.Batch128.certificate1536).LocalMatches CountingCertificates.Batch052.certificate1048 budgets72 := by decide +kernel
theorem budgetsSound72 : ∀ l, (budgets72 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority039.sound787
  · exact CutLabelCertificates.Minority039.sound788
  · exact CutLabelCertificates.Minority039.sound789
  · exact CutLabelCertificates.Minority039.sound790
  · exact CutLabelCertificates.Minority039.sound791
theorem multiplicity72 : (MergedCutGroups.Batch128.certificate1536).cells.length ≤ 447 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound72 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch128.certificate1536).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1048).dm (WitnessCertificates.Batch052.certificate1048).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1048).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate72).exponent:ℝ)*st.R)+((MergedCutGroups.Batch128.certificate1536).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch128.certificate1536).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch052.certificate1048).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch128.certificate1536 CountingCertificates.Batch052.certificate1048 budgets72 CutFailureCertificates.Reverse003.certificate72 matches72 rfl rfl
    MergedCutGroups.Batch128.numericValid1536 MergedCutGroups.Batch128.cellsSound1536 MergedCutGroups.Batch128.cellsEntropyValid1536 MergedCutGroups.Batch128.populationMatches1536
    PopulationCertificates.Batch052.valid1048 PopulationCertificates.Batch052.sound1048 WitnessCertificates.Batch052.valid1048 WitnessCertificates.Batch052.sound1048 CountingCertificates.Batch052.valid1048 CountingCertificates.Batch052.sound1048
    budgetsSound72 CutFailureCertificates.Reverse003.sound72 H st hI
theorem probabilityBound72 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch128.certificate1536).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1048).dm (WitnessCertificates.Batch052.certificate1048).beta (1/125)) ≤ ((CutFailureCertificates.Budget052.certificate1048).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1048 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1048).aa:ℝ)*st.R)+(((894:ℚ):ℝ)*exp (-((MergedCutGroups.Batch128.certificate1536).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate72).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch052.certificate1048).omega:ℝ) ≤ ((CutFailureCertificates.Budget052.certificate1048).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch128.certificate1536).cells.length:ℝ) ≤ (447:ℝ) := by exact_mod_cast multiplicity72
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch128.certificate1536).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound72 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch052.certificate1048).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate72).exponent:ℝ)*st.R)+((MergedCutGroups.Batch128.certificate1536).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch128.certificate1536).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch052.certificate1048).aa:ℝ)*st.R)+((894:ℝ)*exp (-((MergedCutGroups.Batch128.certificate1536).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate72).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch052.sound1048.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets73 : Fin (MergedCutGroups.Batch128.certificate1540).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority039.certificate793,CutLabelCertificates.Minority039.certificate794,CutLabelCertificates.Minority039.certificate795,CutLabelCertificates.Minority039.certificate796,CutLabelCertificates.Minority039.certificate797]
theorem matches73 : (MergedCutGroups.Batch128.certificate1540).LocalMatches CountingCertificates.Batch052.certificate1051 budgets73 := by decide +kernel
theorem budgetsSound73 : ∀ l, (budgets73 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority039.sound793
  · exact CutLabelCertificates.Minority039.sound794
  · exact CutLabelCertificates.Minority039.sound795
  · exact CutLabelCertificates.Minority039.sound796
  · exact CutLabelCertificates.Minority039.sound797
theorem multiplicity73 : (MergedCutGroups.Batch128.certificate1540).cells.length ≤ 446 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound73 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch128.certificate1540).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1051).dm (WitnessCertificates.Batch052.certificate1051).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1051).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate73).exponent:ℝ)*st.R)+((MergedCutGroups.Batch128.certificate1540).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch128.certificate1540).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch052.certificate1051).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch128.certificate1540 CountingCertificates.Batch052.certificate1051 budgets73 CutFailureCertificates.Reverse003.certificate73 matches73 rfl rfl
    MergedCutGroups.Batch128.numericValid1540 MergedCutGroups.Batch128.cellsSound1540 MergedCutGroups.Batch128.cellsEntropyValid1540 MergedCutGroups.Batch128.populationMatches1540
    PopulationCertificates.Batch052.valid1051 PopulationCertificates.Batch052.sound1051 WitnessCertificates.Batch052.valid1051 WitnessCertificates.Batch052.sound1051 CountingCertificates.Batch052.valid1051 CountingCertificates.Batch052.sound1051
    budgetsSound73 CutFailureCertificates.Reverse003.sound73 H st hI
theorem probabilityBound73 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch128.certificate1540).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1051).dm (WitnessCertificates.Batch052.certificate1051).beta (1/125)) ≤ ((CutFailureCertificates.Budget052.certificate1051).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1051 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1051).aa:ℝ)*st.R)+(((892:ℚ):ℝ)*exp (-((MergedCutGroups.Batch128.certificate1540).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate73).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch052.certificate1051).omega:ℝ) ≤ ((CutFailureCertificates.Budget052.certificate1051).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch128.certificate1540).cells.length:ℝ) ≤ (446:ℝ) := by exact_mod_cast multiplicity73
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch128.certificate1540).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound73 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch052.certificate1051).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate73).exponent:ℝ)*st.R)+((MergedCutGroups.Batch128.certificate1540).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch128.certificate1540).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch052.certificate1051).aa:ℝ)*st.R)+((892:ℝ)*exp (-((MergedCutGroups.Batch128.certificate1540).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate73).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch052.sound1051.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets74 : Fin (MergedCutGroups.Batch128.certificate1544).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority039.certificate799,CutLabelCertificates.Minority040.certificate800,CutLabelCertificates.Minority040.certificate801,CutLabelCertificates.Minority040.certificate802,CutLabelCertificates.Minority040.certificate803]
theorem matches74 : (MergedCutGroups.Batch128.certificate1544).LocalMatches CountingCertificates.Batch052.certificate1054 budgets74 := by decide +kernel
theorem budgetsSound74 : ∀ l, (budgets74 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority039.sound799
  · exact CutLabelCertificates.Minority040.sound800
  · exact CutLabelCertificates.Minority040.sound801
  · exact CutLabelCertificates.Minority040.sound802
  · exact CutLabelCertificates.Minority040.sound803
theorem multiplicity74 : (MergedCutGroups.Batch128.certificate1544).cells.length ≤ 446 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound74 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch128.certificate1544).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1054).dm (WitnessCertificates.Batch052.certificate1054).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1054).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate74).exponent:ℝ)*st.R)+((MergedCutGroups.Batch128.certificate1544).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch128.certificate1544).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch052.certificate1054).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch128.certificate1544 CountingCertificates.Batch052.certificate1054 budgets74 CutFailureCertificates.Reverse003.certificate74 matches74 rfl rfl
    MergedCutGroups.Batch128.numericValid1544 MergedCutGroups.Batch128.cellsSound1544 MergedCutGroups.Batch128.cellsEntropyValid1544 MergedCutGroups.Batch128.populationMatches1544
    PopulationCertificates.Batch052.valid1054 PopulationCertificates.Batch052.sound1054 WitnessCertificates.Batch052.valid1054 WitnessCertificates.Batch052.sound1054 CountingCertificates.Batch052.valid1054 CountingCertificates.Batch052.sound1054
    budgetsSound74 CutFailureCertificates.Reverse003.sound74 H st hI
theorem probabilityBound74 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch128.certificate1544).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1054).dm (WitnessCertificates.Batch052.certificate1054).beta (1/125)) ≤ ((CutFailureCertificates.Budget052.certificate1054).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1054 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1054).aa:ℝ)*st.R)+(((892:ℚ):ℝ)*exp (-((MergedCutGroups.Batch128.certificate1544).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate74).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch052.certificate1054).omega:ℝ) ≤ ((CutFailureCertificates.Budget052.certificate1054).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch128.certificate1544).cells.length:ℝ) ≤ (446:ℝ) := by exact_mod_cast multiplicity74
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch128.certificate1544).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound74 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch052.certificate1054).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate74).exponent:ℝ)*st.R)+((MergedCutGroups.Batch128.certificate1544).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch128.certificate1544).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch052.certificate1054).aa:ℝ)*st.R)+((892:ℝ)*exp (-((MergedCutGroups.Batch128.certificate1544).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate74).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch052.sound1054.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets75 : Fin (MergedCutGroups.Batch129.certificate1548).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority040.certificate805,CutLabelCertificates.Minority040.certificate806,CutLabelCertificates.Minority040.certificate807,CutLabelCertificates.Minority040.certificate808,CutLabelCertificates.Minority040.certificate809]
theorem matches75 : (MergedCutGroups.Batch129.certificate1548).LocalMatches CountingCertificates.Batch052.certificate1057 budgets75 := by decide +kernel
theorem budgetsSound75 : ∀ l, (budgets75 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority040.sound805
  · exact CutLabelCertificates.Minority040.sound806
  · exact CutLabelCertificates.Minority040.sound807
  · exact CutLabelCertificates.Minority040.sound808
  · exact CutLabelCertificates.Minority040.sound809
theorem multiplicity75 : (MergedCutGroups.Batch129.certificate1548).cells.length ≤ 445 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound75 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch129.certificate1548).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1057).dm (WitnessCertificates.Batch052.certificate1057).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1057).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate75).exponent:ℝ)*st.R)+((MergedCutGroups.Batch129.certificate1548).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch129.certificate1548).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch052.certificate1057).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch129.certificate1548 CountingCertificates.Batch052.certificate1057 budgets75 CutFailureCertificates.Reverse003.certificate75 matches75 rfl rfl
    MergedCutGroups.Batch129.numericValid1548 MergedCutGroups.Batch129.cellsSound1548 MergedCutGroups.Batch129.cellsEntropyValid1548 MergedCutGroups.Batch129.populationMatches1548
    PopulationCertificates.Batch052.valid1057 PopulationCertificates.Batch052.sound1057 WitnessCertificates.Batch052.valid1057 WitnessCertificates.Batch052.sound1057 CountingCertificates.Batch052.valid1057 CountingCertificates.Batch052.sound1057
    budgetsSound75 CutFailureCertificates.Reverse003.sound75 H st hI
theorem probabilityBound75 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch129.certificate1548).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1057).dm (WitnessCertificates.Batch052.certificate1057).beta (1/125)) ≤ ((CutFailureCertificates.Budget052.certificate1057).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1057 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1057).aa:ℝ)*st.R)+(((890:ℚ):ℝ)*exp (-((MergedCutGroups.Batch129.certificate1548).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate75).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch052.certificate1057).omega:ℝ) ≤ ((CutFailureCertificates.Budget052.certificate1057).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch129.certificate1548).cells.length:ℝ) ≤ (445:ℝ) := by exact_mod_cast multiplicity75
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch129.certificate1548).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound75 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch052.certificate1057).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate75).exponent:ℝ)*st.R)+((MergedCutGroups.Batch129.certificate1548).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch129.certificate1548).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch052.certificate1057).aa:ℝ)*st.R)+((890:ℝ)*exp (-((MergedCutGroups.Batch129.certificate1548).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate75).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch052.sound1057.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets76 : Fin (MergedCutGroups.Batch129.certificate1552).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority040.certificate811,CutLabelCertificates.Minority040.certificate812,CutLabelCertificates.Minority040.certificate813,CutLabelCertificates.Minority040.certificate814,CutLabelCertificates.Minority040.certificate815]
theorem matches76 : (MergedCutGroups.Batch129.certificate1552).LocalMatches CountingCertificates.Batch053.certificate1060 budgets76 := by decide +kernel
theorem budgetsSound76 : ∀ l, (budgets76 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority040.sound811
  · exact CutLabelCertificates.Minority040.sound812
  · exact CutLabelCertificates.Minority040.sound813
  · exact CutLabelCertificates.Minority040.sound814
  · exact CutLabelCertificates.Minority040.sound815
theorem multiplicity76 : (MergedCutGroups.Batch129.certificate1552).cells.length ≤ 445 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound76 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch129.certificate1552).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch053.certificate1060).dm (WitnessCertificates.Batch053.certificate1060).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch053.certificate1060).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate76).exponent:ℝ)*st.R)+((MergedCutGroups.Batch129.certificate1552).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch129.certificate1552).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch053.certificate1060).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch129.certificate1552 CountingCertificates.Batch053.certificate1060 budgets76 CutFailureCertificates.Reverse003.certificate76 matches76 rfl rfl
    MergedCutGroups.Batch129.numericValid1552 MergedCutGroups.Batch129.cellsSound1552 MergedCutGroups.Batch129.cellsEntropyValid1552 MergedCutGroups.Batch129.populationMatches1552
    PopulationCertificates.Batch053.valid1060 PopulationCertificates.Batch053.sound1060 WitnessCertificates.Batch053.valid1060 WitnessCertificates.Batch053.sound1060 CountingCertificates.Batch053.valid1060 CountingCertificates.Batch053.sound1060
    budgetsSound76 CutFailureCertificates.Reverse003.sound76 H st hI
theorem probabilityBound76 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch129.certificate1552).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch053.certificate1060).dm (WitnessCertificates.Batch053.certificate1060).beta (1/125)) ≤ ((CutFailureCertificates.Budget053.certificate1060).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget053.sound1060 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch053.certificate1060).aa:ℝ)*st.R)+(((890:ℚ):ℝ)*exp (-((MergedCutGroups.Batch129.certificate1552).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate76).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch053.certificate1060).omega:ℝ) ≤ ((CutFailureCertificates.Budget053.certificate1060).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch129.certificate1552).cells.length:ℝ) ≤ (445:ℝ) := by exact_mod_cast multiplicity76
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch129.certificate1552).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound76 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch053.certificate1060).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate76).exponent:ℝ)*st.R)+((MergedCutGroups.Batch129.certificate1552).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch129.certificate1552).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch053.certificate1060).aa:ℝ)*st.R)+((890:ℝ)*exp (-((MergedCutGroups.Batch129.certificate1552).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate76).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch053.sound1060.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets77 : Fin (MergedCutGroups.Batch129.certificate1556).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority040.certificate817,CutLabelCertificates.Minority040.certificate818,CutLabelCertificates.Minority040.certificate819,CutLabelCertificates.Minority041.certificate820,CutLabelCertificates.Minority041.certificate821]
theorem matches77 : (MergedCutGroups.Batch129.certificate1556).LocalMatches CountingCertificates.Batch053.certificate1063 budgets77 := by decide +kernel
theorem budgetsSound77 : ∀ l, (budgets77 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority040.sound817
  · exact CutLabelCertificates.Minority040.sound818
  · exact CutLabelCertificates.Minority040.sound819
  · exact CutLabelCertificates.Minority041.sound820
  · exact CutLabelCertificates.Minority041.sound821
theorem multiplicity77 : (MergedCutGroups.Batch129.certificate1556).cells.length ≤ 444 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound77 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch129.certificate1556).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch053.certificate1063).dm (WitnessCertificates.Batch053.certificate1063).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch053.certificate1063).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate77).exponent:ℝ)*st.R)+((MergedCutGroups.Batch129.certificate1556).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch129.certificate1556).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch053.certificate1063).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch129.certificate1556 CountingCertificates.Batch053.certificate1063 budgets77 CutFailureCertificates.Reverse003.certificate77 matches77 rfl rfl
    MergedCutGroups.Batch129.numericValid1556 MergedCutGroups.Batch129.cellsSound1556 MergedCutGroups.Batch129.cellsEntropyValid1556 MergedCutGroups.Batch129.populationMatches1556
    PopulationCertificates.Batch053.valid1063 PopulationCertificates.Batch053.sound1063 WitnessCertificates.Batch053.valid1063 WitnessCertificates.Batch053.sound1063 CountingCertificates.Batch053.valid1063 CountingCertificates.Batch053.sound1063
    budgetsSound77 CutFailureCertificates.Reverse003.sound77 H st hI
theorem probabilityBound77 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch129.certificate1556).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch053.certificate1063).dm (WitnessCertificates.Batch053.certificate1063).beta (1/125)) ≤ ((CutFailureCertificates.Budget053.certificate1063).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget053.sound1063 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch053.certificate1063).aa:ℝ)*st.R)+(((888:ℚ):ℝ)*exp (-((MergedCutGroups.Batch129.certificate1556).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate77).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch053.certificate1063).omega:ℝ) ≤ ((CutFailureCertificates.Budget053.certificate1063).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch129.certificate1556).cells.length:ℝ) ≤ (444:ℝ) := by exact_mod_cast multiplicity77
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch129.certificate1556).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound77 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch053.certificate1063).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate77).exponent:ℝ)*st.R)+((MergedCutGroups.Batch129.certificate1556).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch129.certificate1556).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch053.certificate1063).aa:ℝ)*st.R)+((888:ℝ)*exp (-((MergedCutGroups.Batch129.certificate1556).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate77).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch053.sound1063.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets78 : Fin (MergedCutGroups.Batch130.certificate1560).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority041.certificate823,CutLabelCertificates.Minority041.certificate824,CutLabelCertificates.Minority041.certificate825,CutLabelCertificates.Minority041.certificate826,CutLabelCertificates.Minority041.certificate827]
theorem matches78 : (MergedCutGroups.Batch130.certificate1560).LocalMatches CountingCertificates.Batch053.certificate1066 budgets78 := by decide +kernel
theorem budgetsSound78 : ∀ l, (budgets78 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority041.sound823
  · exact CutLabelCertificates.Minority041.sound824
  · exact CutLabelCertificates.Minority041.sound825
  · exact CutLabelCertificates.Minority041.sound826
  · exact CutLabelCertificates.Minority041.sound827
theorem multiplicity78 : (MergedCutGroups.Batch130.certificate1560).cells.length ≤ 444 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound78 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch130.certificate1560).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch053.certificate1066).dm (WitnessCertificates.Batch053.certificate1066).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch053.certificate1066).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate78).exponent:ℝ)*st.R)+((MergedCutGroups.Batch130.certificate1560).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch130.certificate1560).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch053.certificate1066).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch130.certificate1560 CountingCertificates.Batch053.certificate1066 budgets78 CutFailureCertificates.Reverse003.certificate78 matches78 rfl rfl
    MergedCutGroups.Batch130.numericValid1560 MergedCutGroups.Batch130.cellsSound1560 MergedCutGroups.Batch130.cellsEntropyValid1560 MergedCutGroups.Batch130.populationMatches1560
    PopulationCertificates.Batch053.valid1066 PopulationCertificates.Batch053.sound1066 WitnessCertificates.Batch053.valid1066 WitnessCertificates.Batch053.sound1066 CountingCertificates.Batch053.valid1066 CountingCertificates.Batch053.sound1066
    budgetsSound78 CutFailureCertificates.Reverse003.sound78 H st hI
theorem probabilityBound78 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch130.certificate1560).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch053.certificate1066).dm (WitnessCertificates.Batch053.certificate1066).beta (1/125)) ≤ ((CutFailureCertificates.Budget053.certificate1066).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget053.sound1066 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch053.certificate1066).aa:ℝ)*st.R)+(((888:ℚ):ℝ)*exp (-((MergedCutGroups.Batch130.certificate1560).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse003.certificate78).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch053.certificate1066).omega:ℝ) ≤ ((CutFailureCertificates.Budget053.certificate1066).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch130.certificate1560).cells.length:ℝ) ≤ (444:ℝ) := by exact_mod_cast multiplicity78
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch130.certificate1560).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound78 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch053.certificate1066).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate78).exponent:ℝ)*st.R)+((MergedCutGroups.Batch130.certificate1560).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch130.certificate1560).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch053.certificate1066).aa:ℝ)*st.R)+((888:ℝ)*exp (-((MergedCutGroups.Batch130.certificate1560).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse003.certificate78).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch053.sound1066.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

end Cycle12.CertifiedLocalFailures.Batch003
