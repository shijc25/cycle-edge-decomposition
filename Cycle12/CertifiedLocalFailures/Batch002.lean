import Cycle12.CertifiedLocalFailure
import Cycle12.CountingCertificates.Batch047
import Cycle12.CountingCertificates.Batch048
import Cycle12.CountingCertificates.Batch049
import Cycle12.CountingCertificates.Batch050
import Cycle12.CutFailureCertificates.Budget047
import Cycle12.CutFailureCertificates.Budget048
import Cycle12.CutFailureCertificates.Budget049
import Cycle12.CutFailureCertificates.Budget050
import Cycle12.CutFailureCertificates.Reverse002
import Cycle12.CutLabelCertificates.Minority030
import Cycle12.CutLabelCertificates.Minority031
import Cycle12.CutLabelCertificates.Minority032
import Cycle12.CutLabelCertificates.Minority033
import Cycle12.CutLabelCertificates.Minority034
import Cycle12.CutLabelCertificates.Minority035
import Cycle12.MergedCutGroups.Batch117
import Cycle12.MergedCutGroups.Batch118
import Cycle12.MergedCutGroups.Batch119
import Cycle12.MergedCutGroups.Batch120
import Cycle12.MergedCutGroups.Batch121
import Cycle12.MergedCutGroups.Batch122
import Cycle12.MergedCutGroups.Batch123
import Cycle12.PopulationCertificates.Batch047
import Cycle12.PopulationCertificates.Batch048
import Cycle12.PopulationCertificates.Batch049
import Cycle12.PopulationCertificates.Batch050
import Cycle12.WitnessCertificates.Batch047
import Cycle12.WitnessCertificates.Batch048
import Cycle12.WitnessCertificates.Batch049
import Cycle12.WitnessCertificates.Batch050

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedLocalFailures.Batch002
open Finset SimpleGraph Cycle13 Real

def budgets40 : Fin (MergedCutGroups.Batch117.certificate1408).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority030.certificate607,CutLabelCertificates.Minority030.certificate608,CutLabelCertificates.Minority030.certificate609,CutLabelCertificates.Minority030.certificate610]
theorem matches40 : (MergedCutGroups.Batch117.certificate1408).LocalMatches CountingCertificates.Batch047.certificate952 budgets40 := by decide +kernel
theorem budgetsSound40 : ∀ l, (budgets40 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority030.sound607
  · exact CutLabelCertificates.Minority030.sound608
  · exact CutLabelCertificates.Minority030.sound609
  · exact CutLabelCertificates.Minority030.sound610
theorem multiplicity40 : (MergedCutGroups.Batch117.certificate1408).cells.length ≤ 457 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound40 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch117.certificate1408).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate952).dm (WitnessCertificates.Batch047.certificate952).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch047.certificate952).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate40).exponent:ℝ)*st.R)+((MergedCutGroups.Batch117.certificate1408).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch117.certificate1408).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch047.certificate952).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch117.certificate1408 CountingCertificates.Batch047.certificate952 budgets40 CutFailureCertificates.Reverse002.certificate40 matches40 rfl rfl
    MergedCutGroups.Batch117.numericValid1408 MergedCutGroups.Batch117.cellsSound1408 MergedCutGroups.Batch117.cellsEntropyValid1408 MergedCutGroups.Batch117.populationMatches1408
    PopulationCertificates.Batch047.valid952 PopulationCertificates.Batch047.sound952 WitnessCertificates.Batch047.valid952 WitnessCertificates.Batch047.sound952 CountingCertificates.Batch047.valid952 CountingCertificates.Batch047.sound952
    budgetsSound40 CutFailureCertificates.Reverse002.sound40 H st hI
theorem probabilityBound40 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch117.certificate1408).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate952).dm (WitnessCertificates.Batch047.certificate952).beta (1/125)) ≤ ((CutFailureCertificates.Budget047.certificate952).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound952 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate952).aa:ℝ)*st.R)+(((914:ℚ):ℝ)*exp (-((MergedCutGroups.Batch117.certificate1408).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate40).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch047.certificate952).omega:ℝ) ≤ ((CutFailureCertificates.Budget047.certificate952).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch117.certificate1408).cells.length:ℝ) ≤ (457:ℝ) := by exact_mod_cast multiplicity40
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch117.certificate1408).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound40 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch047.certificate952).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate40).exponent:ℝ)*st.R)+((MergedCutGroups.Batch117.certificate1408).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch117.certificate1408).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch047.certificate952).aa:ℝ)*st.R)+((914:ℝ)*exp (-((MergedCutGroups.Batch117.certificate1408).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate40).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch047.sound952.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets41 : Fin (MergedCutGroups.Batch117.certificate1412).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority030.certificate612,CutLabelCertificates.Minority030.certificate613,CutLabelCertificates.Minority030.certificate614,CutLabelCertificates.Minority030.certificate615]
theorem matches41 : (MergedCutGroups.Batch117.certificate1412).LocalMatches CountingCertificates.Batch047.certificate955 budgets41 := by decide +kernel
theorem budgetsSound41 : ∀ l, (budgets41 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority030.sound612
  · exact CutLabelCertificates.Minority030.sound613
  · exact CutLabelCertificates.Minority030.sound614
  · exact CutLabelCertificates.Minority030.sound615
theorem multiplicity41 : (MergedCutGroups.Batch117.certificate1412).cells.length ≤ 457 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound41 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch117.certificate1412).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate955).dm (WitnessCertificates.Batch047.certificate955).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch047.certificate955).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate41).exponent:ℝ)*st.R)+((MergedCutGroups.Batch117.certificate1412).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch117.certificate1412).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch047.certificate955).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch117.certificate1412 CountingCertificates.Batch047.certificate955 budgets41 CutFailureCertificates.Reverse002.certificate41 matches41 rfl rfl
    MergedCutGroups.Batch117.numericValid1412 MergedCutGroups.Batch117.cellsSound1412 MergedCutGroups.Batch117.cellsEntropyValid1412 MergedCutGroups.Batch117.populationMatches1412
    PopulationCertificates.Batch047.valid955 PopulationCertificates.Batch047.sound955 WitnessCertificates.Batch047.valid955 WitnessCertificates.Batch047.sound955 CountingCertificates.Batch047.valid955 CountingCertificates.Batch047.sound955
    budgetsSound41 CutFailureCertificates.Reverse002.sound41 H st hI
theorem probabilityBound41 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch117.certificate1412).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate955).dm (WitnessCertificates.Batch047.certificate955).beta (1/125)) ≤ ((CutFailureCertificates.Budget047.certificate955).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound955 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate955).aa:ℝ)*st.R)+(((914:ℚ):ℝ)*exp (-((MergedCutGroups.Batch117.certificate1412).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate41).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch047.certificate955).omega:ℝ) ≤ ((CutFailureCertificates.Budget047.certificate955).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch117.certificate1412).cells.length:ℝ) ≤ (457:ℝ) := by exact_mod_cast multiplicity41
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch117.certificate1412).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound41 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch047.certificate955).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate41).exponent:ℝ)*st.R)+((MergedCutGroups.Batch117.certificate1412).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch117.certificate1412).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch047.certificate955).aa:ℝ)*st.R)+((914:ℝ)*exp (-((MergedCutGroups.Batch117.certificate1412).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate41).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch047.sound955.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets42 : Fin (MergedCutGroups.Batch118.certificate1416).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority030.certificate617,CutLabelCertificates.Minority030.certificate618,CutLabelCertificates.Minority030.certificate619,CutLabelCertificates.Minority031.certificate620]
theorem matches42 : (MergedCutGroups.Batch118.certificate1416).LocalMatches CountingCertificates.Batch047.certificate958 budgets42 := by decide +kernel
theorem budgetsSound42 : ∀ l, (budgets42 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority030.sound617
  · exact CutLabelCertificates.Minority030.sound618
  · exact CutLabelCertificates.Minority030.sound619
  · exact CutLabelCertificates.Minority031.sound620
theorem multiplicity42 : (MergedCutGroups.Batch118.certificate1416).cells.length ≤ 458 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound42 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch118.certificate1416).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate958).dm (WitnessCertificates.Batch047.certificate958).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch047.certificate958).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate42).exponent:ℝ)*st.R)+((MergedCutGroups.Batch118.certificate1416).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch118.certificate1416).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch047.certificate958).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch118.certificate1416 CountingCertificates.Batch047.certificate958 budgets42 CutFailureCertificates.Reverse002.certificate42 matches42 rfl rfl
    MergedCutGroups.Batch118.numericValid1416 MergedCutGroups.Batch118.cellsSound1416 MergedCutGroups.Batch118.cellsEntropyValid1416 MergedCutGroups.Batch118.populationMatches1416
    PopulationCertificates.Batch047.valid958 PopulationCertificates.Batch047.sound958 WitnessCertificates.Batch047.valid958 WitnessCertificates.Batch047.sound958 CountingCertificates.Batch047.valid958 CountingCertificates.Batch047.sound958
    budgetsSound42 CutFailureCertificates.Reverse002.sound42 H st hI
theorem probabilityBound42 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch118.certificate1416).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate958).dm (WitnessCertificates.Batch047.certificate958).beta (1/125)) ≤ ((CutFailureCertificates.Budget047.certificate958).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound958 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate958).aa:ℝ)*st.R)+(((916:ℚ):ℝ)*exp (-((MergedCutGroups.Batch118.certificate1416).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate42).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch047.certificate958).omega:ℝ) ≤ ((CutFailureCertificates.Budget047.certificate958).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch118.certificate1416).cells.length:ℝ) ≤ (458:ℝ) := by exact_mod_cast multiplicity42
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch118.certificate1416).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound42 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch047.certificate958).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate42).exponent:ℝ)*st.R)+((MergedCutGroups.Batch118.certificate1416).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch118.certificate1416).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch047.certificate958).aa:ℝ)*st.R)+((916:ℝ)*exp (-((MergedCutGroups.Batch118.certificate1416).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate42).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch047.sound958.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets43 : Fin (MergedCutGroups.Batch118.certificate1420).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority031.certificate622,CutLabelCertificates.Minority031.certificate623,CutLabelCertificates.Minority031.certificate624,CutLabelCertificates.Minority031.certificate625]
theorem matches43 : (MergedCutGroups.Batch118.certificate1420).LocalMatches CountingCertificates.Batch048.certificate961 budgets43 := by decide +kernel
theorem budgetsSound43 : ∀ l, (budgets43 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority031.sound622
  · exact CutLabelCertificates.Minority031.sound623
  · exact CutLabelCertificates.Minority031.sound624
  · exact CutLabelCertificates.Minority031.sound625
theorem multiplicity43 : (MergedCutGroups.Batch118.certificate1420).cells.length ≤ 458 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound43 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch118.certificate1420).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate961).dm (WitnessCertificates.Batch048.certificate961).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch048.certificate961).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate43).exponent:ℝ)*st.R)+((MergedCutGroups.Batch118.certificate1420).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch118.certificate1420).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch048.certificate961).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch118.certificate1420 CountingCertificates.Batch048.certificate961 budgets43 CutFailureCertificates.Reverse002.certificate43 matches43 rfl rfl
    MergedCutGroups.Batch118.numericValid1420 MergedCutGroups.Batch118.cellsSound1420 MergedCutGroups.Batch118.cellsEntropyValid1420 MergedCutGroups.Batch118.populationMatches1420
    PopulationCertificates.Batch048.valid961 PopulationCertificates.Batch048.sound961 WitnessCertificates.Batch048.valid961 WitnessCertificates.Batch048.sound961 CountingCertificates.Batch048.valid961 CountingCertificates.Batch048.sound961
    budgetsSound43 CutFailureCertificates.Reverse002.sound43 H st hI
theorem probabilityBound43 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch118.certificate1420).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate961).dm (WitnessCertificates.Batch048.certificate961).beta (1/125)) ≤ ((CutFailureCertificates.Budget048.certificate961).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound961 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate961).aa:ℝ)*st.R)+(((916:ℚ):ℝ)*exp (-((MergedCutGroups.Batch118.certificate1420).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate43).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch048.certificate961).omega:ℝ) ≤ ((CutFailureCertificates.Budget048.certificate961).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch118.certificate1420).cells.length:ℝ) ≤ (458:ℝ) := by exact_mod_cast multiplicity43
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch118.certificate1420).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound43 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch048.certificate961).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate43).exponent:ℝ)*st.R)+((MergedCutGroups.Batch118.certificate1420).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch118.certificate1420).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch048.certificate961).aa:ℝ)*st.R)+((916:ℝ)*exp (-((MergedCutGroups.Batch118.certificate1420).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate43).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch048.sound961.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets44 : Fin (MergedCutGroups.Batch118.certificate1424).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority031.certificate627,CutLabelCertificates.Minority031.certificate628,CutLabelCertificates.Minority031.certificate629,CutLabelCertificates.Minority031.certificate630]
theorem matches44 : (MergedCutGroups.Batch118.certificate1424).LocalMatches CountingCertificates.Batch048.certificate964 budgets44 := by decide +kernel
theorem budgetsSound44 : ∀ l, (budgets44 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority031.sound627
  · exact CutLabelCertificates.Minority031.sound628
  · exact CutLabelCertificates.Minority031.sound629
  · exact CutLabelCertificates.Minority031.sound630
theorem multiplicity44 : (MergedCutGroups.Batch118.certificate1424).cells.length ≤ 458 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound44 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch118.certificate1424).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate964).dm (WitnessCertificates.Batch048.certificate964).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch048.certificate964).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate44).exponent:ℝ)*st.R)+((MergedCutGroups.Batch118.certificate1424).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch118.certificate1424).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch048.certificate964).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch118.certificate1424 CountingCertificates.Batch048.certificate964 budgets44 CutFailureCertificates.Reverse002.certificate44 matches44 rfl rfl
    MergedCutGroups.Batch118.numericValid1424 MergedCutGroups.Batch118.cellsSound1424 MergedCutGroups.Batch118.cellsEntropyValid1424 MergedCutGroups.Batch118.populationMatches1424
    PopulationCertificates.Batch048.valid964 PopulationCertificates.Batch048.sound964 WitnessCertificates.Batch048.valid964 WitnessCertificates.Batch048.sound964 CountingCertificates.Batch048.valid964 CountingCertificates.Batch048.sound964
    budgetsSound44 CutFailureCertificates.Reverse002.sound44 H st hI
theorem probabilityBound44 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch118.certificate1424).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate964).dm (WitnessCertificates.Batch048.certificate964).beta (1/125)) ≤ ((CutFailureCertificates.Budget048.certificate964).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound964 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate964).aa:ℝ)*st.R)+(((916:ℚ):ℝ)*exp (-((MergedCutGroups.Batch118.certificate1424).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate44).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch048.certificate964).omega:ℝ) ≤ ((CutFailureCertificates.Budget048.certificate964).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch118.certificate1424).cells.length:ℝ) ≤ (458:ℝ) := by exact_mod_cast multiplicity44
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch118.certificate1424).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound44 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch048.certificate964).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate44).exponent:ℝ)*st.R)+((MergedCutGroups.Batch118.certificate1424).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch118.certificate1424).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch048.certificate964).aa:ℝ)*st.R)+((916:ℝ)*exp (-((MergedCutGroups.Batch118.certificate1424).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate44).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch048.sound964.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets45 : Fin (MergedCutGroups.Batch119.certificate1428).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority031.certificate632,CutLabelCertificates.Minority031.certificate633,CutLabelCertificates.Minority031.certificate634,CutLabelCertificates.Minority031.certificate635]
theorem matches45 : (MergedCutGroups.Batch119.certificate1428).LocalMatches CountingCertificates.Batch048.certificate967 budgets45 := by decide +kernel
theorem budgetsSound45 : ∀ l, (budgets45 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority031.sound632
  · exact CutLabelCertificates.Minority031.sound633
  · exact CutLabelCertificates.Minority031.sound634
  · exact CutLabelCertificates.Minority031.sound635
theorem multiplicity45 : (MergedCutGroups.Batch119.certificate1428).cells.length ≤ 457 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound45 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch119.certificate1428).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate967).dm (WitnessCertificates.Batch048.certificate967).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch048.certificate967).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate45).exponent:ℝ)*st.R)+((MergedCutGroups.Batch119.certificate1428).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch119.certificate1428).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch048.certificate967).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch119.certificate1428 CountingCertificates.Batch048.certificate967 budgets45 CutFailureCertificates.Reverse002.certificate45 matches45 rfl rfl
    MergedCutGroups.Batch119.numericValid1428 MergedCutGroups.Batch119.cellsSound1428 MergedCutGroups.Batch119.cellsEntropyValid1428 MergedCutGroups.Batch119.populationMatches1428
    PopulationCertificates.Batch048.valid967 PopulationCertificates.Batch048.sound967 WitnessCertificates.Batch048.valid967 WitnessCertificates.Batch048.sound967 CountingCertificates.Batch048.valid967 CountingCertificates.Batch048.sound967
    budgetsSound45 CutFailureCertificates.Reverse002.sound45 H st hI
theorem probabilityBound45 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch119.certificate1428).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate967).dm (WitnessCertificates.Batch048.certificate967).beta (1/125)) ≤ ((CutFailureCertificates.Budget048.certificate967).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound967 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate967).aa:ℝ)*st.R)+(((914:ℚ):ℝ)*exp (-((MergedCutGroups.Batch119.certificate1428).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate45).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch048.certificate967).omega:ℝ) ≤ ((CutFailureCertificates.Budget048.certificate967).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch119.certificate1428).cells.length:ℝ) ≤ (457:ℝ) := by exact_mod_cast multiplicity45
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch119.certificate1428).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound45 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch048.certificate967).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate45).exponent:ℝ)*st.R)+((MergedCutGroups.Batch119.certificate1428).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch119.certificate1428).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch048.certificate967).aa:ℝ)*st.R)+((914:ℝ)*exp (-((MergedCutGroups.Batch119.certificate1428).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate45).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch048.sound967.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets46 : Fin (MergedCutGroups.Batch119.certificate1432).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority031.certificate637,CutLabelCertificates.Minority031.certificate638,CutLabelCertificates.Minority031.certificate639,CutLabelCertificates.Minority032.certificate640]
theorem matches46 : (MergedCutGroups.Batch119.certificate1432).LocalMatches CountingCertificates.Batch048.certificate970 budgets46 := by decide +kernel
theorem budgetsSound46 : ∀ l, (budgets46 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority031.sound637
  · exact CutLabelCertificates.Minority031.sound638
  · exact CutLabelCertificates.Minority031.sound639
  · exact CutLabelCertificates.Minority032.sound640
theorem multiplicity46 : (MergedCutGroups.Batch119.certificate1432).cells.length ≤ 457 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound46 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch119.certificate1432).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate970).dm (WitnessCertificates.Batch048.certificate970).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch048.certificate970).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate46).exponent:ℝ)*st.R)+((MergedCutGroups.Batch119.certificate1432).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch119.certificate1432).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch048.certificate970).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch119.certificate1432 CountingCertificates.Batch048.certificate970 budgets46 CutFailureCertificates.Reverse002.certificate46 matches46 rfl rfl
    MergedCutGroups.Batch119.numericValid1432 MergedCutGroups.Batch119.cellsSound1432 MergedCutGroups.Batch119.cellsEntropyValid1432 MergedCutGroups.Batch119.populationMatches1432
    PopulationCertificates.Batch048.valid970 PopulationCertificates.Batch048.sound970 WitnessCertificates.Batch048.valid970 WitnessCertificates.Batch048.sound970 CountingCertificates.Batch048.valid970 CountingCertificates.Batch048.sound970
    budgetsSound46 CutFailureCertificates.Reverse002.sound46 H st hI
theorem probabilityBound46 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch119.certificate1432).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate970).dm (WitnessCertificates.Batch048.certificate970).beta (1/125)) ≤ ((CutFailureCertificates.Budget048.certificate970).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound970 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate970).aa:ℝ)*st.R)+(((914:ℚ):ℝ)*exp (-((MergedCutGroups.Batch119.certificate1432).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate46).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch048.certificate970).omega:ℝ) ≤ ((CutFailureCertificates.Budget048.certificate970).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch119.certificate1432).cells.length:ℝ) ≤ (457:ℝ) := by exact_mod_cast multiplicity46
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch119.certificate1432).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound46 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch048.certificate970).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate46).exponent:ℝ)*st.R)+((MergedCutGroups.Batch119.certificate1432).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch119.certificate1432).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch048.certificate970).aa:ℝ)*st.R)+((914:ℝ)*exp (-((MergedCutGroups.Batch119.certificate1432).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate46).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch048.sound970.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets47 : Fin (MergedCutGroups.Batch119.certificate1436).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority032.certificate642,CutLabelCertificates.Minority032.certificate643,CutLabelCertificates.Minority032.certificate644,CutLabelCertificates.Minority032.certificate645]
theorem matches47 : (MergedCutGroups.Batch119.certificate1436).LocalMatches CountingCertificates.Batch048.certificate973 budgets47 := by decide +kernel
theorem budgetsSound47 : ∀ l, (budgets47 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority032.sound642
  · exact CutLabelCertificates.Minority032.sound643
  · exact CutLabelCertificates.Minority032.sound644
  · exact CutLabelCertificates.Minority032.sound645
theorem multiplicity47 : (MergedCutGroups.Batch119.certificate1436).cells.length ≤ 457 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound47 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch119.certificate1436).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate973).dm (WitnessCertificates.Batch048.certificate973).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch048.certificate973).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate47).exponent:ℝ)*st.R)+((MergedCutGroups.Batch119.certificate1436).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch119.certificate1436).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch048.certificate973).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch119.certificate1436 CountingCertificates.Batch048.certificate973 budgets47 CutFailureCertificates.Reverse002.certificate47 matches47 rfl rfl
    MergedCutGroups.Batch119.numericValid1436 MergedCutGroups.Batch119.cellsSound1436 MergedCutGroups.Batch119.cellsEntropyValid1436 MergedCutGroups.Batch119.populationMatches1436
    PopulationCertificates.Batch048.valid973 PopulationCertificates.Batch048.sound973 WitnessCertificates.Batch048.valid973 WitnessCertificates.Batch048.sound973 CountingCertificates.Batch048.valid973 CountingCertificates.Batch048.sound973
    budgetsSound47 CutFailureCertificates.Reverse002.sound47 H st hI
theorem probabilityBound47 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch119.certificate1436).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate973).dm (WitnessCertificates.Batch048.certificate973).beta (1/125)) ≤ ((CutFailureCertificates.Budget048.certificate973).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound973 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate973).aa:ℝ)*st.R)+(((914:ℚ):ℝ)*exp (-((MergedCutGroups.Batch119.certificate1436).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate47).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch048.certificate973).omega:ℝ) ≤ ((CutFailureCertificates.Budget048.certificate973).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch119.certificate1436).cells.length:ℝ) ≤ (457:ℝ) := by exact_mod_cast multiplicity47
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch119.certificate1436).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound47 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch048.certificate973).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate47).exponent:ℝ)*st.R)+((MergedCutGroups.Batch119.certificate1436).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch119.certificate1436).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch048.certificate973).aa:ℝ)*st.R)+((914:ℝ)*exp (-((MergedCutGroups.Batch119.certificate1436).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate47).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch048.sound973.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets48 : Fin (MergedCutGroups.Batch120.certificate1440).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority032.certificate647,CutLabelCertificates.Minority032.certificate648,CutLabelCertificates.Minority032.certificate649,CutLabelCertificates.Minority032.certificate650]
theorem matches48 : (MergedCutGroups.Batch120.certificate1440).LocalMatches CountingCertificates.Batch048.certificate976 budgets48 := by decide +kernel
theorem budgetsSound48 : ∀ l, (budgets48 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority032.sound647
  · exact CutLabelCertificates.Minority032.sound648
  · exact CutLabelCertificates.Minority032.sound649
  · exact CutLabelCertificates.Minority032.sound650
theorem multiplicity48 : (MergedCutGroups.Batch120.certificate1440).cells.length ≤ 457 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound48 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch120.certificate1440).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate976).dm (WitnessCertificates.Batch048.certificate976).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch048.certificate976).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate48).exponent:ℝ)*st.R)+((MergedCutGroups.Batch120.certificate1440).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch120.certificate1440).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch048.certificate976).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch120.certificate1440 CountingCertificates.Batch048.certificate976 budgets48 CutFailureCertificates.Reverse002.certificate48 matches48 rfl rfl
    MergedCutGroups.Batch120.numericValid1440 MergedCutGroups.Batch120.cellsSound1440 MergedCutGroups.Batch120.cellsEntropyValid1440 MergedCutGroups.Batch120.populationMatches1440
    PopulationCertificates.Batch048.valid976 PopulationCertificates.Batch048.sound976 WitnessCertificates.Batch048.valid976 WitnessCertificates.Batch048.sound976 CountingCertificates.Batch048.valid976 CountingCertificates.Batch048.sound976
    budgetsSound48 CutFailureCertificates.Reverse002.sound48 H st hI
theorem probabilityBound48 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch120.certificate1440).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate976).dm (WitnessCertificates.Batch048.certificate976).beta (1/125)) ≤ ((CutFailureCertificates.Budget048.certificate976).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound976 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate976).aa:ℝ)*st.R)+(((914:ℚ):ℝ)*exp (-((MergedCutGroups.Batch120.certificate1440).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate48).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch048.certificate976).omega:ℝ) ≤ ((CutFailureCertificates.Budget048.certificate976).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch120.certificate1440).cells.length:ℝ) ≤ (457:ℝ) := by exact_mod_cast multiplicity48
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch120.certificate1440).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound48 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch048.certificate976).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate48).exponent:ℝ)*st.R)+((MergedCutGroups.Batch120.certificate1440).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch120.certificate1440).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch048.certificate976).aa:ℝ)*st.R)+((914:ℝ)*exp (-((MergedCutGroups.Batch120.certificate1440).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate48).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch048.sound976.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets49 : Fin (MergedCutGroups.Batch120.certificate1444).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority032.certificate652,CutLabelCertificates.Minority032.certificate653,CutLabelCertificates.Minority032.certificate654,CutLabelCertificates.Minority032.certificate655]
theorem matches49 : (MergedCutGroups.Batch120.certificate1444).LocalMatches CountingCertificates.Batch048.certificate979 budgets49 := by decide +kernel
theorem budgetsSound49 : ∀ l, (budgets49 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority032.sound652
  · exact CutLabelCertificates.Minority032.sound653
  · exact CutLabelCertificates.Minority032.sound654
  · exact CutLabelCertificates.Minority032.sound655
theorem multiplicity49 : (MergedCutGroups.Batch120.certificate1444).cells.length ≤ 457 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound49 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch120.certificate1444).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate979).dm (WitnessCertificates.Batch048.certificate979).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch048.certificate979).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate49).exponent:ℝ)*st.R)+((MergedCutGroups.Batch120.certificate1444).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch120.certificate1444).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch048.certificate979).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch120.certificate1444 CountingCertificates.Batch048.certificate979 budgets49 CutFailureCertificates.Reverse002.certificate49 matches49 rfl rfl
    MergedCutGroups.Batch120.numericValid1444 MergedCutGroups.Batch120.cellsSound1444 MergedCutGroups.Batch120.cellsEntropyValid1444 MergedCutGroups.Batch120.populationMatches1444
    PopulationCertificates.Batch048.valid979 PopulationCertificates.Batch048.sound979 WitnessCertificates.Batch048.valid979 WitnessCertificates.Batch048.sound979 CountingCertificates.Batch048.valid979 CountingCertificates.Batch048.sound979
    budgetsSound49 CutFailureCertificates.Reverse002.sound49 H st hI
theorem probabilityBound49 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch120.certificate1444).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch048.certificate979).dm (WitnessCertificates.Batch048.certificate979).beta (1/125)) ≤ ((CutFailureCertificates.Budget048.certificate979).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound979 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate979).aa:ℝ)*st.R)+(((914:ℚ):ℝ)*exp (-((MergedCutGroups.Batch120.certificate1444).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate49).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch048.certificate979).omega:ℝ) ≤ ((CutFailureCertificates.Budget048.certificate979).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch120.certificate1444).cells.length:ℝ) ≤ (457:ℝ) := by exact_mod_cast multiplicity49
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch120.certificate1444).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound49 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch048.certificate979).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate49).exponent:ℝ)*st.R)+((MergedCutGroups.Batch120.certificate1444).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch120.certificate1444).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch048.certificate979).aa:ℝ)*st.R)+((914:ℝ)*exp (-((MergedCutGroups.Batch120.certificate1444).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate49).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch048.sound979.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets50 : Fin (MergedCutGroups.Batch120.certificate1448).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority032.certificate657,CutLabelCertificates.Minority032.certificate658,CutLabelCertificates.Minority032.certificate659,CutLabelCertificates.Minority033.certificate660]
theorem matches50 : (MergedCutGroups.Batch120.certificate1448).LocalMatches CountingCertificates.Batch049.certificate982 budgets50 := by decide +kernel
theorem budgetsSound50 : ∀ l, (budgets50 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority032.sound657
  · exact CutLabelCertificates.Minority032.sound658
  · exact CutLabelCertificates.Minority032.sound659
  · exact CutLabelCertificates.Minority033.sound660
theorem multiplicity50 : (MergedCutGroups.Batch120.certificate1448).cells.length ≤ 456 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound50 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch120.certificate1448).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate982).dm (WitnessCertificates.Batch049.certificate982).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch049.certificate982).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate50).exponent:ℝ)*st.R)+((MergedCutGroups.Batch120.certificate1448).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch120.certificate1448).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch049.certificate982).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch120.certificate1448 CountingCertificates.Batch049.certificate982 budgets50 CutFailureCertificates.Reverse002.certificate50 matches50 rfl rfl
    MergedCutGroups.Batch120.numericValid1448 MergedCutGroups.Batch120.cellsSound1448 MergedCutGroups.Batch120.cellsEntropyValid1448 MergedCutGroups.Batch120.populationMatches1448
    PopulationCertificates.Batch049.valid982 PopulationCertificates.Batch049.sound982 WitnessCertificates.Batch049.valid982 WitnessCertificates.Batch049.sound982 CountingCertificates.Batch049.valid982 CountingCertificates.Batch049.sound982
    budgetsSound50 CutFailureCertificates.Reverse002.sound50 H st hI
theorem probabilityBound50 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch120.certificate1448).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate982).dm (WitnessCertificates.Batch049.certificate982).beta (1/125)) ≤ ((CutFailureCertificates.Budget049.certificate982).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound982 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate982).aa:ℝ)*st.R)+(((912:ℚ):ℝ)*exp (-((MergedCutGroups.Batch120.certificate1448).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate50).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch049.certificate982).omega:ℝ) ≤ ((CutFailureCertificates.Budget049.certificate982).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch120.certificate1448).cells.length:ℝ) ≤ (456:ℝ) := by exact_mod_cast multiplicity50
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch120.certificate1448).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound50 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch049.certificate982).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate50).exponent:ℝ)*st.R)+((MergedCutGroups.Batch120.certificate1448).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch120.certificate1448).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch049.certificate982).aa:ℝ)*st.R)+((912:ℝ)*exp (-((MergedCutGroups.Batch120.certificate1448).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate50).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch049.sound982.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets51 : Fin (MergedCutGroups.Batch121.certificate1452).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority033.certificate662,CutLabelCertificates.Minority033.certificate663,CutLabelCertificates.Minority033.certificate664,CutLabelCertificates.Minority033.certificate665]
theorem matches51 : (MergedCutGroups.Batch121.certificate1452).LocalMatches CountingCertificates.Batch049.certificate985 budgets51 := by decide +kernel
theorem budgetsSound51 : ∀ l, (budgets51 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority033.sound662
  · exact CutLabelCertificates.Minority033.sound663
  · exact CutLabelCertificates.Minority033.sound664
  · exact CutLabelCertificates.Minority033.sound665
theorem multiplicity51 : (MergedCutGroups.Batch121.certificate1452).cells.length ≤ 456 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound51 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch121.certificate1452).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate985).dm (WitnessCertificates.Batch049.certificate985).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch049.certificate985).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate51).exponent:ℝ)*st.R)+((MergedCutGroups.Batch121.certificate1452).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch121.certificate1452).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch049.certificate985).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch121.certificate1452 CountingCertificates.Batch049.certificate985 budgets51 CutFailureCertificates.Reverse002.certificate51 matches51 rfl rfl
    MergedCutGroups.Batch121.numericValid1452 MergedCutGroups.Batch121.cellsSound1452 MergedCutGroups.Batch121.cellsEntropyValid1452 MergedCutGroups.Batch121.populationMatches1452
    PopulationCertificates.Batch049.valid985 PopulationCertificates.Batch049.sound985 WitnessCertificates.Batch049.valid985 WitnessCertificates.Batch049.sound985 CountingCertificates.Batch049.valid985 CountingCertificates.Batch049.sound985
    budgetsSound51 CutFailureCertificates.Reverse002.sound51 H st hI
theorem probabilityBound51 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch121.certificate1452).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate985).dm (WitnessCertificates.Batch049.certificate985).beta (1/125)) ≤ ((CutFailureCertificates.Budget049.certificate985).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound985 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate985).aa:ℝ)*st.R)+(((912:ℚ):ℝ)*exp (-((MergedCutGroups.Batch121.certificate1452).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate51).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch049.certificate985).omega:ℝ) ≤ ((CutFailureCertificates.Budget049.certificate985).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch121.certificate1452).cells.length:ℝ) ≤ (456:ℝ) := by exact_mod_cast multiplicity51
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch121.certificate1452).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound51 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch049.certificate985).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate51).exponent:ℝ)*st.R)+((MergedCutGroups.Batch121.certificate1452).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch121.certificate1452).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch049.certificate985).aa:ℝ)*st.R)+((912:ℝ)*exp (-((MergedCutGroups.Batch121.certificate1452).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate51).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch049.sound985.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets52 : Fin (MergedCutGroups.Batch121.certificate1456).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority033.certificate667,CutLabelCertificates.Minority033.certificate668,CutLabelCertificates.Minority033.certificate669,CutLabelCertificates.Minority033.certificate670,CutLabelCertificates.Minority033.certificate671]
theorem matches52 : (MergedCutGroups.Batch121.certificate1456).LocalMatches CountingCertificates.Batch049.certificate988 budgets52 := by decide +kernel
theorem budgetsSound52 : ∀ l, (budgets52 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority033.sound667
  · exact CutLabelCertificates.Minority033.sound668
  · exact CutLabelCertificates.Minority033.sound669
  · exact CutLabelCertificates.Minority033.sound670
  · exact CutLabelCertificates.Minority033.sound671
theorem multiplicity52 : (MergedCutGroups.Batch121.certificate1456).cells.length ≤ 457 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound52 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch121.certificate1456).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate988).dm (WitnessCertificates.Batch049.certificate988).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch049.certificate988).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate52).exponent:ℝ)*st.R)+((MergedCutGroups.Batch121.certificate1456).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch121.certificate1456).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch049.certificate988).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch121.certificate1456 CountingCertificates.Batch049.certificate988 budgets52 CutFailureCertificates.Reverse002.certificate52 matches52 rfl rfl
    MergedCutGroups.Batch121.numericValid1456 MergedCutGroups.Batch121.cellsSound1456 MergedCutGroups.Batch121.cellsEntropyValid1456 MergedCutGroups.Batch121.populationMatches1456
    PopulationCertificates.Batch049.valid988 PopulationCertificates.Batch049.sound988 WitnessCertificates.Batch049.valid988 WitnessCertificates.Batch049.sound988 CountingCertificates.Batch049.valid988 CountingCertificates.Batch049.sound988
    budgetsSound52 CutFailureCertificates.Reverse002.sound52 H st hI
theorem probabilityBound52 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch121.certificate1456).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate988).dm (WitnessCertificates.Batch049.certificate988).beta (1/125)) ≤ ((CutFailureCertificates.Budget049.certificate988).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound988 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate988).aa:ℝ)*st.R)+(((914:ℚ):ℝ)*exp (-((MergedCutGroups.Batch121.certificate1456).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate52).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch049.certificate988).omega:ℝ) ≤ ((CutFailureCertificates.Budget049.certificate988).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch121.certificate1456).cells.length:ℝ) ≤ (457:ℝ) := by exact_mod_cast multiplicity52
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch121.certificate1456).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound52 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch049.certificate988).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate52).exponent:ℝ)*st.R)+((MergedCutGroups.Batch121.certificate1456).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch121.certificate1456).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch049.certificate988).aa:ℝ)*st.R)+((914:ℝ)*exp (-((MergedCutGroups.Batch121.certificate1456).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate52).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch049.sound988.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets53 : Fin (MergedCutGroups.Batch121.certificate1460).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority033.certificate673,CutLabelCertificates.Minority033.certificate674,CutLabelCertificates.Minority033.certificate675,CutLabelCertificates.Minority033.certificate676,CutLabelCertificates.Minority033.certificate677]
theorem matches53 : (MergedCutGroups.Batch121.certificate1460).LocalMatches CountingCertificates.Batch049.certificate991 budgets53 := by decide +kernel
theorem budgetsSound53 : ∀ l, (budgets53 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority033.sound673
  · exact CutLabelCertificates.Minority033.sound674
  · exact CutLabelCertificates.Minority033.sound675
  · exact CutLabelCertificates.Minority033.sound676
  · exact CutLabelCertificates.Minority033.sound677
theorem multiplicity53 : (MergedCutGroups.Batch121.certificate1460).cells.length ≤ 456 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound53 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch121.certificate1460).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate991).dm (WitnessCertificates.Batch049.certificate991).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch049.certificate991).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate53).exponent:ℝ)*st.R)+((MergedCutGroups.Batch121.certificate1460).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch121.certificate1460).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch049.certificate991).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch121.certificate1460 CountingCertificates.Batch049.certificate991 budgets53 CutFailureCertificates.Reverse002.certificate53 matches53 rfl rfl
    MergedCutGroups.Batch121.numericValid1460 MergedCutGroups.Batch121.cellsSound1460 MergedCutGroups.Batch121.cellsEntropyValid1460 MergedCutGroups.Batch121.populationMatches1460
    PopulationCertificates.Batch049.valid991 PopulationCertificates.Batch049.sound991 WitnessCertificates.Batch049.valid991 WitnessCertificates.Batch049.sound991 CountingCertificates.Batch049.valid991 CountingCertificates.Batch049.sound991
    budgetsSound53 CutFailureCertificates.Reverse002.sound53 H st hI
theorem probabilityBound53 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch121.certificate1460).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate991).dm (WitnessCertificates.Batch049.certificate991).beta (1/125)) ≤ ((CutFailureCertificates.Budget049.certificate991).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound991 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate991).aa:ℝ)*st.R)+(((912:ℚ):ℝ)*exp (-((MergedCutGroups.Batch121.certificate1460).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate53).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch049.certificate991).omega:ℝ) ≤ ((CutFailureCertificates.Budget049.certificate991).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch121.certificate1460).cells.length:ℝ) ≤ (456:ℝ) := by exact_mod_cast multiplicity53
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch121.certificate1460).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound53 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch049.certificate991).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate53).exponent:ℝ)*st.R)+((MergedCutGroups.Batch121.certificate1460).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch121.certificate1460).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch049.certificate991).aa:ℝ)*st.R)+((912:ℝ)*exp (-((MergedCutGroups.Batch121.certificate1460).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate53).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch049.sound991.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets54 : Fin (MergedCutGroups.Batch122.certificate1464).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority033.certificate679,CutLabelCertificates.Minority034.certificate680,CutLabelCertificates.Minority034.certificate681,CutLabelCertificates.Minority034.certificate682,CutLabelCertificates.Minority034.certificate683]
theorem matches54 : (MergedCutGroups.Batch122.certificate1464).LocalMatches CountingCertificates.Batch049.certificate994 budgets54 := by decide +kernel
theorem budgetsSound54 : ∀ l, (budgets54 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority033.sound679
  · exact CutLabelCertificates.Minority034.sound680
  · exact CutLabelCertificates.Minority034.sound681
  · exact CutLabelCertificates.Minority034.sound682
  · exact CutLabelCertificates.Minority034.sound683
theorem multiplicity54 : (MergedCutGroups.Batch122.certificate1464).cells.length ≤ 456 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound54 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch122.certificate1464).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate994).dm (WitnessCertificates.Batch049.certificate994).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch049.certificate994).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate54).exponent:ℝ)*st.R)+((MergedCutGroups.Batch122.certificate1464).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch122.certificate1464).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch049.certificate994).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch122.certificate1464 CountingCertificates.Batch049.certificate994 budgets54 CutFailureCertificates.Reverse002.certificate54 matches54 rfl rfl
    MergedCutGroups.Batch122.numericValid1464 MergedCutGroups.Batch122.cellsSound1464 MergedCutGroups.Batch122.cellsEntropyValid1464 MergedCutGroups.Batch122.populationMatches1464
    PopulationCertificates.Batch049.valid994 PopulationCertificates.Batch049.sound994 WitnessCertificates.Batch049.valid994 WitnessCertificates.Batch049.sound994 CountingCertificates.Batch049.valid994 CountingCertificates.Batch049.sound994
    budgetsSound54 CutFailureCertificates.Reverse002.sound54 H st hI
theorem probabilityBound54 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch122.certificate1464).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate994).dm (WitnessCertificates.Batch049.certificate994).beta (1/125)) ≤ ((CutFailureCertificates.Budget049.certificate994).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound994 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate994).aa:ℝ)*st.R)+(((912:ℚ):ℝ)*exp (-((MergedCutGroups.Batch122.certificate1464).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate54).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch049.certificate994).omega:ℝ) ≤ ((CutFailureCertificates.Budget049.certificate994).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch122.certificate1464).cells.length:ℝ) ≤ (456:ℝ) := by exact_mod_cast multiplicity54
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch122.certificate1464).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound54 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch049.certificate994).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate54).exponent:ℝ)*st.R)+((MergedCutGroups.Batch122.certificate1464).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch122.certificate1464).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch049.certificate994).aa:ℝ)*st.R)+((912:ℝ)*exp (-((MergedCutGroups.Batch122.certificate1464).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate54).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch049.sound994.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets55 : Fin (MergedCutGroups.Batch122.certificate1468).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority034.certificate685,CutLabelCertificates.Minority034.certificate686,CutLabelCertificates.Minority034.certificate687,CutLabelCertificates.Minority034.certificate688,CutLabelCertificates.Minority034.certificate689]
theorem matches55 : (MergedCutGroups.Batch122.certificate1468).LocalMatches CountingCertificates.Batch049.certificate997 budgets55 := by decide +kernel
theorem budgetsSound55 : ∀ l, (budgets55 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority034.sound685
  · exact CutLabelCertificates.Minority034.sound686
  · exact CutLabelCertificates.Minority034.sound687
  · exact CutLabelCertificates.Minority034.sound688
  · exact CutLabelCertificates.Minority034.sound689
theorem multiplicity55 : (MergedCutGroups.Batch122.certificate1468).cells.length ≤ 456 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound55 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch122.certificate1468).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate997).dm (WitnessCertificates.Batch049.certificate997).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch049.certificate997).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate55).exponent:ℝ)*st.R)+((MergedCutGroups.Batch122.certificate1468).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch122.certificate1468).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch049.certificate997).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch122.certificate1468 CountingCertificates.Batch049.certificate997 budgets55 CutFailureCertificates.Reverse002.certificate55 matches55 rfl rfl
    MergedCutGroups.Batch122.numericValid1468 MergedCutGroups.Batch122.cellsSound1468 MergedCutGroups.Batch122.cellsEntropyValid1468 MergedCutGroups.Batch122.populationMatches1468
    PopulationCertificates.Batch049.valid997 PopulationCertificates.Batch049.sound997 WitnessCertificates.Batch049.valid997 WitnessCertificates.Batch049.sound997 CountingCertificates.Batch049.valid997 CountingCertificates.Batch049.sound997
    budgetsSound55 CutFailureCertificates.Reverse002.sound55 H st hI
theorem probabilityBound55 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch122.certificate1468).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch049.certificate997).dm (WitnessCertificates.Batch049.certificate997).beta (1/125)) ≤ ((CutFailureCertificates.Budget049.certificate997).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget049.sound997 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch049.certificate997).aa:ℝ)*st.R)+(((912:ℚ):ℝ)*exp (-((MergedCutGroups.Batch122.certificate1468).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate55).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch049.certificate997).omega:ℝ) ≤ ((CutFailureCertificates.Budget049.certificate997).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch122.certificate1468).cells.length:ℝ) ≤ (456:ℝ) := by exact_mod_cast multiplicity55
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch122.certificate1468).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound55 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch049.certificate997).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate55).exponent:ℝ)*st.R)+((MergedCutGroups.Batch122.certificate1468).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch122.certificate1468).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch049.certificate997).aa:ℝ)*st.R)+((912:ℝ)*exp (-((MergedCutGroups.Batch122.certificate1468).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate55).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch049.sound997.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets56 : Fin (MergedCutGroups.Batch122.certificate1472).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority034.certificate691,CutLabelCertificates.Minority034.certificate692,CutLabelCertificates.Minority034.certificate693,CutLabelCertificates.Minority034.certificate694,CutLabelCertificates.Minority034.certificate695]
theorem matches56 : (MergedCutGroups.Batch122.certificate1472).LocalMatches CountingCertificates.Batch050.certificate1000 budgets56 := by decide +kernel
theorem budgetsSound56 : ∀ l, (budgets56 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority034.sound691
  · exact CutLabelCertificates.Minority034.sound692
  · exact CutLabelCertificates.Minority034.sound693
  · exact CutLabelCertificates.Minority034.sound694
  · exact CutLabelCertificates.Minority034.sound695
theorem multiplicity56 : (MergedCutGroups.Batch122.certificate1472).cells.length ≤ 455 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound56 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch122.certificate1472).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1000).dm (WitnessCertificates.Batch050.certificate1000).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1000).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate56).exponent:ℝ)*st.R)+((MergedCutGroups.Batch122.certificate1472).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch122.certificate1472).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch050.certificate1000).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch122.certificate1472 CountingCertificates.Batch050.certificate1000 budgets56 CutFailureCertificates.Reverse002.certificate56 matches56 rfl rfl
    MergedCutGroups.Batch122.numericValid1472 MergedCutGroups.Batch122.cellsSound1472 MergedCutGroups.Batch122.cellsEntropyValid1472 MergedCutGroups.Batch122.populationMatches1472
    PopulationCertificates.Batch050.valid1000 PopulationCertificates.Batch050.sound1000 WitnessCertificates.Batch050.valid1000 WitnessCertificates.Batch050.sound1000 CountingCertificates.Batch050.valid1000 CountingCertificates.Batch050.sound1000
    budgetsSound56 CutFailureCertificates.Reverse002.sound56 H st hI
theorem probabilityBound56 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch122.certificate1472).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1000).dm (WitnessCertificates.Batch050.certificate1000).beta (1/125)) ≤ ((CutFailureCertificates.Budget050.certificate1000).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1000 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1000).aa:ℝ)*st.R)+(((910:ℚ):ℝ)*exp (-((MergedCutGroups.Batch122.certificate1472).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate56).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch050.certificate1000).omega:ℝ) ≤ ((CutFailureCertificates.Budget050.certificate1000).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch122.certificate1472).cells.length:ℝ) ≤ (455:ℝ) := by exact_mod_cast multiplicity56
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch122.certificate1472).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound56 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch050.certificate1000).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate56).exponent:ℝ)*st.R)+((MergedCutGroups.Batch122.certificate1472).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch122.certificate1472).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch050.certificate1000).aa:ℝ)*st.R)+((910:ℝ)*exp (-((MergedCutGroups.Batch122.certificate1472).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate56).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch050.sound1000.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets57 : Fin (MergedCutGroups.Batch123.certificate1476).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority034.certificate697,CutLabelCertificates.Minority034.certificate698,CutLabelCertificates.Minority034.certificate699,CutLabelCertificates.Minority035.certificate700,CutLabelCertificates.Minority035.certificate701]
theorem matches57 : (MergedCutGroups.Batch123.certificate1476).LocalMatches CountingCertificates.Batch050.certificate1003 budgets57 := by decide +kernel
theorem budgetsSound57 : ∀ l, (budgets57 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority034.sound697
  · exact CutLabelCertificates.Minority034.sound698
  · exact CutLabelCertificates.Minority034.sound699
  · exact CutLabelCertificates.Minority035.sound700
  · exact CutLabelCertificates.Minority035.sound701
theorem multiplicity57 : (MergedCutGroups.Batch123.certificate1476).cells.length ≤ 455 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound57 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch123.certificate1476).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1003).dm (WitnessCertificates.Batch050.certificate1003).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1003).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate57).exponent:ℝ)*st.R)+((MergedCutGroups.Batch123.certificate1476).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch123.certificate1476).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch050.certificate1003).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch123.certificate1476 CountingCertificates.Batch050.certificate1003 budgets57 CutFailureCertificates.Reverse002.certificate57 matches57 rfl rfl
    MergedCutGroups.Batch123.numericValid1476 MergedCutGroups.Batch123.cellsSound1476 MergedCutGroups.Batch123.cellsEntropyValid1476 MergedCutGroups.Batch123.populationMatches1476
    PopulationCertificates.Batch050.valid1003 PopulationCertificates.Batch050.sound1003 WitnessCertificates.Batch050.valid1003 WitnessCertificates.Batch050.sound1003 CountingCertificates.Batch050.valid1003 CountingCertificates.Batch050.sound1003
    budgetsSound57 CutFailureCertificates.Reverse002.sound57 H st hI
theorem probabilityBound57 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch123.certificate1476).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1003).dm (WitnessCertificates.Batch050.certificate1003).beta (1/125)) ≤ ((CutFailureCertificates.Budget050.certificate1003).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1003 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1003).aa:ℝ)*st.R)+(((910:ℚ):ℝ)*exp (-((MergedCutGroups.Batch123.certificate1476).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate57).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch050.certificate1003).omega:ℝ) ≤ ((CutFailureCertificates.Budget050.certificate1003).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch123.certificate1476).cells.length:ℝ) ≤ (455:ℝ) := by exact_mod_cast multiplicity57
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch123.certificate1476).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound57 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch050.certificate1003).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate57).exponent:ℝ)*st.R)+((MergedCutGroups.Batch123.certificate1476).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch123.certificate1476).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch050.certificate1003).aa:ℝ)*st.R)+((910:ℝ)*exp (-((MergedCutGroups.Batch123.certificate1476).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate57).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch050.sound1003.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets58 : Fin (MergedCutGroups.Batch123.certificate1480).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority035.certificate703,CutLabelCertificates.Minority035.certificate704,CutLabelCertificates.Minority035.certificate705,CutLabelCertificates.Minority035.certificate706,CutLabelCertificates.Minority035.certificate707]
theorem matches58 : (MergedCutGroups.Batch123.certificate1480).LocalMatches CountingCertificates.Batch050.certificate1006 budgets58 := by decide +kernel
theorem budgetsSound58 : ∀ l, (budgets58 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority035.sound703
  · exact CutLabelCertificates.Minority035.sound704
  · exact CutLabelCertificates.Minority035.sound705
  · exact CutLabelCertificates.Minority035.sound706
  · exact CutLabelCertificates.Minority035.sound707
theorem multiplicity58 : (MergedCutGroups.Batch123.certificate1480).cells.length ≤ 455 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound58 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch123.certificate1480).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1006).dm (WitnessCertificates.Batch050.certificate1006).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1006).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate58).exponent:ℝ)*st.R)+((MergedCutGroups.Batch123.certificate1480).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch123.certificate1480).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch050.certificate1006).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch123.certificate1480 CountingCertificates.Batch050.certificate1006 budgets58 CutFailureCertificates.Reverse002.certificate58 matches58 rfl rfl
    MergedCutGroups.Batch123.numericValid1480 MergedCutGroups.Batch123.cellsSound1480 MergedCutGroups.Batch123.cellsEntropyValid1480 MergedCutGroups.Batch123.populationMatches1480
    PopulationCertificates.Batch050.valid1006 PopulationCertificates.Batch050.sound1006 WitnessCertificates.Batch050.valid1006 WitnessCertificates.Batch050.sound1006 CountingCertificates.Batch050.valid1006 CountingCertificates.Batch050.sound1006
    budgetsSound58 CutFailureCertificates.Reverse002.sound58 H st hI
theorem probabilityBound58 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch123.certificate1480).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1006).dm (WitnessCertificates.Batch050.certificate1006).beta (1/125)) ≤ ((CutFailureCertificates.Budget050.certificate1006).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1006 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1006).aa:ℝ)*st.R)+(((910:ℚ):ℝ)*exp (-((MergedCutGroups.Batch123.certificate1480).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate58).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch050.certificate1006).omega:ℝ) ≤ ((CutFailureCertificates.Budget050.certificate1006).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch123.certificate1480).cells.length:ℝ) ≤ (455:ℝ) := by exact_mod_cast multiplicity58
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch123.certificate1480).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound58 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch050.certificate1006).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate58).exponent:ℝ)*st.R)+((MergedCutGroups.Batch123.certificate1480).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch123.certificate1480).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch050.certificate1006).aa:ℝ)*st.R)+((910:ℝ)*exp (-((MergedCutGroups.Batch123.certificate1480).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate58).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch050.sound1006.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets59 : Fin (MergedCutGroups.Batch123.certificate1484).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority035.certificate709,CutLabelCertificates.Minority035.certificate710,CutLabelCertificates.Minority035.certificate711,CutLabelCertificates.Minority035.certificate712,CutLabelCertificates.Minority035.certificate713]
theorem matches59 : (MergedCutGroups.Batch123.certificate1484).LocalMatches CountingCertificates.Batch050.certificate1009 budgets59 := by decide +kernel
theorem budgetsSound59 : ∀ l, (budgets59 l).Sound := by
  intro l
  change Fin 5 at l
  fin_cases l
  · exact CutLabelCertificates.Minority035.sound709
  · exact CutLabelCertificates.Minority035.sound710
  · exact CutLabelCertificates.Minority035.sound711
  · exact CutLabelCertificates.Minority035.sound712
  · exact CutLabelCertificates.Minority035.sound713
theorem multiplicity59 : (MergedCutGroups.Batch123.certificate1484).cells.length ≤ 454 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound59 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch123.certificate1484).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1009).dm (WitnessCertificates.Batch050.certificate1009).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch050.certificate1009).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate59).exponent:ℝ)*st.R)+((MergedCutGroups.Batch123.certificate1484).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch123.certificate1484).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch050.certificate1009).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch123.certificate1484 CountingCertificates.Batch050.certificate1009 budgets59 CutFailureCertificates.Reverse002.certificate59 matches59 rfl rfl
    MergedCutGroups.Batch123.numericValid1484 MergedCutGroups.Batch123.cellsSound1484 MergedCutGroups.Batch123.cellsEntropyValid1484 MergedCutGroups.Batch123.populationMatches1484
    PopulationCertificates.Batch050.valid1009 PopulationCertificates.Batch050.sound1009 WitnessCertificates.Batch050.valid1009 WitnessCertificates.Batch050.sound1009 CountingCertificates.Batch050.valid1009 CountingCertificates.Batch050.sound1009
    budgetsSound59 CutFailureCertificates.Reverse002.sound59 H st hI
theorem probabilityBound59 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch123.certificate1484).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch050.certificate1009).dm (WitnessCertificates.Batch050.certificate1009).beta (1/125)) ≤ ((CutFailureCertificates.Budget050.certificate1009).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget050.sound1009 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch050.certificate1009).aa:ℝ)*st.R)+(((908:ℚ):ℝ)*exp (-((MergedCutGroups.Batch123.certificate1484).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse002.certificate59).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch050.certificate1009).omega:ℝ) ≤ ((CutFailureCertificates.Budget050.certificate1009).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch123.certificate1484).cells.length:ℝ) ≤ (454:ℝ) := by exact_mod_cast multiplicity59
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch123.certificate1484).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound59 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch050.certificate1009).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate59).exponent:ℝ)*st.R)+((MergedCutGroups.Batch123.certificate1484).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch123.certificate1484).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch050.certificate1009).aa:ℝ)*st.R)+((908:ℝ)*exp (-((MergedCutGroups.Batch123.certificate1484).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse002.certificate59).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch050.sound1009.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

end Cycle12.CertifiedLocalFailures.Batch002
