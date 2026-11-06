import Cycle12.CertifiedLocalFailure
import Cycle12.CountingCertificates.Batch041
import Cycle12.CountingCertificates.Batch042
import Cycle12.CountingCertificates.Batch043
import Cycle12.CountingCertificates.Batch044
import Cycle12.CutFailureCertificates.Budget041
import Cycle12.CutFailureCertificates.Budget042
import Cycle12.CutFailureCertificates.Budget043
import Cycle12.CutFailureCertificates.Budget044
import Cycle12.CutFailureCertificates.Reverse000
import Cycle12.CutLabelCertificates.Minority020
import Cycle12.CutLabelCertificates.Minority021
import Cycle12.CutLabelCertificates.Minority022
import Cycle12.CutLabelCertificates.Minority023
import Cycle12.CutLabelCertificates.Minority024
import Cycle12.CutLabelCertificates.Minority025
import Cycle12.MergedCutGroups.Batch104
import Cycle12.MergedCutGroups.Batch105
import Cycle12.MergedCutGroups.Batch106
import Cycle12.MergedCutGroups.Batch107
import Cycle12.MergedCutGroups.Batch108
import Cycle12.MergedCutGroups.Batch109
import Cycle12.MergedCutGroups.Batch110
import Cycle12.PopulationCertificates.Batch041
import Cycle12.PopulationCertificates.Batch042
import Cycle12.PopulationCertificates.Batch043
import Cycle12.PopulationCertificates.Batch044
import Cycle12.WitnessCertificates.Batch041
import Cycle12.WitnessCertificates.Batch042
import Cycle12.WitnessCertificates.Batch043
import Cycle12.WitnessCertificates.Batch044

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedLocalFailures.Batch000
open Finset SimpleGraph Cycle13 Real

def budgets0 : Fin (MergedCutGroups.Batch104.certificate1248).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority020.certificate416,CutLabelCertificates.Minority020.certificate417,CutLabelCertificates.Minority020.certificate418]
theorem matches0 : (MergedCutGroups.Batch104.certificate1248).LocalMatches CountingCertificates.Batch041.certificate832 budgets0 := by decide +kernel
theorem budgetsSound0 : ∀ l, (budgets0 l).Sound := by
  intro l
  change Fin 3 at l
  fin_cases l
  · exact CutLabelCertificates.Minority020.sound416
  · exact CutLabelCertificates.Minority020.sound417
  · exact CutLabelCertificates.Minority020.sound418
theorem multiplicity0 : (MergedCutGroups.Batch104.certificate1248).cells.length ≤ 456 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound0 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch104.certificate1248).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate832).dm (WitnessCertificates.Batch041.certificate832).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch041.certificate832).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate0).exponent:ℝ)*st.R)+((MergedCutGroups.Batch104.certificate1248).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch104.certificate1248).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch041.certificate832).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch104.certificate1248 CountingCertificates.Batch041.certificate832 budgets0 CutFailureCertificates.Reverse000.certificate0 matches0 rfl rfl
    MergedCutGroups.Batch104.numericValid1248 MergedCutGroups.Batch104.cellsSound1248 MergedCutGroups.Batch104.cellsEntropyValid1248 MergedCutGroups.Batch104.populationMatches1248
    PopulationCertificates.Batch041.valid832 PopulationCertificates.Batch041.sound832 WitnessCertificates.Batch041.valid832 WitnessCertificates.Batch041.sound832 CountingCertificates.Batch041.valid832 CountingCertificates.Batch041.sound832
    budgetsSound0 CutFailureCertificates.Reverse000.sound0 H st hI
theorem probabilityBound0 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch104.certificate1248).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate832).dm (WitnessCertificates.Batch041.certificate832).beta (1/125)) ≤ ((CutFailureCertificates.Budget041.certificate832).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound832 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate832).aa:ℝ)*st.R)+(((912:ℚ):ℝ)*exp (-((MergedCutGroups.Batch104.certificate1248).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate0).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch041.certificate832).omega:ℝ) ≤ ((CutFailureCertificates.Budget041.certificate832).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch104.certificate1248).cells.length:ℝ) ≤ (456:ℝ) := by exact_mod_cast multiplicity0
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch104.certificate1248).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound0 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch041.certificate832).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate0).exponent:ℝ)*st.R)+((MergedCutGroups.Batch104.certificate1248).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch104.certificate1248).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch041.certificate832).aa:ℝ)*st.R)+((912:ℝ)*exp (-((MergedCutGroups.Batch104.certificate1248).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate0).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch041.sound832.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets1 : Fin (MergedCutGroups.Batch104.certificate1252).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority021.certificate420,CutLabelCertificates.Minority021.certificate421,CutLabelCertificates.Minority021.certificate422]
theorem matches1 : (MergedCutGroups.Batch104.certificate1252).LocalMatches CountingCertificates.Batch041.certificate835 budgets1 := by decide +kernel
theorem budgetsSound1 : ∀ l, (budgets1 l).Sound := by
  intro l
  change Fin 3 at l
  fin_cases l
  · exact CutLabelCertificates.Minority021.sound420
  · exact CutLabelCertificates.Minority021.sound421
  · exact CutLabelCertificates.Minority021.sound422
theorem multiplicity1 : (MergedCutGroups.Batch104.certificate1252).cells.length ≤ 456 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound1 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch104.certificate1252).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate835).dm (WitnessCertificates.Batch041.certificate835).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch041.certificate835).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate1).exponent:ℝ)*st.R)+((MergedCutGroups.Batch104.certificate1252).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch104.certificate1252).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch041.certificate835).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch104.certificate1252 CountingCertificates.Batch041.certificate835 budgets1 CutFailureCertificates.Reverse000.certificate1 matches1 rfl rfl
    MergedCutGroups.Batch104.numericValid1252 MergedCutGroups.Batch104.cellsSound1252 MergedCutGroups.Batch104.cellsEntropyValid1252 MergedCutGroups.Batch104.populationMatches1252
    PopulationCertificates.Batch041.valid835 PopulationCertificates.Batch041.sound835 WitnessCertificates.Batch041.valid835 WitnessCertificates.Batch041.sound835 CountingCertificates.Batch041.valid835 CountingCertificates.Batch041.sound835
    budgetsSound1 CutFailureCertificates.Reverse000.sound1 H st hI
theorem probabilityBound1 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch104.certificate1252).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate835).dm (WitnessCertificates.Batch041.certificate835).beta (1/125)) ≤ ((CutFailureCertificates.Budget041.certificate835).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound835 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate835).aa:ℝ)*st.R)+(((912:ℚ):ℝ)*exp (-((MergedCutGroups.Batch104.certificate1252).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate1).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch041.certificate835).omega:ℝ) ≤ ((CutFailureCertificates.Budget041.certificate835).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch104.certificate1252).cells.length:ℝ) ≤ (456:ℝ) := by exact_mod_cast multiplicity1
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch104.certificate1252).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound1 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch041.certificate835).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate1).exponent:ℝ)*st.R)+((MergedCutGroups.Batch104.certificate1252).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch104.certificate1252).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch041.certificate835).aa:ℝ)*st.R)+((912:ℝ)*exp (-((MergedCutGroups.Batch104.certificate1252).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate1).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch041.sound835.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets2 : Fin (MergedCutGroups.Batch104.certificate1256).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority021.certificate424,CutLabelCertificates.Minority021.certificate425,CutLabelCertificates.Minority021.certificate426]
theorem matches2 : (MergedCutGroups.Batch104.certificate1256).LocalMatches CountingCertificates.Batch041.certificate838 budgets2 := by decide +kernel
theorem budgetsSound2 : ∀ l, (budgets2 l).Sound := by
  intro l
  change Fin 3 at l
  fin_cases l
  · exact CutLabelCertificates.Minority021.sound424
  · exact CutLabelCertificates.Minority021.sound425
  · exact CutLabelCertificates.Minority021.sound426
theorem multiplicity2 : (MergedCutGroups.Batch104.certificate1256).cells.length ≤ 456 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound2 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch104.certificate1256).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate838).dm (WitnessCertificates.Batch041.certificate838).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch041.certificate838).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate2).exponent:ℝ)*st.R)+((MergedCutGroups.Batch104.certificate1256).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch104.certificate1256).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch041.certificate838).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch104.certificate1256 CountingCertificates.Batch041.certificate838 budgets2 CutFailureCertificates.Reverse000.certificate2 matches2 rfl rfl
    MergedCutGroups.Batch104.numericValid1256 MergedCutGroups.Batch104.cellsSound1256 MergedCutGroups.Batch104.cellsEntropyValid1256 MergedCutGroups.Batch104.populationMatches1256
    PopulationCertificates.Batch041.valid838 PopulationCertificates.Batch041.sound838 WitnessCertificates.Batch041.valid838 WitnessCertificates.Batch041.sound838 CountingCertificates.Batch041.valid838 CountingCertificates.Batch041.sound838
    budgetsSound2 CutFailureCertificates.Reverse000.sound2 H st hI
theorem probabilityBound2 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch104.certificate1256).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch041.certificate838).dm (WitnessCertificates.Batch041.certificate838).beta (1/125)) ≤ ((CutFailureCertificates.Budget041.certificate838).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget041.sound838 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch041.certificate838).aa:ℝ)*st.R)+(((912:ℚ):ℝ)*exp (-((MergedCutGroups.Batch104.certificate1256).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate2).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch041.certificate838).omega:ℝ) ≤ ((CutFailureCertificates.Budget041.certificate838).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch104.certificate1256).cells.length:ℝ) ≤ (456:ℝ) := by exact_mod_cast multiplicity2
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch104.certificate1256).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound2 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch041.certificate838).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate2).exponent:ℝ)*st.R)+((MergedCutGroups.Batch104.certificate1256).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch104.certificate1256).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch041.certificate838).aa:ℝ)*st.R)+((912:ℝ)*exp (-((MergedCutGroups.Batch104.certificate1256).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate2).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch041.sound838.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets3 : Fin (MergedCutGroups.Batch105.certificate1260).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority021.certificate428,CutLabelCertificates.Minority021.certificate429,CutLabelCertificates.Minority021.certificate430]
theorem matches3 : (MergedCutGroups.Batch105.certificate1260).LocalMatches CountingCertificates.Batch042.certificate841 budgets3 := by decide +kernel
theorem budgetsSound3 : ∀ l, (budgets3 l).Sound := by
  intro l
  change Fin 3 at l
  fin_cases l
  · exact CutLabelCertificates.Minority021.sound428
  · exact CutLabelCertificates.Minority021.sound429
  · exact CutLabelCertificates.Minority021.sound430
theorem multiplicity3 : (MergedCutGroups.Batch105.certificate1260).cells.length ≤ 459 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound3 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch105.certificate1260).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate841).dm (WitnessCertificates.Batch042.certificate841).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch042.certificate841).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate3).exponent:ℝ)*st.R)+((MergedCutGroups.Batch105.certificate1260).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch105.certificate1260).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch042.certificate841).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch105.certificate1260 CountingCertificates.Batch042.certificate841 budgets3 CutFailureCertificates.Reverse000.certificate3 matches3 rfl rfl
    MergedCutGroups.Batch105.numericValid1260 MergedCutGroups.Batch105.cellsSound1260 MergedCutGroups.Batch105.cellsEntropyValid1260 MergedCutGroups.Batch105.populationMatches1260
    PopulationCertificates.Batch042.valid841 PopulationCertificates.Batch042.sound841 WitnessCertificates.Batch042.valid841 WitnessCertificates.Batch042.sound841 CountingCertificates.Batch042.valid841 CountingCertificates.Batch042.sound841
    budgetsSound3 CutFailureCertificates.Reverse000.sound3 H st hI
theorem probabilityBound3 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch105.certificate1260).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate841).dm (WitnessCertificates.Batch042.certificate841).beta (1/125)) ≤ ((CutFailureCertificates.Budget042.certificate841).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound841 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate841).aa:ℝ)*st.R)+(((918:ℚ):ℝ)*exp (-((MergedCutGroups.Batch105.certificate1260).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate3).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch042.certificate841).omega:ℝ) ≤ ((CutFailureCertificates.Budget042.certificate841).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch105.certificate1260).cells.length:ℝ) ≤ (459:ℝ) := by exact_mod_cast multiplicity3
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch105.certificate1260).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound3 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch042.certificate841).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate3).exponent:ℝ)*st.R)+((MergedCutGroups.Batch105.certificate1260).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch105.certificate1260).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch042.certificate841).aa:ℝ)*st.R)+((918:ℝ)*exp (-((MergedCutGroups.Batch105.certificate1260).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate3).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch042.sound841.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets4 : Fin (MergedCutGroups.Batch105.certificate1264).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority021.certificate432,CutLabelCertificates.Minority021.certificate433,CutLabelCertificates.Minority021.certificate434]
theorem matches4 : (MergedCutGroups.Batch105.certificate1264).LocalMatches CountingCertificates.Batch042.certificate844 budgets4 := by decide +kernel
theorem budgetsSound4 : ∀ l, (budgets4 l).Sound := by
  intro l
  change Fin 3 at l
  fin_cases l
  · exact CutLabelCertificates.Minority021.sound432
  · exact CutLabelCertificates.Minority021.sound433
  · exact CutLabelCertificates.Minority021.sound434
theorem multiplicity4 : (MergedCutGroups.Batch105.certificate1264).cells.length ≤ 459 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound4 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch105.certificate1264).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate844).dm (WitnessCertificates.Batch042.certificate844).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch042.certificate844).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate4).exponent:ℝ)*st.R)+((MergedCutGroups.Batch105.certificate1264).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch105.certificate1264).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch042.certificate844).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch105.certificate1264 CountingCertificates.Batch042.certificate844 budgets4 CutFailureCertificates.Reverse000.certificate4 matches4 rfl rfl
    MergedCutGroups.Batch105.numericValid1264 MergedCutGroups.Batch105.cellsSound1264 MergedCutGroups.Batch105.cellsEntropyValid1264 MergedCutGroups.Batch105.populationMatches1264
    PopulationCertificates.Batch042.valid844 PopulationCertificates.Batch042.sound844 WitnessCertificates.Batch042.valid844 WitnessCertificates.Batch042.sound844 CountingCertificates.Batch042.valid844 CountingCertificates.Batch042.sound844
    budgetsSound4 CutFailureCertificates.Reverse000.sound4 H st hI
theorem probabilityBound4 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch105.certificate1264).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate844).dm (WitnessCertificates.Batch042.certificate844).beta (1/125)) ≤ ((CutFailureCertificates.Budget042.certificate844).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound844 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate844).aa:ℝ)*st.R)+(((918:ℚ):ℝ)*exp (-((MergedCutGroups.Batch105.certificate1264).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate4).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch042.certificate844).omega:ℝ) ≤ ((CutFailureCertificates.Budget042.certificate844).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch105.certificate1264).cells.length:ℝ) ≤ (459:ℝ) := by exact_mod_cast multiplicity4
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch105.certificate1264).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound4 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch042.certificate844).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate4).exponent:ℝ)*st.R)+((MergedCutGroups.Batch105.certificate1264).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch105.certificate1264).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch042.certificate844).aa:ℝ)*st.R)+((918:ℝ)*exp (-((MergedCutGroups.Batch105.certificate1264).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate4).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch042.sound844.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets5 : Fin (MergedCutGroups.Batch105.certificate1268).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority021.certificate436,CutLabelCertificates.Minority021.certificate437,CutLabelCertificates.Minority021.certificate438]
theorem matches5 : (MergedCutGroups.Batch105.certificate1268).LocalMatches CountingCertificates.Batch042.certificate847 budgets5 := by decide +kernel
theorem budgetsSound5 : ∀ l, (budgets5 l).Sound := by
  intro l
  change Fin 3 at l
  fin_cases l
  · exact CutLabelCertificates.Minority021.sound436
  · exact CutLabelCertificates.Minority021.sound437
  · exact CutLabelCertificates.Minority021.sound438
theorem multiplicity5 : (MergedCutGroups.Batch105.certificate1268).cells.length ≤ 458 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound5 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch105.certificate1268).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate847).dm (WitnessCertificates.Batch042.certificate847).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch042.certificate847).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate5).exponent:ℝ)*st.R)+((MergedCutGroups.Batch105.certificate1268).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch105.certificate1268).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch042.certificate847).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch105.certificate1268 CountingCertificates.Batch042.certificate847 budgets5 CutFailureCertificates.Reverse000.certificate5 matches5 rfl rfl
    MergedCutGroups.Batch105.numericValid1268 MergedCutGroups.Batch105.cellsSound1268 MergedCutGroups.Batch105.cellsEntropyValid1268 MergedCutGroups.Batch105.populationMatches1268
    PopulationCertificates.Batch042.valid847 PopulationCertificates.Batch042.sound847 WitnessCertificates.Batch042.valid847 WitnessCertificates.Batch042.sound847 CountingCertificates.Batch042.valid847 CountingCertificates.Batch042.sound847
    budgetsSound5 CutFailureCertificates.Reverse000.sound5 H st hI
theorem probabilityBound5 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch105.certificate1268).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate847).dm (WitnessCertificates.Batch042.certificate847).beta (1/125)) ≤ ((CutFailureCertificates.Budget042.certificate847).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound847 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate847).aa:ℝ)*st.R)+(((916:ℚ):ℝ)*exp (-((MergedCutGroups.Batch105.certificate1268).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate5).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch042.certificate847).omega:ℝ) ≤ ((CutFailureCertificates.Budget042.certificate847).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch105.certificate1268).cells.length:ℝ) ≤ (458:ℝ) := by exact_mod_cast multiplicity5
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch105.certificate1268).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound5 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch042.certificate847).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate5).exponent:ℝ)*st.R)+((MergedCutGroups.Batch105.certificate1268).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch105.certificate1268).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch042.certificate847).aa:ℝ)*st.R)+((916:ℝ)*exp (-((MergedCutGroups.Batch105.certificate1268).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate5).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch042.sound847.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets6 : Fin (MergedCutGroups.Batch106.certificate1272).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority022.certificate440,CutLabelCertificates.Minority022.certificate441,CutLabelCertificates.Minority022.certificate442]
theorem matches6 : (MergedCutGroups.Batch106.certificate1272).LocalMatches CountingCertificates.Batch042.certificate850 budgets6 := by decide +kernel
theorem budgetsSound6 : ∀ l, (budgets6 l).Sound := by
  intro l
  change Fin 3 at l
  fin_cases l
  · exact CutLabelCertificates.Minority022.sound440
  · exact CutLabelCertificates.Minority022.sound441
  · exact CutLabelCertificates.Minority022.sound442
theorem multiplicity6 : (MergedCutGroups.Batch106.certificate1272).cells.length ≤ 458 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound6 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch106.certificate1272).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate850).dm (WitnessCertificates.Batch042.certificate850).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch042.certificate850).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate6).exponent:ℝ)*st.R)+((MergedCutGroups.Batch106.certificate1272).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch106.certificate1272).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch042.certificate850).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch106.certificate1272 CountingCertificates.Batch042.certificate850 budgets6 CutFailureCertificates.Reverse000.certificate6 matches6 rfl rfl
    MergedCutGroups.Batch106.numericValid1272 MergedCutGroups.Batch106.cellsSound1272 MergedCutGroups.Batch106.cellsEntropyValid1272 MergedCutGroups.Batch106.populationMatches1272
    PopulationCertificates.Batch042.valid850 PopulationCertificates.Batch042.sound850 WitnessCertificates.Batch042.valid850 WitnessCertificates.Batch042.sound850 CountingCertificates.Batch042.valid850 CountingCertificates.Batch042.sound850
    budgetsSound6 CutFailureCertificates.Reverse000.sound6 H st hI
theorem probabilityBound6 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch106.certificate1272).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate850).dm (WitnessCertificates.Batch042.certificate850).beta (1/125)) ≤ ((CutFailureCertificates.Budget042.certificate850).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound850 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate850).aa:ℝ)*st.R)+(((916:ℚ):ℝ)*exp (-((MergedCutGroups.Batch106.certificate1272).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate6).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch042.certificate850).omega:ℝ) ≤ ((CutFailureCertificates.Budget042.certificate850).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch106.certificate1272).cells.length:ℝ) ≤ (458:ℝ) := by exact_mod_cast multiplicity6
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch106.certificate1272).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound6 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch042.certificate850).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate6).exponent:ℝ)*st.R)+((MergedCutGroups.Batch106.certificate1272).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch106.certificate1272).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch042.certificate850).aa:ℝ)*st.R)+((916:ℝ)*exp (-((MergedCutGroups.Batch106.certificate1272).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate6).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch042.sound850.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets7 : Fin (MergedCutGroups.Batch106.certificate1276).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority022.certificate444,CutLabelCertificates.Minority022.certificate445,CutLabelCertificates.Minority022.certificate446]
theorem matches7 : (MergedCutGroups.Batch106.certificate1276).LocalMatches CountingCertificates.Batch042.certificate853 budgets7 := by decide +kernel
theorem budgetsSound7 : ∀ l, (budgets7 l).Sound := by
  intro l
  change Fin 3 at l
  fin_cases l
  · exact CutLabelCertificates.Minority022.sound444
  · exact CutLabelCertificates.Minority022.sound445
  · exact CutLabelCertificates.Minority022.sound446
theorem multiplicity7 : (MergedCutGroups.Batch106.certificate1276).cells.length ≤ 458 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound7 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch106.certificate1276).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate853).dm (WitnessCertificates.Batch042.certificate853).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch042.certificate853).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate7).exponent:ℝ)*st.R)+((MergedCutGroups.Batch106.certificate1276).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch106.certificate1276).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch042.certificate853).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch106.certificate1276 CountingCertificates.Batch042.certificate853 budgets7 CutFailureCertificates.Reverse000.certificate7 matches7 rfl rfl
    MergedCutGroups.Batch106.numericValid1276 MergedCutGroups.Batch106.cellsSound1276 MergedCutGroups.Batch106.cellsEntropyValid1276 MergedCutGroups.Batch106.populationMatches1276
    PopulationCertificates.Batch042.valid853 PopulationCertificates.Batch042.sound853 WitnessCertificates.Batch042.valid853 WitnessCertificates.Batch042.sound853 CountingCertificates.Batch042.valid853 CountingCertificates.Batch042.sound853
    budgetsSound7 CutFailureCertificates.Reverse000.sound7 H st hI
theorem probabilityBound7 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch106.certificate1276).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate853).dm (WitnessCertificates.Batch042.certificate853).beta (1/125)) ≤ ((CutFailureCertificates.Budget042.certificate853).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound853 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate853).aa:ℝ)*st.R)+(((916:ℚ):ℝ)*exp (-((MergedCutGroups.Batch106.certificate1276).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate7).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch042.certificate853).omega:ℝ) ≤ ((CutFailureCertificates.Budget042.certificate853).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch106.certificate1276).cells.length:ℝ) ≤ (458:ℝ) := by exact_mod_cast multiplicity7
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch106.certificate1276).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound7 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch042.certificate853).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate7).exponent:ℝ)*st.R)+((MergedCutGroups.Batch106.certificate1276).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch106.certificate1276).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch042.certificate853).aa:ℝ)*st.R)+((916:ℝ)*exp (-((MergedCutGroups.Batch106.certificate1276).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate7).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch042.sound853.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets8 : Fin (MergedCutGroups.Batch106.certificate1280).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority022.certificate448,CutLabelCertificates.Minority022.certificate449,CutLabelCertificates.Minority022.certificate450]
theorem matches8 : (MergedCutGroups.Batch106.certificate1280).LocalMatches CountingCertificates.Batch042.certificate856 budgets8 := by decide +kernel
theorem budgetsSound8 : ∀ l, (budgets8 l).Sound := by
  intro l
  change Fin 3 at l
  fin_cases l
  · exact CutLabelCertificates.Minority022.sound448
  · exact CutLabelCertificates.Minority022.sound449
  · exact CutLabelCertificates.Minority022.sound450
theorem multiplicity8 : (MergedCutGroups.Batch106.certificate1280).cells.length ≤ 457 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound8 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch106.certificate1280).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate856).dm (WitnessCertificates.Batch042.certificate856).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch042.certificate856).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate8).exponent:ℝ)*st.R)+((MergedCutGroups.Batch106.certificate1280).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch106.certificate1280).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch042.certificate856).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch106.certificate1280 CountingCertificates.Batch042.certificate856 budgets8 CutFailureCertificates.Reverse000.certificate8 matches8 rfl rfl
    MergedCutGroups.Batch106.numericValid1280 MergedCutGroups.Batch106.cellsSound1280 MergedCutGroups.Batch106.cellsEntropyValid1280 MergedCutGroups.Batch106.populationMatches1280
    PopulationCertificates.Batch042.valid856 PopulationCertificates.Batch042.sound856 WitnessCertificates.Batch042.valid856 WitnessCertificates.Batch042.sound856 CountingCertificates.Batch042.valid856 CountingCertificates.Batch042.sound856
    budgetsSound8 CutFailureCertificates.Reverse000.sound8 H st hI
theorem probabilityBound8 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch106.certificate1280).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate856).dm (WitnessCertificates.Batch042.certificate856).beta (1/125)) ≤ ((CutFailureCertificates.Budget042.certificate856).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound856 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate856).aa:ℝ)*st.R)+(((914:ℚ):ℝ)*exp (-((MergedCutGroups.Batch106.certificate1280).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate8).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch042.certificate856).omega:ℝ) ≤ ((CutFailureCertificates.Budget042.certificate856).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch106.certificate1280).cells.length:ℝ) ≤ (457:ℝ) := by exact_mod_cast multiplicity8
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch106.certificate1280).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound8 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch042.certificate856).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate8).exponent:ℝ)*st.R)+((MergedCutGroups.Batch106.certificate1280).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch106.certificate1280).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch042.certificate856).aa:ℝ)*st.R)+((914:ℝ)*exp (-((MergedCutGroups.Batch106.certificate1280).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate8).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch042.sound856.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets9 : Fin (MergedCutGroups.Batch107.certificate1284).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority022.certificate452,CutLabelCertificates.Minority022.certificate453,CutLabelCertificates.Minority022.certificate454,CutLabelCertificates.Minority022.certificate455]
theorem matches9 : (MergedCutGroups.Batch107.certificate1284).LocalMatches CountingCertificates.Batch042.certificate859 budgets9 := by decide +kernel
theorem budgetsSound9 : ∀ l, (budgets9 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority022.sound452
  · exact CutLabelCertificates.Minority022.sound453
  · exact CutLabelCertificates.Minority022.sound454
  · exact CutLabelCertificates.Minority022.sound455
theorem multiplicity9 : (MergedCutGroups.Batch107.certificate1284).cells.length ≤ 461 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound9 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch107.certificate1284).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate859).dm (WitnessCertificates.Batch042.certificate859).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch042.certificate859).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate9).exponent:ℝ)*st.R)+((MergedCutGroups.Batch107.certificate1284).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch107.certificate1284).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch042.certificate859).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch107.certificate1284 CountingCertificates.Batch042.certificate859 budgets9 CutFailureCertificates.Reverse000.certificate9 matches9 rfl rfl
    MergedCutGroups.Batch107.numericValid1284 MergedCutGroups.Batch107.cellsSound1284 MergedCutGroups.Batch107.cellsEntropyValid1284 MergedCutGroups.Batch107.populationMatches1284
    PopulationCertificates.Batch042.valid859 PopulationCertificates.Batch042.sound859 WitnessCertificates.Batch042.valid859 WitnessCertificates.Batch042.sound859 CountingCertificates.Batch042.valid859 CountingCertificates.Batch042.sound859
    budgetsSound9 CutFailureCertificates.Reverse000.sound9 H st hI
theorem probabilityBound9 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch107.certificate1284).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch042.certificate859).dm (WitnessCertificates.Batch042.certificate859).beta (1/125)) ≤ ((CutFailureCertificates.Budget042.certificate859).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget042.sound859 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch042.certificate859).aa:ℝ)*st.R)+(((922:ℚ):ℝ)*exp (-((MergedCutGroups.Batch107.certificate1284).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate9).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch042.certificate859).omega:ℝ) ≤ ((CutFailureCertificates.Budget042.certificate859).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch107.certificate1284).cells.length:ℝ) ≤ (461:ℝ) := by exact_mod_cast multiplicity9
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch107.certificate1284).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound9 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch042.certificate859).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate9).exponent:ℝ)*st.R)+((MergedCutGroups.Batch107.certificate1284).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch107.certificate1284).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch042.certificate859).aa:ℝ)*st.R)+((922:ℝ)*exp (-((MergedCutGroups.Batch107.certificate1284).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate9).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch042.sound859.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets10 : Fin (MergedCutGroups.Batch107.certificate1288).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority022.certificate457,CutLabelCertificates.Minority022.certificate458,CutLabelCertificates.Minority022.certificate459,CutLabelCertificates.Minority023.certificate460]
theorem matches10 : (MergedCutGroups.Batch107.certificate1288).LocalMatches CountingCertificates.Batch043.certificate862 budgets10 := by decide +kernel
theorem budgetsSound10 : ∀ l, (budgets10 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority022.sound457
  · exact CutLabelCertificates.Minority022.sound458
  · exact CutLabelCertificates.Minority022.sound459
  · exact CutLabelCertificates.Minority023.sound460
theorem multiplicity10 : (MergedCutGroups.Batch107.certificate1288).cells.length ≤ 461 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound10 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch107.certificate1288).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate862).dm (WitnessCertificates.Batch043.certificate862).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch043.certificate862).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate10).exponent:ℝ)*st.R)+((MergedCutGroups.Batch107.certificate1288).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch107.certificate1288).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch043.certificate862).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch107.certificate1288 CountingCertificates.Batch043.certificate862 budgets10 CutFailureCertificates.Reverse000.certificate10 matches10 rfl rfl
    MergedCutGroups.Batch107.numericValid1288 MergedCutGroups.Batch107.cellsSound1288 MergedCutGroups.Batch107.cellsEntropyValid1288 MergedCutGroups.Batch107.populationMatches1288
    PopulationCertificates.Batch043.valid862 PopulationCertificates.Batch043.sound862 WitnessCertificates.Batch043.valid862 WitnessCertificates.Batch043.sound862 CountingCertificates.Batch043.valid862 CountingCertificates.Batch043.sound862
    budgetsSound10 CutFailureCertificates.Reverse000.sound10 H st hI
theorem probabilityBound10 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch107.certificate1288).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate862).dm (WitnessCertificates.Batch043.certificate862).beta (1/125)) ≤ ((CutFailureCertificates.Budget043.certificate862).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound862 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate862).aa:ℝ)*st.R)+(((922:ℚ):ℝ)*exp (-((MergedCutGroups.Batch107.certificate1288).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate10).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch043.certificate862).omega:ℝ) ≤ ((CutFailureCertificates.Budget043.certificate862).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch107.certificate1288).cells.length:ℝ) ≤ (461:ℝ) := by exact_mod_cast multiplicity10
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch107.certificate1288).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound10 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch043.certificate862).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate10).exponent:ℝ)*st.R)+((MergedCutGroups.Batch107.certificate1288).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch107.certificate1288).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch043.certificate862).aa:ℝ)*st.R)+((922:ℝ)*exp (-((MergedCutGroups.Batch107.certificate1288).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate10).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch043.sound862.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets11 : Fin (MergedCutGroups.Batch107.certificate1292).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority023.certificate462,CutLabelCertificates.Minority023.certificate463,CutLabelCertificates.Minority023.certificate464,CutLabelCertificates.Minority023.certificate465]
theorem matches11 : (MergedCutGroups.Batch107.certificate1292).LocalMatches CountingCertificates.Batch043.certificate865 budgets11 := by decide +kernel
theorem budgetsSound11 : ∀ l, (budgets11 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority023.sound462
  · exact CutLabelCertificates.Minority023.sound463
  · exact CutLabelCertificates.Minority023.sound464
  · exact CutLabelCertificates.Minority023.sound465
theorem multiplicity11 : (MergedCutGroups.Batch107.certificate1292).cells.length ≤ 460 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound11 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch107.certificate1292).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate865).dm (WitnessCertificates.Batch043.certificate865).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch043.certificate865).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate11).exponent:ℝ)*st.R)+((MergedCutGroups.Batch107.certificate1292).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch107.certificate1292).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch043.certificate865).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch107.certificate1292 CountingCertificates.Batch043.certificate865 budgets11 CutFailureCertificates.Reverse000.certificate11 matches11 rfl rfl
    MergedCutGroups.Batch107.numericValid1292 MergedCutGroups.Batch107.cellsSound1292 MergedCutGroups.Batch107.cellsEntropyValid1292 MergedCutGroups.Batch107.populationMatches1292
    PopulationCertificates.Batch043.valid865 PopulationCertificates.Batch043.sound865 WitnessCertificates.Batch043.valid865 WitnessCertificates.Batch043.sound865 CountingCertificates.Batch043.valid865 CountingCertificates.Batch043.sound865
    budgetsSound11 CutFailureCertificates.Reverse000.sound11 H st hI
theorem probabilityBound11 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch107.certificate1292).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate865).dm (WitnessCertificates.Batch043.certificate865).beta (1/125)) ≤ ((CutFailureCertificates.Budget043.certificate865).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound865 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate865).aa:ℝ)*st.R)+(((920:ℚ):ℝ)*exp (-((MergedCutGroups.Batch107.certificate1292).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate11).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch043.certificate865).omega:ℝ) ≤ ((CutFailureCertificates.Budget043.certificate865).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch107.certificate1292).cells.length:ℝ) ≤ (460:ℝ) := by exact_mod_cast multiplicity11
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch107.certificate1292).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound11 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch043.certificate865).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate11).exponent:ℝ)*st.R)+((MergedCutGroups.Batch107.certificate1292).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch107.certificate1292).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch043.certificate865).aa:ℝ)*st.R)+((920:ℝ)*exp (-((MergedCutGroups.Batch107.certificate1292).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate11).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch043.sound865.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets12 : Fin (MergedCutGroups.Batch108.certificate1296).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority023.certificate467,CutLabelCertificates.Minority023.certificate468,CutLabelCertificates.Minority023.certificate469,CutLabelCertificates.Minority023.certificate470]
theorem matches12 : (MergedCutGroups.Batch108.certificate1296).LocalMatches CountingCertificates.Batch043.certificate868 budgets12 := by decide +kernel
theorem budgetsSound12 : ∀ l, (budgets12 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority023.sound467
  · exact CutLabelCertificates.Minority023.sound468
  · exact CutLabelCertificates.Minority023.sound469
  · exact CutLabelCertificates.Minority023.sound470
theorem multiplicity12 : (MergedCutGroups.Batch108.certificate1296).cells.length ≤ 460 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound12 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch108.certificate1296).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate868).dm (WitnessCertificates.Batch043.certificate868).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch043.certificate868).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate12).exponent:ℝ)*st.R)+((MergedCutGroups.Batch108.certificate1296).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch108.certificate1296).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch043.certificate868).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch108.certificate1296 CountingCertificates.Batch043.certificate868 budgets12 CutFailureCertificates.Reverse000.certificate12 matches12 rfl rfl
    MergedCutGroups.Batch108.numericValid1296 MergedCutGroups.Batch108.cellsSound1296 MergedCutGroups.Batch108.cellsEntropyValid1296 MergedCutGroups.Batch108.populationMatches1296
    PopulationCertificates.Batch043.valid868 PopulationCertificates.Batch043.sound868 WitnessCertificates.Batch043.valid868 WitnessCertificates.Batch043.sound868 CountingCertificates.Batch043.valid868 CountingCertificates.Batch043.sound868
    budgetsSound12 CutFailureCertificates.Reverse000.sound12 H st hI
theorem probabilityBound12 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch108.certificate1296).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate868).dm (WitnessCertificates.Batch043.certificate868).beta (1/125)) ≤ ((CutFailureCertificates.Budget043.certificate868).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound868 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate868).aa:ℝ)*st.R)+(((920:ℚ):ℝ)*exp (-((MergedCutGroups.Batch108.certificate1296).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate12).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch043.certificate868).omega:ℝ) ≤ ((CutFailureCertificates.Budget043.certificate868).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch108.certificate1296).cells.length:ℝ) ≤ (460:ℝ) := by exact_mod_cast multiplicity12
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch108.certificate1296).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound12 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch043.certificate868).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate12).exponent:ℝ)*st.R)+((MergedCutGroups.Batch108.certificate1296).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch108.certificate1296).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch043.certificate868).aa:ℝ)*st.R)+((920:ℝ)*exp (-((MergedCutGroups.Batch108.certificate1296).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate12).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch043.sound868.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets13 : Fin (MergedCutGroups.Batch108.certificate1300).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority023.certificate472,CutLabelCertificates.Minority023.certificate473,CutLabelCertificates.Minority023.certificate474,CutLabelCertificates.Minority023.certificate475]
theorem matches13 : (MergedCutGroups.Batch108.certificate1300).LocalMatches CountingCertificates.Batch043.certificate871 budgets13 := by decide +kernel
theorem budgetsSound13 : ∀ l, (budgets13 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority023.sound472
  · exact CutLabelCertificates.Minority023.sound473
  · exact CutLabelCertificates.Minority023.sound474
  · exact CutLabelCertificates.Minority023.sound475
theorem multiplicity13 : (MergedCutGroups.Batch108.certificate1300).cells.length ≤ 460 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound13 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch108.certificate1300).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate871).dm (WitnessCertificates.Batch043.certificate871).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch043.certificate871).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate13).exponent:ℝ)*st.R)+((MergedCutGroups.Batch108.certificate1300).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch108.certificate1300).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch043.certificate871).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch108.certificate1300 CountingCertificates.Batch043.certificate871 budgets13 CutFailureCertificates.Reverse000.certificate13 matches13 rfl rfl
    MergedCutGroups.Batch108.numericValid1300 MergedCutGroups.Batch108.cellsSound1300 MergedCutGroups.Batch108.cellsEntropyValid1300 MergedCutGroups.Batch108.populationMatches1300
    PopulationCertificates.Batch043.valid871 PopulationCertificates.Batch043.sound871 WitnessCertificates.Batch043.valid871 WitnessCertificates.Batch043.sound871 CountingCertificates.Batch043.valid871 CountingCertificates.Batch043.sound871
    budgetsSound13 CutFailureCertificates.Reverse000.sound13 H st hI
theorem probabilityBound13 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch108.certificate1300).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate871).dm (WitnessCertificates.Batch043.certificate871).beta (1/125)) ≤ ((CutFailureCertificates.Budget043.certificate871).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound871 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate871).aa:ℝ)*st.R)+(((920:ℚ):ℝ)*exp (-((MergedCutGroups.Batch108.certificate1300).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate13).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch043.certificate871).omega:ℝ) ≤ ((CutFailureCertificates.Budget043.certificate871).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch108.certificate1300).cells.length:ℝ) ≤ (460:ℝ) := by exact_mod_cast multiplicity13
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch108.certificate1300).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound13 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch043.certificate871).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate13).exponent:ℝ)*st.R)+((MergedCutGroups.Batch108.certificate1300).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch108.certificate1300).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch043.certificate871).aa:ℝ)*st.R)+((920:ℝ)*exp (-((MergedCutGroups.Batch108.certificate1300).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate13).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch043.sound871.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets14 : Fin (MergedCutGroups.Batch108.certificate1304).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority023.certificate477,CutLabelCertificates.Minority023.certificate478,CutLabelCertificates.Minority023.certificate479,CutLabelCertificates.Minority024.certificate480]
theorem matches14 : (MergedCutGroups.Batch108.certificate1304).LocalMatches CountingCertificates.Batch043.certificate874 budgets14 := by decide +kernel
theorem budgetsSound14 : ∀ l, (budgets14 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority023.sound477
  · exact CutLabelCertificates.Minority023.sound478
  · exact CutLabelCertificates.Minority023.sound479
  · exact CutLabelCertificates.Minority024.sound480
theorem multiplicity14 : (MergedCutGroups.Batch108.certificate1304).cells.length ≤ 459 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound14 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch108.certificate1304).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate874).dm (WitnessCertificates.Batch043.certificate874).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch043.certificate874).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate14).exponent:ℝ)*st.R)+((MergedCutGroups.Batch108.certificate1304).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch108.certificate1304).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch043.certificate874).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch108.certificate1304 CountingCertificates.Batch043.certificate874 budgets14 CutFailureCertificates.Reverse000.certificate14 matches14 rfl rfl
    MergedCutGroups.Batch108.numericValid1304 MergedCutGroups.Batch108.cellsSound1304 MergedCutGroups.Batch108.cellsEntropyValid1304 MergedCutGroups.Batch108.populationMatches1304
    PopulationCertificates.Batch043.valid874 PopulationCertificates.Batch043.sound874 WitnessCertificates.Batch043.valid874 WitnessCertificates.Batch043.sound874 CountingCertificates.Batch043.valid874 CountingCertificates.Batch043.sound874
    budgetsSound14 CutFailureCertificates.Reverse000.sound14 H st hI
theorem probabilityBound14 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch108.certificate1304).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate874).dm (WitnessCertificates.Batch043.certificate874).beta (1/125)) ≤ ((CutFailureCertificates.Budget043.certificate874).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound874 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate874).aa:ℝ)*st.R)+(((918:ℚ):ℝ)*exp (-((MergedCutGroups.Batch108.certificate1304).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate14).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch043.certificate874).omega:ℝ) ≤ ((CutFailureCertificates.Budget043.certificate874).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch108.certificate1304).cells.length:ℝ) ≤ (459:ℝ) := by exact_mod_cast multiplicity14
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch108.certificate1304).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound14 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch043.certificate874).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate14).exponent:ℝ)*st.R)+((MergedCutGroups.Batch108.certificate1304).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch108.certificate1304).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch043.certificate874).aa:ℝ)*st.R)+((918:ℝ)*exp (-((MergedCutGroups.Batch108.certificate1304).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate14).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch043.sound874.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets15 : Fin (MergedCutGroups.Batch109.certificate1308).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority024.certificate482,CutLabelCertificates.Minority024.certificate483,CutLabelCertificates.Minority024.certificate484,CutLabelCertificates.Minority024.certificate485]
theorem matches15 : (MergedCutGroups.Batch109.certificate1308).LocalMatches CountingCertificates.Batch043.certificate877 budgets15 := by decide +kernel
theorem budgetsSound15 : ∀ l, (budgets15 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority024.sound482
  · exact CutLabelCertificates.Minority024.sound483
  · exact CutLabelCertificates.Minority024.sound484
  · exact CutLabelCertificates.Minority024.sound485
theorem multiplicity15 : (MergedCutGroups.Batch109.certificate1308).cells.length ≤ 459 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound15 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch109.certificate1308).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate877).dm (WitnessCertificates.Batch043.certificate877).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch043.certificate877).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate15).exponent:ℝ)*st.R)+((MergedCutGroups.Batch109.certificate1308).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch109.certificate1308).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch043.certificate877).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch109.certificate1308 CountingCertificates.Batch043.certificate877 budgets15 CutFailureCertificates.Reverse000.certificate15 matches15 rfl rfl
    MergedCutGroups.Batch109.numericValid1308 MergedCutGroups.Batch109.cellsSound1308 MergedCutGroups.Batch109.cellsEntropyValid1308 MergedCutGroups.Batch109.populationMatches1308
    PopulationCertificates.Batch043.valid877 PopulationCertificates.Batch043.sound877 WitnessCertificates.Batch043.valid877 WitnessCertificates.Batch043.sound877 CountingCertificates.Batch043.valid877 CountingCertificates.Batch043.sound877
    budgetsSound15 CutFailureCertificates.Reverse000.sound15 H st hI
theorem probabilityBound15 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch109.certificate1308).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch043.certificate877).dm (WitnessCertificates.Batch043.certificate877).beta (1/125)) ≤ ((CutFailureCertificates.Budget043.certificate877).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget043.sound877 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch043.certificate877).aa:ℝ)*st.R)+(((918:ℚ):ℝ)*exp (-((MergedCutGroups.Batch109.certificate1308).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate15).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch043.certificate877).omega:ℝ) ≤ ((CutFailureCertificates.Budget043.certificate877).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch109.certificate1308).cells.length:ℝ) ≤ (459:ℝ) := by exact_mod_cast multiplicity15
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch109.certificate1308).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound15 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch043.certificate877).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate15).exponent:ℝ)*st.R)+((MergedCutGroups.Batch109.certificate1308).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch109.certificate1308).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch043.certificate877).aa:ℝ)*st.R)+((918:ℝ)*exp (-((MergedCutGroups.Batch109.certificate1308).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate15).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch043.sound877.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets16 : Fin (MergedCutGroups.Batch109.certificate1312).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority024.certificate487,CutLabelCertificates.Minority024.certificate488,CutLabelCertificates.Minority024.certificate489,CutLabelCertificates.Minority024.certificate490]
theorem matches16 : (MergedCutGroups.Batch109.certificate1312).LocalMatches CountingCertificates.Batch044.certificate880 budgets16 := by decide +kernel
theorem budgetsSound16 : ∀ l, (budgets16 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority024.sound487
  · exact CutLabelCertificates.Minority024.sound488
  · exact CutLabelCertificates.Minority024.sound489
  · exact CutLabelCertificates.Minority024.sound490
theorem multiplicity16 : (MergedCutGroups.Batch109.certificate1312).cells.length ≤ 458 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound16 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch109.certificate1312).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate880).dm (WitnessCertificates.Batch044.certificate880).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch044.certificate880).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate16).exponent:ℝ)*st.R)+((MergedCutGroups.Batch109.certificate1312).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch109.certificate1312).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch044.certificate880).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch109.certificate1312 CountingCertificates.Batch044.certificate880 budgets16 CutFailureCertificates.Reverse000.certificate16 matches16 rfl rfl
    MergedCutGroups.Batch109.numericValid1312 MergedCutGroups.Batch109.cellsSound1312 MergedCutGroups.Batch109.cellsEntropyValid1312 MergedCutGroups.Batch109.populationMatches1312
    PopulationCertificates.Batch044.valid880 PopulationCertificates.Batch044.sound880 WitnessCertificates.Batch044.valid880 WitnessCertificates.Batch044.sound880 CountingCertificates.Batch044.valid880 CountingCertificates.Batch044.sound880
    budgetsSound16 CutFailureCertificates.Reverse000.sound16 H st hI
theorem probabilityBound16 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch109.certificate1312).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate880).dm (WitnessCertificates.Batch044.certificate880).beta (1/125)) ≤ ((CutFailureCertificates.Budget044.certificate880).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound880 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate880).aa:ℝ)*st.R)+(((916:ℚ):ℝ)*exp (-((MergedCutGroups.Batch109.certificate1312).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate16).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch044.certificate880).omega:ℝ) ≤ ((CutFailureCertificates.Budget044.certificate880).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch109.certificate1312).cells.length:ℝ) ≤ (458:ℝ) := by exact_mod_cast multiplicity16
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch109.certificate1312).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound16 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch044.certificate880).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate16).exponent:ℝ)*st.R)+((MergedCutGroups.Batch109.certificate1312).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch109.certificate1312).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch044.certificate880).aa:ℝ)*st.R)+((916:ℝ)*exp (-((MergedCutGroups.Batch109.certificate1312).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate16).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch044.sound880.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets17 : Fin (MergedCutGroups.Batch109.certificate1316).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority024.certificate492,CutLabelCertificates.Minority024.certificate493,CutLabelCertificates.Minority024.certificate494,CutLabelCertificates.Minority024.certificate495]
theorem matches17 : (MergedCutGroups.Batch109.certificate1316).LocalMatches CountingCertificates.Batch044.certificate883 budgets17 := by decide +kernel
theorem budgetsSound17 : ∀ l, (budgets17 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority024.sound492
  · exact CutLabelCertificates.Minority024.sound493
  · exact CutLabelCertificates.Minority024.sound494
  · exact CutLabelCertificates.Minority024.sound495
theorem multiplicity17 : (MergedCutGroups.Batch109.certificate1316).cells.length ≤ 460 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound17 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch109.certificate1316).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate883).dm (WitnessCertificates.Batch044.certificate883).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch044.certificate883).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate17).exponent:ℝ)*st.R)+((MergedCutGroups.Batch109.certificate1316).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch109.certificate1316).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch044.certificate883).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch109.certificate1316 CountingCertificates.Batch044.certificate883 budgets17 CutFailureCertificates.Reverse000.certificate17 matches17 rfl rfl
    MergedCutGroups.Batch109.numericValid1316 MergedCutGroups.Batch109.cellsSound1316 MergedCutGroups.Batch109.cellsEntropyValid1316 MergedCutGroups.Batch109.populationMatches1316
    PopulationCertificates.Batch044.valid883 PopulationCertificates.Batch044.sound883 WitnessCertificates.Batch044.valid883 WitnessCertificates.Batch044.sound883 CountingCertificates.Batch044.valid883 CountingCertificates.Batch044.sound883
    budgetsSound17 CutFailureCertificates.Reverse000.sound17 H st hI
theorem probabilityBound17 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch109.certificate1316).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate883).dm (WitnessCertificates.Batch044.certificate883).beta (1/125)) ≤ ((CutFailureCertificates.Budget044.certificate883).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound883 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate883).aa:ℝ)*st.R)+(((920:ℚ):ℝ)*exp (-((MergedCutGroups.Batch109.certificate1316).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate17).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch044.certificate883).omega:ℝ) ≤ ((CutFailureCertificates.Budget044.certificate883).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch109.certificate1316).cells.length:ℝ) ≤ (460:ℝ) := by exact_mod_cast multiplicity17
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch109.certificate1316).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound17 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch044.certificate883).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate17).exponent:ℝ)*st.R)+((MergedCutGroups.Batch109.certificate1316).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch109.certificate1316).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch044.certificate883).aa:ℝ)*st.R)+((920:ℝ)*exp (-((MergedCutGroups.Batch109.certificate1316).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate17).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch044.sound883.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets18 : Fin (MergedCutGroups.Batch110.certificate1320).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority024.certificate497,CutLabelCertificates.Minority024.certificate498,CutLabelCertificates.Minority024.certificate499,CutLabelCertificates.Minority025.certificate500]
theorem matches18 : (MergedCutGroups.Batch110.certificate1320).LocalMatches CountingCertificates.Batch044.certificate886 budgets18 := by decide +kernel
theorem budgetsSound18 : ∀ l, (budgets18 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority024.sound497
  · exact CutLabelCertificates.Minority024.sound498
  · exact CutLabelCertificates.Minority024.sound499
  · exact CutLabelCertificates.Minority025.sound500
theorem multiplicity18 : (MergedCutGroups.Batch110.certificate1320).cells.length ≤ 460 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound18 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch110.certificate1320).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate886).dm (WitnessCertificates.Batch044.certificate886).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch044.certificate886).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate18).exponent:ℝ)*st.R)+((MergedCutGroups.Batch110.certificate1320).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch110.certificate1320).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch044.certificate886).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch110.certificate1320 CountingCertificates.Batch044.certificate886 budgets18 CutFailureCertificates.Reverse000.certificate18 matches18 rfl rfl
    MergedCutGroups.Batch110.numericValid1320 MergedCutGroups.Batch110.cellsSound1320 MergedCutGroups.Batch110.cellsEntropyValid1320 MergedCutGroups.Batch110.populationMatches1320
    PopulationCertificates.Batch044.valid886 PopulationCertificates.Batch044.sound886 WitnessCertificates.Batch044.valid886 WitnessCertificates.Batch044.sound886 CountingCertificates.Batch044.valid886 CountingCertificates.Batch044.sound886
    budgetsSound18 CutFailureCertificates.Reverse000.sound18 H st hI
theorem probabilityBound18 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch110.certificate1320).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate886).dm (WitnessCertificates.Batch044.certificate886).beta (1/125)) ≤ ((CutFailureCertificates.Budget044.certificate886).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound886 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate886).aa:ℝ)*st.R)+(((920:ℚ):ℝ)*exp (-((MergedCutGroups.Batch110.certificate1320).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate18).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch044.certificate886).omega:ℝ) ≤ ((CutFailureCertificates.Budget044.certificate886).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch110.certificate1320).cells.length:ℝ) ≤ (460:ℝ) := by exact_mod_cast multiplicity18
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch110.certificate1320).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound18 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch044.certificate886).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate18).exponent:ℝ)*st.R)+((MergedCutGroups.Batch110.certificate1320).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch110.certificate1320).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch044.certificate886).aa:ℝ)*st.R)+((920:ℝ)*exp (-((MergedCutGroups.Batch110.certificate1320).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate18).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch044.sound886.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets19 : Fin (MergedCutGroups.Batch110.certificate1324).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority025.certificate502,CutLabelCertificates.Minority025.certificate503,CutLabelCertificates.Minority025.certificate504,CutLabelCertificates.Minority025.certificate505]
theorem matches19 : (MergedCutGroups.Batch110.certificate1324).LocalMatches CountingCertificates.Batch044.certificate889 budgets19 := by decide +kernel
theorem budgetsSound19 : ∀ l, (budgets19 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority025.sound502
  · exact CutLabelCertificates.Minority025.sound503
  · exact CutLabelCertificates.Minority025.sound504
  · exact CutLabelCertificates.Minority025.sound505
theorem multiplicity19 : (MergedCutGroups.Batch110.certificate1324).cells.length ≤ 459 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound19 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch110.certificate1324).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate889).dm (WitnessCertificates.Batch044.certificate889).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch044.certificate889).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate19).exponent:ℝ)*st.R)+((MergedCutGroups.Batch110.certificate1324).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch110.certificate1324).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch044.certificate889).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch110.certificate1324 CountingCertificates.Batch044.certificate889 budgets19 CutFailureCertificates.Reverse000.certificate19 matches19 rfl rfl
    MergedCutGroups.Batch110.numericValid1324 MergedCutGroups.Batch110.cellsSound1324 MergedCutGroups.Batch110.cellsEntropyValid1324 MergedCutGroups.Batch110.populationMatches1324
    PopulationCertificates.Batch044.valid889 PopulationCertificates.Batch044.sound889 WitnessCertificates.Batch044.valid889 WitnessCertificates.Batch044.sound889 CountingCertificates.Batch044.valid889 CountingCertificates.Batch044.sound889
    budgetsSound19 CutFailureCertificates.Reverse000.sound19 H st hI
theorem probabilityBound19 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch110.certificate1324).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate889).dm (WitnessCertificates.Batch044.certificate889).beta (1/125)) ≤ ((CutFailureCertificates.Budget044.certificate889).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound889 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate889).aa:ℝ)*st.R)+(((918:ℚ):ℝ)*exp (-((MergedCutGroups.Batch110.certificate1324).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse000.certificate19).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch044.certificate889).omega:ℝ) ≤ ((CutFailureCertificates.Budget044.certificate889).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch110.certificate1324).cells.length:ℝ) ≤ (459:ℝ) := by exact_mod_cast multiplicity19
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch110.certificate1324).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound19 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch044.certificate889).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate19).exponent:ℝ)*st.R)+((MergedCutGroups.Batch110.certificate1324).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch110.certificate1324).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch044.certificate889).aa:ℝ)*st.R)+((918:ℝ)*exp (-((MergedCutGroups.Batch110.certificate1324).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse000.certificate19).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch044.sound889.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

end Cycle12.CertifiedLocalFailures.Batch000
