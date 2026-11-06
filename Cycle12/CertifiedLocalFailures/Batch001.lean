import Cycle12.CertifiedLocalFailure
import Cycle12.CountingCertificates.Batch044
import Cycle12.CountingCertificates.Batch045
import Cycle12.CountingCertificates.Batch046
import Cycle12.CountingCertificates.Batch047
import Cycle12.CutFailureCertificates.Budget044
import Cycle12.CutFailureCertificates.Budget045
import Cycle12.CutFailureCertificates.Budget046
import Cycle12.CutFailureCertificates.Budget047
import Cycle12.CutFailureCertificates.Reverse001
import Cycle12.CutLabelCertificates.Minority025
import Cycle12.CutLabelCertificates.Minority026
import Cycle12.CutLabelCertificates.Minority027
import Cycle12.CutLabelCertificates.Minority028
import Cycle12.CutLabelCertificates.Minority029
import Cycle12.CutLabelCertificates.Minority030
import Cycle12.MergedCutGroups.Batch110
import Cycle12.MergedCutGroups.Batch111
import Cycle12.MergedCutGroups.Batch112
import Cycle12.MergedCutGroups.Batch113
import Cycle12.MergedCutGroups.Batch114
import Cycle12.MergedCutGroups.Batch115
import Cycle12.MergedCutGroups.Batch116
import Cycle12.MergedCutGroups.Batch117
import Cycle12.PopulationCertificates.Batch044
import Cycle12.PopulationCertificates.Batch045
import Cycle12.PopulationCertificates.Batch046
import Cycle12.PopulationCertificates.Batch047
import Cycle12.WitnessCertificates.Batch044
import Cycle12.WitnessCertificates.Batch045
import Cycle12.WitnessCertificates.Batch046
import Cycle12.WitnessCertificates.Batch047

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedLocalFailures.Batch001
open Finset SimpleGraph Cycle13 Real

def budgets20 : Fin (MergedCutGroups.Batch110.certificate1328).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority025.certificate507,CutLabelCertificates.Minority025.certificate508,CutLabelCertificates.Minority025.certificate509,CutLabelCertificates.Minority025.certificate510]
theorem matches20 : (MergedCutGroups.Batch110.certificate1328).LocalMatches CountingCertificates.Batch044.certificate892 budgets20 := by decide +kernel
theorem budgetsSound20 : ∀ l, (budgets20 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority025.sound507
  · exact CutLabelCertificates.Minority025.sound508
  · exact CutLabelCertificates.Minority025.sound509
  · exact CutLabelCertificates.Minority025.sound510
theorem multiplicity20 : (MergedCutGroups.Batch110.certificate1328).cells.length ≤ 459 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound20 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch110.certificate1328).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate892).dm (WitnessCertificates.Batch044.certificate892).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch044.certificate892).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate20).exponent:ℝ)*st.R)+((MergedCutGroups.Batch110.certificate1328).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch110.certificate1328).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch044.certificate892).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch110.certificate1328 CountingCertificates.Batch044.certificate892 budgets20 CutFailureCertificates.Reverse001.certificate20 matches20 rfl rfl
    MergedCutGroups.Batch110.numericValid1328 MergedCutGroups.Batch110.cellsSound1328 MergedCutGroups.Batch110.cellsEntropyValid1328 MergedCutGroups.Batch110.populationMatches1328
    PopulationCertificates.Batch044.valid892 PopulationCertificates.Batch044.sound892 WitnessCertificates.Batch044.valid892 WitnessCertificates.Batch044.sound892 CountingCertificates.Batch044.valid892 CountingCertificates.Batch044.sound892
    budgetsSound20 CutFailureCertificates.Reverse001.sound20 H st hI
theorem probabilityBound20 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch110.certificate1328).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate892).dm (WitnessCertificates.Batch044.certificate892).beta (1/125)) ≤ ((CutFailureCertificates.Budget044.certificate892).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound892 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate892).aa:ℝ)*st.R)+(((918:ℚ):ℝ)*exp (-((MergedCutGroups.Batch110.certificate1328).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate20).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch044.certificate892).omega:ℝ) ≤ ((CutFailureCertificates.Budget044.certificate892).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch110.certificate1328).cells.length:ℝ) ≤ (459:ℝ) := by exact_mod_cast multiplicity20
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch110.certificate1328).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound20 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch044.certificate892).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate20).exponent:ℝ)*st.R)+((MergedCutGroups.Batch110.certificate1328).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch110.certificate1328).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch044.certificate892).aa:ℝ)*st.R)+((918:ℝ)*exp (-((MergedCutGroups.Batch110.certificate1328).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate20).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch044.sound892.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets21 : Fin (MergedCutGroups.Batch111.certificate1332).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority025.certificate512,CutLabelCertificates.Minority025.certificate513,CutLabelCertificates.Minority025.certificate514,CutLabelCertificates.Minority025.certificate515]
theorem matches21 : (MergedCutGroups.Batch111.certificate1332).LocalMatches CountingCertificates.Batch044.certificate895 budgets21 := by decide +kernel
theorem budgetsSound21 : ∀ l, (budgets21 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority025.sound512
  · exact CutLabelCertificates.Minority025.sound513
  · exact CutLabelCertificates.Minority025.sound514
  · exact CutLabelCertificates.Minority025.sound515
theorem multiplicity21 : (MergedCutGroups.Batch111.certificate1332).cells.length ≤ 458 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound21 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch111.certificate1332).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate895).dm (WitnessCertificates.Batch044.certificate895).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch044.certificate895).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate21).exponent:ℝ)*st.R)+((MergedCutGroups.Batch111.certificate1332).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch111.certificate1332).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch044.certificate895).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch111.certificate1332 CountingCertificates.Batch044.certificate895 budgets21 CutFailureCertificates.Reverse001.certificate21 matches21 rfl rfl
    MergedCutGroups.Batch111.numericValid1332 MergedCutGroups.Batch111.cellsSound1332 MergedCutGroups.Batch111.cellsEntropyValid1332 MergedCutGroups.Batch111.populationMatches1332
    PopulationCertificates.Batch044.valid895 PopulationCertificates.Batch044.sound895 WitnessCertificates.Batch044.valid895 WitnessCertificates.Batch044.sound895 CountingCertificates.Batch044.valid895 CountingCertificates.Batch044.sound895
    budgetsSound21 CutFailureCertificates.Reverse001.sound21 H st hI
theorem probabilityBound21 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch111.certificate1332).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate895).dm (WitnessCertificates.Batch044.certificate895).beta (1/125)) ≤ ((CutFailureCertificates.Budget044.certificate895).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound895 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate895).aa:ℝ)*st.R)+(((916:ℚ):ℝ)*exp (-((MergedCutGroups.Batch111.certificate1332).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate21).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch044.certificate895).omega:ℝ) ≤ ((CutFailureCertificates.Budget044.certificate895).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch111.certificate1332).cells.length:ℝ) ≤ (458:ℝ) := by exact_mod_cast multiplicity21
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch111.certificate1332).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound21 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch044.certificate895).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate21).exponent:ℝ)*st.R)+((MergedCutGroups.Batch111.certificate1332).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch111.certificate1332).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch044.certificate895).aa:ℝ)*st.R)+((916:ℝ)*exp (-((MergedCutGroups.Batch111.certificate1332).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate21).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch044.sound895.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets22 : Fin (MergedCutGroups.Batch111.certificate1336).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority025.certificate517,CutLabelCertificates.Minority025.certificate518,CutLabelCertificates.Minority025.certificate519,CutLabelCertificates.Minority026.certificate520]
theorem matches22 : (MergedCutGroups.Batch111.certificate1336).LocalMatches CountingCertificates.Batch044.certificate898 budgets22 := by decide +kernel
theorem budgetsSound22 : ∀ l, (budgets22 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority025.sound517
  · exact CutLabelCertificates.Minority025.sound518
  · exact CutLabelCertificates.Minority025.sound519
  · exact CutLabelCertificates.Minority026.sound520
theorem multiplicity22 : (MergedCutGroups.Batch111.certificate1336).cells.length ≤ 462 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound22 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch111.certificate1336).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate898).dm (WitnessCertificates.Batch044.certificate898).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch044.certificate898).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate22).exponent:ℝ)*st.R)+((MergedCutGroups.Batch111.certificate1336).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch111.certificate1336).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch044.certificate898).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch111.certificate1336 CountingCertificates.Batch044.certificate898 budgets22 CutFailureCertificates.Reverse001.certificate22 matches22 rfl rfl
    MergedCutGroups.Batch111.numericValid1336 MergedCutGroups.Batch111.cellsSound1336 MergedCutGroups.Batch111.cellsEntropyValid1336 MergedCutGroups.Batch111.populationMatches1336
    PopulationCertificates.Batch044.valid898 PopulationCertificates.Batch044.sound898 WitnessCertificates.Batch044.valid898 WitnessCertificates.Batch044.sound898 CountingCertificates.Batch044.valid898 CountingCertificates.Batch044.sound898
    budgetsSound22 CutFailureCertificates.Reverse001.sound22 H st hI
theorem probabilityBound22 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch111.certificate1336).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch044.certificate898).dm (WitnessCertificates.Batch044.certificate898).beta (1/125)) ≤ ((CutFailureCertificates.Budget044.certificate898).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget044.sound898 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch044.certificate898).aa:ℝ)*st.R)+(((924:ℚ):ℝ)*exp (-((MergedCutGroups.Batch111.certificate1336).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate22).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch044.certificate898).omega:ℝ) ≤ ((CutFailureCertificates.Budget044.certificate898).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch111.certificate1336).cells.length:ℝ) ≤ (462:ℝ) := by exact_mod_cast multiplicity22
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch111.certificate1336).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound22 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch044.certificate898).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate22).exponent:ℝ)*st.R)+((MergedCutGroups.Batch111.certificate1336).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch111.certificate1336).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch044.certificate898).aa:ℝ)*st.R)+((924:ℝ)*exp (-((MergedCutGroups.Batch111.certificate1336).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate22).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch044.sound898.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets23 : Fin (MergedCutGroups.Batch111.certificate1340).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority026.certificate522,CutLabelCertificates.Minority026.certificate523,CutLabelCertificates.Minority026.certificate524,CutLabelCertificates.Minority026.certificate525]
theorem matches23 : (MergedCutGroups.Batch111.certificate1340).LocalMatches CountingCertificates.Batch045.certificate901 budgets23 := by decide +kernel
theorem budgetsSound23 : ∀ l, (budgets23 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority026.sound522
  · exact CutLabelCertificates.Minority026.sound523
  · exact CutLabelCertificates.Minority026.sound524
  · exact CutLabelCertificates.Minority026.sound525
theorem multiplicity23 : (MergedCutGroups.Batch111.certificate1340).cells.length ≤ 461 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound23 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch111.certificate1340).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate901).dm (WitnessCertificates.Batch045.certificate901).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch045.certificate901).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate23).exponent:ℝ)*st.R)+((MergedCutGroups.Batch111.certificate1340).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch111.certificate1340).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch045.certificate901).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch111.certificate1340 CountingCertificates.Batch045.certificate901 budgets23 CutFailureCertificates.Reverse001.certificate23 matches23 rfl rfl
    MergedCutGroups.Batch111.numericValid1340 MergedCutGroups.Batch111.cellsSound1340 MergedCutGroups.Batch111.cellsEntropyValid1340 MergedCutGroups.Batch111.populationMatches1340
    PopulationCertificates.Batch045.valid901 PopulationCertificates.Batch045.sound901 WitnessCertificates.Batch045.valid901 WitnessCertificates.Batch045.sound901 CountingCertificates.Batch045.valid901 CountingCertificates.Batch045.sound901
    budgetsSound23 CutFailureCertificates.Reverse001.sound23 H st hI
theorem probabilityBound23 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch111.certificate1340).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate901).dm (WitnessCertificates.Batch045.certificate901).beta (1/125)) ≤ ((CutFailureCertificates.Budget045.certificate901).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound901 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate901).aa:ℝ)*st.R)+(((922:ℚ):ℝ)*exp (-((MergedCutGroups.Batch111.certificate1340).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate23).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch045.certificate901).omega:ℝ) ≤ ((CutFailureCertificates.Budget045.certificate901).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch111.certificate1340).cells.length:ℝ) ≤ (461:ℝ) := by exact_mod_cast multiplicity23
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch111.certificate1340).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound23 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch045.certificate901).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate23).exponent:ℝ)*st.R)+((MergedCutGroups.Batch111.certificate1340).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch111.certificate1340).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch045.certificate901).aa:ℝ)*st.R)+((922:ℝ)*exp (-((MergedCutGroups.Batch111.certificate1340).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate23).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch045.sound901.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets24 : Fin (MergedCutGroups.Batch112.certificate1344).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority026.certificate527,CutLabelCertificates.Minority026.certificate528,CutLabelCertificates.Minority026.certificate529,CutLabelCertificates.Minority026.certificate530]
theorem matches24 : (MergedCutGroups.Batch112.certificate1344).LocalMatches CountingCertificates.Batch045.certificate904 budgets24 := by decide +kernel
theorem budgetsSound24 : ∀ l, (budgets24 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority026.sound527
  · exact CutLabelCertificates.Minority026.sound528
  · exact CutLabelCertificates.Minority026.sound529
  · exact CutLabelCertificates.Minority026.sound530
theorem multiplicity24 : (MergedCutGroups.Batch112.certificate1344).cells.length ≤ 461 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound24 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch112.certificate1344).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate904).dm (WitnessCertificates.Batch045.certificate904).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch045.certificate904).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate24).exponent:ℝ)*st.R)+((MergedCutGroups.Batch112.certificate1344).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch112.certificate1344).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch045.certificate904).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch112.certificate1344 CountingCertificates.Batch045.certificate904 budgets24 CutFailureCertificates.Reverse001.certificate24 matches24 rfl rfl
    MergedCutGroups.Batch112.numericValid1344 MergedCutGroups.Batch112.cellsSound1344 MergedCutGroups.Batch112.cellsEntropyValid1344 MergedCutGroups.Batch112.populationMatches1344
    PopulationCertificates.Batch045.valid904 PopulationCertificates.Batch045.sound904 WitnessCertificates.Batch045.valid904 WitnessCertificates.Batch045.sound904 CountingCertificates.Batch045.valid904 CountingCertificates.Batch045.sound904
    budgetsSound24 CutFailureCertificates.Reverse001.sound24 H st hI
theorem probabilityBound24 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch112.certificate1344).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate904).dm (WitnessCertificates.Batch045.certificate904).beta (1/125)) ≤ ((CutFailureCertificates.Budget045.certificate904).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound904 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate904).aa:ℝ)*st.R)+(((922:ℚ):ℝ)*exp (-((MergedCutGroups.Batch112.certificate1344).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate24).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch045.certificate904).omega:ℝ) ≤ ((CutFailureCertificates.Budget045.certificate904).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch112.certificate1344).cells.length:ℝ) ≤ (461:ℝ) := by exact_mod_cast multiplicity24
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch112.certificate1344).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound24 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch045.certificate904).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate24).exponent:ℝ)*st.R)+((MergedCutGroups.Batch112.certificate1344).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch112.certificate1344).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch045.certificate904).aa:ℝ)*st.R)+((922:ℝ)*exp (-((MergedCutGroups.Batch112.certificate1344).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate24).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch045.sound904.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets25 : Fin (MergedCutGroups.Batch112.certificate1348).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority026.certificate532,CutLabelCertificates.Minority026.certificate533,CutLabelCertificates.Minority026.certificate534,CutLabelCertificates.Minority026.certificate535]
theorem matches25 : (MergedCutGroups.Batch112.certificate1348).LocalMatches CountingCertificates.Batch045.certificate907 budgets25 := by decide +kernel
theorem budgetsSound25 : ∀ l, (budgets25 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority026.sound532
  · exact CutLabelCertificates.Minority026.sound533
  · exact CutLabelCertificates.Minority026.sound534
  · exact CutLabelCertificates.Minority026.sound535
theorem multiplicity25 : (MergedCutGroups.Batch112.certificate1348).cells.length ≤ 460 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound25 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch112.certificate1348).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate907).dm (WitnessCertificates.Batch045.certificate907).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch045.certificate907).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate25).exponent:ℝ)*st.R)+((MergedCutGroups.Batch112.certificate1348).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch112.certificate1348).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch045.certificate907).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch112.certificate1348 CountingCertificates.Batch045.certificate907 budgets25 CutFailureCertificates.Reverse001.certificate25 matches25 rfl rfl
    MergedCutGroups.Batch112.numericValid1348 MergedCutGroups.Batch112.cellsSound1348 MergedCutGroups.Batch112.cellsEntropyValid1348 MergedCutGroups.Batch112.populationMatches1348
    PopulationCertificates.Batch045.valid907 PopulationCertificates.Batch045.sound907 WitnessCertificates.Batch045.valid907 WitnessCertificates.Batch045.sound907 CountingCertificates.Batch045.valid907 CountingCertificates.Batch045.sound907
    budgetsSound25 CutFailureCertificates.Reverse001.sound25 H st hI
theorem probabilityBound25 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch112.certificate1348).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate907).dm (WitnessCertificates.Batch045.certificate907).beta (1/125)) ≤ ((CutFailureCertificates.Budget045.certificate907).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound907 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate907).aa:ℝ)*st.R)+(((920:ℚ):ℝ)*exp (-((MergedCutGroups.Batch112.certificate1348).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate25).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch045.certificate907).omega:ℝ) ≤ ((CutFailureCertificates.Budget045.certificate907).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch112.certificate1348).cells.length:ℝ) ≤ (460:ℝ) := by exact_mod_cast multiplicity25
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch112.certificate1348).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound25 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch045.certificate907).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate25).exponent:ℝ)*st.R)+((MergedCutGroups.Batch112.certificate1348).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch112.certificate1348).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch045.certificate907).aa:ℝ)*st.R)+((920:ℝ)*exp (-((MergedCutGroups.Batch112.certificate1348).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate25).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch045.sound907.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets26 : Fin (MergedCutGroups.Batch112.certificate1352).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority026.certificate537,CutLabelCertificates.Minority026.certificate538,CutLabelCertificates.Minority026.certificate539,CutLabelCertificates.Minority027.certificate540]
theorem matches26 : (MergedCutGroups.Batch112.certificate1352).LocalMatches CountingCertificates.Batch045.certificate910 budgets26 := by decide +kernel
theorem budgetsSound26 : ∀ l, (budgets26 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority026.sound537
  · exact CutLabelCertificates.Minority026.sound538
  · exact CutLabelCertificates.Minority026.sound539
  · exact CutLabelCertificates.Minority027.sound540
theorem multiplicity26 : (MergedCutGroups.Batch112.certificate1352).cells.length ≤ 459 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound26 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch112.certificate1352).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate910).dm (WitnessCertificates.Batch045.certificate910).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch045.certificate910).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate26).exponent:ℝ)*st.R)+((MergedCutGroups.Batch112.certificate1352).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch112.certificate1352).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch045.certificate910).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch112.certificate1352 CountingCertificates.Batch045.certificate910 budgets26 CutFailureCertificates.Reverse001.certificate26 matches26 rfl rfl
    MergedCutGroups.Batch112.numericValid1352 MergedCutGroups.Batch112.cellsSound1352 MergedCutGroups.Batch112.cellsEntropyValid1352 MergedCutGroups.Batch112.populationMatches1352
    PopulationCertificates.Batch045.valid910 PopulationCertificates.Batch045.sound910 WitnessCertificates.Batch045.valid910 WitnessCertificates.Batch045.sound910 CountingCertificates.Batch045.valid910 CountingCertificates.Batch045.sound910
    budgetsSound26 CutFailureCertificates.Reverse001.sound26 H st hI
theorem probabilityBound26 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch112.certificate1352).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate910).dm (WitnessCertificates.Batch045.certificate910).beta (1/125)) ≤ ((CutFailureCertificates.Budget045.certificate910).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound910 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate910).aa:ℝ)*st.R)+(((918:ℚ):ℝ)*exp (-((MergedCutGroups.Batch112.certificate1352).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate26).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch045.certificate910).omega:ℝ) ≤ ((CutFailureCertificates.Budget045.certificate910).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch112.certificate1352).cells.length:ℝ) ≤ (459:ℝ) := by exact_mod_cast multiplicity26
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch112.certificate1352).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound26 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch045.certificate910).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate26).exponent:ℝ)*st.R)+((MergedCutGroups.Batch112.certificate1352).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch112.certificate1352).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch045.certificate910).aa:ℝ)*st.R)+((918:ℝ)*exp (-((MergedCutGroups.Batch112.certificate1352).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate26).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch045.sound910.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets27 : Fin (MergedCutGroups.Batch113.certificate1356).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority027.certificate542,CutLabelCertificates.Minority027.certificate543,CutLabelCertificates.Minority027.certificate544,CutLabelCertificates.Minority027.certificate545]
theorem matches27 : (MergedCutGroups.Batch113.certificate1356).LocalMatches CountingCertificates.Batch045.certificate913 budgets27 := by decide +kernel
theorem budgetsSound27 : ∀ l, (budgets27 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority027.sound542
  · exact CutLabelCertificates.Minority027.sound543
  · exact CutLabelCertificates.Minority027.sound544
  · exact CutLabelCertificates.Minority027.sound545
theorem multiplicity27 : (MergedCutGroups.Batch113.certificate1356).cells.length ≤ 460 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound27 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch113.certificate1356).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate913).dm (WitnessCertificates.Batch045.certificate913).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch045.certificate913).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate27).exponent:ℝ)*st.R)+((MergedCutGroups.Batch113.certificate1356).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch113.certificate1356).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch045.certificate913).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch113.certificate1356 CountingCertificates.Batch045.certificate913 budgets27 CutFailureCertificates.Reverse001.certificate27 matches27 rfl rfl
    MergedCutGroups.Batch113.numericValid1356 MergedCutGroups.Batch113.cellsSound1356 MergedCutGroups.Batch113.cellsEntropyValid1356 MergedCutGroups.Batch113.populationMatches1356
    PopulationCertificates.Batch045.valid913 PopulationCertificates.Batch045.sound913 WitnessCertificates.Batch045.valid913 WitnessCertificates.Batch045.sound913 CountingCertificates.Batch045.valid913 CountingCertificates.Batch045.sound913
    budgetsSound27 CutFailureCertificates.Reverse001.sound27 H st hI
theorem probabilityBound27 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch113.certificate1356).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate913).dm (WitnessCertificates.Batch045.certificate913).beta (1/125)) ≤ ((CutFailureCertificates.Budget045.certificate913).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound913 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate913).aa:ℝ)*st.R)+(((920:ℚ):ℝ)*exp (-((MergedCutGroups.Batch113.certificate1356).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate27).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch045.certificate913).omega:ℝ) ≤ ((CutFailureCertificates.Budget045.certificate913).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch113.certificate1356).cells.length:ℝ) ≤ (460:ℝ) := by exact_mod_cast multiplicity27
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch113.certificate1356).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound27 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch045.certificate913).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate27).exponent:ℝ)*st.R)+((MergedCutGroups.Batch113.certificate1356).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch113.certificate1356).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch045.certificate913).aa:ℝ)*st.R)+((920:ℝ)*exp (-((MergedCutGroups.Batch113.certificate1356).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate27).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch045.sound913.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets28 : Fin (MergedCutGroups.Batch113.certificate1360).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority027.certificate547,CutLabelCertificates.Minority027.certificate548,CutLabelCertificates.Minority027.certificate549,CutLabelCertificates.Minority027.certificate550]
theorem matches28 : (MergedCutGroups.Batch113.certificate1360).LocalMatches CountingCertificates.Batch045.certificate916 budgets28 := by decide +kernel
theorem budgetsSound28 : ∀ l, (budgets28 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority027.sound547
  · exact CutLabelCertificates.Minority027.sound548
  · exact CutLabelCertificates.Minority027.sound549
  · exact CutLabelCertificates.Minority027.sound550
theorem multiplicity28 : (MergedCutGroups.Batch113.certificate1360).cells.length ≤ 460 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound28 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch113.certificate1360).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate916).dm (WitnessCertificates.Batch045.certificate916).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch045.certificate916).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate28).exponent:ℝ)*st.R)+((MergedCutGroups.Batch113.certificate1360).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch113.certificate1360).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch045.certificate916).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch113.certificate1360 CountingCertificates.Batch045.certificate916 budgets28 CutFailureCertificates.Reverse001.certificate28 matches28 rfl rfl
    MergedCutGroups.Batch113.numericValid1360 MergedCutGroups.Batch113.cellsSound1360 MergedCutGroups.Batch113.cellsEntropyValid1360 MergedCutGroups.Batch113.populationMatches1360
    PopulationCertificates.Batch045.valid916 PopulationCertificates.Batch045.sound916 WitnessCertificates.Batch045.valid916 WitnessCertificates.Batch045.sound916 CountingCertificates.Batch045.valid916 CountingCertificates.Batch045.sound916
    budgetsSound28 CutFailureCertificates.Reverse001.sound28 H st hI
theorem probabilityBound28 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch113.certificate1360).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate916).dm (WitnessCertificates.Batch045.certificate916).beta (1/125)) ≤ ((CutFailureCertificates.Budget045.certificate916).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound916 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate916).aa:ℝ)*st.R)+(((920:ℚ):ℝ)*exp (-((MergedCutGroups.Batch113.certificate1360).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate28).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch045.certificate916).omega:ℝ) ≤ ((CutFailureCertificates.Budget045.certificate916).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch113.certificate1360).cells.length:ℝ) ≤ (460:ℝ) := by exact_mod_cast multiplicity28
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch113.certificate1360).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound28 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch045.certificate916).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate28).exponent:ℝ)*st.R)+((MergedCutGroups.Batch113.certificate1360).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch113.certificate1360).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch045.certificate916).aa:ℝ)*st.R)+((920:ℝ)*exp (-((MergedCutGroups.Batch113.certificate1360).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate28).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch045.sound916.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets29 : Fin (MergedCutGroups.Batch113.certificate1364).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority027.certificate552,CutLabelCertificates.Minority027.certificate553,CutLabelCertificates.Minority027.certificate554,CutLabelCertificates.Minority027.certificate555]
theorem matches29 : (MergedCutGroups.Batch113.certificate1364).LocalMatches CountingCertificates.Batch045.certificate919 budgets29 := by decide +kernel
theorem budgetsSound29 : ∀ l, (budgets29 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority027.sound552
  · exact CutLabelCertificates.Minority027.sound553
  · exact CutLabelCertificates.Minority027.sound554
  · exact CutLabelCertificates.Minority027.sound555
theorem multiplicity29 : (MergedCutGroups.Batch113.certificate1364).cells.length ≤ 459 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound29 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch113.certificate1364).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate919).dm (WitnessCertificates.Batch045.certificate919).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch045.certificate919).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate29).exponent:ℝ)*st.R)+((MergedCutGroups.Batch113.certificate1364).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch113.certificate1364).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch045.certificate919).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch113.certificate1364 CountingCertificates.Batch045.certificate919 budgets29 CutFailureCertificates.Reverse001.certificate29 matches29 rfl rfl
    MergedCutGroups.Batch113.numericValid1364 MergedCutGroups.Batch113.cellsSound1364 MergedCutGroups.Batch113.cellsEntropyValid1364 MergedCutGroups.Batch113.populationMatches1364
    PopulationCertificates.Batch045.valid919 PopulationCertificates.Batch045.sound919 WitnessCertificates.Batch045.valid919 WitnessCertificates.Batch045.sound919 CountingCertificates.Batch045.valid919 CountingCertificates.Batch045.sound919
    budgetsSound29 CutFailureCertificates.Reverse001.sound29 H st hI
theorem probabilityBound29 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch113.certificate1364).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch045.certificate919).dm (WitnessCertificates.Batch045.certificate919).beta (1/125)) ≤ ((CutFailureCertificates.Budget045.certificate919).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound919 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate919).aa:ℝ)*st.R)+(((918:ℚ):ℝ)*exp (-((MergedCutGroups.Batch113.certificate1364).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate29).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch045.certificate919).omega:ℝ) ≤ ((CutFailureCertificates.Budget045.certificate919).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch113.certificate1364).cells.length:ℝ) ≤ (459:ℝ) := by exact_mod_cast multiplicity29
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch113.certificate1364).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound29 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch045.certificate919).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate29).exponent:ℝ)*st.R)+((MergedCutGroups.Batch113.certificate1364).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch113.certificate1364).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch045.certificate919).aa:ℝ)*st.R)+((918:ℝ)*exp (-((MergedCutGroups.Batch113.certificate1364).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate29).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch045.sound919.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets30 : Fin (MergedCutGroups.Batch114.certificate1368).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority027.certificate557,CutLabelCertificates.Minority027.certificate558,CutLabelCertificates.Minority027.certificate559,CutLabelCertificates.Minority028.certificate560]
theorem matches30 : (MergedCutGroups.Batch114.certificate1368).LocalMatches CountingCertificates.Batch046.certificate922 budgets30 := by decide +kernel
theorem budgetsSound30 : ∀ l, (budgets30 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority027.sound557
  · exact CutLabelCertificates.Minority027.sound558
  · exact CutLabelCertificates.Minority027.sound559
  · exact CutLabelCertificates.Minority028.sound560
theorem multiplicity30 : (MergedCutGroups.Batch114.certificate1368).cells.length ≤ 459 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound30 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch114.certificate1368).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate922).dm (WitnessCertificates.Batch046.certificate922).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch046.certificate922).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate30).exponent:ℝ)*st.R)+((MergedCutGroups.Batch114.certificate1368).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch114.certificate1368).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch046.certificate922).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch114.certificate1368 CountingCertificates.Batch046.certificate922 budgets30 CutFailureCertificates.Reverse001.certificate30 matches30 rfl rfl
    MergedCutGroups.Batch114.numericValid1368 MergedCutGroups.Batch114.cellsSound1368 MergedCutGroups.Batch114.cellsEntropyValid1368 MergedCutGroups.Batch114.populationMatches1368
    PopulationCertificates.Batch046.valid922 PopulationCertificates.Batch046.sound922 WitnessCertificates.Batch046.valid922 WitnessCertificates.Batch046.sound922 CountingCertificates.Batch046.valid922 CountingCertificates.Batch046.sound922
    budgetsSound30 CutFailureCertificates.Reverse001.sound30 H st hI
theorem probabilityBound30 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch114.certificate1368).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate922).dm (WitnessCertificates.Batch046.certificate922).beta (1/125)) ≤ ((CutFailureCertificates.Budget046.certificate922).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound922 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate922).aa:ℝ)*st.R)+(((918:ℚ):ℝ)*exp (-((MergedCutGroups.Batch114.certificate1368).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate30).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch046.certificate922).omega:ℝ) ≤ ((CutFailureCertificates.Budget046.certificate922).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch114.certificate1368).cells.length:ℝ) ≤ (459:ℝ) := by exact_mod_cast multiplicity30
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch114.certificate1368).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound30 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch046.certificate922).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate30).exponent:ℝ)*st.R)+((MergedCutGroups.Batch114.certificate1368).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch114.certificate1368).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch046.certificate922).aa:ℝ)*st.R)+((918:ℝ)*exp (-((MergedCutGroups.Batch114.certificate1368).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate30).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch046.sound922.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets31 : Fin (MergedCutGroups.Batch114.certificate1372).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority028.certificate562,CutLabelCertificates.Minority028.certificate563,CutLabelCertificates.Minority028.certificate564,CutLabelCertificates.Minority028.certificate565]
theorem matches31 : (MergedCutGroups.Batch114.certificate1372).LocalMatches CountingCertificates.Batch046.certificate925 budgets31 := by decide +kernel
theorem budgetsSound31 : ∀ l, (budgets31 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority028.sound562
  · exact CutLabelCertificates.Minority028.sound563
  · exact CutLabelCertificates.Minority028.sound564
  · exact CutLabelCertificates.Minority028.sound565
theorem multiplicity31 : (MergedCutGroups.Batch114.certificate1372).cells.length ≤ 458 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound31 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch114.certificate1372).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate925).dm (WitnessCertificates.Batch046.certificate925).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch046.certificate925).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate31).exponent:ℝ)*st.R)+((MergedCutGroups.Batch114.certificate1372).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch114.certificate1372).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch046.certificate925).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch114.certificate1372 CountingCertificates.Batch046.certificate925 budgets31 CutFailureCertificates.Reverse001.certificate31 matches31 rfl rfl
    MergedCutGroups.Batch114.numericValid1372 MergedCutGroups.Batch114.cellsSound1372 MergedCutGroups.Batch114.cellsEntropyValid1372 MergedCutGroups.Batch114.populationMatches1372
    PopulationCertificates.Batch046.valid925 PopulationCertificates.Batch046.sound925 WitnessCertificates.Batch046.valid925 WitnessCertificates.Batch046.sound925 CountingCertificates.Batch046.valid925 CountingCertificates.Batch046.sound925
    budgetsSound31 CutFailureCertificates.Reverse001.sound31 H st hI
theorem probabilityBound31 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch114.certificate1372).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate925).dm (WitnessCertificates.Batch046.certificate925).beta (1/125)) ≤ ((CutFailureCertificates.Budget046.certificate925).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound925 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate925).aa:ℝ)*st.R)+(((916:ℚ):ℝ)*exp (-((MergedCutGroups.Batch114.certificate1372).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate31).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch046.certificate925).omega:ℝ) ≤ ((CutFailureCertificates.Budget046.certificate925).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch114.certificate1372).cells.length:ℝ) ≤ (458:ℝ) := by exact_mod_cast multiplicity31
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch114.certificate1372).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound31 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch046.certificate925).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate31).exponent:ℝ)*st.R)+((MergedCutGroups.Batch114.certificate1372).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch114.certificate1372).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch046.certificate925).aa:ℝ)*st.R)+((916:ℝ)*exp (-((MergedCutGroups.Batch114.certificate1372).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate31).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch046.sound925.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets32 : Fin (MergedCutGroups.Batch114.certificate1376).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority028.certificate567,CutLabelCertificates.Minority028.certificate568,CutLabelCertificates.Minority028.certificate569,CutLabelCertificates.Minority028.certificate570]
theorem matches32 : (MergedCutGroups.Batch114.certificate1376).LocalMatches CountingCertificates.Batch046.certificate928 budgets32 := by decide +kernel
theorem budgetsSound32 : ∀ l, (budgets32 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority028.sound567
  · exact CutLabelCertificates.Minority028.sound568
  · exact CutLabelCertificates.Minority028.sound569
  · exact CutLabelCertificates.Minority028.sound570
theorem multiplicity32 : (MergedCutGroups.Batch114.certificate1376).cells.length ≤ 458 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound32 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch114.certificate1376).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate928).dm (WitnessCertificates.Batch046.certificate928).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch046.certificate928).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate32).exponent:ℝ)*st.R)+((MergedCutGroups.Batch114.certificate1376).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch114.certificate1376).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch046.certificate928).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch114.certificate1376 CountingCertificates.Batch046.certificate928 budgets32 CutFailureCertificates.Reverse001.certificate32 matches32 rfl rfl
    MergedCutGroups.Batch114.numericValid1376 MergedCutGroups.Batch114.cellsSound1376 MergedCutGroups.Batch114.cellsEntropyValid1376 MergedCutGroups.Batch114.populationMatches1376
    PopulationCertificates.Batch046.valid928 PopulationCertificates.Batch046.sound928 WitnessCertificates.Batch046.valid928 WitnessCertificates.Batch046.sound928 CountingCertificates.Batch046.valid928 CountingCertificates.Batch046.sound928
    budgetsSound32 CutFailureCertificates.Reverse001.sound32 H st hI
theorem probabilityBound32 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch114.certificate1376).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate928).dm (WitnessCertificates.Batch046.certificate928).beta (1/125)) ≤ ((CutFailureCertificates.Budget046.certificate928).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound928 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate928).aa:ℝ)*st.R)+(((916:ℚ):ℝ)*exp (-((MergedCutGroups.Batch114.certificate1376).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate32).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch046.certificate928).omega:ℝ) ≤ ((CutFailureCertificates.Budget046.certificate928).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch114.certificate1376).cells.length:ℝ) ≤ (458:ℝ) := by exact_mod_cast multiplicity32
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch114.certificate1376).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound32 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch046.certificate928).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate32).exponent:ℝ)*st.R)+((MergedCutGroups.Batch114.certificate1376).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch114.certificate1376).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch046.certificate928).aa:ℝ)*st.R)+((916:ℝ)*exp (-((MergedCutGroups.Batch114.certificate1376).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate32).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch046.sound928.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets33 : Fin (MergedCutGroups.Batch115.certificate1380).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority028.certificate572,CutLabelCertificates.Minority028.certificate573,CutLabelCertificates.Minority028.certificate574,CutLabelCertificates.Minority028.certificate575]
theorem matches33 : (MergedCutGroups.Batch115.certificate1380).LocalMatches CountingCertificates.Batch046.certificate931 budgets33 := by decide +kernel
theorem budgetsSound33 : ∀ l, (budgets33 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority028.sound572
  · exact CutLabelCertificates.Minority028.sound573
  · exact CutLabelCertificates.Minority028.sound574
  · exact CutLabelCertificates.Minority028.sound575
theorem multiplicity33 : (MergedCutGroups.Batch115.certificate1380).cells.length ≤ 457 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound33 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch115.certificate1380).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate931).dm (WitnessCertificates.Batch046.certificate931).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch046.certificate931).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate33).exponent:ℝ)*st.R)+((MergedCutGroups.Batch115.certificate1380).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch115.certificate1380).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch046.certificate931).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch115.certificate1380 CountingCertificates.Batch046.certificate931 budgets33 CutFailureCertificates.Reverse001.certificate33 matches33 rfl rfl
    MergedCutGroups.Batch115.numericValid1380 MergedCutGroups.Batch115.cellsSound1380 MergedCutGroups.Batch115.cellsEntropyValid1380 MergedCutGroups.Batch115.populationMatches1380
    PopulationCertificates.Batch046.valid931 PopulationCertificates.Batch046.sound931 WitnessCertificates.Batch046.valid931 WitnessCertificates.Batch046.sound931 CountingCertificates.Batch046.valid931 CountingCertificates.Batch046.sound931
    budgetsSound33 CutFailureCertificates.Reverse001.sound33 H st hI
theorem probabilityBound33 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch115.certificate1380).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate931).dm (WitnessCertificates.Batch046.certificate931).beta (1/125)) ≤ ((CutFailureCertificates.Budget046.certificate931).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound931 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate931).aa:ℝ)*st.R)+(((914:ℚ):ℝ)*exp (-((MergedCutGroups.Batch115.certificate1380).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate33).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch046.certificate931).omega:ℝ) ≤ ((CutFailureCertificates.Budget046.certificate931).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch115.certificate1380).cells.length:ℝ) ≤ (457:ℝ) := by exact_mod_cast multiplicity33
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch115.certificate1380).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound33 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch046.certificate931).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate33).exponent:ℝ)*st.R)+((MergedCutGroups.Batch115.certificate1380).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch115.certificate1380).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch046.certificate931).aa:ℝ)*st.R)+((914:ℝ)*exp (-((MergedCutGroups.Batch115.certificate1380).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate33).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch046.sound931.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets34 : Fin (MergedCutGroups.Batch115.certificate1384).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority028.certificate577,CutLabelCertificates.Minority028.certificate578,CutLabelCertificates.Minority028.certificate579,CutLabelCertificates.Minority029.certificate580]
theorem matches34 : (MergedCutGroups.Batch115.certificate1384).LocalMatches CountingCertificates.Batch046.certificate934 budgets34 := by decide +kernel
theorem budgetsSound34 : ∀ l, (budgets34 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority028.sound577
  · exact CutLabelCertificates.Minority028.sound578
  · exact CutLabelCertificates.Minority028.sound579
  · exact CutLabelCertificates.Minority029.sound580
theorem multiplicity34 : (MergedCutGroups.Batch115.certificate1384).cells.length ≤ 458 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound34 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch115.certificate1384).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate934).dm (WitnessCertificates.Batch046.certificate934).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch046.certificate934).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate34).exponent:ℝ)*st.R)+((MergedCutGroups.Batch115.certificate1384).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch115.certificate1384).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch046.certificate934).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch115.certificate1384 CountingCertificates.Batch046.certificate934 budgets34 CutFailureCertificates.Reverse001.certificate34 matches34 rfl rfl
    MergedCutGroups.Batch115.numericValid1384 MergedCutGroups.Batch115.cellsSound1384 MergedCutGroups.Batch115.cellsEntropyValid1384 MergedCutGroups.Batch115.populationMatches1384
    PopulationCertificates.Batch046.valid934 PopulationCertificates.Batch046.sound934 WitnessCertificates.Batch046.valid934 WitnessCertificates.Batch046.sound934 CountingCertificates.Batch046.valid934 CountingCertificates.Batch046.sound934
    budgetsSound34 CutFailureCertificates.Reverse001.sound34 H st hI
theorem probabilityBound34 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch115.certificate1384).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate934).dm (WitnessCertificates.Batch046.certificate934).beta (1/125)) ≤ ((CutFailureCertificates.Budget046.certificate934).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound934 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate934).aa:ℝ)*st.R)+(((916:ℚ):ℝ)*exp (-((MergedCutGroups.Batch115.certificate1384).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate34).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch046.certificate934).omega:ℝ) ≤ ((CutFailureCertificates.Budget046.certificate934).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch115.certificate1384).cells.length:ℝ) ≤ (458:ℝ) := by exact_mod_cast multiplicity34
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch115.certificate1384).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound34 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch046.certificate934).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate34).exponent:ℝ)*st.R)+((MergedCutGroups.Batch115.certificate1384).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch115.certificate1384).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch046.certificate934).aa:ℝ)*st.R)+((916:ℝ)*exp (-((MergedCutGroups.Batch115.certificate1384).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate34).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch046.sound934.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets35 : Fin (MergedCutGroups.Batch115.certificate1388).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority029.certificate582,CutLabelCertificates.Minority029.certificate583,CutLabelCertificates.Minority029.certificate584,CutLabelCertificates.Minority029.certificate585]
theorem matches35 : (MergedCutGroups.Batch115.certificate1388).LocalMatches CountingCertificates.Batch046.certificate937 budgets35 := by decide +kernel
theorem budgetsSound35 : ∀ l, (budgets35 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority029.sound582
  · exact CutLabelCertificates.Minority029.sound583
  · exact CutLabelCertificates.Minority029.sound584
  · exact CutLabelCertificates.Minority029.sound585
theorem multiplicity35 : (MergedCutGroups.Batch115.certificate1388).cells.length ≤ 458 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound35 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch115.certificate1388).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate937).dm (WitnessCertificates.Batch046.certificate937).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch046.certificate937).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate35).exponent:ℝ)*st.R)+((MergedCutGroups.Batch115.certificate1388).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch115.certificate1388).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch046.certificate937).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch115.certificate1388 CountingCertificates.Batch046.certificate937 budgets35 CutFailureCertificates.Reverse001.certificate35 matches35 rfl rfl
    MergedCutGroups.Batch115.numericValid1388 MergedCutGroups.Batch115.cellsSound1388 MergedCutGroups.Batch115.cellsEntropyValid1388 MergedCutGroups.Batch115.populationMatches1388
    PopulationCertificates.Batch046.valid937 PopulationCertificates.Batch046.sound937 WitnessCertificates.Batch046.valid937 WitnessCertificates.Batch046.sound937 CountingCertificates.Batch046.valid937 CountingCertificates.Batch046.sound937
    budgetsSound35 CutFailureCertificates.Reverse001.sound35 H st hI
theorem probabilityBound35 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch115.certificate1388).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch046.certificate937).dm (WitnessCertificates.Batch046.certificate937).beta (1/125)) ≤ ((CutFailureCertificates.Budget046.certificate937).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound937 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate937).aa:ℝ)*st.R)+(((916:ℚ):ℝ)*exp (-((MergedCutGroups.Batch115.certificate1388).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate35).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch046.certificate937).omega:ℝ) ≤ ((CutFailureCertificates.Budget046.certificate937).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch115.certificate1388).cells.length:ℝ) ≤ (458:ℝ) := by exact_mod_cast multiplicity35
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch115.certificate1388).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound35 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch046.certificate937).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate35).exponent:ℝ)*st.R)+((MergedCutGroups.Batch115.certificate1388).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch115.certificate1388).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch046.certificate937).aa:ℝ)*st.R)+((916:ℝ)*exp (-((MergedCutGroups.Batch115.certificate1388).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate35).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch046.sound937.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets36 : Fin (MergedCutGroups.Batch116.certificate1392).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority029.certificate587,CutLabelCertificates.Minority029.certificate588,CutLabelCertificates.Minority029.certificate589,CutLabelCertificates.Minority029.certificate590]
theorem matches36 : (MergedCutGroups.Batch116.certificate1392).LocalMatches CountingCertificates.Batch047.certificate940 budgets36 := by decide +kernel
theorem budgetsSound36 : ∀ l, (budgets36 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority029.sound587
  · exact CutLabelCertificates.Minority029.sound588
  · exact CutLabelCertificates.Minority029.sound589
  · exact CutLabelCertificates.Minority029.sound590
theorem multiplicity36 : (MergedCutGroups.Batch116.certificate1392).cells.length ≤ 458 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound36 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch116.certificate1392).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate940).dm (WitnessCertificates.Batch047.certificate940).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch047.certificate940).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate36).exponent:ℝ)*st.R)+((MergedCutGroups.Batch116.certificate1392).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch116.certificate1392).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch047.certificate940).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch116.certificate1392 CountingCertificates.Batch047.certificate940 budgets36 CutFailureCertificates.Reverse001.certificate36 matches36 rfl rfl
    MergedCutGroups.Batch116.numericValid1392 MergedCutGroups.Batch116.cellsSound1392 MergedCutGroups.Batch116.cellsEntropyValid1392 MergedCutGroups.Batch116.populationMatches1392
    PopulationCertificates.Batch047.valid940 PopulationCertificates.Batch047.sound940 WitnessCertificates.Batch047.valid940 WitnessCertificates.Batch047.sound940 CountingCertificates.Batch047.valid940 CountingCertificates.Batch047.sound940
    budgetsSound36 CutFailureCertificates.Reverse001.sound36 H st hI
theorem probabilityBound36 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch116.certificate1392).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate940).dm (WitnessCertificates.Batch047.certificate940).beta (1/125)) ≤ ((CutFailureCertificates.Budget047.certificate940).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound940 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate940).aa:ℝ)*st.R)+(((916:ℚ):ℝ)*exp (-((MergedCutGroups.Batch116.certificate1392).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate36).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch047.certificate940).omega:ℝ) ≤ ((CutFailureCertificates.Budget047.certificate940).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch116.certificate1392).cells.length:ℝ) ≤ (458:ℝ) := by exact_mod_cast multiplicity36
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch116.certificate1392).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound36 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch047.certificate940).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate36).exponent:ℝ)*st.R)+((MergedCutGroups.Batch116.certificate1392).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch116.certificate1392).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch047.certificate940).aa:ℝ)*st.R)+((916:ℝ)*exp (-((MergedCutGroups.Batch116.certificate1392).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate36).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch047.sound940.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets37 : Fin (MergedCutGroups.Batch116.certificate1396).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority029.certificate592,CutLabelCertificates.Minority029.certificate593,CutLabelCertificates.Minority029.certificate594,CutLabelCertificates.Minority029.certificate595]
theorem matches37 : (MergedCutGroups.Batch116.certificate1396).LocalMatches CountingCertificates.Batch047.certificate943 budgets37 := by decide +kernel
theorem budgetsSound37 : ∀ l, (budgets37 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority029.sound592
  · exact CutLabelCertificates.Minority029.sound593
  · exact CutLabelCertificates.Minority029.sound594
  · exact CutLabelCertificates.Minority029.sound595
theorem multiplicity37 : (MergedCutGroups.Batch116.certificate1396).cells.length ≤ 457 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound37 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch116.certificate1396).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate943).dm (WitnessCertificates.Batch047.certificate943).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch047.certificate943).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate37).exponent:ℝ)*st.R)+((MergedCutGroups.Batch116.certificate1396).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch116.certificate1396).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch047.certificate943).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch116.certificate1396 CountingCertificates.Batch047.certificate943 budgets37 CutFailureCertificates.Reverse001.certificate37 matches37 rfl rfl
    MergedCutGroups.Batch116.numericValid1396 MergedCutGroups.Batch116.cellsSound1396 MergedCutGroups.Batch116.cellsEntropyValid1396 MergedCutGroups.Batch116.populationMatches1396
    PopulationCertificates.Batch047.valid943 PopulationCertificates.Batch047.sound943 WitnessCertificates.Batch047.valid943 WitnessCertificates.Batch047.sound943 CountingCertificates.Batch047.valid943 CountingCertificates.Batch047.sound943
    budgetsSound37 CutFailureCertificates.Reverse001.sound37 H st hI
theorem probabilityBound37 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch116.certificate1396).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate943).dm (WitnessCertificates.Batch047.certificate943).beta (1/125)) ≤ ((CutFailureCertificates.Budget047.certificate943).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound943 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate943).aa:ℝ)*st.R)+(((914:ℚ):ℝ)*exp (-((MergedCutGroups.Batch116.certificate1396).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate37).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch047.certificate943).omega:ℝ) ≤ ((CutFailureCertificates.Budget047.certificate943).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch116.certificate1396).cells.length:ℝ) ≤ (457:ℝ) := by exact_mod_cast multiplicity37
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch116.certificate1396).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound37 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch047.certificate943).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate37).exponent:ℝ)*st.R)+((MergedCutGroups.Batch116.certificate1396).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch116.certificate1396).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch047.certificate943).aa:ℝ)*st.R)+((914:ℝ)*exp (-((MergedCutGroups.Batch116.certificate1396).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate37).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch047.sound943.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets38 : Fin (MergedCutGroups.Batch116.certificate1400).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority029.certificate597,CutLabelCertificates.Minority029.certificate598,CutLabelCertificates.Minority029.certificate599,CutLabelCertificates.Minority030.certificate600]
theorem matches38 : (MergedCutGroups.Batch116.certificate1400).LocalMatches CountingCertificates.Batch047.certificate946 budgets38 := by decide +kernel
theorem budgetsSound38 : ∀ l, (budgets38 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority029.sound597
  · exact CutLabelCertificates.Minority029.sound598
  · exact CutLabelCertificates.Minority029.sound599
  · exact CutLabelCertificates.Minority030.sound600
theorem multiplicity38 : (MergedCutGroups.Batch116.certificate1400).cells.length ≤ 457 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound38 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch116.certificate1400).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate946).dm (WitnessCertificates.Batch047.certificate946).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch047.certificate946).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate38).exponent:ℝ)*st.R)+((MergedCutGroups.Batch116.certificate1400).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch116.certificate1400).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch047.certificate946).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch116.certificate1400 CountingCertificates.Batch047.certificate946 budgets38 CutFailureCertificates.Reverse001.certificate38 matches38 rfl rfl
    MergedCutGroups.Batch116.numericValid1400 MergedCutGroups.Batch116.cellsSound1400 MergedCutGroups.Batch116.cellsEntropyValid1400 MergedCutGroups.Batch116.populationMatches1400
    PopulationCertificates.Batch047.valid946 PopulationCertificates.Batch047.sound946 WitnessCertificates.Batch047.valid946 WitnessCertificates.Batch047.sound946 CountingCertificates.Batch047.valid946 CountingCertificates.Batch047.sound946
    budgetsSound38 CutFailureCertificates.Reverse001.sound38 H st hI
theorem probabilityBound38 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch116.certificate1400).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate946).dm (WitnessCertificates.Batch047.certificate946).beta (1/125)) ≤ ((CutFailureCertificates.Budget047.certificate946).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound946 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate946).aa:ℝ)*st.R)+(((914:ℚ):ℝ)*exp (-((MergedCutGroups.Batch116.certificate1400).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate38).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch047.certificate946).omega:ℝ) ≤ ((CutFailureCertificates.Budget047.certificate946).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch116.certificate1400).cells.length:ℝ) ≤ (457:ℝ) := by exact_mod_cast multiplicity38
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch116.certificate1400).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound38 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch047.certificate946).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate38).exponent:ℝ)*st.R)+((MergedCutGroups.Batch116.certificate1400).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch116.certificate1400).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch047.certificate946).aa:ℝ)*st.R)+((914:ℝ)*exp (-((MergedCutGroups.Batch116.certificate1400).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate38).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch047.sound946.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

def budgets39 : Fin (MergedCutGroups.Batch117.certificate1404).cells.length → RatMinorityBudgetCertificate := ![CutLabelCertificates.Minority030.certificate602,CutLabelCertificates.Minority030.certificate603,CutLabelCertificates.Minority030.certificate604,CutLabelCertificates.Minority030.certificate605]
theorem matches39 : (MergedCutGroups.Batch117.certificate1404).LocalMatches CountingCertificates.Batch047.certificate949 budgets39 := by decide +kernel
theorem budgetsSound39 : ∀ l, (budgets39 l).Sound := by
  intro l
  change Fin 4 at l
  fin_cases l
  · exact CutLabelCertificates.Minority030.sound602
  · exact CutLabelCertificates.Minority030.sound603
  · exact CutLabelCertificates.Minority030.sound604
  · exact CutLabelCertificates.Minority030.sound605
theorem multiplicity39 : (MergedCutGroups.Batch117.certificate1404).cells.length ≤ 457 := by decide +kernel

attribute [local instance] Classical.propDecidable
theorem exponentialBound39 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch117.certificate1404).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate949).dm (WitnessCertificates.Batch047.certificate949).beta (1/125)) ≤ (2*exp (-((CountingCertificates.Batch047.certificate949).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate39).exponent:ℝ)*st.R)+((MergedCutGroups.Batch117.certificate1404).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch117.certificate1404).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch047.certificate949).omega:ℝ) :=
  certified_local_failure MergedCutGroups.Batch117.certificate1404 CountingCertificates.Batch047.certificate949 budgets39 CutFailureCertificates.Reverse001.certificate39 matches39 rfl rfl
    MergedCutGroups.Batch117.numericValid1404 MergedCutGroups.Batch117.cellsSound1404 MergedCutGroups.Batch117.cellsEntropyValid1404 MergedCutGroups.Batch117.populationMatches1404
    PopulationCertificates.Batch047.valid949 PopulationCertificates.Batch047.sound949 WitnessCertificates.Batch047.valid949 WitnessCertificates.Batch047.sound949 CountingCertificates.Batch047.valid949 CountingCertificates.Batch047.sound949
    budgetsSound39 CutFailureCertificates.Reverse001.sound39 H st hI
theorem probabilityBound39 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch117.certificate1404).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedRestrictedCutFailure H univ st.N st.z (WitnessCertificates.Batch047.certificate949).dm (WitnessCertificates.Batch047.certificate949).beta (1/125)) ≤ ((CutFailureCertificates.Budget047.certificate949).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound949 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate949).aa:ℝ)*st.R)+(((914:ℚ):ℝ)*exp (-((MergedCutGroups.Batch117.certificate1404).exponent:ℝ)*st.R)+(((1:ℚ):ℝ)*exp (-((CutFailureCertificates.Reverse001.certificate39).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch047.certificate949).omega:ℝ) ≤ ((CutFailureCertificates.Budget047.certificate949).bound:ℝ) at hb
  have hlen : ((MergedCutGroups.Batch117.certificate1404).cells.length:ℝ) ≤ (457:ℝ) := by exact_mod_cast multiplicity39
  have hm := mul_le_mul_of_nonneg_right hlen (show (0:ℝ) ≤ 2*exp (-((MergedCutGroups.Batch117.certificate1404).exponent:ℝ)*st.R) by positivity)
  apply (exponentialBound39 H st hI).trans
  apply (div_le_div_of_nonneg_right (show 2*exp (-((CountingCertificates.Batch047.certificate949).aa:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate39).exponent:ℝ)*st.R)+((MergedCutGroups.Batch117.certificate1404).cells.length:ℝ)*(2*exp (-((MergedCutGroups.Batch117.certificate1404).exponent:ℝ)*st.R)) ≤ 2*exp (-((CountingCertificates.Batch047.certificate949).aa:ℝ)*st.R)+((914:ℝ)*exp (-((MergedCutGroups.Batch117.certificate1404).exponent:ℝ)*st.R)+exp (-((CutFailureCertificates.Reverse001.certificate39).exponent:ℝ)*st.R)) by nlinarith only [hm]) WitnessCertificates.Batch047.sound949.1.le).trans
  simpa only [Rat.cast_ofNat,Rat.cast_one,one_mul,add_zero] using hb

end Cycle12.CertifiedLocalFailures.Batch001
