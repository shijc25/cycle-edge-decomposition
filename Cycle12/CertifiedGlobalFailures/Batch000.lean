import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch000
import Cycle12.CountingCertificates.Batch001
import Cycle12.CutFailureCertificates.Budget000
import Cycle12.CutFailureCertificates.Budget001
import Cycle12.CutLabelCertificates.Entropy000
import Cycle12.CutLabelCertificates.Entropy001
import Cycle12.CutLabelCertificates.Minority000
import Cycle12.MergedCutGroups.Batch000
import Cycle12.MergedCutGroups.Batch001
import Cycle12.MergedCutGroups.Batch002
import Cycle12.MergedCutGroups.Batch003
import Cycle12.MergedCutGroups.Batch004
import Cycle12.PopulationCertificates.Batch000
import Cycle12.PopulationCertificates.Batch001
import Cycle12.WitnessCertificates.Batch000
import Cycle12.WitnessCertificates.Batch001

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch000
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches0 : (MergedCutGroups.Batch000.certificate0).GlobalMatches MergedCutGroups.Batch000.certificate1 CountingCertificates.Batch000.certificate0 CutLabelCertificates.Entropy000.certificate0 CutLabelCertificates.Minority000.certificate0 := by decide +kernel
theorem exponentialBound0 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch000.certificate0).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate0).dm (WitnessCertificates.Batch000.certificate0).beta) ≤ (2*exp (-((CountingCertificates.Batch000.certificate0).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch000.certificate0).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch000.certificate1).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch000.certificate0).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch000.certificate0 MergedCutGroups.Batch000.certificate1 CountingCertificates.Batch000.certificate0 CutLabelCertificates.Entropy000.certificate0 CutLabelCertificates.Minority000.certificate0 matches0 rfl rfl
    MergedCutGroups.Batch000.numericValid0 MergedCutGroups.Batch000.numericValid1 MergedCutGroups.Batch000.cellsSound0 MergedCutGroups.Batch000.cellsSound1
    MergedCutGroups.Batch000.cellsNumeric0 MergedCutGroups.Batch000.cellsNumeric1 MergedCutGroups.Batch000.populationMatches0 MergedCutGroups.Batch000.populationMatches1
    PopulationCertificates.Batch000.valid0 PopulationCertificates.Batch000.sound0 WitnessCertificates.Batch000.valid0 WitnessCertificates.Batch000.sound0 CountingCertificates.Batch000.valid0 CountingCertificates.Batch000.sound0
    CutLabelCertificates.Entropy000.valid0 CutLabelCertificates.Minority000.valid0 CutLabelCertificates.Minority000.sound0 H st hI
theorem probabilityBound0 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch000.certificate0).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate0).dm (WitnessCertificates.Batch000.certificate0).beta) ≤ ((CutFailureCertificates.Budget000.certificate0).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound0 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate0).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch000.certificate0).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch000.certificate1).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch000.certificate0).omega:ℝ) ≤ ((CutFailureCertificates.Budget000.certificate0).bound:ℝ) at hb
  exact (exponentialBound0 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches1 : (MergedCutGroups.Batch000.certificate3).GlobalMatches MergedCutGroups.Batch000.certificate4 CountingCertificates.Batch000.certificate2 CutLabelCertificates.Entropy000.certificate2 CutLabelCertificates.Minority000.certificate1 := by decide +kernel
theorem exponentialBound1 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch000.certificate3).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate2).dm (WitnessCertificates.Batch000.certificate2).beta) ≤ (2*exp (-((CountingCertificates.Batch000.certificate2).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch000.certificate3).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch000.certificate4).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch000.certificate2).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch000.certificate3 MergedCutGroups.Batch000.certificate4 CountingCertificates.Batch000.certificate2 CutLabelCertificates.Entropy000.certificate2 CutLabelCertificates.Minority000.certificate1 matches1 rfl rfl
    MergedCutGroups.Batch000.numericValid3 MergedCutGroups.Batch000.numericValid4 MergedCutGroups.Batch000.cellsSound3 MergedCutGroups.Batch000.cellsSound4
    MergedCutGroups.Batch000.cellsNumeric3 MergedCutGroups.Batch000.cellsNumeric4 MergedCutGroups.Batch000.populationMatches3 MergedCutGroups.Batch000.populationMatches4
    PopulationCertificates.Batch000.valid2 PopulationCertificates.Batch000.sound2 WitnessCertificates.Batch000.valid2 WitnessCertificates.Batch000.sound2 CountingCertificates.Batch000.valid2 CountingCertificates.Batch000.sound2
    CutLabelCertificates.Entropy000.valid2 CutLabelCertificates.Minority000.valid1 CutLabelCertificates.Minority000.sound1 H st hI
theorem probabilityBound1 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch000.certificate3).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate2).dm (WitnessCertificates.Batch000.certificate2).beta) ≤ ((CutFailureCertificates.Budget000.certificate2).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound2 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate2).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch000.certificate3).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch000.certificate4).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch000.certificate2).omega:ℝ) ≤ ((CutFailureCertificates.Budget000.certificate2).bound:ℝ) at hb
  exact (exponentialBound1 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches2 : (MergedCutGroups.Batch000.certificate6).GlobalMatches MergedCutGroups.Batch000.certificate7 CountingCertificates.Batch000.certificate4 CutLabelCertificates.Entropy000.certificate3 CutLabelCertificates.Minority000.certificate2 := by decide +kernel
theorem exponentialBound2 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch000.certificate6).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate4).dm (WitnessCertificates.Batch000.certificate4).beta) ≤ (2*exp (-((CountingCertificates.Batch000.certificate4).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch000.certificate6).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch000.certificate7).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch000.certificate4).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch000.certificate6 MergedCutGroups.Batch000.certificate7 CountingCertificates.Batch000.certificate4 CutLabelCertificates.Entropy000.certificate3 CutLabelCertificates.Minority000.certificate2 matches2 rfl rfl
    MergedCutGroups.Batch000.numericValid6 MergedCutGroups.Batch000.numericValid7 MergedCutGroups.Batch000.cellsSound6 MergedCutGroups.Batch000.cellsSound7
    MergedCutGroups.Batch000.cellsNumeric6 MergedCutGroups.Batch000.cellsNumeric7 MergedCutGroups.Batch000.populationMatches6 MergedCutGroups.Batch000.populationMatches7
    PopulationCertificates.Batch000.valid4 PopulationCertificates.Batch000.sound4 WitnessCertificates.Batch000.valid4 WitnessCertificates.Batch000.sound4 CountingCertificates.Batch000.valid4 CountingCertificates.Batch000.sound4
    CutLabelCertificates.Entropy000.valid3 CutLabelCertificates.Minority000.valid2 CutLabelCertificates.Minority000.sound2 H st hI
theorem probabilityBound2 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch000.certificate6).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate4).dm (WitnessCertificates.Batch000.certificate4).beta) ≤ ((CutFailureCertificates.Budget000.certificate4).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound4 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate4).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch000.certificate6).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch000.certificate7).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch000.certificate4).omega:ℝ) ≤ ((CutFailureCertificates.Budget000.certificate4).bound:ℝ) at hb
  exact (exponentialBound2 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches3 : (MergedCutGroups.Batch000.certificate9).GlobalMatches MergedCutGroups.Batch000.certificate10 CountingCertificates.Batch000.certificate6 CutLabelCertificates.Entropy000.certificate4 CutLabelCertificates.Minority000.certificate3 := by decide +kernel
theorem exponentialBound3 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch000.certificate9).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate6).dm (WitnessCertificates.Batch000.certificate6).beta) ≤ (2*exp (-((CountingCertificates.Batch000.certificate6).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch000.certificate9).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch000.certificate10).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch000.certificate6).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch000.certificate9 MergedCutGroups.Batch000.certificate10 CountingCertificates.Batch000.certificate6 CutLabelCertificates.Entropy000.certificate4 CutLabelCertificates.Minority000.certificate3 matches3 rfl rfl
    MergedCutGroups.Batch000.numericValid9 MergedCutGroups.Batch000.numericValid10 MergedCutGroups.Batch000.cellsSound9 MergedCutGroups.Batch000.cellsSound10
    MergedCutGroups.Batch000.cellsNumeric9 MergedCutGroups.Batch000.cellsNumeric10 MergedCutGroups.Batch000.populationMatches9 MergedCutGroups.Batch000.populationMatches10
    PopulationCertificates.Batch000.valid6 PopulationCertificates.Batch000.sound6 WitnessCertificates.Batch000.valid6 WitnessCertificates.Batch000.sound6 CountingCertificates.Batch000.valid6 CountingCertificates.Batch000.sound6
    CutLabelCertificates.Entropy000.valid4 CutLabelCertificates.Minority000.valid3 CutLabelCertificates.Minority000.sound3 H st hI
theorem probabilityBound3 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch000.certificate9).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate6).dm (WitnessCertificates.Batch000.certificate6).beta) ≤ ((CutFailureCertificates.Budget000.certificate6).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound6 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate6).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch000.certificate9).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch000.certificate10).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch000.certificate6).omega:ℝ) ≤ ((CutFailureCertificates.Budget000.certificate6).bound:ℝ) at hb
  exact (exponentialBound3 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches4 : (MergedCutGroups.Batch001.certificate12).GlobalMatches MergedCutGroups.Batch001.certificate13 CountingCertificates.Batch000.certificate8 CutLabelCertificates.Entropy000.certificate5 CutLabelCertificates.Minority000.certificate4 := by decide +kernel
theorem exponentialBound4 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch001.certificate12).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate8).dm (WitnessCertificates.Batch000.certificate8).beta) ≤ (2*exp (-((CountingCertificates.Batch000.certificate8).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch001.certificate12).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch001.certificate13).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch000.certificate8).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch001.certificate12 MergedCutGroups.Batch001.certificate13 CountingCertificates.Batch000.certificate8 CutLabelCertificates.Entropy000.certificate5 CutLabelCertificates.Minority000.certificate4 matches4 rfl rfl
    MergedCutGroups.Batch001.numericValid12 MergedCutGroups.Batch001.numericValid13 MergedCutGroups.Batch001.cellsSound12 MergedCutGroups.Batch001.cellsSound13
    MergedCutGroups.Batch001.cellsNumeric12 MergedCutGroups.Batch001.cellsNumeric13 MergedCutGroups.Batch001.populationMatches12 MergedCutGroups.Batch001.populationMatches13
    PopulationCertificates.Batch000.valid8 PopulationCertificates.Batch000.sound8 WitnessCertificates.Batch000.valid8 WitnessCertificates.Batch000.sound8 CountingCertificates.Batch000.valid8 CountingCertificates.Batch000.sound8
    CutLabelCertificates.Entropy000.valid5 CutLabelCertificates.Minority000.valid4 CutLabelCertificates.Minority000.sound4 H st hI
theorem probabilityBound4 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch001.certificate12).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate8).dm (WitnessCertificates.Batch000.certificate8).beta) ≤ ((CutFailureCertificates.Budget000.certificate8).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound8 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate8).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch001.certificate12).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch001.certificate13).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch000.certificate8).omega:ℝ) ≤ ((CutFailureCertificates.Budget000.certificate8).bound:ℝ) at hb
  exact (exponentialBound4 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches5 : (MergedCutGroups.Batch001.certificate15).GlobalMatches MergedCutGroups.Batch001.certificate16 CountingCertificates.Batch000.certificate10 CutLabelCertificates.Entropy000.certificate6 CutLabelCertificates.Minority000.certificate5 := by decide +kernel
theorem exponentialBound5 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch001.certificate15).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate10).dm (WitnessCertificates.Batch000.certificate10).beta) ≤ (2*exp (-((CountingCertificates.Batch000.certificate10).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch001.certificate15).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch001.certificate16).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch000.certificate10).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch001.certificate15 MergedCutGroups.Batch001.certificate16 CountingCertificates.Batch000.certificate10 CutLabelCertificates.Entropy000.certificate6 CutLabelCertificates.Minority000.certificate5 matches5 rfl rfl
    MergedCutGroups.Batch001.numericValid15 MergedCutGroups.Batch001.numericValid16 MergedCutGroups.Batch001.cellsSound15 MergedCutGroups.Batch001.cellsSound16
    MergedCutGroups.Batch001.cellsNumeric15 MergedCutGroups.Batch001.cellsNumeric16 MergedCutGroups.Batch001.populationMatches15 MergedCutGroups.Batch001.populationMatches16
    PopulationCertificates.Batch000.valid10 PopulationCertificates.Batch000.sound10 WitnessCertificates.Batch000.valid10 WitnessCertificates.Batch000.sound10 CountingCertificates.Batch000.valid10 CountingCertificates.Batch000.sound10
    CutLabelCertificates.Entropy000.valid6 CutLabelCertificates.Minority000.valid5 CutLabelCertificates.Minority000.sound5 H st hI
theorem probabilityBound5 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch001.certificate15).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate10).dm (WitnessCertificates.Batch000.certificate10).beta) ≤ ((CutFailureCertificates.Budget000.certificate10).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound10 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate10).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch001.certificate15).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch001.certificate16).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch000.certificate10).omega:ℝ) ≤ ((CutFailureCertificates.Budget000.certificate10).bound:ℝ) at hb
  exact (exponentialBound5 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches6 : (MergedCutGroups.Batch001.certificate18).GlobalMatches MergedCutGroups.Batch001.certificate19 CountingCertificates.Batch000.certificate12 CutLabelCertificates.Entropy000.certificate7 CutLabelCertificates.Minority000.certificate6 := by decide +kernel
theorem exponentialBound6 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch001.certificate18).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate12).dm (WitnessCertificates.Batch000.certificate12).beta) ≤ (2*exp (-((CountingCertificates.Batch000.certificate12).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch001.certificate18).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch001.certificate19).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch000.certificate12).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch001.certificate18 MergedCutGroups.Batch001.certificate19 CountingCertificates.Batch000.certificate12 CutLabelCertificates.Entropy000.certificate7 CutLabelCertificates.Minority000.certificate6 matches6 rfl rfl
    MergedCutGroups.Batch001.numericValid18 MergedCutGroups.Batch001.numericValid19 MergedCutGroups.Batch001.cellsSound18 MergedCutGroups.Batch001.cellsSound19
    MergedCutGroups.Batch001.cellsNumeric18 MergedCutGroups.Batch001.cellsNumeric19 MergedCutGroups.Batch001.populationMatches18 MergedCutGroups.Batch001.populationMatches19
    PopulationCertificates.Batch000.valid12 PopulationCertificates.Batch000.sound12 WitnessCertificates.Batch000.valid12 WitnessCertificates.Batch000.sound12 CountingCertificates.Batch000.valid12 CountingCertificates.Batch000.sound12
    CutLabelCertificates.Entropy000.valid7 CutLabelCertificates.Minority000.valid6 CutLabelCertificates.Minority000.sound6 H st hI
theorem probabilityBound6 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch001.certificate18).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate12).dm (WitnessCertificates.Batch000.certificate12).beta) ≤ ((CutFailureCertificates.Budget000.certificate12).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound12 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate12).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch001.certificate18).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch001.certificate19).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch000.certificate12).omega:ℝ) ≤ ((CutFailureCertificates.Budget000.certificate12).bound:ℝ) at hb
  exact (exponentialBound6 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches7 : (MergedCutGroups.Batch001.certificate21).GlobalMatches MergedCutGroups.Batch001.certificate22 CountingCertificates.Batch000.certificate14 CutLabelCertificates.Entropy000.certificate8 CutLabelCertificates.Minority000.certificate7 := by decide +kernel
theorem exponentialBound7 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch001.certificate21).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate14).dm (WitnessCertificates.Batch000.certificate14).beta) ≤ (2*exp (-((CountingCertificates.Batch000.certificate14).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch001.certificate21).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch001.certificate22).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch000.certificate14).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch001.certificate21 MergedCutGroups.Batch001.certificate22 CountingCertificates.Batch000.certificate14 CutLabelCertificates.Entropy000.certificate8 CutLabelCertificates.Minority000.certificate7 matches7 rfl rfl
    MergedCutGroups.Batch001.numericValid21 MergedCutGroups.Batch001.numericValid22 MergedCutGroups.Batch001.cellsSound21 MergedCutGroups.Batch001.cellsSound22
    MergedCutGroups.Batch001.cellsNumeric21 MergedCutGroups.Batch001.cellsNumeric22 MergedCutGroups.Batch001.populationMatches21 MergedCutGroups.Batch001.populationMatches22
    PopulationCertificates.Batch000.valid14 PopulationCertificates.Batch000.sound14 WitnessCertificates.Batch000.valid14 WitnessCertificates.Batch000.sound14 CountingCertificates.Batch000.valid14 CountingCertificates.Batch000.sound14
    CutLabelCertificates.Entropy000.valid8 CutLabelCertificates.Minority000.valid7 CutLabelCertificates.Minority000.sound7 H st hI
theorem probabilityBound7 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch001.certificate21).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate14).dm (WitnessCertificates.Batch000.certificate14).beta) ≤ ((CutFailureCertificates.Budget000.certificate14).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound14 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate14).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch001.certificate21).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch001.certificate22).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch000.certificate14).omega:ℝ) ≤ ((CutFailureCertificates.Budget000.certificate14).bound:ℝ) at hb
  exact (exponentialBound7 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches8 : (MergedCutGroups.Batch002.certificate24).GlobalMatches MergedCutGroups.Batch002.certificate25 CountingCertificates.Batch000.certificate16 CutLabelCertificates.Entropy000.certificate9 CutLabelCertificates.Minority000.certificate8 := by decide +kernel
theorem exponentialBound8 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch002.certificate24).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate16).dm (WitnessCertificates.Batch000.certificate16).beta) ≤ (2*exp (-((CountingCertificates.Batch000.certificate16).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch002.certificate24).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch002.certificate25).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch000.certificate16).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch002.certificate24 MergedCutGroups.Batch002.certificate25 CountingCertificates.Batch000.certificate16 CutLabelCertificates.Entropy000.certificate9 CutLabelCertificates.Minority000.certificate8 matches8 rfl rfl
    MergedCutGroups.Batch002.numericValid24 MergedCutGroups.Batch002.numericValid25 MergedCutGroups.Batch002.cellsSound24 MergedCutGroups.Batch002.cellsSound25
    MergedCutGroups.Batch002.cellsNumeric24 MergedCutGroups.Batch002.cellsNumeric25 MergedCutGroups.Batch002.populationMatches24 MergedCutGroups.Batch002.populationMatches25
    PopulationCertificates.Batch000.valid16 PopulationCertificates.Batch000.sound16 WitnessCertificates.Batch000.valid16 WitnessCertificates.Batch000.sound16 CountingCertificates.Batch000.valid16 CountingCertificates.Batch000.sound16
    CutLabelCertificates.Entropy000.valid9 CutLabelCertificates.Minority000.valid8 CutLabelCertificates.Minority000.sound8 H st hI
theorem probabilityBound8 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch002.certificate24).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate16).dm (WitnessCertificates.Batch000.certificate16).beta) ≤ ((CutFailureCertificates.Budget000.certificate16).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound16 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate16).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch002.certificate24).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch002.certificate25).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch000.certificate16).omega:ℝ) ≤ ((CutFailureCertificates.Budget000.certificate16).bound:ℝ) at hb
  exact (exponentialBound8 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches9 : (MergedCutGroups.Batch002.certificate27).GlobalMatches MergedCutGroups.Batch002.certificate28 CountingCertificates.Batch000.certificate18 CutLabelCertificates.Entropy000.certificate10 CutLabelCertificates.Minority000.certificate9 := by decide +kernel
theorem exponentialBound9 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch002.certificate27).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate18).dm (WitnessCertificates.Batch000.certificate18).beta) ≤ (2*exp (-((CountingCertificates.Batch000.certificate18).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch002.certificate27).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch002.certificate28).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch000.certificate18).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch002.certificate27 MergedCutGroups.Batch002.certificate28 CountingCertificates.Batch000.certificate18 CutLabelCertificates.Entropy000.certificate10 CutLabelCertificates.Minority000.certificate9 matches9 rfl rfl
    MergedCutGroups.Batch002.numericValid27 MergedCutGroups.Batch002.numericValid28 MergedCutGroups.Batch002.cellsSound27 MergedCutGroups.Batch002.cellsSound28
    MergedCutGroups.Batch002.cellsNumeric27 MergedCutGroups.Batch002.cellsNumeric28 MergedCutGroups.Batch002.populationMatches27 MergedCutGroups.Batch002.populationMatches28
    PopulationCertificates.Batch000.valid18 PopulationCertificates.Batch000.sound18 WitnessCertificates.Batch000.valid18 WitnessCertificates.Batch000.sound18 CountingCertificates.Batch000.valid18 CountingCertificates.Batch000.sound18
    CutLabelCertificates.Entropy000.valid10 CutLabelCertificates.Minority000.valid9 CutLabelCertificates.Minority000.sound9 H st hI
theorem probabilityBound9 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch002.certificate27).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch000.certificate18).dm (WitnessCertificates.Batch000.certificate18).beta) ≤ ((CutFailureCertificates.Budget000.certificate18).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound18 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate18).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch002.certificate27).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch002.certificate28).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch000.certificate18).omega:ℝ) ≤ ((CutFailureCertificates.Budget000.certificate18).bound:ℝ) at hb
  exact (exponentialBound9 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches10 : (MergedCutGroups.Batch002.certificate30).GlobalMatches MergedCutGroups.Batch002.certificate31 CountingCertificates.Batch001.certificate20 CutLabelCertificates.Entropy000.certificate11 CutLabelCertificates.Minority000.certificate10 := by decide +kernel
theorem exponentialBound10 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch002.certificate30).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate20).dm (WitnessCertificates.Batch001.certificate20).beta) ≤ (2*exp (-((CountingCertificates.Batch001.certificate20).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch002.certificate30).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch002.certificate31).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch001.certificate20).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch002.certificate30 MergedCutGroups.Batch002.certificate31 CountingCertificates.Batch001.certificate20 CutLabelCertificates.Entropy000.certificate11 CutLabelCertificates.Minority000.certificate10 matches10 rfl rfl
    MergedCutGroups.Batch002.numericValid30 MergedCutGroups.Batch002.numericValid31 MergedCutGroups.Batch002.cellsSound30 MergedCutGroups.Batch002.cellsSound31
    MergedCutGroups.Batch002.cellsNumeric30 MergedCutGroups.Batch002.cellsNumeric31 MergedCutGroups.Batch002.populationMatches30 MergedCutGroups.Batch002.populationMatches31
    PopulationCertificates.Batch001.valid20 PopulationCertificates.Batch001.sound20 WitnessCertificates.Batch001.valid20 WitnessCertificates.Batch001.sound20 CountingCertificates.Batch001.valid20 CountingCertificates.Batch001.sound20
    CutLabelCertificates.Entropy000.valid11 CutLabelCertificates.Minority000.valid10 CutLabelCertificates.Minority000.sound10 H st hI
theorem probabilityBound10 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch002.certificate30).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate20).dm (WitnessCertificates.Batch001.certificate20).beta) ≤ ((CutFailureCertificates.Budget001.certificate20).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound20 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate20).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch002.certificate30).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch002.certificate31).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch001.certificate20).omega:ℝ) ≤ ((CutFailureCertificates.Budget001.certificate20).bound:ℝ) at hb
  exact (exponentialBound10 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches11 : (MergedCutGroups.Batch002.certificate33).GlobalMatches MergedCutGroups.Batch002.certificate34 CountingCertificates.Batch001.certificate22 CutLabelCertificates.Entropy000.certificate12 CutLabelCertificates.Minority000.certificate11 := by decide +kernel
theorem exponentialBound11 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch002.certificate33).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate22).dm (WitnessCertificates.Batch001.certificate22).beta) ≤ (2*exp (-((CountingCertificates.Batch001.certificate22).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch002.certificate33).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch002.certificate34).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch001.certificate22).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch002.certificate33 MergedCutGroups.Batch002.certificate34 CountingCertificates.Batch001.certificate22 CutLabelCertificates.Entropy000.certificate12 CutLabelCertificates.Minority000.certificate11 matches11 rfl rfl
    MergedCutGroups.Batch002.numericValid33 MergedCutGroups.Batch002.numericValid34 MergedCutGroups.Batch002.cellsSound33 MergedCutGroups.Batch002.cellsSound34
    MergedCutGroups.Batch002.cellsNumeric33 MergedCutGroups.Batch002.cellsNumeric34 MergedCutGroups.Batch002.populationMatches33 MergedCutGroups.Batch002.populationMatches34
    PopulationCertificates.Batch001.valid22 PopulationCertificates.Batch001.sound22 WitnessCertificates.Batch001.valid22 WitnessCertificates.Batch001.sound22 CountingCertificates.Batch001.valid22 CountingCertificates.Batch001.sound22
    CutLabelCertificates.Entropy000.valid12 CutLabelCertificates.Minority000.valid11 CutLabelCertificates.Minority000.sound11 H st hI
theorem probabilityBound11 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch002.certificate33).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate22).dm (WitnessCertificates.Batch001.certificate22).beta) ≤ ((CutFailureCertificates.Budget001.certificate22).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound22 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate22).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch002.certificate33).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch002.certificate34).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch001.certificate22).omega:ℝ) ≤ ((CutFailureCertificates.Budget001.certificate22).bound:ℝ) at hb
  exact (exponentialBound11 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches12 : (MergedCutGroups.Batch003.certificate36).GlobalMatches MergedCutGroups.Batch003.certificate37 CountingCertificates.Batch001.certificate24 CutLabelCertificates.Entropy000.certificate13 CutLabelCertificates.Minority000.certificate12 := by decide +kernel
theorem exponentialBound12 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch003.certificate36).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate24).dm (WitnessCertificates.Batch001.certificate24).beta) ≤ (2*exp (-((CountingCertificates.Batch001.certificate24).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch003.certificate36).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch003.certificate37).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch001.certificate24).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch003.certificate36 MergedCutGroups.Batch003.certificate37 CountingCertificates.Batch001.certificate24 CutLabelCertificates.Entropy000.certificate13 CutLabelCertificates.Minority000.certificate12 matches12 rfl rfl
    MergedCutGroups.Batch003.numericValid36 MergedCutGroups.Batch003.numericValid37 MergedCutGroups.Batch003.cellsSound36 MergedCutGroups.Batch003.cellsSound37
    MergedCutGroups.Batch003.cellsNumeric36 MergedCutGroups.Batch003.cellsNumeric37 MergedCutGroups.Batch003.populationMatches36 MergedCutGroups.Batch003.populationMatches37
    PopulationCertificates.Batch001.valid24 PopulationCertificates.Batch001.sound24 WitnessCertificates.Batch001.valid24 WitnessCertificates.Batch001.sound24 CountingCertificates.Batch001.valid24 CountingCertificates.Batch001.sound24
    CutLabelCertificates.Entropy000.valid13 CutLabelCertificates.Minority000.valid12 CutLabelCertificates.Minority000.sound12 H st hI
theorem probabilityBound12 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch003.certificate36).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate24).dm (WitnessCertificates.Batch001.certificate24).beta) ≤ ((CutFailureCertificates.Budget001.certificate24).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound24 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate24).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch003.certificate36).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch003.certificate37).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch001.certificate24).omega:ℝ) ≤ ((CutFailureCertificates.Budget001.certificate24).bound:ℝ) at hb
  exact (exponentialBound12 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches13 : (MergedCutGroups.Batch003.certificate39).GlobalMatches MergedCutGroups.Batch003.certificate40 CountingCertificates.Batch001.certificate26 CutLabelCertificates.Entropy000.certificate14 CutLabelCertificates.Minority000.certificate13 := by decide +kernel
theorem exponentialBound13 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch003.certificate39).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate26).dm (WitnessCertificates.Batch001.certificate26).beta) ≤ (2*exp (-((CountingCertificates.Batch001.certificate26).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch003.certificate39).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch003.certificate40).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch001.certificate26).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch003.certificate39 MergedCutGroups.Batch003.certificate40 CountingCertificates.Batch001.certificate26 CutLabelCertificates.Entropy000.certificate14 CutLabelCertificates.Minority000.certificate13 matches13 rfl rfl
    MergedCutGroups.Batch003.numericValid39 MergedCutGroups.Batch003.numericValid40 MergedCutGroups.Batch003.cellsSound39 MergedCutGroups.Batch003.cellsSound40
    MergedCutGroups.Batch003.cellsNumeric39 MergedCutGroups.Batch003.cellsNumeric40 MergedCutGroups.Batch003.populationMatches39 MergedCutGroups.Batch003.populationMatches40
    PopulationCertificates.Batch001.valid26 PopulationCertificates.Batch001.sound26 WitnessCertificates.Batch001.valid26 WitnessCertificates.Batch001.sound26 CountingCertificates.Batch001.valid26 CountingCertificates.Batch001.sound26
    CutLabelCertificates.Entropy000.valid14 CutLabelCertificates.Minority000.valid13 CutLabelCertificates.Minority000.sound13 H st hI
theorem probabilityBound13 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch003.certificate39).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate26).dm (WitnessCertificates.Batch001.certificate26).beta) ≤ ((CutFailureCertificates.Budget001.certificate26).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound26 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate26).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch003.certificate39).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch003.certificate40).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch001.certificate26).omega:ℝ) ≤ ((CutFailureCertificates.Budget001.certificate26).bound:ℝ) at hb
  exact (exponentialBound13 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches14 : (MergedCutGroups.Batch003.certificate42).GlobalMatches MergedCutGroups.Batch003.certificate43 CountingCertificates.Batch001.certificate28 CutLabelCertificates.Entropy000.certificate15 CutLabelCertificates.Minority000.certificate14 := by decide +kernel
theorem exponentialBound14 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch003.certificate42).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate28).dm (WitnessCertificates.Batch001.certificate28).beta) ≤ (2*exp (-((CountingCertificates.Batch001.certificate28).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch003.certificate42).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch003.certificate43).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch001.certificate28).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch003.certificate42 MergedCutGroups.Batch003.certificate43 CountingCertificates.Batch001.certificate28 CutLabelCertificates.Entropy000.certificate15 CutLabelCertificates.Minority000.certificate14 matches14 rfl rfl
    MergedCutGroups.Batch003.numericValid42 MergedCutGroups.Batch003.numericValid43 MergedCutGroups.Batch003.cellsSound42 MergedCutGroups.Batch003.cellsSound43
    MergedCutGroups.Batch003.cellsNumeric42 MergedCutGroups.Batch003.cellsNumeric43 MergedCutGroups.Batch003.populationMatches42 MergedCutGroups.Batch003.populationMatches43
    PopulationCertificates.Batch001.valid28 PopulationCertificates.Batch001.sound28 WitnessCertificates.Batch001.valid28 WitnessCertificates.Batch001.sound28 CountingCertificates.Batch001.valid28 CountingCertificates.Batch001.sound28
    CutLabelCertificates.Entropy000.valid15 CutLabelCertificates.Minority000.valid14 CutLabelCertificates.Minority000.sound14 H st hI
theorem probabilityBound14 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch003.certificate42).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate28).dm (WitnessCertificates.Batch001.certificate28).beta) ≤ ((CutFailureCertificates.Budget001.certificate28).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound28 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate28).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch003.certificate42).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch003.certificate43).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch001.certificate28).omega:ℝ) ≤ ((CutFailureCertificates.Budget001.certificate28).bound:ℝ) at hb
  exact (exponentialBound14 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches15 : (MergedCutGroups.Batch003.certificate45).GlobalMatches MergedCutGroups.Batch003.certificate46 CountingCertificates.Batch001.certificate30 CutLabelCertificates.Entropy000.certificate16 CutLabelCertificates.Minority000.certificate15 := by decide +kernel
theorem exponentialBound15 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch003.certificate45).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate30).dm (WitnessCertificates.Batch001.certificate30).beta) ≤ (2*exp (-((CountingCertificates.Batch001.certificate30).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch003.certificate45).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch003.certificate46).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch001.certificate30).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch003.certificate45 MergedCutGroups.Batch003.certificate46 CountingCertificates.Batch001.certificate30 CutLabelCertificates.Entropy000.certificate16 CutLabelCertificates.Minority000.certificate15 matches15 rfl rfl
    MergedCutGroups.Batch003.numericValid45 MergedCutGroups.Batch003.numericValid46 MergedCutGroups.Batch003.cellsSound45 MergedCutGroups.Batch003.cellsSound46
    MergedCutGroups.Batch003.cellsNumeric45 MergedCutGroups.Batch003.cellsNumeric46 MergedCutGroups.Batch003.populationMatches45 MergedCutGroups.Batch003.populationMatches46
    PopulationCertificates.Batch001.valid30 PopulationCertificates.Batch001.sound30 WitnessCertificates.Batch001.valid30 WitnessCertificates.Batch001.sound30 CountingCertificates.Batch001.valid30 CountingCertificates.Batch001.sound30
    CutLabelCertificates.Entropy000.valid16 CutLabelCertificates.Minority000.valid15 CutLabelCertificates.Minority000.sound15 H st hI
theorem probabilityBound15 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch003.certificate45).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate30).dm (WitnessCertificates.Batch001.certificate30).beta) ≤ ((CutFailureCertificates.Budget001.certificate30).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound30 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate30).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch003.certificate45).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch003.certificate46).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch001.certificate30).omega:ℝ) ≤ ((CutFailureCertificates.Budget001.certificate30).bound:ℝ) at hb
  exact (exponentialBound15 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches16 : (MergedCutGroups.Batch004.certificate48).GlobalMatches MergedCutGroups.Batch004.certificate49 CountingCertificates.Batch001.certificate32 CutLabelCertificates.Entropy000.certificate17 CutLabelCertificates.Minority000.certificate16 := by decide +kernel
theorem exponentialBound16 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch004.certificate48).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate32).dm (WitnessCertificates.Batch001.certificate32).beta) ≤ (2*exp (-((CountingCertificates.Batch001.certificate32).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch004.certificate48).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch004.certificate49).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch001.certificate32).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch004.certificate48 MergedCutGroups.Batch004.certificate49 CountingCertificates.Batch001.certificate32 CutLabelCertificates.Entropy000.certificate17 CutLabelCertificates.Minority000.certificate16 matches16 rfl rfl
    MergedCutGroups.Batch004.numericValid48 MergedCutGroups.Batch004.numericValid49 MergedCutGroups.Batch004.cellsSound48 MergedCutGroups.Batch004.cellsSound49
    MergedCutGroups.Batch004.cellsNumeric48 MergedCutGroups.Batch004.cellsNumeric49 MergedCutGroups.Batch004.populationMatches48 MergedCutGroups.Batch004.populationMatches49
    PopulationCertificates.Batch001.valid32 PopulationCertificates.Batch001.sound32 WitnessCertificates.Batch001.valid32 WitnessCertificates.Batch001.sound32 CountingCertificates.Batch001.valid32 CountingCertificates.Batch001.sound32
    CutLabelCertificates.Entropy000.valid17 CutLabelCertificates.Minority000.valid16 CutLabelCertificates.Minority000.sound16 H st hI
theorem probabilityBound16 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch004.certificate48).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate32).dm (WitnessCertificates.Batch001.certificate32).beta) ≤ ((CutFailureCertificates.Budget001.certificate32).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound32 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate32).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch004.certificate48).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch004.certificate49).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch001.certificate32).omega:ℝ) ≤ ((CutFailureCertificates.Budget001.certificate32).bound:ℝ) at hb
  exact (exponentialBound16 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches17 : (MergedCutGroups.Batch004.certificate51).GlobalMatches MergedCutGroups.Batch004.certificate52 CountingCertificates.Batch001.certificate34 CutLabelCertificates.Entropy000.certificate18 CutLabelCertificates.Minority000.certificate17 := by decide +kernel
theorem exponentialBound17 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch004.certificate51).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate34).dm (WitnessCertificates.Batch001.certificate34).beta) ≤ (2*exp (-((CountingCertificates.Batch001.certificate34).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch004.certificate51).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch004.certificate52).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch001.certificate34).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch004.certificate51 MergedCutGroups.Batch004.certificate52 CountingCertificates.Batch001.certificate34 CutLabelCertificates.Entropy000.certificate18 CutLabelCertificates.Minority000.certificate17 matches17 rfl rfl
    MergedCutGroups.Batch004.numericValid51 MergedCutGroups.Batch004.numericValid52 MergedCutGroups.Batch004.cellsSound51 MergedCutGroups.Batch004.cellsSound52
    MergedCutGroups.Batch004.cellsNumeric51 MergedCutGroups.Batch004.cellsNumeric52 MergedCutGroups.Batch004.populationMatches51 MergedCutGroups.Batch004.populationMatches52
    PopulationCertificates.Batch001.valid34 PopulationCertificates.Batch001.sound34 WitnessCertificates.Batch001.valid34 WitnessCertificates.Batch001.sound34 CountingCertificates.Batch001.valid34 CountingCertificates.Batch001.sound34
    CutLabelCertificates.Entropy000.valid18 CutLabelCertificates.Minority000.valid17 CutLabelCertificates.Minority000.sound17 H st hI
theorem probabilityBound17 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch004.certificate51).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate34).dm (WitnessCertificates.Batch001.certificate34).beta) ≤ ((CutFailureCertificates.Budget001.certificate34).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound34 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate34).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch004.certificate51).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch004.certificate52).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch001.certificate34).omega:ℝ) ≤ ((CutFailureCertificates.Budget001.certificate34).bound:ℝ) at hb
  exact (exponentialBound17 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches18 : (MergedCutGroups.Batch004.certificate54).GlobalMatches MergedCutGroups.Batch004.certificate55 CountingCertificates.Batch001.certificate36 CutLabelCertificates.Entropy000.certificate19 CutLabelCertificates.Minority000.certificate18 := by decide +kernel
theorem exponentialBound18 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch004.certificate54).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate36).dm (WitnessCertificates.Batch001.certificate36).beta) ≤ (2*exp (-((CountingCertificates.Batch001.certificate36).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch004.certificate54).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch004.certificate55).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch001.certificate36).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch004.certificate54 MergedCutGroups.Batch004.certificate55 CountingCertificates.Batch001.certificate36 CutLabelCertificates.Entropy000.certificate19 CutLabelCertificates.Minority000.certificate18 matches18 rfl rfl
    MergedCutGroups.Batch004.numericValid54 MergedCutGroups.Batch004.numericValid55 MergedCutGroups.Batch004.cellsSound54 MergedCutGroups.Batch004.cellsSound55
    MergedCutGroups.Batch004.cellsNumeric54 MergedCutGroups.Batch004.cellsNumeric55 MergedCutGroups.Batch004.populationMatches54 MergedCutGroups.Batch004.populationMatches55
    PopulationCertificates.Batch001.valid36 PopulationCertificates.Batch001.sound36 WitnessCertificates.Batch001.valid36 WitnessCertificates.Batch001.sound36 CountingCertificates.Batch001.valid36 CountingCertificates.Batch001.sound36
    CutLabelCertificates.Entropy000.valid19 CutLabelCertificates.Minority000.valid18 CutLabelCertificates.Minority000.sound18 H st hI
theorem probabilityBound18 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch004.certificate54).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate36).dm (WitnessCertificates.Batch001.certificate36).beta) ≤ ((CutFailureCertificates.Budget001.certificate36).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound36 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate36).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch004.certificate54).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch004.certificate55).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch001.certificate36).omega:ℝ) ≤ ((CutFailureCertificates.Budget001.certificate36).bound:ℝ) at hb
  exact (exponentialBound18 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches19 : (MergedCutGroups.Batch004.certificate57).GlobalMatches MergedCutGroups.Batch004.certificate58 CountingCertificates.Batch001.certificate38 CutLabelCertificates.Entropy001.certificate20 CutLabelCertificates.Minority000.certificate19 := by decide +kernel
theorem exponentialBound19 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch004.certificate57).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate38).dm (WitnessCertificates.Batch001.certificate38).beta) ≤ (2*exp (-((CountingCertificates.Batch001.certificate38).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch004.certificate57).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch004.certificate58).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch001.certificate38).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch004.certificate57 MergedCutGroups.Batch004.certificate58 CountingCertificates.Batch001.certificate38 CutLabelCertificates.Entropy001.certificate20 CutLabelCertificates.Minority000.certificate19 matches19 rfl rfl
    MergedCutGroups.Batch004.numericValid57 MergedCutGroups.Batch004.numericValid58 MergedCutGroups.Batch004.cellsSound57 MergedCutGroups.Batch004.cellsSound58
    MergedCutGroups.Batch004.cellsNumeric57 MergedCutGroups.Batch004.cellsNumeric58 MergedCutGroups.Batch004.populationMatches57 MergedCutGroups.Batch004.populationMatches58
    PopulationCertificates.Batch001.valid38 PopulationCertificates.Batch001.sound38 WitnessCertificates.Batch001.valid38 WitnessCertificates.Batch001.sound38 CountingCertificates.Batch001.valid38 CountingCertificates.Batch001.sound38
    CutLabelCertificates.Entropy001.valid20 CutLabelCertificates.Minority000.valid19 CutLabelCertificates.Minority000.sound19 H st hI
theorem probabilityBound19 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch004.certificate57).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch001.certificate38).dm (WitnessCertificates.Batch001.certificate38).beta) ≤ ((CutFailureCertificates.Budget001.certificate38).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound38 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate38).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch004.certificate57).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch004.certificate58).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch001.certificate38).omega:ℝ) ≤ ((CutFailureCertificates.Budget001.certificate38).bound:ℝ) at hb
  exact (exponentialBound19 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch000
