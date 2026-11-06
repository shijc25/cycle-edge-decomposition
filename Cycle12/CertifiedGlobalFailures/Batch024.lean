import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch051
import Cycle12.CountingCertificates.Batch052
import Cycle12.CountingCertificates.Batch053
import Cycle12.CutFailureCertificates.Budget051
import Cycle12.CutFailureCertificates.Budget052
import Cycle12.CutFailureCertificates.Budget053
import Cycle12.CutLabelCertificates.Entropy037
import Cycle12.CutLabelCertificates.Entropy038
import Cycle12.CutLabelCertificates.Entropy039
import Cycle12.CutLabelCertificates.Entropy040
import Cycle12.CutLabelCertificates.Entropy041
import Cycle12.CutLabelCertificates.Minority037
import Cycle12.CutLabelCertificates.Minority038
import Cycle12.CutLabelCertificates.Minority039
import Cycle12.CutLabelCertificates.Minority040
import Cycle12.CutLabelCertificates.Minority041
import Cycle12.MergedCutGroups.Batch125
import Cycle12.MergedCutGroups.Batch126
import Cycle12.MergedCutGroups.Batch127
import Cycle12.MergedCutGroups.Batch128
import Cycle12.MergedCutGroups.Batch129
import Cycle12.PopulationCertificates.Batch051
import Cycle12.PopulationCertificates.Batch052
import Cycle12.PopulationCertificates.Batch053
import Cycle12.WitnessCertificates.Batch051
import Cycle12.WitnessCertificates.Batch052
import Cycle12.WitnessCertificates.Batch053

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch024
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches480 : (MergedCutGroups.Batch125.certificate1505).GlobalMatches MergedCutGroups.Batch125.certificate1506 CountingCertificates.Batch051.certificate1025 CutLabelCertificates.Entropy037.certificate745 CutLabelCertificates.Minority037.certificate744 := by decide +kernel
theorem exponentialBound480 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch125.certificate1505).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1025).dm (WitnessCertificates.Batch051.certificate1025).beta) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1025).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch125.certificate1505).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch125.certificate1506).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch051.certificate1025).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch125.certificate1505 MergedCutGroups.Batch125.certificate1506 CountingCertificates.Batch051.certificate1025 CutLabelCertificates.Entropy037.certificate745 CutLabelCertificates.Minority037.certificate744 matches480 rfl rfl
    MergedCutGroups.Batch125.numericValid1505 MergedCutGroups.Batch125.numericValid1506 MergedCutGroups.Batch125.cellsSound1505 MergedCutGroups.Batch125.cellsSound1506
    MergedCutGroups.Batch125.cellsNumeric1505 MergedCutGroups.Batch125.cellsNumeric1506 MergedCutGroups.Batch125.populationMatches1505 MergedCutGroups.Batch125.populationMatches1506
    PopulationCertificates.Batch051.valid1025 PopulationCertificates.Batch051.sound1025 WitnessCertificates.Batch051.valid1025 WitnessCertificates.Batch051.sound1025 CountingCertificates.Batch051.valid1025 CountingCertificates.Batch051.sound1025
    CutLabelCertificates.Entropy037.valid745 CutLabelCertificates.Minority037.valid744 CutLabelCertificates.Minority037.sound744 H st hI
theorem probabilityBound480 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch125.certificate1505).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1025).dm (WitnessCertificates.Batch051.certificate1025).beta) ≤ ((CutFailureCertificates.Budget051.certificate1025).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1025 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1025).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch125.certificate1505).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch125.certificate1506).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch051.certificate1025).omega:ℝ) ≤ ((CutFailureCertificates.Budget051.certificate1025).bound:ℝ) at hb
  exact (exponentialBound480 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches481 : (MergedCutGroups.Batch125.certificate1509).GlobalMatches MergedCutGroups.Batch125.certificate1510 CountingCertificates.Batch051.certificate1028 CutLabelCertificates.Entropy037.certificate751 CutLabelCertificates.Minority037.certificate750 := by decide +kernel
theorem exponentialBound481 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch125.certificate1509).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1028).dm (WitnessCertificates.Batch051.certificate1028).beta) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1028).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch125.certificate1509).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch125.certificate1510).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch051.certificate1028).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch125.certificate1509 MergedCutGroups.Batch125.certificate1510 CountingCertificates.Batch051.certificate1028 CutLabelCertificates.Entropy037.certificate751 CutLabelCertificates.Minority037.certificate750 matches481 rfl rfl
    MergedCutGroups.Batch125.numericValid1509 MergedCutGroups.Batch125.numericValid1510 MergedCutGroups.Batch125.cellsSound1509 MergedCutGroups.Batch125.cellsSound1510
    MergedCutGroups.Batch125.cellsNumeric1509 MergedCutGroups.Batch125.cellsNumeric1510 MergedCutGroups.Batch125.populationMatches1509 MergedCutGroups.Batch125.populationMatches1510
    PopulationCertificates.Batch051.valid1028 PopulationCertificates.Batch051.sound1028 WitnessCertificates.Batch051.valid1028 WitnessCertificates.Batch051.sound1028 CountingCertificates.Batch051.valid1028 CountingCertificates.Batch051.sound1028
    CutLabelCertificates.Entropy037.valid751 CutLabelCertificates.Minority037.valid750 CutLabelCertificates.Minority037.sound750 H st hI
theorem probabilityBound481 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch125.certificate1509).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1028).dm (WitnessCertificates.Batch051.certificate1028).beta) ≤ ((CutFailureCertificates.Budget051.certificate1028).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1028 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1028).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch125.certificate1509).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch125.certificate1510).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch051.certificate1028).omega:ℝ) ≤ ((CutFailureCertificates.Budget051.certificate1028).bound:ℝ) at hb
  exact (exponentialBound481 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches482 : (MergedCutGroups.Batch126.certificate1513).GlobalMatches MergedCutGroups.Batch126.certificate1514 CountingCertificates.Batch051.certificate1031 CutLabelCertificates.Entropy037.certificate757 CutLabelCertificates.Minority037.certificate756 := by decide +kernel
theorem exponentialBound482 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch126.certificate1513).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1031).dm (WitnessCertificates.Batch051.certificate1031).beta) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1031).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch126.certificate1513).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch126.certificate1514).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch051.certificate1031).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch126.certificate1513 MergedCutGroups.Batch126.certificate1514 CountingCertificates.Batch051.certificate1031 CutLabelCertificates.Entropy037.certificate757 CutLabelCertificates.Minority037.certificate756 matches482 rfl rfl
    MergedCutGroups.Batch126.numericValid1513 MergedCutGroups.Batch126.numericValid1514 MergedCutGroups.Batch126.cellsSound1513 MergedCutGroups.Batch126.cellsSound1514
    MergedCutGroups.Batch126.cellsNumeric1513 MergedCutGroups.Batch126.cellsNumeric1514 MergedCutGroups.Batch126.populationMatches1513 MergedCutGroups.Batch126.populationMatches1514
    PopulationCertificates.Batch051.valid1031 PopulationCertificates.Batch051.sound1031 WitnessCertificates.Batch051.valid1031 WitnessCertificates.Batch051.sound1031 CountingCertificates.Batch051.valid1031 CountingCertificates.Batch051.sound1031
    CutLabelCertificates.Entropy037.valid757 CutLabelCertificates.Minority037.valid756 CutLabelCertificates.Minority037.sound756 H st hI
theorem probabilityBound482 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch126.certificate1513).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1031).dm (WitnessCertificates.Batch051.certificate1031).beta) ≤ ((CutFailureCertificates.Budget051.certificate1031).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1031 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1031).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch126.certificate1513).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch126.certificate1514).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch051.certificate1031).omega:ℝ) ≤ ((CutFailureCertificates.Budget051.certificate1031).bound:ℝ) at hb
  exact (exponentialBound482 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches483 : (MergedCutGroups.Batch126.certificate1517).GlobalMatches MergedCutGroups.Batch126.certificate1518 CountingCertificates.Batch051.certificate1034 CutLabelCertificates.Entropy038.certificate763 CutLabelCertificates.Minority038.certificate762 := by decide +kernel
theorem exponentialBound483 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch126.certificate1517).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1034).dm (WitnessCertificates.Batch051.certificate1034).beta) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1034).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch126.certificate1517).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch126.certificate1518).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch051.certificate1034).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch126.certificate1517 MergedCutGroups.Batch126.certificate1518 CountingCertificates.Batch051.certificate1034 CutLabelCertificates.Entropy038.certificate763 CutLabelCertificates.Minority038.certificate762 matches483 rfl rfl
    MergedCutGroups.Batch126.numericValid1517 MergedCutGroups.Batch126.numericValid1518 MergedCutGroups.Batch126.cellsSound1517 MergedCutGroups.Batch126.cellsSound1518
    MergedCutGroups.Batch126.cellsNumeric1517 MergedCutGroups.Batch126.cellsNumeric1518 MergedCutGroups.Batch126.populationMatches1517 MergedCutGroups.Batch126.populationMatches1518
    PopulationCertificates.Batch051.valid1034 PopulationCertificates.Batch051.sound1034 WitnessCertificates.Batch051.valid1034 WitnessCertificates.Batch051.sound1034 CountingCertificates.Batch051.valid1034 CountingCertificates.Batch051.sound1034
    CutLabelCertificates.Entropy038.valid763 CutLabelCertificates.Minority038.valid762 CutLabelCertificates.Minority038.sound762 H st hI
theorem probabilityBound483 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch126.certificate1517).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1034).dm (WitnessCertificates.Batch051.certificate1034).beta) ≤ ((CutFailureCertificates.Budget051.certificate1034).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1034 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1034).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch126.certificate1517).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch126.certificate1518).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch051.certificate1034).omega:ℝ) ≤ ((CutFailureCertificates.Budget051.certificate1034).bound:ℝ) at hb
  exact (exponentialBound483 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches484 : (MergedCutGroups.Batch126.certificate1521).GlobalMatches MergedCutGroups.Batch126.certificate1522 CountingCertificates.Batch051.certificate1037 CutLabelCertificates.Entropy038.certificate769 CutLabelCertificates.Minority038.certificate768 := by decide +kernel
theorem exponentialBound484 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch126.certificate1521).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1037).dm (WitnessCertificates.Batch051.certificate1037).beta) ≤ (2*exp (-((CountingCertificates.Batch051.certificate1037).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch126.certificate1521).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch126.certificate1522).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch051.certificate1037).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch126.certificate1521 MergedCutGroups.Batch126.certificate1522 CountingCertificates.Batch051.certificate1037 CutLabelCertificates.Entropy038.certificate769 CutLabelCertificates.Minority038.certificate768 matches484 rfl rfl
    MergedCutGroups.Batch126.numericValid1521 MergedCutGroups.Batch126.numericValid1522 MergedCutGroups.Batch126.cellsSound1521 MergedCutGroups.Batch126.cellsSound1522
    MergedCutGroups.Batch126.cellsNumeric1521 MergedCutGroups.Batch126.cellsNumeric1522 MergedCutGroups.Batch126.populationMatches1521 MergedCutGroups.Batch126.populationMatches1522
    PopulationCertificates.Batch051.valid1037 PopulationCertificates.Batch051.sound1037 WitnessCertificates.Batch051.valid1037 WitnessCertificates.Batch051.sound1037 CountingCertificates.Batch051.valid1037 CountingCertificates.Batch051.sound1037
    CutLabelCertificates.Entropy038.valid769 CutLabelCertificates.Minority038.valid768 CutLabelCertificates.Minority038.sound768 H st hI
theorem probabilityBound484 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch126.certificate1521).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch051.certificate1037).dm (WitnessCertificates.Batch051.certificate1037).beta) ≤ ((CutFailureCertificates.Budget051.certificate1037).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget051.sound1037 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch051.certificate1037).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch126.certificate1521).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch126.certificate1522).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch051.certificate1037).omega:ℝ) ≤ ((CutFailureCertificates.Budget051.certificate1037).bound:ℝ) at hb
  exact (exponentialBound484 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches485 : (MergedCutGroups.Batch127.certificate1525).GlobalMatches MergedCutGroups.Batch127.certificate1526 CountingCertificates.Batch052.certificate1040 CutLabelCertificates.Entropy038.certificate775 CutLabelCertificates.Minority038.certificate774 := by decide +kernel
theorem exponentialBound485 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch127.certificate1525).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1040).dm (WitnessCertificates.Batch052.certificate1040).beta) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1040).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch127.certificate1525).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch127.certificate1526).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch052.certificate1040).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch127.certificate1525 MergedCutGroups.Batch127.certificate1526 CountingCertificates.Batch052.certificate1040 CutLabelCertificates.Entropy038.certificate775 CutLabelCertificates.Minority038.certificate774 matches485 rfl rfl
    MergedCutGroups.Batch127.numericValid1525 MergedCutGroups.Batch127.numericValid1526 MergedCutGroups.Batch127.cellsSound1525 MergedCutGroups.Batch127.cellsSound1526
    MergedCutGroups.Batch127.cellsNumeric1525 MergedCutGroups.Batch127.cellsNumeric1526 MergedCutGroups.Batch127.populationMatches1525 MergedCutGroups.Batch127.populationMatches1526
    PopulationCertificates.Batch052.valid1040 PopulationCertificates.Batch052.sound1040 WitnessCertificates.Batch052.valid1040 WitnessCertificates.Batch052.sound1040 CountingCertificates.Batch052.valid1040 CountingCertificates.Batch052.sound1040
    CutLabelCertificates.Entropy038.valid775 CutLabelCertificates.Minority038.valid774 CutLabelCertificates.Minority038.sound774 H st hI
theorem probabilityBound485 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch127.certificate1525).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1040).dm (WitnessCertificates.Batch052.certificate1040).beta) ≤ ((CutFailureCertificates.Budget052.certificate1040).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1040 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1040).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch127.certificate1525).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch127.certificate1526).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch052.certificate1040).omega:ℝ) ≤ ((CutFailureCertificates.Budget052.certificate1040).bound:ℝ) at hb
  exact (exponentialBound485 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches486 : (MergedCutGroups.Batch127.certificate1529).GlobalMatches MergedCutGroups.Batch127.certificate1530 CountingCertificates.Batch052.certificate1043 CutLabelCertificates.Entropy039.certificate781 CutLabelCertificates.Minority039.certificate780 := by decide +kernel
theorem exponentialBound486 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch127.certificate1529).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1043).dm (WitnessCertificates.Batch052.certificate1043).beta) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1043).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch127.certificate1529).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch127.certificate1530).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch052.certificate1043).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch127.certificate1529 MergedCutGroups.Batch127.certificate1530 CountingCertificates.Batch052.certificate1043 CutLabelCertificates.Entropy039.certificate781 CutLabelCertificates.Minority039.certificate780 matches486 rfl rfl
    MergedCutGroups.Batch127.numericValid1529 MergedCutGroups.Batch127.numericValid1530 MergedCutGroups.Batch127.cellsSound1529 MergedCutGroups.Batch127.cellsSound1530
    MergedCutGroups.Batch127.cellsNumeric1529 MergedCutGroups.Batch127.cellsNumeric1530 MergedCutGroups.Batch127.populationMatches1529 MergedCutGroups.Batch127.populationMatches1530
    PopulationCertificates.Batch052.valid1043 PopulationCertificates.Batch052.sound1043 WitnessCertificates.Batch052.valid1043 WitnessCertificates.Batch052.sound1043 CountingCertificates.Batch052.valid1043 CountingCertificates.Batch052.sound1043
    CutLabelCertificates.Entropy039.valid781 CutLabelCertificates.Minority039.valid780 CutLabelCertificates.Minority039.sound780 H st hI
theorem probabilityBound486 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch127.certificate1529).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1043).dm (WitnessCertificates.Batch052.certificate1043).beta) ≤ ((CutFailureCertificates.Budget052.certificate1043).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1043 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1043).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch127.certificate1529).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch127.certificate1530).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch052.certificate1043).omega:ℝ) ≤ ((CutFailureCertificates.Budget052.certificate1043).bound:ℝ) at hb
  exact (exponentialBound486 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches487 : (MergedCutGroups.Batch127.certificate1533).GlobalMatches MergedCutGroups.Batch127.certificate1534 CountingCertificates.Batch052.certificate1046 CutLabelCertificates.Entropy039.certificate787 CutLabelCertificates.Minority039.certificate786 := by decide +kernel
theorem exponentialBound487 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch127.certificate1533).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1046).dm (WitnessCertificates.Batch052.certificate1046).beta) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1046).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch127.certificate1533).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch127.certificate1534).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch052.certificate1046).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch127.certificate1533 MergedCutGroups.Batch127.certificate1534 CountingCertificates.Batch052.certificate1046 CutLabelCertificates.Entropy039.certificate787 CutLabelCertificates.Minority039.certificate786 matches487 rfl rfl
    MergedCutGroups.Batch127.numericValid1533 MergedCutGroups.Batch127.numericValid1534 MergedCutGroups.Batch127.cellsSound1533 MergedCutGroups.Batch127.cellsSound1534
    MergedCutGroups.Batch127.cellsNumeric1533 MergedCutGroups.Batch127.cellsNumeric1534 MergedCutGroups.Batch127.populationMatches1533 MergedCutGroups.Batch127.populationMatches1534
    PopulationCertificates.Batch052.valid1046 PopulationCertificates.Batch052.sound1046 WitnessCertificates.Batch052.valid1046 WitnessCertificates.Batch052.sound1046 CountingCertificates.Batch052.valid1046 CountingCertificates.Batch052.sound1046
    CutLabelCertificates.Entropy039.valid787 CutLabelCertificates.Minority039.valid786 CutLabelCertificates.Minority039.sound786 H st hI
theorem probabilityBound487 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch127.certificate1533).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1046).dm (WitnessCertificates.Batch052.certificate1046).beta) ≤ ((CutFailureCertificates.Budget052.certificate1046).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1046 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1046).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch127.certificate1533).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch127.certificate1534).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch052.certificate1046).omega:ℝ) ≤ ((CutFailureCertificates.Budget052.certificate1046).bound:ℝ) at hb
  exact (exponentialBound487 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches488 : (MergedCutGroups.Batch128.certificate1537).GlobalMatches MergedCutGroups.Batch128.certificate1538 CountingCertificates.Batch052.certificate1049 CutLabelCertificates.Entropy039.certificate793 CutLabelCertificates.Minority039.certificate792 := by decide +kernel
theorem exponentialBound488 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch128.certificate1537).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1049).dm (WitnessCertificates.Batch052.certificate1049).beta) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1049).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch128.certificate1537).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch128.certificate1538).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch052.certificate1049).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch128.certificate1537 MergedCutGroups.Batch128.certificate1538 CountingCertificates.Batch052.certificate1049 CutLabelCertificates.Entropy039.certificate793 CutLabelCertificates.Minority039.certificate792 matches488 rfl rfl
    MergedCutGroups.Batch128.numericValid1537 MergedCutGroups.Batch128.numericValid1538 MergedCutGroups.Batch128.cellsSound1537 MergedCutGroups.Batch128.cellsSound1538
    MergedCutGroups.Batch128.cellsNumeric1537 MergedCutGroups.Batch128.cellsNumeric1538 MergedCutGroups.Batch128.populationMatches1537 MergedCutGroups.Batch128.populationMatches1538
    PopulationCertificates.Batch052.valid1049 PopulationCertificates.Batch052.sound1049 WitnessCertificates.Batch052.valid1049 WitnessCertificates.Batch052.sound1049 CountingCertificates.Batch052.valid1049 CountingCertificates.Batch052.sound1049
    CutLabelCertificates.Entropy039.valid793 CutLabelCertificates.Minority039.valid792 CutLabelCertificates.Minority039.sound792 H st hI
theorem probabilityBound488 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch128.certificate1537).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1049).dm (WitnessCertificates.Batch052.certificate1049).beta) ≤ ((CutFailureCertificates.Budget052.certificate1049).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1049 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1049).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch128.certificate1537).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch128.certificate1538).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch052.certificate1049).omega:ℝ) ≤ ((CutFailureCertificates.Budget052.certificate1049).bound:ℝ) at hb
  exact (exponentialBound488 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches489 : (MergedCutGroups.Batch128.certificate1541).GlobalMatches MergedCutGroups.Batch128.certificate1542 CountingCertificates.Batch052.certificate1052 CutLabelCertificates.Entropy039.certificate799 CutLabelCertificates.Minority039.certificate798 := by decide +kernel
theorem exponentialBound489 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch128.certificate1541).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1052).dm (WitnessCertificates.Batch052.certificate1052).beta) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1052).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch128.certificate1541).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch128.certificate1542).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch052.certificate1052).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch128.certificate1541 MergedCutGroups.Batch128.certificate1542 CountingCertificates.Batch052.certificate1052 CutLabelCertificates.Entropy039.certificate799 CutLabelCertificates.Minority039.certificate798 matches489 rfl rfl
    MergedCutGroups.Batch128.numericValid1541 MergedCutGroups.Batch128.numericValid1542 MergedCutGroups.Batch128.cellsSound1541 MergedCutGroups.Batch128.cellsSound1542
    MergedCutGroups.Batch128.cellsNumeric1541 MergedCutGroups.Batch128.cellsNumeric1542 MergedCutGroups.Batch128.populationMatches1541 MergedCutGroups.Batch128.populationMatches1542
    PopulationCertificates.Batch052.valid1052 PopulationCertificates.Batch052.sound1052 WitnessCertificates.Batch052.valid1052 WitnessCertificates.Batch052.sound1052 CountingCertificates.Batch052.valid1052 CountingCertificates.Batch052.sound1052
    CutLabelCertificates.Entropy039.valid799 CutLabelCertificates.Minority039.valid798 CutLabelCertificates.Minority039.sound798 H st hI
theorem probabilityBound489 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch128.certificate1541).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1052).dm (WitnessCertificates.Batch052.certificate1052).beta) ≤ ((CutFailureCertificates.Budget052.certificate1052).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1052 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1052).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch128.certificate1541).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch128.certificate1542).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch052.certificate1052).omega:ℝ) ≤ ((CutFailureCertificates.Budget052.certificate1052).bound:ℝ) at hb
  exact (exponentialBound489 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches490 : (MergedCutGroups.Batch128.certificate1545).GlobalMatches MergedCutGroups.Batch128.certificate1546 CountingCertificates.Batch052.certificate1055 CutLabelCertificates.Entropy040.certificate805 CutLabelCertificates.Minority040.certificate804 := by decide +kernel
theorem exponentialBound490 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch128.certificate1545).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1055).dm (WitnessCertificates.Batch052.certificate1055).beta) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1055).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch128.certificate1545).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch128.certificate1546).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch052.certificate1055).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch128.certificate1545 MergedCutGroups.Batch128.certificate1546 CountingCertificates.Batch052.certificate1055 CutLabelCertificates.Entropy040.certificate805 CutLabelCertificates.Minority040.certificate804 matches490 rfl rfl
    MergedCutGroups.Batch128.numericValid1545 MergedCutGroups.Batch128.numericValid1546 MergedCutGroups.Batch128.cellsSound1545 MergedCutGroups.Batch128.cellsSound1546
    MergedCutGroups.Batch128.cellsNumeric1545 MergedCutGroups.Batch128.cellsNumeric1546 MergedCutGroups.Batch128.populationMatches1545 MergedCutGroups.Batch128.populationMatches1546
    PopulationCertificates.Batch052.valid1055 PopulationCertificates.Batch052.sound1055 WitnessCertificates.Batch052.valid1055 WitnessCertificates.Batch052.sound1055 CountingCertificates.Batch052.valid1055 CountingCertificates.Batch052.sound1055
    CutLabelCertificates.Entropy040.valid805 CutLabelCertificates.Minority040.valid804 CutLabelCertificates.Minority040.sound804 H st hI
theorem probabilityBound490 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch128.certificate1545).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1055).dm (WitnessCertificates.Batch052.certificate1055).beta) ≤ ((CutFailureCertificates.Budget052.certificate1055).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1055 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1055).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch128.certificate1545).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch128.certificate1546).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch052.certificate1055).omega:ℝ) ≤ ((CutFailureCertificates.Budget052.certificate1055).bound:ℝ) at hb
  exact (exponentialBound490 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches491 : (MergedCutGroups.Batch129.certificate1549).GlobalMatches MergedCutGroups.Batch129.certificate1550 CountingCertificates.Batch052.certificate1058 CutLabelCertificates.Entropy040.certificate811 CutLabelCertificates.Minority040.certificate810 := by decide +kernel
theorem exponentialBound491 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch129.certificate1549).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1058).dm (WitnessCertificates.Batch052.certificate1058).beta) ≤ (2*exp (-((CountingCertificates.Batch052.certificate1058).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch129.certificate1549).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch129.certificate1550).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch052.certificate1058).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch129.certificate1549 MergedCutGroups.Batch129.certificate1550 CountingCertificates.Batch052.certificate1058 CutLabelCertificates.Entropy040.certificate811 CutLabelCertificates.Minority040.certificate810 matches491 rfl rfl
    MergedCutGroups.Batch129.numericValid1549 MergedCutGroups.Batch129.numericValid1550 MergedCutGroups.Batch129.cellsSound1549 MergedCutGroups.Batch129.cellsSound1550
    MergedCutGroups.Batch129.cellsNumeric1549 MergedCutGroups.Batch129.cellsNumeric1550 MergedCutGroups.Batch129.populationMatches1549 MergedCutGroups.Batch129.populationMatches1550
    PopulationCertificates.Batch052.valid1058 PopulationCertificates.Batch052.sound1058 WitnessCertificates.Batch052.valid1058 WitnessCertificates.Batch052.sound1058 CountingCertificates.Batch052.valid1058 CountingCertificates.Batch052.sound1058
    CutLabelCertificates.Entropy040.valid811 CutLabelCertificates.Minority040.valid810 CutLabelCertificates.Minority040.sound810 H st hI
theorem probabilityBound491 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch129.certificate1549).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch052.certificate1058).dm (WitnessCertificates.Batch052.certificate1058).beta) ≤ ((CutFailureCertificates.Budget052.certificate1058).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget052.sound1058 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch052.certificate1058).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch129.certificate1549).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch129.certificate1550).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch052.certificate1058).omega:ℝ) ≤ ((CutFailureCertificates.Budget052.certificate1058).bound:ℝ) at hb
  exact (exponentialBound491 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches492 : (MergedCutGroups.Batch129.certificate1553).GlobalMatches MergedCutGroups.Batch129.certificate1554 CountingCertificates.Batch053.certificate1061 CutLabelCertificates.Entropy040.certificate817 CutLabelCertificates.Minority040.certificate816 := by decide +kernel
theorem exponentialBound492 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch129.certificate1553).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch053.certificate1061).dm (WitnessCertificates.Batch053.certificate1061).beta) ≤ (2*exp (-((CountingCertificates.Batch053.certificate1061).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch129.certificate1553).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch129.certificate1554).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch053.certificate1061).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch129.certificate1553 MergedCutGroups.Batch129.certificate1554 CountingCertificates.Batch053.certificate1061 CutLabelCertificates.Entropy040.certificate817 CutLabelCertificates.Minority040.certificate816 matches492 rfl rfl
    MergedCutGroups.Batch129.numericValid1553 MergedCutGroups.Batch129.numericValid1554 MergedCutGroups.Batch129.cellsSound1553 MergedCutGroups.Batch129.cellsSound1554
    MergedCutGroups.Batch129.cellsNumeric1553 MergedCutGroups.Batch129.cellsNumeric1554 MergedCutGroups.Batch129.populationMatches1553 MergedCutGroups.Batch129.populationMatches1554
    PopulationCertificates.Batch053.valid1061 PopulationCertificates.Batch053.sound1061 WitnessCertificates.Batch053.valid1061 WitnessCertificates.Batch053.sound1061 CountingCertificates.Batch053.valid1061 CountingCertificates.Batch053.sound1061
    CutLabelCertificates.Entropy040.valid817 CutLabelCertificates.Minority040.valid816 CutLabelCertificates.Minority040.sound816 H st hI
theorem probabilityBound492 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch129.certificate1553).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch053.certificate1061).dm (WitnessCertificates.Batch053.certificate1061).beta) ≤ ((CutFailureCertificates.Budget053.certificate1061).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget053.sound1061 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch053.certificate1061).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch129.certificate1553).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch129.certificate1554).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch053.certificate1061).omega:ℝ) ≤ ((CutFailureCertificates.Budget053.certificate1061).bound:ℝ) at hb
  exact (exponentialBound492 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches493 : (MergedCutGroups.Batch129.certificate1557).GlobalMatches MergedCutGroups.Batch129.certificate1558 CountingCertificates.Batch053.certificate1064 CutLabelCertificates.Entropy041.certificate823 CutLabelCertificates.Minority041.certificate822 := by decide +kernel
theorem exponentialBound493 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch129.certificate1557).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch053.certificate1064).dm (WitnessCertificates.Batch053.certificate1064).beta) ≤ (2*exp (-((CountingCertificates.Batch053.certificate1064).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch129.certificate1557).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch129.certificate1558).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch053.certificate1064).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch129.certificate1557 MergedCutGroups.Batch129.certificate1558 CountingCertificates.Batch053.certificate1064 CutLabelCertificates.Entropy041.certificate823 CutLabelCertificates.Minority041.certificate822 matches493 rfl rfl
    MergedCutGroups.Batch129.numericValid1557 MergedCutGroups.Batch129.numericValid1558 MergedCutGroups.Batch129.cellsSound1557 MergedCutGroups.Batch129.cellsSound1558
    MergedCutGroups.Batch129.cellsNumeric1557 MergedCutGroups.Batch129.cellsNumeric1558 MergedCutGroups.Batch129.populationMatches1557 MergedCutGroups.Batch129.populationMatches1558
    PopulationCertificates.Batch053.valid1064 PopulationCertificates.Batch053.sound1064 WitnessCertificates.Batch053.valid1064 WitnessCertificates.Batch053.sound1064 CountingCertificates.Batch053.valid1064 CountingCertificates.Batch053.sound1064
    CutLabelCertificates.Entropy041.valid823 CutLabelCertificates.Minority041.valid822 CutLabelCertificates.Minority041.sound822 H st hI
theorem probabilityBound493 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch129.certificate1557).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch053.certificate1064).dm (WitnessCertificates.Batch053.certificate1064).beta) ≤ ((CutFailureCertificates.Budget053.certificate1064).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget053.sound1064 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch053.certificate1064).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch129.certificate1557).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch129.certificate1558).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch053.certificate1064).omega:ℝ) ≤ ((CutFailureCertificates.Budget053.certificate1064).bound:ℝ) at hb
  exact (exponentialBound493 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch024
