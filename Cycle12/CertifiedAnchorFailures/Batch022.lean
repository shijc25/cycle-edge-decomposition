import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch045
import Cycle12.CountingCertificates.Batch046
import Cycle12.CountingCertificates.Batch047
import Cycle12.CountingCertificates.Batch048
import Cycle12.CutFailureCertificates.Budget045
import Cycle12.CutFailureCertificates.Budget046
import Cycle12.CutFailureCertificates.Budget047
import Cycle12.CutFailureCertificates.Budget048
import Cycle12.MergedCutGroups.Batch112
import Cycle12.MergedCutGroups.Batch113
import Cycle12.MergedCutGroups.Batch114
import Cycle12.MergedCutGroups.Batch115
import Cycle12.MergedCutGroups.Batch116
import Cycle12.MergedCutGroups.Batch117
import Cycle12.MergedCutGroups.Batch118
import Cycle12.PopulationCertificates.Batch045
import Cycle12.PopulationCertificates.Batch046
import Cycle12.PopulationCertificates.Batch047
import Cycle12.PopulationCertificates.Batch048
import Cycle12.WitnessCertificates.Batch045
import Cycle12.WitnessCertificates.Batch046
import Cycle12.WitnessCertificates.Batch047
import Cycle12.WitnessCertificates.Batch048

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedAnchorFailures.Batch022
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches440 : (MergedCutGroups.Batch112.certificate1347).AnchorMatches CountingCertificates.Batch045.certificate906 := by decide +kernel
theorem exponentialBound440 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch112.certificate1347).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch045.certificate906).dm (WitnessCertificates.Batch045.certificate906).beta (WitnessCertificates.Batch045.certificate906).L) ≤ (2*exp (-((CountingCertificates.Batch045.certificate906).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch112.certificate1347).exponent:ℝ)*st.R))/((WitnessCertificates.Batch045.certificate906).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch112.certificate1347 CountingCertificates.Batch045.certificate906 matches440 MergedCutGroups.Batch112.numericValid1347 MergedCutGroups.Batch112.cellsSound1347 MergedCutGroups.Batch112.cellsNumeric1347 MergedCutGroups.Batch112.populationMatches1347
    PopulationCertificates.Batch045.valid906 PopulationCertificates.Batch045.sound906 WitnessCertificates.Batch045.valid906 WitnessCertificates.Batch045.sound906 CountingCertificates.Batch045.valid906 CountingCertificates.Batch045.sound906 H st hI
theorem probabilityBound440 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch112.certificate1347).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch045.certificate906).dm (WitnessCertificates.Batch045.certificate906).beta (WitnessCertificates.Batch045.certificate906).L) ≤ ((CutFailureCertificates.Budget045.certificate906).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound906 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate906).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch112.certificate1347).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch045.certificate906).omega:ℝ)) ≤ ((CutFailureCertificates.Budget045.certificate906).bound:ℝ) at hb
  exact (exponentialBound440 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches441 : (MergedCutGroups.Batch112.certificate1351).AnchorMatches CountingCertificates.Batch045.certificate909 := by decide +kernel
theorem exponentialBound441 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch112.certificate1351).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch045.certificate909).dm (WitnessCertificates.Batch045.certificate909).beta (WitnessCertificates.Batch045.certificate909).L) ≤ (2*exp (-((CountingCertificates.Batch045.certificate909).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch112.certificate1351).exponent:ℝ)*st.R))/((WitnessCertificates.Batch045.certificate909).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch112.certificate1351 CountingCertificates.Batch045.certificate909 matches441 MergedCutGroups.Batch112.numericValid1351 MergedCutGroups.Batch112.cellsSound1351 MergedCutGroups.Batch112.cellsNumeric1351 MergedCutGroups.Batch112.populationMatches1351
    PopulationCertificates.Batch045.valid909 PopulationCertificates.Batch045.sound909 WitnessCertificates.Batch045.valid909 WitnessCertificates.Batch045.sound909 CountingCertificates.Batch045.valid909 CountingCertificates.Batch045.sound909 H st hI
theorem probabilityBound441 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch112.certificate1351).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch045.certificate909).dm (WitnessCertificates.Batch045.certificate909).beta (WitnessCertificates.Batch045.certificate909).L) ≤ ((CutFailureCertificates.Budget045.certificate909).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound909 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate909).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch112.certificate1351).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch045.certificate909).omega:ℝ)) ≤ ((CutFailureCertificates.Budget045.certificate909).bound:ℝ) at hb
  exact (exponentialBound441 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches442 : (MergedCutGroups.Batch112.certificate1355).AnchorMatches CountingCertificates.Batch045.certificate912 := by decide +kernel
theorem exponentialBound442 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch112.certificate1355).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch045.certificate912).dm (WitnessCertificates.Batch045.certificate912).beta (WitnessCertificates.Batch045.certificate912).L) ≤ (2*exp (-((CountingCertificates.Batch045.certificate912).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch112.certificate1355).exponent:ℝ)*st.R))/((WitnessCertificates.Batch045.certificate912).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch112.certificate1355 CountingCertificates.Batch045.certificate912 matches442 MergedCutGroups.Batch112.numericValid1355 MergedCutGroups.Batch112.cellsSound1355 MergedCutGroups.Batch112.cellsNumeric1355 MergedCutGroups.Batch112.populationMatches1355
    PopulationCertificates.Batch045.valid912 PopulationCertificates.Batch045.sound912 WitnessCertificates.Batch045.valid912 WitnessCertificates.Batch045.sound912 CountingCertificates.Batch045.valid912 CountingCertificates.Batch045.sound912 H st hI
theorem probabilityBound442 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch112.certificate1355).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch045.certificate912).dm (WitnessCertificates.Batch045.certificate912).beta (WitnessCertificates.Batch045.certificate912).L) ≤ ((CutFailureCertificates.Budget045.certificate912).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound912 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate912).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch112.certificate1355).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch045.certificate912).omega:ℝ)) ≤ ((CutFailureCertificates.Budget045.certificate912).bound:ℝ) at hb
  exact (exponentialBound442 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches443 : (MergedCutGroups.Batch113.certificate1359).AnchorMatches CountingCertificates.Batch045.certificate915 := by decide +kernel
theorem exponentialBound443 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch113.certificate1359).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch045.certificate915).dm (WitnessCertificates.Batch045.certificate915).beta (WitnessCertificates.Batch045.certificate915).L) ≤ (2*exp (-((CountingCertificates.Batch045.certificate915).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch113.certificate1359).exponent:ℝ)*st.R))/((WitnessCertificates.Batch045.certificate915).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch113.certificate1359 CountingCertificates.Batch045.certificate915 matches443 MergedCutGroups.Batch113.numericValid1359 MergedCutGroups.Batch113.cellsSound1359 MergedCutGroups.Batch113.cellsNumeric1359 MergedCutGroups.Batch113.populationMatches1359
    PopulationCertificates.Batch045.valid915 PopulationCertificates.Batch045.sound915 WitnessCertificates.Batch045.valid915 WitnessCertificates.Batch045.sound915 CountingCertificates.Batch045.valid915 CountingCertificates.Batch045.sound915 H st hI
theorem probabilityBound443 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch113.certificate1359).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch045.certificate915).dm (WitnessCertificates.Batch045.certificate915).beta (WitnessCertificates.Batch045.certificate915).L) ≤ ((CutFailureCertificates.Budget045.certificate915).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound915 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate915).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch113.certificate1359).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch045.certificate915).omega:ℝ)) ≤ ((CutFailureCertificates.Budget045.certificate915).bound:ℝ) at hb
  exact (exponentialBound443 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches444 : (MergedCutGroups.Batch113.certificate1363).AnchorMatches CountingCertificates.Batch045.certificate918 := by decide +kernel
theorem exponentialBound444 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch113.certificate1363).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch045.certificate918).dm (WitnessCertificates.Batch045.certificate918).beta (WitnessCertificates.Batch045.certificate918).L) ≤ (2*exp (-((CountingCertificates.Batch045.certificate918).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch113.certificate1363).exponent:ℝ)*st.R))/((WitnessCertificates.Batch045.certificate918).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch113.certificate1363 CountingCertificates.Batch045.certificate918 matches444 MergedCutGroups.Batch113.numericValid1363 MergedCutGroups.Batch113.cellsSound1363 MergedCutGroups.Batch113.cellsNumeric1363 MergedCutGroups.Batch113.populationMatches1363
    PopulationCertificates.Batch045.valid918 PopulationCertificates.Batch045.sound918 WitnessCertificates.Batch045.valid918 WitnessCertificates.Batch045.sound918 CountingCertificates.Batch045.valid918 CountingCertificates.Batch045.sound918 H st hI
theorem probabilityBound444 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch113.certificate1363).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch045.certificate918).dm (WitnessCertificates.Batch045.certificate918).beta (WitnessCertificates.Batch045.certificate918).L) ≤ ((CutFailureCertificates.Budget045.certificate918).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget045.sound918 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch045.certificate918).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch113.certificate1363).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch045.certificate918).omega:ℝ)) ≤ ((CutFailureCertificates.Budget045.certificate918).bound:ℝ) at hb
  exact (exponentialBound444 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches445 : (MergedCutGroups.Batch113.certificate1367).AnchorMatches CountingCertificates.Batch046.certificate921 := by decide +kernel
theorem exponentialBound445 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch113.certificate1367).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch046.certificate921).dm (WitnessCertificates.Batch046.certificate921).beta (WitnessCertificates.Batch046.certificate921).L) ≤ (2*exp (-((CountingCertificates.Batch046.certificate921).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch113.certificate1367).exponent:ℝ)*st.R))/((WitnessCertificates.Batch046.certificate921).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch113.certificate1367 CountingCertificates.Batch046.certificate921 matches445 MergedCutGroups.Batch113.numericValid1367 MergedCutGroups.Batch113.cellsSound1367 MergedCutGroups.Batch113.cellsNumeric1367 MergedCutGroups.Batch113.populationMatches1367
    PopulationCertificates.Batch046.valid921 PopulationCertificates.Batch046.sound921 WitnessCertificates.Batch046.valid921 WitnessCertificates.Batch046.sound921 CountingCertificates.Batch046.valid921 CountingCertificates.Batch046.sound921 H st hI
theorem probabilityBound445 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch113.certificate1367).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch046.certificate921).dm (WitnessCertificates.Batch046.certificate921).beta (WitnessCertificates.Batch046.certificate921).L) ≤ ((CutFailureCertificates.Budget046.certificate921).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound921 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate921).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch113.certificate1367).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch046.certificate921).omega:ℝ)) ≤ ((CutFailureCertificates.Budget046.certificate921).bound:ℝ) at hb
  exact (exponentialBound445 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches446 : (MergedCutGroups.Batch114.certificate1371).AnchorMatches CountingCertificates.Batch046.certificate924 := by decide +kernel
theorem exponentialBound446 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch114.certificate1371).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch046.certificate924).dm (WitnessCertificates.Batch046.certificate924).beta (WitnessCertificates.Batch046.certificate924).L) ≤ (2*exp (-((CountingCertificates.Batch046.certificate924).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch114.certificate1371).exponent:ℝ)*st.R))/((WitnessCertificates.Batch046.certificate924).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch114.certificate1371 CountingCertificates.Batch046.certificate924 matches446 MergedCutGroups.Batch114.numericValid1371 MergedCutGroups.Batch114.cellsSound1371 MergedCutGroups.Batch114.cellsNumeric1371 MergedCutGroups.Batch114.populationMatches1371
    PopulationCertificates.Batch046.valid924 PopulationCertificates.Batch046.sound924 WitnessCertificates.Batch046.valid924 WitnessCertificates.Batch046.sound924 CountingCertificates.Batch046.valid924 CountingCertificates.Batch046.sound924 H st hI
theorem probabilityBound446 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch114.certificate1371).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch046.certificate924).dm (WitnessCertificates.Batch046.certificate924).beta (WitnessCertificates.Batch046.certificate924).L) ≤ ((CutFailureCertificates.Budget046.certificate924).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound924 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate924).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch114.certificate1371).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch046.certificate924).omega:ℝ)) ≤ ((CutFailureCertificates.Budget046.certificate924).bound:ℝ) at hb
  exact (exponentialBound446 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches447 : (MergedCutGroups.Batch114.certificate1375).AnchorMatches CountingCertificates.Batch046.certificate927 := by decide +kernel
theorem exponentialBound447 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch114.certificate1375).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch046.certificate927).dm (WitnessCertificates.Batch046.certificate927).beta (WitnessCertificates.Batch046.certificate927).L) ≤ (2*exp (-((CountingCertificates.Batch046.certificate927).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch114.certificate1375).exponent:ℝ)*st.R))/((WitnessCertificates.Batch046.certificate927).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch114.certificate1375 CountingCertificates.Batch046.certificate927 matches447 MergedCutGroups.Batch114.numericValid1375 MergedCutGroups.Batch114.cellsSound1375 MergedCutGroups.Batch114.cellsNumeric1375 MergedCutGroups.Batch114.populationMatches1375
    PopulationCertificates.Batch046.valid927 PopulationCertificates.Batch046.sound927 WitnessCertificates.Batch046.valid927 WitnessCertificates.Batch046.sound927 CountingCertificates.Batch046.valid927 CountingCertificates.Batch046.sound927 H st hI
theorem probabilityBound447 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch114.certificate1375).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch046.certificate927).dm (WitnessCertificates.Batch046.certificate927).beta (WitnessCertificates.Batch046.certificate927).L) ≤ ((CutFailureCertificates.Budget046.certificate927).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound927 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate927).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch114.certificate1375).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch046.certificate927).omega:ℝ)) ≤ ((CutFailureCertificates.Budget046.certificate927).bound:ℝ) at hb
  exact (exponentialBound447 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches448 : (MergedCutGroups.Batch114.certificate1379).AnchorMatches CountingCertificates.Batch046.certificate930 := by decide +kernel
theorem exponentialBound448 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch114.certificate1379).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch046.certificate930).dm (WitnessCertificates.Batch046.certificate930).beta (WitnessCertificates.Batch046.certificate930).L) ≤ (2*exp (-((CountingCertificates.Batch046.certificate930).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch114.certificate1379).exponent:ℝ)*st.R))/((WitnessCertificates.Batch046.certificate930).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch114.certificate1379 CountingCertificates.Batch046.certificate930 matches448 MergedCutGroups.Batch114.numericValid1379 MergedCutGroups.Batch114.cellsSound1379 MergedCutGroups.Batch114.cellsNumeric1379 MergedCutGroups.Batch114.populationMatches1379
    PopulationCertificates.Batch046.valid930 PopulationCertificates.Batch046.sound930 WitnessCertificates.Batch046.valid930 WitnessCertificates.Batch046.sound930 CountingCertificates.Batch046.valid930 CountingCertificates.Batch046.sound930 H st hI
theorem probabilityBound448 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch114.certificate1379).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch046.certificate930).dm (WitnessCertificates.Batch046.certificate930).beta (WitnessCertificates.Batch046.certificate930).L) ≤ ((CutFailureCertificates.Budget046.certificate930).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound930 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate930).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch114.certificate1379).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch046.certificate930).omega:ℝ)) ≤ ((CutFailureCertificates.Budget046.certificate930).bound:ℝ) at hb
  exact (exponentialBound448 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches449 : (MergedCutGroups.Batch115.certificate1383).AnchorMatches CountingCertificates.Batch046.certificate933 := by decide +kernel
theorem exponentialBound449 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch115.certificate1383).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch046.certificate933).dm (WitnessCertificates.Batch046.certificate933).beta (WitnessCertificates.Batch046.certificate933).L) ≤ (2*exp (-((CountingCertificates.Batch046.certificate933).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch115.certificate1383).exponent:ℝ)*st.R))/((WitnessCertificates.Batch046.certificate933).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch115.certificate1383 CountingCertificates.Batch046.certificate933 matches449 MergedCutGroups.Batch115.numericValid1383 MergedCutGroups.Batch115.cellsSound1383 MergedCutGroups.Batch115.cellsNumeric1383 MergedCutGroups.Batch115.populationMatches1383
    PopulationCertificates.Batch046.valid933 PopulationCertificates.Batch046.sound933 WitnessCertificates.Batch046.valid933 WitnessCertificates.Batch046.sound933 CountingCertificates.Batch046.valid933 CountingCertificates.Batch046.sound933 H st hI
theorem probabilityBound449 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch115.certificate1383).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch046.certificate933).dm (WitnessCertificates.Batch046.certificate933).beta (WitnessCertificates.Batch046.certificate933).L) ≤ ((CutFailureCertificates.Budget046.certificate933).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound933 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate933).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch115.certificate1383).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch046.certificate933).omega:ℝ)) ≤ ((CutFailureCertificates.Budget046.certificate933).bound:ℝ) at hb
  exact (exponentialBound449 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches450 : (MergedCutGroups.Batch115.certificate1387).AnchorMatches CountingCertificates.Batch046.certificate936 := by decide +kernel
theorem exponentialBound450 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch115.certificate1387).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch046.certificate936).dm (WitnessCertificates.Batch046.certificate936).beta (WitnessCertificates.Batch046.certificate936).L) ≤ (2*exp (-((CountingCertificates.Batch046.certificate936).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch115.certificate1387).exponent:ℝ)*st.R))/((WitnessCertificates.Batch046.certificate936).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch115.certificate1387 CountingCertificates.Batch046.certificate936 matches450 MergedCutGroups.Batch115.numericValid1387 MergedCutGroups.Batch115.cellsSound1387 MergedCutGroups.Batch115.cellsNumeric1387 MergedCutGroups.Batch115.populationMatches1387
    PopulationCertificates.Batch046.valid936 PopulationCertificates.Batch046.sound936 WitnessCertificates.Batch046.valid936 WitnessCertificates.Batch046.sound936 CountingCertificates.Batch046.valid936 CountingCertificates.Batch046.sound936 H st hI
theorem probabilityBound450 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch115.certificate1387).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch046.certificate936).dm (WitnessCertificates.Batch046.certificate936).beta (WitnessCertificates.Batch046.certificate936).L) ≤ ((CutFailureCertificates.Budget046.certificate936).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound936 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate936).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch115.certificate1387).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch046.certificate936).omega:ℝ)) ≤ ((CutFailureCertificates.Budget046.certificate936).bound:ℝ) at hb
  exact (exponentialBound450 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches451 : (MergedCutGroups.Batch115.certificate1391).AnchorMatches CountingCertificates.Batch046.certificate939 := by decide +kernel
theorem exponentialBound451 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch115.certificate1391).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch046.certificate939).dm (WitnessCertificates.Batch046.certificate939).beta (WitnessCertificates.Batch046.certificate939).L) ≤ (2*exp (-((CountingCertificates.Batch046.certificate939).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch115.certificate1391).exponent:ℝ)*st.R))/((WitnessCertificates.Batch046.certificate939).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch115.certificate1391 CountingCertificates.Batch046.certificate939 matches451 MergedCutGroups.Batch115.numericValid1391 MergedCutGroups.Batch115.cellsSound1391 MergedCutGroups.Batch115.cellsNumeric1391 MergedCutGroups.Batch115.populationMatches1391
    PopulationCertificates.Batch046.valid939 PopulationCertificates.Batch046.sound939 WitnessCertificates.Batch046.valid939 WitnessCertificates.Batch046.sound939 CountingCertificates.Batch046.valid939 CountingCertificates.Batch046.sound939 H st hI
theorem probabilityBound451 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch115.certificate1391).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch046.certificate939).dm (WitnessCertificates.Batch046.certificate939).beta (WitnessCertificates.Batch046.certificate939).L) ≤ ((CutFailureCertificates.Budget046.certificate939).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget046.sound939 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch046.certificate939).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch115.certificate1391).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch046.certificate939).omega:ℝ)) ≤ ((CutFailureCertificates.Budget046.certificate939).bound:ℝ) at hb
  exact (exponentialBound451 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches452 : (MergedCutGroups.Batch116.certificate1395).AnchorMatches CountingCertificates.Batch047.certificate942 := by decide +kernel
theorem exponentialBound452 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch116.certificate1395).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch047.certificate942).dm (WitnessCertificates.Batch047.certificate942).beta (WitnessCertificates.Batch047.certificate942).L) ≤ (2*exp (-((CountingCertificates.Batch047.certificate942).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch116.certificate1395).exponent:ℝ)*st.R))/((WitnessCertificates.Batch047.certificate942).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch116.certificate1395 CountingCertificates.Batch047.certificate942 matches452 MergedCutGroups.Batch116.numericValid1395 MergedCutGroups.Batch116.cellsSound1395 MergedCutGroups.Batch116.cellsNumeric1395 MergedCutGroups.Batch116.populationMatches1395
    PopulationCertificates.Batch047.valid942 PopulationCertificates.Batch047.sound942 WitnessCertificates.Batch047.valid942 WitnessCertificates.Batch047.sound942 CountingCertificates.Batch047.valid942 CountingCertificates.Batch047.sound942 H st hI
theorem probabilityBound452 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch116.certificate1395).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch047.certificate942).dm (WitnessCertificates.Batch047.certificate942).beta (WitnessCertificates.Batch047.certificate942).L) ≤ ((CutFailureCertificates.Budget047.certificate942).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound942 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate942).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch116.certificate1395).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch047.certificate942).omega:ℝ)) ≤ ((CutFailureCertificates.Budget047.certificate942).bound:ℝ) at hb
  exact (exponentialBound452 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches453 : (MergedCutGroups.Batch116.certificate1399).AnchorMatches CountingCertificates.Batch047.certificate945 := by decide +kernel
theorem exponentialBound453 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch116.certificate1399).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch047.certificate945).dm (WitnessCertificates.Batch047.certificate945).beta (WitnessCertificates.Batch047.certificate945).L) ≤ (2*exp (-((CountingCertificates.Batch047.certificate945).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch116.certificate1399).exponent:ℝ)*st.R))/((WitnessCertificates.Batch047.certificate945).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch116.certificate1399 CountingCertificates.Batch047.certificate945 matches453 MergedCutGroups.Batch116.numericValid1399 MergedCutGroups.Batch116.cellsSound1399 MergedCutGroups.Batch116.cellsNumeric1399 MergedCutGroups.Batch116.populationMatches1399
    PopulationCertificates.Batch047.valid945 PopulationCertificates.Batch047.sound945 WitnessCertificates.Batch047.valid945 WitnessCertificates.Batch047.sound945 CountingCertificates.Batch047.valid945 CountingCertificates.Batch047.sound945 H st hI
theorem probabilityBound453 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch116.certificate1399).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch047.certificate945).dm (WitnessCertificates.Batch047.certificate945).beta (WitnessCertificates.Batch047.certificate945).L) ≤ ((CutFailureCertificates.Budget047.certificate945).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound945 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate945).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch116.certificate1399).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch047.certificate945).omega:ℝ)) ≤ ((CutFailureCertificates.Budget047.certificate945).bound:ℝ) at hb
  exact (exponentialBound453 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches454 : (MergedCutGroups.Batch116.certificate1403).AnchorMatches CountingCertificates.Batch047.certificate948 := by decide +kernel
theorem exponentialBound454 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch116.certificate1403).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch047.certificate948).dm (WitnessCertificates.Batch047.certificate948).beta (WitnessCertificates.Batch047.certificate948).L) ≤ (2*exp (-((CountingCertificates.Batch047.certificate948).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch116.certificate1403).exponent:ℝ)*st.R))/((WitnessCertificates.Batch047.certificate948).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch116.certificate1403 CountingCertificates.Batch047.certificate948 matches454 MergedCutGroups.Batch116.numericValid1403 MergedCutGroups.Batch116.cellsSound1403 MergedCutGroups.Batch116.cellsNumeric1403 MergedCutGroups.Batch116.populationMatches1403
    PopulationCertificates.Batch047.valid948 PopulationCertificates.Batch047.sound948 WitnessCertificates.Batch047.valid948 WitnessCertificates.Batch047.sound948 CountingCertificates.Batch047.valid948 CountingCertificates.Batch047.sound948 H st hI
theorem probabilityBound454 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch116.certificate1403).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch047.certificate948).dm (WitnessCertificates.Batch047.certificate948).beta (WitnessCertificates.Batch047.certificate948).L) ≤ ((CutFailureCertificates.Budget047.certificate948).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound948 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate948).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch116.certificate1403).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch047.certificate948).omega:ℝ)) ≤ ((CutFailureCertificates.Budget047.certificate948).bound:ℝ) at hb
  exact (exponentialBound454 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches455 : (MergedCutGroups.Batch117.certificate1407).AnchorMatches CountingCertificates.Batch047.certificate951 := by decide +kernel
theorem exponentialBound455 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch117.certificate1407).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch047.certificate951).dm (WitnessCertificates.Batch047.certificate951).beta (WitnessCertificates.Batch047.certificate951).L) ≤ (2*exp (-((CountingCertificates.Batch047.certificate951).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch117.certificate1407).exponent:ℝ)*st.R))/((WitnessCertificates.Batch047.certificate951).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch117.certificate1407 CountingCertificates.Batch047.certificate951 matches455 MergedCutGroups.Batch117.numericValid1407 MergedCutGroups.Batch117.cellsSound1407 MergedCutGroups.Batch117.cellsNumeric1407 MergedCutGroups.Batch117.populationMatches1407
    PopulationCertificates.Batch047.valid951 PopulationCertificates.Batch047.sound951 WitnessCertificates.Batch047.valid951 WitnessCertificates.Batch047.sound951 CountingCertificates.Batch047.valid951 CountingCertificates.Batch047.sound951 H st hI
theorem probabilityBound455 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch117.certificate1407).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch047.certificate951).dm (WitnessCertificates.Batch047.certificate951).beta (WitnessCertificates.Batch047.certificate951).L) ≤ ((CutFailureCertificates.Budget047.certificate951).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound951 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate951).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch117.certificate1407).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch047.certificate951).omega:ℝ)) ≤ ((CutFailureCertificates.Budget047.certificate951).bound:ℝ) at hb
  exact (exponentialBound455 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches456 : (MergedCutGroups.Batch117.certificate1411).AnchorMatches CountingCertificates.Batch047.certificate954 := by decide +kernel
theorem exponentialBound456 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch117.certificate1411).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch047.certificate954).dm (WitnessCertificates.Batch047.certificate954).beta (WitnessCertificates.Batch047.certificate954).L) ≤ (2*exp (-((CountingCertificates.Batch047.certificate954).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch117.certificate1411).exponent:ℝ)*st.R))/((WitnessCertificates.Batch047.certificate954).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch117.certificate1411 CountingCertificates.Batch047.certificate954 matches456 MergedCutGroups.Batch117.numericValid1411 MergedCutGroups.Batch117.cellsSound1411 MergedCutGroups.Batch117.cellsNumeric1411 MergedCutGroups.Batch117.populationMatches1411
    PopulationCertificates.Batch047.valid954 PopulationCertificates.Batch047.sound954 WitnessCertificates.Batch047.valid954 WitnessCertificates.Batch047.sound954 CountingCertificates.Batch047.valid954 CountingCertificates.Batch047.sound954 H st hI
theorem probabilityBound456 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch117.certificate1411).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch047.certificate954).dm (WitnessCertificates.Batch047.certificate954).beta (WitnessCertificates.Batch047.certificate954).L) ≤ ((CutFailureCertificates.Budget047.certificate954).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound954 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate954).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch117.certificate1411).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch047.certificate954).omega:ℝ)) ≤ ((CutFailureCertificates.Budget047.certificate954).bound:ℝ) at hb
  exact (exponentialBound456 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches457 : (MergedCutGroups.Batch117.certificate1415).AnchorMatches CountingCertificates.Batch047.certificate957 := by decide +kernel
theorem exponentialBound457 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch117.certificate1415).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch047.certificate957).dm (WitnessCertificates.Batch047.certificate957).beta (WitnessCertificates.Batch047.certificate957).L) ≤ (2*exp (-((CountingCertificates.Batch047.certificate957).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch117.certificate1415).exponent:ℝ)*st.R))/((WitnessCertificates.Batch047.certificate957).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch117.certificate1415 CountingCertificates.Batch047.certificate957 matches457 MergedCutGroups.Batch117.numericValid1415 MergedCutGroups.Batch117.cellsSound1415 MergedCutGroups.Batch117.cellsNumeric1415 MergedCutGroups.Batch117.populationMatches1415
    PopulationCertificates.Batch047.valid957 PopulationCertificates.Batch047.sound957 WitnessCertificates.Batch047.valid957 WitnessCertificates.Batch047.sound957 CountingCertificates.Batch047.valid957 CountingCertificates.Batch047.sound957 H st hI
theorem probabilityBound457 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch117.certificate1415).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch047.certificate957).dm (WitnessCertificates.Batch047.certificate957).beta (WitnessCertificates.Batch047.certificate957).L) ≤ ((CutFailureCertificates.Budget047.certificate957).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget047.sound957 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch047.certificate957).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch117.certificate1415).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch047.certificate957).omega:ℝ)) ≤ ((CutFailureCertificates.Budget047.certificate957).bound:ℝ) at hb
  exact (exponentialBound457 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches458 : (MergedCutGroups.Batch118.certificate1419).AnchorMatches CountingCertificates.Batch048.certificate960 := by decide +kernel
theorem exponentialBound458 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch118.certificate1419).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch048.certificate960).dm (WitnessCertificates.Batch048.certificate960).beta (WitnessCertificates.Batch048.certificate960).L) ≤ (2*exp (-((CountingCertificates.Batch048.certificate960).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch118.certificate1419).exponent:ℝ)*st.R))/((WitnessCertificates.Batch048.certificate960).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch118.certificate1419 CountingCertificates.Batch048.certificate960 matches458 MergedCutGroups.Batch118.numericValid1419 MergedCutGroups.Batch118.cellsSound1419 MergedCutGroups.Batch118.cellsNumeric1419 MergedCutGroups.Batch118.populationMatches1419
    PopulationCertificates.Batch048.valid960 PopulationCertificates.Batch048.sound960 WitnessCertificates.Batch048.valid960 WitnessCertificates.Batch048.sound960 CountingCertificates.Batch048.valid960 CountingCertificates.Batch048.sound960 H st hI
theorem probabilityBound458 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch118.certificate1419).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch048.certificate960).dm (WitnessCertificates.Batch048.certificate960).beta (WitnessCertificates.Batch048.certificate960).L) ≤ ((CutFailureCertificates.Budget048.certificate960).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound960 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate960).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch118.certificate1419).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch048.certificate960).omega:ℝ)) ≤ ((CutFailureCertificates.Budget048.certificate960).bound:ℝ) at hb
  exact (exponentialBound458 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches459 : (MergedCutGroups.Batch118.certificate1423).AnchorMatches CountingCertificates.Batch048.certificate963 := by decide +kernel
theorem exponentialBound459 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch118.certificate1423).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch048.certificate963).dm (WitnessCertificates.Batch048.certificate963).beta (WitnessCertificates.Batch048.certificate963).L) ≤ (2*exp (-((CountingCertificates.Batch048.certificate963).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch118.certificate1423).exponent:ℝ)*st.R))/((WitnessCertificates.Batch048.certificate963).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch118.certificate1423 CountingCertificates.Batch048.certificate963 matches459 MergedCutGroups.Batch118.numericValid1423 MergedCutGroups.Batch118.cellsSound1423 MergedCutGroups.Batch118.cellsNumeric1423 MergedCutGroups.Batch118.populationMatches1423
    PopulationCertificates.Batch048.valid963 PopulationCertificates.Batch048.sound963 WitnessCertificates.Batch048.valid963 WitnessCertificates.Batch048.sound963 CountingCertificates.Batch048.valid963 CountingCertificates.Batch048.sound963 H st hI
theorem probabilityBound459 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch118.certificate1423).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch048.certificate963).dm (WitnessCertificates.Batch048.certificate963).beta (WitnessCertificates.Batch048.certificate963).L) ≤ ((CutFailureCertificates.Budget048.certificate963).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget048.sound963 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch048.certificate963).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch118.certificate1423).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch048.certificate963).omega:ℝ)) ≤ ((CutFailureCertificates.Budget048.certificate963).bound:ℝ) at hb
  exact (exponentialBound459 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch022
