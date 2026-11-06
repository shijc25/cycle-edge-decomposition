import Cycle12.CertifiedGlobalFailure
import Cycle12.CountingCertificates.Batch036
import Cycle12.CountingCertificates.Batch037
import Cycle12.CutFailureCertificates.Budget036
import Cycle12.CutFailureCertificates.Budget037
import Cycle12.CutLabelCertificates.Entropy018
import Cycle12.CutLabelCertificates.Entropy019
import Cycle12.CutLabelCertificates.Minority018
import Cycle12.MergedCutGroups.Batch090
import Cycle12.MergedCutGroups.Batch091
import Cycle12.MergedCutGroups.Batch092
import Cycle12.MergedCutGroups.Batch093
import Cycle12.MergedCutGroups.Batch094
import Cycle12.PopulationCertificates.Batch036
import Cycle12.PopulationCertificates.Batch037
import Cycle12.WitnessCertificates.Batch036
import Cycle12.WitnessCertificates.Batch037

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedGlobalFailures.Batch018
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches360 : (MergedCutGroups.Batch090.certificate1080).GlobalMatches MergedCutGroups.Batch090.certificate1081 CountingCertificates.Batch036.certificate720 CutLabelCertificates.Entropy018.certificate361 CutLabelCertificates.Minority018.certificate360 := by decide +kernel
theorem exponentialBound360 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch090.certificate1080).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate720).dm (WitnessCertificates.Batch036.certificate720).beta) ≤ (2*exp (-((CountingCertificates.Batch036.certificate720).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch090.certificate1080).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch090.certificate1081).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch036.certificate720).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch090.certificate1080 MergedCutGroups.Batch090.certificate1081 CountingCertificates.Batch036.certificate720 CutLabelCertificates.Entropy018.certificate361 CutLabelCertificates.Minority018.certificate360 matches360 rfl rfl
    MergedCutGroups.Batch090.numericValid1080 MergedCutGroups.Batch090.numericValid1081 MergedCutGroups.Batch090.cellsSound1080 MergedCutGroups.Batch090.cellsSound1081
    MergedCutGroups.Batch090.cellsNumeric1080 MergedCutGroups.Batch090.cellsNumeric1081 MergedCutGroups.Batch090.populationMatches1080 MergedCutGroups.Batch090.populationMatches1081
    PopulationCertificates.Batch036.valid720 PopulationCertificates.Batch036.sound720 WitnessCertificates.Batch036.valid720 WitnessCertificates.Batch036.sound720 CountingCertificates.Batch036.valid720 CountingCertificates.Batch036.sound720
    CutLabelCertificates.Entropy018.valid361 CutLabelCertificates.Minority018.valid360 CutLabelCertificates.Minority018.sound360 H st hI
theorem probabilityBound360 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch090.certificate1080).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate720).dm (WitnessCertificates.Batch036.certificate720).beta) ≤ ((CutFailureCertificates.Budget036.certificate720).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound720 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate720).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch090.certificate1080).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch090.certificate1081).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch036.certificate720).omega:ℝ) ≤ ((CutFailureCertificates.Budget036.certificate720).bound:ℝ) at hb
  exact (exponentialBound360 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches361 : (MergedCutGroups.Batch090.certificate1083).GlobalMatches MergedCutGroups.Batch090.certificate1084 CountingCertificates.Batch036.certificate722 CutLabelCertificates.Entropy018.certificate362 CutLabelCertificates.Minority018.certificate361 := by decide +kernel
theorem exponentialBound361 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch090.certificate1083).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate722).dm (WitnessCertificates.Batch036.certificate722).beta) ≤ (2*exp (-((CountingCertificates.Batch036.certificate722).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch090.certificate1083).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch090.certificate1084).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch036.certificate722).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch090.certificate1083 MergedCutGroups.Batch090.certificate1084 CountingCertificates.Batch036.certificate722 CutLabelCertificates.Entropy018.certificate362 CutLabelCertificates.Minority018.certificate361 matches361 rfl rfl
    MergedCutGroups.Batch090.numericValid1083 MergedCutGroups.Batch090.numericValid1084 MergedCutGroups.Batch090.cellsSound1083 MergedCutGroups.Batch090.cellsSound1084
    MergedCutGroups.Batch090.cellsNumeric1083 MergedCutGroups.Batch090.cellsNumeric1084 MergedCutGroups.Batch090.populationMatches1083 MergedCutGroups.Batch090.populationMatches1084
    PopulationCertificates.Batch036.valid722 PopulationCertificates.Batch036.sound722 WitnessCertificates.Batch036.valid722 WitnessCertificates.Batch036.sound722 CountingCertificates.Batch036.valid722 CountingCertificates.Batch036.sound722
    CutLabelCertificates.Entropy018.valid362 CutLabelCertificates.Minority018.valid361 CutLabelCertificates.Minority018.sound361 H st hI
theorem probabilityBound361 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch090.certificate1083).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate722).dm (WitnessCertificates.Batch036.certificate722).beta) ≤ ((CutFailureCertificates.Budget036.certificate722).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound722 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate722).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch090.certificate1083).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch090.certificate1084).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch036.certificate722).omega:ℝ) ≤ ((CutFailureCertificates.Budget036.certificate722).bound:ℝ) at hb
  exact (exponentialBound361 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches362 : (MergedCutGroups.Batch090.certificate1086).GlobalMatches MergedCutGroups.Batch090.certificate1087 CountingCertificates.Batch036.certificate724 CutLabelCertificates.Entropy018.certificate363 CutLabelCertificates.Minority018.certificate362 := by decide +kernel
theorem exponentialBound362 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch090.certificate1086).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate724).dm (WitnessCertificates.Batch036.certificate724).beta) ≤ (2*exp (-((CountingCertificates.Batch036.certificate724).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch090.certificate1086).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch090.certificate1087).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch036.certificate724).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch090.certificate1086 MergedCutGroups.Batch090.certificate1087 CountingCertificates.Batch036.certificate724 CutLabelCertificates.Entropy018.certificate363 CutLabelCertificates.Minority018.certificate362 matches362 rfl rfl
    MergedCutGroups.Batch090.numericValid1086 MergedCutGroups.Batch090.numericValid1087 MergedCutGroups.Batch090.cellsSound1086 MergedCutGroups.Batch090.cellsSound1087
    MergedCutGroups.Batch090.cellsNumeric1086 MergedCutGroups.Batch090.cellsNumeric1087 MergedCutGroups.Batch090.populationMatches1086 MergedCutGroups.Batch090.populationMatches1087
    PopulationCertificates.Batch036.valid724 PopulationCertificates.Batch036.sound724 WitnessCertificates.Batch036.valid724 WitnessCertificates.Batch036.sound724 CountingCertificates.Batch036.valid724 CountingCertificates.Batch036.sound724
    CutLabelCertificates.Entropy018.valid363 CutLabelCertificates.Minority018.valid362 CutLabelCertificates.Minority018.sound362 H st hI
theorem probabilityBound362 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch090.certificate1086).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate724).dm (WitnessCertificates.Batch036.certificate724).beta) ≤ ((CutFailureCertificates.Budget036.certificate724).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound724 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate724).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch090.certificate1086).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch090.certificate1087).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch036.certificate724).omega:ℝ) ≤ ((CutFailureCertificates.Budget036.certificate724).bound:ℝ) at hb
  exact (exponentialBound362 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches363 : (MergedCutGroups.Batch090.certificate1089).GlobalMatches MergedCutGroups.Batch090.certificate1090 CountingCertificates.Batch036.certificate726 CutLabelCertificates.Entropy018.certificate364 CutLabelCertificates.Minority018.certificate363 := by decide +kernel
theorem exponentialBound363 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch090.certificate1089).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate726).dm (WitnessCertificates.Batch036.certificate726).beta) ≤ (2*exp (-((CountingCertificates.Batch036.certificate726).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch090.certificate1089).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch090.certificate1090).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch036.certificate726).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch090.certificate1089 MergedCutGroups.Batch090.certificate1090 CountingCertificates.Batch036.certificate726 CutLabelCertificates.Entropy018.certificate364 CutLabelCertificates.Minority018.certificate363 matches363 rfl rfl
    MergedCutGroups.Batch090.numericValid1089 MergedCutGroups.Batch090.numericValid1090 MergedCutGroups.Batch090.cellsSound1089 MergedCutGroups.Batch090.cellsSound1090
    MergedCutGroups.Batch090.cellsNumeric1089 MergedCutGroups.Batch090.cellsNumeric1090 MergedCutGroups.Batch090.populationMatches1089 MergedCutGroups.Batch090.populationMatches1090
    PopulationCertificates.Batch036.valid726 PopulationCertificates.Batch036.sound726 WitnessCertificates.Batch036.valid726 WitnessCertificates.Batch036.sound726 CountingCertificates.Batch036.valid726 CountingCertificates.Batch036.sound726
    CutLabelCertificates.Entropy018.valid364 CutLabelCertificates.Minority018.valid363 CutLabelCertificates.Minority018.sound363 H st hI
theorem probabilityBound363 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch090.certificate1089).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate726).dm (WitnessCertificates.Batch036.certificate726).beta) ≤ ((CutFailureCertificates.Budget036.certificate726).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound726 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate726).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch090.certificate1089).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch090.certificate1090).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch036.certificate726).omega:ℝ) ≤ ((CutFailureCertificates.Budget036.certificate726).bound:ℝ) at hb
  exact (exponentialBound363 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches364 : (MergedCutGroups.Batch091.certificate1092).GlobalMatches MergedCutGroups.Batch091.certificate1093 CountingCertificates.Batch036.certificate728 CutLabelCertificates.Entropy018.certificate365 CutLabelCertificates.Minority018.certificate364 := by decide +kernel
theorem exponentialBound364 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch091.certificate1092).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate728).dm (WitnessCertificates.Batch036.certificate728).beta) ≤ (2*exp (-((CountingCertificates.Batch036.certificate728).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch091.certificate1092).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch091.certificate1093).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch036.certificate728).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch091.certificate1092 MergedCutGroups.Batch091.certificate1093 CountingCertificates.Batch036.certificate728 CutLabelCertificates.Entropy018.certificate365 CutLabelCertificates.Minority018.certificate364 matches364 rfl rfl
    MergedCutGroups.Batch091.numericValid1092 MergedCutGroups.Batch091.numericValid1093 MergedCutGroups.Batch091.cellsSound1092 MergedCutGroups.Batch091.cellsSound1093
    MergedCutGroups.Batch091.cellsNumeric1092 MergedCutGroups.Batch091.cellsNumeric1093 MergedCutGroups.Batch091.populationMatches1092 MergedCutGroups.Batch091.populationMatches1093
    PopulationCertificates.Batch036.valid728 PopulationCertificates.Batch036.sound728 WitnessCertificates.Batch036.valid728 WitnessCertificates.Batch036.sound728 CountingCertificates.Batch036.valid728 CountingCertificates.Batch036.sound728
    CutLabelCertificates.Entropy018.valid365 CutLabelCertificates.Minority018.valid364 CutLabelCertificates.Minority018.sound364 H st hI
theorem probabilityBound364 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch091.certificate1092).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate728).dm (WitnessCertificates.Batch036.certificate728).beta) ≤ ((CutFailureCertificates.Budget036.certificate728).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound728 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate728).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch091.certificate1092).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch091.certificate1093).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch036.certificate728).omega:ℝ) ≤ ((CutFailureCertificates.Budget036.certificate728).bound:ℝ) at hb
  exact (exponentialBound364 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches365 : (MergedCutGroups.Batch091.certificate1095).GlobalMatches MergedCutGroups.Batch091.certificate1096 CountingCertificates.Batch036.certificate730 CutLabelCertificates.Entropy018.certificate366 CutLabelCertificates.Minority018.certificate365 := by decide +kernel
theorem exponentialBound365 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch091.certificate1095).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate730).dm (WitnessCertificates.Batch036.certificate730).beta) ≤ (2*exp (-((CountingCertificates.Batch036.certificate730).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch091.certificate1095).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch091.certificate1096).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch036.certificate730).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch091.certificate1095 MergedCutGroups.Batch091.certificate1096 CountingCertificates.Batch036.certificate730 CutLabelCertificates.Entropy018.certificate366 CutLabelCertificates.Minority018.certificate365 matches365 rfl rfl
    MergedCutGroups.Batch091.numericValid1095 MergedCutGroups.Batch091.numericValid1096 MergedCutGroups.Batch091.cellsSound1095 MergedCutGroups.Batch091.cellsSound1096
    MergedCutGroups.Batch091.cellsNumeric1095 MergedCutGroups.Batch091.cellsNumeric1096 MergedCutGroups.Batch091.populationMatches1095 MergedCutGroups.Batch091.populationMatches1096
    PopulationCertificates.Batch036.valid730 PopulationCertificates.Batch036.sound730 WitnessCertificates.Batch036.valid730 WitnessCertificates.Batch036.sound730 CountingCertificates.Batch036.valid730 CountingCertificates.Batch036.sound730
    CutLabelCertificates.Entropy018.valid366 CutLabelCertificates.Minority018.valid365 CutLabelCertificates.Minority018.sound365 H st hI
theorem probabilityBound365 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch091.certificate1095).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate730).dm (WitnessCertificates.Batch036.certificate730).beta) ≤ ((CutFailureCertificates.Budget036.certificate730).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound730 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate730).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch091.certificate1095).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch091.certificate1096).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch036.certificate730).omega:ℝ) ≤ ((CutFailureCertificates.Budget036.certificate730).bound:ℝ) at hb
  exact (exponentialBound365 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches366 : (MergedCutGroups.Batch091.certificate1098).GlobalMatches MergedCutGroups.Batch091.certificate1099 CountingCertificates.Batch036.certificate732 CutLabelCertificates.Entropy018.certificate367 CutLabelCertificates.Minority018.certificate366 := by decide +kernel
theorem exponentialBound366 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch091.certificate1098).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate732).dm (WitnessCertificates.Batch036.certificate732).beta) ≤ (2*exp (-((CountingCertificates.Batch036.certificate732).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch091.certificate1098).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch091.certificate1099).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch036.certificate732).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch091.certificate1098 MergedCutGroups.Batch091.certificate1099 CountingCertificates.Batch036.certificate732 CutLabelCertificates.Entropy018.certificate367 CutLabelCertificates.Minority018.certificate366 matches366 rfl rfl
    MergedCutGroups.Batch091.numericValid1098 MergedCutGroups.Batch091.numericValid1099 MergedCutGroups.Batch091.cellsSound1098 MergedCutGroups.Batch091.cellsSound1099
    MergedCutGroups.Batch091.cellsNumeric1098 MergedCutGroups.Batch091.cellsNumeric1099 MergedCutGroups.Batch091.populationMatches1098 MergedCutGroups.Batch091.populationMatches1099
    PopulationCertificates.Batch036.valid732 PopulationCertificates.Batch036.sound732 WitnessCertificates.Batch036.valid732 WitnessCertificates.Batch036.sound732 CountingCertificates.Batch036.valid732 CountingCertificates.Batch036.sound732
    CutLabelCertificates.Entropy018.valid367 CutLabelCertificates.Minority018.valid366 CutLabelCertificates.Minority018.sound366 H st hI
theorem probabilityBound366 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch091.certificate1098).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate732).dm (WitnessCertificates.Batch036.certificate732).beta) ≤ ((CutFailureCertificates.Budget036.certificate732).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound732 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate732).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch091.certificate1098).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch091.certificate1099).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch036.certificate732).omega:ℝ) ≤ ((CutFailureCertificates.Budget036.certificate732).bound:ℝ) at hb
  exact (exponentialBound366 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches367 : (MergedCutGroups.Batch091.certificate1101).GlobalMatches MergedCutGroups.Batch091.certificate1102 CountingCertificates.Batch036.certificate734 CutLabelCertificates.Entropy018.certificate368 CutLabelCertificates.Minority018.certificate367 := by decide +kernel
theorem exponentialBound367 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch091.certificate1101).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate734).dm (WitnessCertificates.Batch036.certificate734).beta) ≤ (2*exp (-((CountingCertificates.Batch036.certificate734).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch091.certificate1101).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch091.certificate1102).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch036.certificate734).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch091.certificate1101 MergedCutGroups.Batch091.certificate1102 CountingCertificates.Batch036.certificate734 CutLabelCertificates.Entropy018.certificate368 CutLabelCertificates.Minority018.certificate367 matches367 rfl rfl
    MergedCutGroups.Batch091.numericValid1101 MergedCutGroups.Batch091.numericValid1102 MergedCutGroups.Batch091.cellsSound1101 MergedCutGroups.Batch091.cellsSound1102
    MergedCutGroups.Batch091.cellsNumeric1101 MergedCutGroups.Batch091.cellsNumeric1102 MergedCutGroups.Batch091.populationMatches1101 MergedCutGroups.Batch091.populationMatches1102
    PopulationCertificates.Batch036.valid734 PopulationCertificates.Batch036.sound734 WitnessCertificates.Batch036.valid734 WitnessCertificates.Batch036.sound734 CountingCertificates.Batch036.valid734 CountingCertificates.Batch036.sound734
    CutLabelCertificates.Entropy018.valid368 CutLabelCertificates.Minority018.valid367 CutLabelCertificates.Minority018.sound367 H st hI
theorem probabilityBound367 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch091.certificate1101).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate734).dm (WitnessCertificates.Batch036.certificate734).beta) ≤ ((CutFailureCertificates.Budget036.certificate734).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound734 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate734).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch091.certificate1101).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch091.certificate1102).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch036.certificate734).omega:ℝ) ≤ ((CutFailureCertificates.Budget036.certificate734).bound:ℝ) at hb
  exact (exponentialBound367 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches368 : (MergedCutGroups.Batch092.certificate1104).GlobalMatches MergedCutGroups.Batch092.certificate1105 CountingCertificates.Batch036.certificate736 CutLabelCertificates.Entropy018.certificate369 CutLabelCertificates.Minority018.certificate368 := by decide +kernel
theorem exponentialBound368 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch092.certificate1104).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate736).dm (WitnessCertificates.Batch036.certificate736).beta) ≤ (2*exp (-((CountingCertificates.Batch036.certificate736).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch092.certificate1104).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch092.certificate1105).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch036.certificate736).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch092.certificate1104 MergedCutGroups.Batch092.certificate1105 CountingCertificates.Batch036.certificate736 CutLabelCertificates.Entropy018.certificate369 CutLabelCertificates.Minority018.certificate368 matches368 rfl rfl
    MergedCutGroups.Batch092.numericValid1104 MergedCutGroups.Batch092.numericValid1105 MergedCutGroups.Batch092.cellsSound1104 MergedCutGroups.Batch092.cellsSound1105
    MergedCutGroups.Batch092.cellsNumeric1104 MergedCutGroups.Batch092.cellsNumeric1105 MergedCutGroups.Batch092.populationMatches1104 MergedCutGroups.Batch092.populationMatches1105
    PopulationCertificates.Batch036.valid736 PopulationCertificates.Batch036.sound736 WitnessCertificates.Batch036.valid736 WitnessCertificates.Batch036.sound736 CountingCertificates.Batch036.valid736 CountingCertificates.Batch036.sound736
    CutLabelCertificates.Entropy018.valid369 CutLabelCertificates.Minority018.valid368 CutLabelCertificates.Minority018.sound368 H st hI
theorem probabilityBound368 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch092.certificate1104).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate736).dm (WitnessCertificates.Batch036.certificate736).beta) ≤ ((CutFailureCertificates.Budget036.certificate736).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound736 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate736).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch092.certificate1104).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch092.certificate1105).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch036.certificate736).omega:ℝ) ≤ ((CutFailureCertificates.Budget036.certificate736).bound:ℝ) at hb
  exact (exponentialBound368 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches369 : (MergedCutGroups.Batch092.certificate1107).GlobalMatches MergedCutGroups.Batch092.certificate1108 CountingCertificates.Batch036.certificate738 CutLabelCertificates.Entropy018.certificate370 CutLabelCertificates.Minority018.certificate369 := by decide +kernel
theorem exponentialBound369 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch092.certificate1107).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate738).dm (WitnessCertificates.Batch036.certificate738).beta) ≤ (2*exp (-((CountingCertificates.Batch036.certificate738).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch092.certificate1107).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch092.certificate1108).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch036.certificate738).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch092.certificate1107 MergedCutGroups.Batch092.certificate1108 CountingCertificates.Batch036.certificate738 CutLabelCertificates.Entropy018.certificate370 CutLabelCertificates.Minority018.certificate369 matches369 rfl rfl
    MergedCutGroups.Batch092.numericValid1107 MergedCutGroups.Batch092.numericValid1108 MergedCutGroups.Batch092.cellsSound1107 MergedCutGroups.Batch092.cellsSound1108
    MergedCutGroups.Batch092.cellsNumeric1107 MergedCutGroups.Batch092.cellsNumeric1108 MergedCutGroups.Batch092.populationMatches1107 MergedCutGroups.Batch092.populationMatches1108
    PopulationCertificates.Batch036.valid738 PopulationCertificates.Batch036.sound738 WitnessCertificates.Batch036.valid738 WitnessCertificates.Batch036.sound738 CountingCertificates.Batch036.valid738 CountingCertificates.Batch036.sound738
    CutLabelCertificates.Entropy018.valid370 CutLabelCertificates.Minority018.valid369 CutLabelCertificates.Minority018.sound369 H st hI
theorem probabilityBound369 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch092.certificate1107).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch036.certificate738).dm (WitnessCertificates.Batch036.certificate738).beta) ≤ ((CutFailureCertificates.Budget036.certificate738).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget036.sound738 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch036.certificate738).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch092.certificate1107).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch092.certificate1108).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch036.certificate738).omega:ℝ) ≤ ((CutFailureCertificates.Budget036.certificate738).bound:ℝ) at hb
  exact (exponentialBound369 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches370 : (MergedCutGroups.Batch092.certificate1110).GlobalMatches MergedCutGroups.Batch092.certificate1111 CountingCertificates.Batch037.certificate740 CutLabelCertificates.Entropy018.certificate371 CutLabelCertificates.Minority018.certificate370 := by decide +kernel
theorem exponentialBound370 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch092.certificate1110).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate740).dm (WitnessCertificates.Batch037.certificate740).beta) ≤ (2*exp (-((CountingCertificates.Batch037.certificate740).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch092.certificate1110).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch092.certificate1111).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch037.certificate740).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch092.certificate1110 MergedCutGroups.Batch092.certificate1111 CountingCertificates.Batch037.certificate740 CutLabelCertificates.Entropy018.certificate371 CutLabelCertificates.Minority018.certificate370 matches370 rfl rfl
    MergedCutGroups.Batch092.numericValid1110 MergedCutGroups.Batch092.numericValid1111 MergedCutGroups.Batch092.cellsSound1110 MergedCutGroups.Batch092.cellsSound1111
    MergedCutGroups.Batch092.cellsNumeric1110 MergedCutGroups.Batch092.cellsNumeric1111 MergedCutGroups.Batch092.populationMatches1110 MergedCutGroups.Batch092.populationMatches1111
    PopulationCertificates.Batch037.valid740 PopulationCertificates.Batch037.sound740 WitnessCertificates.Batch037.valid740 WitnessCertificates.Batch037.sound740 CountingCertificates.Batch037.valid740 CountingCertificates.Batch037.sound740
    CutLabelCertificates.Entropy018.valid371 CutLabelCertificates.Minority018.valid370 CutLabelCertificates.Minority018.sound370 H st hI
theorem probabilityBound370 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch092.certificate1110).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate740).dm (WitnessCertificates.Batch037.certificate740).beta) ≤ ((CutFailureCertificates.Budget037.certificate740).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound740 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate740).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch092.certificate1110).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch092.certificate1111).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch037.certificate740).omega:ℝ) ≤ ((CutFailureCertificates.Budget037.certificate740).bound:ℝ) at hb
  exact (exponentialBound370 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches371 : (MergedCutGroups.Batch092.certificate1113).GlobalMatches MergedCutGroups.Batch092.certificate1114 CountingCertificates.Batch037.certificate742 CutLabelCertificates.Entropy018.certificate372 CutLabelCertificates.Minority018.certificate371 := by decide +kernel
theorem exponentialBound371 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch092.certificate1113).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate742).dm (WitnessCertificates.Batch037.certificate742).beta) ≤ (2*exp (-((CountingCertificates.Batch037.certificate742).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch092.certificate1113).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch092.certificate1114).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch037.certificate742).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch092.certificate1113 MergedCutGroups.Batch092.certificate1114 CountingCertificates.Batch037.certificate742 CutLabelCertificates.Entropy018.certificate372 CutLabelCertificates.Minority018.certificate371 matches371 rfl rfl
    MergedCutGroups.Batch092.numericValid1113 MergedCutGroups.Batch092.numericValid1114 MergedCutGroups.Batch092.cellsSound1113 MergedCutGroups.Batch092.cellsSound1114
    MergedCutGroups.Batch092.cellsNumeric1113 MergedCutGroups.Batch092.cellsNumeric1114 MergedCutGroups.Batch092.populationMatches1113 MergedCutGroups.Batch092.populationMatches1114
    PopulationCertificates.Batch037.valid742 PopulationCertificates.Batch037.sound742 WitnessCertificates.Batch037.valid742 WitnessCertificates.Batch037.sound742 CountingCertificates.Batch037.valid742 CountingCertificates.Batch037.sound742
    CutLabelCertificates.Entropy018.valid372 CutLabelCertificates.Minority018.valid371 CutLabelCertificates.Minority018.sound371 H st hI
theorem probabilityBound371 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch092.certificate1113).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate742).dm (WitnessCertificates.Batch037.certificate742).beta) ≤ ((CutFailureCertificates.Budget037.certificate742).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound742 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate742).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch092.certificate1113).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch092.certificate1114).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch037.certificate742).omega:ℝ) ≤ ((CutFailureCertificates.Budget037.certificate742).bound:ℝ) at hb
  exact (exponentialBound371 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches372 : (MergedCutGroups.Batch093.certificate1116).GlobalMatches MergedCutGroups.Batch093.certificate1117 CountingCertificates.Batch037.certificate744 CutLabelCertificates.Entropy018.certificate373 CutLabelCertificates.Minority018.certificate372 := by decide +kernel
theorem exponentialBound372 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch093.certificate1116).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate744).dm (WitnessCertificates.Batch037.certificate744).beta) ≤ (2*exp (-((CountingCertificates.Batch037.certificate744).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch093.certificate1116).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch093.certificate1117).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch037.certificate744).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch093.certificate1116 MergedCutGroups.Batch093.certificate1117 CountingCertificates.Batch037.certificate744 CutLabelCertificates.Entropy018.certificate373 CutLabelCertificates.Minority018.certificate372 matches372 rfl rfl
    MergedCutGroups.Batch093.numericValid1116 MergedCutGroups.Batch093.numericValid1117 MergedCutGroups.Batch093.cellsSound1116 MergedCutGroups.Batch093.cellsSound1117
    MergedCutGroups.Batch093.cellsNumeric1116 MergedCutGroups.Batch093.cellsNumeric1117 MergedCutGroups.Batch093.populationMatches1116 MergedCutGroups.Batch093.populationMatches1117
    PopulationCertificates.Batch037.valid744 PopulationCertificates.Batch037.sound744 WitnessCertificates.Batch037.valid744 WitnessCertificates.Batch037.sound744 CountingCertificates.Batch037.valid744 CountingCertificates.Batch037.sound744
    CutLabelCertificates.Entropy018.valid373 CutLabelCertificates.Minority018.valid372 CutLabelCertificates.Minority018.sound372 H st hI
theorem probabilityBound372 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch093.certificate1116).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate744).dm (WitnessCertificates.Batch037.certificate744).beta) ≤ ((CutFailureCertificates.Budget037.certificate744).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound744 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate744).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch093.certificate1116).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch093.certificate1117).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch037.certificate744).omega:ℝ) ≤ ((CutFailureCertificates.Budget037.certificate744).bound:ℝ) at hb
  exact (exponentialBound372 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches373 : (MergedCutGroups.Batch093.certificate1119).GlobalMatches MergedCutGroups.Batch093.certificate1120 CountingCertificates.Batch037.certificate746 CutLabelCertificates.Entropy018.certificate374 CutLabelCertificates.Minority018.certificate373 := by decide +kernel
theorem exponentialBound373 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch093.certificate1119).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate746).dm (WitnessCertificates.Batch037.certificate746).beta) ≤ (2*exp (-((CountingCertificates.Batch037.certificate746).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch093.certificate1119).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch093.certificate1120).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch037.certificate746).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch093.certificate1119 MergedCutGroups.Batch093.certificate1120 CountingCertificates.Batch037.certificate746 CutLabelCertificates.Entropy018.certificate374 CutLabelCertificates.Minority018.certificate373 matches373 rfl rfl
    MergedCutGroups.Batch093.numericValid1119 MergedCutGroups.Batch093.numericValid1120 MergedCutGroups.Batch093.cellsSound1119 MergedCutGroups.Batch093.cellsSound1120
    MergedCutGroups.Batch093.cellsNumeric1119 MergedCutGroups.Batch093.cellsNumeric1120 MergedCutGroups.Batch093.populationMatches1119 MergedCutGroups.Batch093.populationMatches1120
    PopulationCertificates.Batch037.valid746 PopulationCertificates.Batch037.sound746 WitnessCertificates.Batch037.valid746 WitnessCertificates.Batch037.sound746 CountingCertificates.Batch037.valid746 CountingCertificates.Batch037.sound746
    CutLabelCertificates.Entropy018.valid374 CutLabelCertificates.Minority018.valid373 CutLabelCertificates.Minority018.sound373 H st hI
theorem probabilityBound373 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch093.certificate1119).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate746).dm (WitnessCertificates.Batch037.certificate746).beta) ≤ ((CutFailureCertificates.Budget037.certificate746).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound746 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate746).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch093.certificate1119).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch093.certificate1120).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch037.certificate746).omega:ℝ) ≤ ((CutFailureCertificates.Budget037.certificate746).bound:ℝ) at hb
  exact (exponentialBound373 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches374 : (MergedCutGroups.Batch093.certificate1122).GlobalMatches MergedCutGroups.Batch093.certificate1123 CountingCertificates.Batch037.certificate748 CutLabelCertificates.Entropy018.certificate375 CutLabelCertificates.Minority018.certificate374 := by decide +kernel
theorem exponentialBound374 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch093.certificate1122).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate748).dm (WitnessCertificates.Batch037.certificate748).beta) ≤ (2*exp (-((CountingCertificates.Batch037.certificate748).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch093.certificate1122).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch093.certificate1123).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch037.certificate748).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch093.certificate1122 MergedCutGroups.Batch093.certificate1123 CountingCertificates.Batch037.certificate748 CutLabelCertificates.Entropy018.certificate375 CutLabelCertificates.Minority018.certificate374 matches374 rfl rfl
    MergedCutGroups.Batch093.numericValid1122 MergedCutGroups.Batch093.numericValid1123 MergedCutGroups.Batch093.cellsSound1122 MergedCutGroups.Batch093.cellsSound1123
    MergedCutGroups.Batch093.cellsNumeric1122 MergedCutGroups.Batch093.cellsNumeric1123 MergedCutGroups.Batch093.populationMatches1122 MergedCutGroups.Batch093.populationMatches1123
    PopulationCertificates.Batch037.valid748 PopulationCertificates.Batch037.sound748 WitnessCertificates.Batch037.valid748 WitnessCertificates.Batch037.sound748 CountingCertificates.Batch037.valid748 CountingCertificates.Batch037.sound748
    CutLabelCertificates.Entropy018.valid375 CutLabelCertificates.Minority018.valid374 CutLabelCertificates.Minority018.sound374 H st hI
theorem probabilityBound374 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch093.certificate1122).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate748).dm (WitnessCertificates.Batch037.certificate748).beta) ≤ ((CutFailureCertificates.Budget037.certificate748).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound748 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate748).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch093.certificate1122).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch093.certificate1123).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch037.certificate748).omega:ℝ) ≤ ((CutFailureCertificates.Budget037.certificate748).bound:ℝ) at hb
  exact (exponentialBound374 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches375 : (MergedCutGroups.Batch093.certificate1125).GlobalMatches MergedCutGroups.Batch093.certificate1126 CountingCertificates.Batch037.certificate750 CutLabelCertificates.Entropy018.certificate376 CutLabelCertificates.Minority018.certificate375 := by decide +kernel
theorem exponentialBound375 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch093.certificate1125).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate750).dm (WitnessCertificates.Batch037.certificate750).beta) ≤ (2*exp (-((CountingCertificates.Batch037.certificate750).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch093.certificate1125).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch093.certificate1126).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch037.certificate750).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch093.certificate1125 MergedCutGroups.Batch093.certificate1126 CountingCertificates.Batch037.certificate750 CutLabelCertificates.Entropy018.certificate376 CutLabelCertificates.Minority018.certificate375 matches375 rfl rfl
    MergedCutGroups.Batch093.numericValid1125 MergedCutGroups.Batch093.numericValid1126 MergedCutGroups.Batch093.cellsSound1125 MergedCutGroups.Batch093.cellsSound1126
    MergedCutGroups.Batch093.cellsNumeric1125 MergedCutGroups.Batch093.cellsNumeric1126 MergedCutGroups.Batch093.populationMatches1125 MergedCutGroups.Batch093.populationMatches1126
    PopulationCertificates.Batch037.valid750 PopulationCertificates.Batch037.sound750 WitnessCertificates.Batch037.valid750 WitnessCertificates.Batch037.sound750 CountingCertificates.Batch037.valid750 CountingCertificates.Batch037.sound750
    CutLabelCertificates.Entropy018.valid376 CutLabelCertificates.Minority018.valid375 CutLabelCertificates.Minority018.sound375 H st hI
theorem probabilityBound375 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch093.certificate1125).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate750).dm (WitnessCertificates.Batch037.certificate750).beta) ≤ ((CutFailureCertificates.Budget037.certificate750).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound750 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate750).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch093.certificate1125).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch093.certificate1126).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch037.certificate750).omega:ℝ) ≤ ((CutFailureCertificates.Budget037.certificate750).bound:ℝ) at hb
  exact (exponentialBound375 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches376 : (MergedCutGroups.Batch094.certificate1128).GlobalMatches MergedCutGroups.Batch094.certificate1129 CountingCertificates.Batch037.certificate752 CutLabelCertificates.Entropy018.certificate377 CutLabelCertificates.Minority018.certificate376 := by decide +kernel
theorem exponentialBound376 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch094.certificate1128).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate752).dm (WitnessCertificates.Batch037.certificate752).beta) ≤ (2*exp (-((CountingCertificates.Batch037.certificate752).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch094.certificate1128).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch094.certificate1129).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch037.certificate752).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch094.certificate1128 MergedCutGroups.Batch094.certificate1129 CountingCertificates.Batch037.certificate752 CutLabelCertificates.Entropy018.certificate377 CutLabelCertificates.Minority018.certificate376 matches376 rfl rfl
    MergedCutGroups.Batch094.numericValid1128 MergedCutGroups.Batch094.numericValid1129 MergedCutGroups.Batch094.cellsSound1128 MergedCutGroups.Batch094.cellsSound1129
    MergedCutGroups.Batch094.cellsNumeric1128 MergedCutGroups.Batch094.cellsNumeric1129 MergedCutGroups.Batch094.populationMatches1128 MergedCutGroups.Batch094.populationMatches1129
    PopulationCertificates.Batch037.valid752 PopulationCertificates.Batch037.sound752 WitnessCertificates.Batch037.valid752 WitnessCertificates.Batch037.sound752 CountingCertificates.Batch037.valid752 CountingCertificates.Batch037.sound752
    CutLabelCertificates.Entropy018.valid377 CutLabelCertificates.Minority018.valid376 CutLabelCertificates.Minority018.sound376 H st hI
theorem probabilityBound376 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch094.certificate1128).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate752).dm (WitnessCertificates.Batch037.certificate752).beta) ≤ ((CutFailureCertificates.Budget037.certificate752).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound752 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate752).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch094.certificate1128).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch094.certificate1129).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch037.certificate752).omega:ℝ) ≤ ((CutFailureCertificates.Budget037.certificate752).bound:ℝ) at hb
  exact (exponentialBound376 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches377 : (MergedCutGroups.Batch094.certificate1131).GlobalMatches MergedCutGroups.Batch094.certificate1132 CountingCertificates.Batch037.certificate754 CutLabelCertificates.Entropy018.certificate378 CutLabelCertificates.Minority018.certificate377 := by decide +kernel
theorem exponentialBound377 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch094.certificate1131).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate754).dm (WitnessCertificates.Batch037.certificate754).beta) ≤ (2*exp (-((CountingCertificates.Batch037.certificate754).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch094.certificate1131).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch094.certificate1132).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch037.certificate754).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch094.certificate1131 MergedCutGroups.Batch094.certificate1132 CountingCertificates.Batch037.certificate754 CutLabelCertificates.Entropy018.certificate378 CutLabelCertificates.Minority018.certificate377 matches377 rfl rfl
    MergedCutGroups.Batch094.numericValid1131 MergedCutGroups.Batch094.numericValid1132 MergedCutGroups.Batch094.cellsSound1131 MergedCutGroups.Batch094.cellsSound1132
    MergedCutGroups.Batch094.cellsNumeric1131 MergedCutGroups.Batch094.cellsNumeric1132 MergedCutGroups.Batch094.populationMatches1131 MergedCutGroups.Batch094.populationMatches1132
    PopulationCertificates.Batch037.valid754 PopulationCertificates.Batch037.sound754 WitnessCertificates.Batch037.valid754 WitnessCertificates.Batch037.sound754 CountingCertificates.Batch037.valid754 CountingCertificates.Batch037.sound754
    CutLabelCertificates.Entropy018.valid378 CutLabelCertificates.Minority018.valid377 CutLabelCertificates.Minority018.sound377 H st hI
theorem probabilityBound377 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch094.certificate1131).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate754).dm (WitnessCertificates.Batch037.certificate754).beta) ≤ ((CutFailureCertificates.Budget037.certificate754).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound754 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate754).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch094.certificate1131).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch094.certificate1132).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch037.certificate754).omega:ℝ) ≤ ((CutFailureCertificates.Budget037.certificate754).bound:ℝ) at hb
  exact (exponentialBound377 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches378 : (MergedCutGroups.Batch094.certificate1134).GlobalMatches MergedCutGroups.Batch094.certificate1135 CountingCertificates.Batch037.certificate756 CutLabelCertificates.Entropy018.certificate379 CutLabelCertificates.Minority018.certificate378 := by decide +kernel
theorem exponentialBound378 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch094.certificate1134).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate756).dm (WitnessCertificates.Batch037.certificate756).beta) ≤ (2*exp (-((CountingCertificates.Batch037.certificate756).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch094.certificate1134).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch094.certificate1135).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch037.certificate756).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch094.certificate1134 MergedCutGroups.Batch094.certificate1135 CountingCertificates.Batch037.certificate756 CutLabelCertificates.Entropy018.certificate379 CutLabelCertificates.Minority018.certificate378 matches378 rfl rfl
    MergedCutGroups.Batch094.numericValid1134 MergedCutGroups.Batch094.numericValid1135 MergedCutGroups.Batch094.cellsSound1134 MergedCutGroups.Batch094.cellsSound1135
    MergedCutGroups.Batch094.cellsNumeric1134 MergedCutGroups.Batch094.cellsNumeric1135 MergedCutGroups.Batch094.populationMatches1134 MergedCutGroups.Batch094.populationMatches1135
    PopulationCertificates.Batch037.valid756 PopulationCertificates.Batch037.sound756 WitnessCertificates.Batch037.valid756 WitnessCertificates.Batch037.sound756 CountingCertificates.Batch037.valid756 CountingCertificates.Batch037.sound756
    CutLabelCertificates.Entropy018.valid379 CutLabelCertificates.Minority018.valid378 CutLabelCertificates.Minority018.sound378 H st hI
theorem probabilityBound378 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch094.certificate1134).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate756).dm (WitnessCertificates.Batch037.certificate756).beta) ≤ ((CutFailureCertificates.Budget037.certificate756).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound756 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate756).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch094.certificate1134).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch094.certificate1135).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch037.certificate756).omega:ℝ) ≤ ((CutFailureCertificates.Budget037.certificate756).bound:ℝ) at hb
  exact (exponentialBound378 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches379 : (MergedCutGroups.Batch094.certificate1137).GlobalMatches MergedCutGroups.Batch094.certificate1138 CountingCertificates.Batch037.certificate758 CutLabelCertificates.Entropy019.certificate380 CutLabelCertificates.Minority018.certificate379 := by decide +kernel
theorem exponentialBound379 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch094.certificate1137).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate758).dm (WitnessCertificates.Batch037.certificate758).beta) ≤ (2*exp (-((CountingCertificates.Batch037.certificate758).aa:ℝ)*st.R)+(2*exp (-((MergedCutGroups.Batch094.certificate1137).exponent:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch094.certificate1138).exponent:ℝ)*st.R)))/((WitnessCertificates.Batch037.certificate758).omega:ℝ) :=
  certified_global_failure MergedCutGroups.Batch094.certificate1137 MergedCutGroups.Batch094.certificate1138 CountingCertificates.Batch037.certificate758 CutLabelCertificates.Entropy019.certificate380 CutLabelCertificates.Minority018.certificate379 matches379 rfl rfl
    MergedCutGroups.Batch094.numericValid1137 MergedCutGroups.Batch094.numericValid1138 MergedCutGroups.Batch094.cellsSound1137 MergedCutGroups.Batch094.cellsSound1138
    MergedCutGroups.Batch094.cellsNumeric1137 MergedCutGroups.Batch094.cellsNumeric1138 MergedCutGroups.Batch094.populationMatches1137 MergedCutGroups.Batch094.populationMatches1138
    PopulationCertificates.Batch037.valid758 PopulationCertificates.Batch037.sound758 WitnessCertificates.Batch037.valid758 WitnessCertificates.Batch037.sound758 CountingCertificates.Batch037.valid758 CountingCertificates.Batch037.sound758
    CutLabelCertificates.Entropy019.valid380 CutLabelCertificates.Minority018.valid379 CutLabelCertificates.Minority018.sound379 H st hI
theorem probabilityBound379 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch094.certificate1137).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedExpansionFailure H univ st.N st.z (WitnessCertificates.Batch037.certificate758).dm (WitnessCertificates.Batch037.certificate758).beta) ≤ ((CutFailureCertificates.Budget037.certificate758).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget037.sound758 st.R st.scale_lower
  change (((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch037.certificate758).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch094.certificate1137).exponent:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch094.certificate1138).exponent:ℝ)*st.R)+0)))/((WitnessCertificates.Batch037.certificate758).omega:ℝ) ≤ ((CutFailureCertificates.Budget037.certificate758).bound:ℝ) at hb
  exact (exponentialBound379 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedGlobalFailures.Batch018
