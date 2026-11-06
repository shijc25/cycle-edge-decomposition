import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch012
import Cycle12.CountingCertificates.Batch013
import Cycle12.CutFailureCertificates.Budget012
import Cycle12.CutFailureCertificates.Budget013
import Cycle12.MergedCutGroups.Batch030
import Cycle12.MergedCutGroups.Batch031
import Cycle12.MergedCutGroups.Batch032
import Cycle12.MergedCutGroups.Batch033
import Cycle12.MergedCutGroups.Batch034
import Cycle12.PopulationCertificates.Batch012
import Cycle12.PopulationCertificates.Batch013
import Cycle12.WitnessCertificates.Batch012
import Cycle12.WitnessCertificates.Batch013

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedAnchorFailures.Batch006
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches120 : (MergedCutGroups.Batch030.certificate362).AnchorMatches CountingCertificates.Batch012.certificate241 := by decide +kernel
theorem exponentialBound120 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch030.certificate362).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate241).dm (WitnessCertificates.Batch012.certificate241).beta (WitnessCertificates.Batch012.certificate241).L) ≤ (2*exp (-((CountingCertificates.Batch012.certificate241).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch030.certificate362).exponent:ℝ)*st.R))/((WitnessCertificates.Batch012.certificate241).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch030.certificate362 CountingCertificates.Batch012.certificate241 matches120 MergedCutGroups.Batch030.numericValid362 MergedCutGroups.Batch030.cellsSound362 MergedCutGroups.Batch030.cellsNumeric362 MergedCutGroups.Batch030.populationMatches362
    PopulationCertificates.Batch012.valid241 PopulationCertificates.Batch012.sound241 WitnessCertificates.Batch012.valid241 WitnessCertificates.Batch012.sound241 CountingCertificates.Batch012.valid241 CountingCertificates.Batch012.sound241 H st hI
theorem probabilityBound120 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch030.certificate362).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate241).dm (WitnessCertificates.Batch012.certificate241).beta (WitnessCertificates.Batch012.certificate241).L) ≤ ((CutFailureCertificates.Budget012.certificate241).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound241 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate241).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch030.certificate362).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch012.certificate241).omega:ℝ)) ≤ ((CutFailureCertificates.Budget012.certificate241).bound:ℝ) at hb
  exact (exponentialBound120 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches121 : (MergedCutGroups.Batch030.certificate365).AnchorMatches CountingCertificates.Batch012.certificate243 := by decide +kernel
theorem exponentialBound121 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch030.certificate365).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate243).dm (WitnessCertificates.Batch012.certificate243).beta (WitnessCertificates.Batch012.certificate243).L) ≤ (2*exp (-((CountingCertificates.Batch012.certificate243).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch030.certificate365).exponent:ℝ)*st.R))/((WitnessCertificates.Batch012.certificate243).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch030.certificate365 CountingCertificates.Batch012.certificate243 matches121 MergedCutGroups.Batch030.numericValid365 MergedCutGroups.Batch030.cellsSound365 MergedCutGroups.Batch030.cellsNumeric365 MergedCutGroups.Batch030.populationMatches365
    PopulationCertificates.Batch012.valid243 PopulationCertificates.Batch012.sound243 WitnessCertificates.Batch012.valid243 WitnessCertificates.Batch012.sound243 CountingCertificates.Batch012.valid243 CountingCertificates.Batch012.sound243 H st hI
theorem probabilityBound121 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch030.certificate365).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate243).dm (WitnessCertificates.Batch012.certificate243).beta (WitnessCertificates.Batch012.certificate243).L) ≤ ((CutFailureCertificates.Budget012.certificate243).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound243 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate243).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch030.certificate365).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch012.certificate243).omega:ℝ)) ≤ ((CutFailureCertificates.Budget012.certificate243).bound:ℝ) at hb
  exact (exponentialBound121 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches122 : (MergedCutGroups.Batch030.certificate368).AnchorMatches CountingCertificates.Batch012.certificate245 := by decide +kernel
theorem exponentialBound122 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch030.certificate368).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate245).dm (WitnessCertificates.Batch012.certificate245).beta (WitnessCertificates.Batch012.certificate245).L) ≤ (2*exp (-((CountingCertificates.Batch012.certificate245).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch030.certificate368).exponent:ℝ)*st.R))/((WitnessCertificates.Batch012.certificate245).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch030.certificate368 CountingCertificates.Batch012.certificate245 matches122 MergedCutGroups.Batch030.numericValid368 MergedCutGroups.Batch030.cellsSound368 MergedCutGroups.Batch030.cellsNumeric368 MergedCutGroups.Batch030.populationMatches368
    PopulationCertificates.Batch012.valid245 PopulationCertificates.Batch012.sound245 WitnessCertificates.Batch012.valid245 WitnessCertificates.Batch012.sound245 CountingCertificates.Batch012.valid245 CountingCertificates.Batch012.sound245 H st hI
theorem probabilityBound122 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch030.certificate368).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate245).dm (WitnessCertificates.Batch012.certificate245).beta (WitnessCertificates.Batch012.certificate245).L) ≤ ((CutFailureCertificates.Budget012.certificate245).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound245 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate245).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch030.certificate368).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch012.certificate245).omega:ℝ)) ≤ ((CutFailureCertificates.Budget012.certificate245).bound:ℝ) at hb
  exact (exponentialBound122 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches123 : (MergedCutGroups.Batch030.certificate371).AnchorMatches CountingCertificates.Batch012.certificate247 := by decide +kernel
theorem exponentialBound123 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch030.certificate371).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate247).dm (WitnessCertificates.Batch012.certificate247).beta (WitnessCertificates.Batch012.certificate247).L) ≤ (2*exp (-((CountingCertificates.Batch012.certificate247).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch030.certificate371).exponent:ℝ)*st.R))/((WitnessCertificates.Batch012.certificate247).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch030.certificate371 CountingCertificates.Batch012.certificate247 matches123 MergedCutGroups.Batch030.numericValid371 MergedCutGroups.Batch030.cellsSound371 MergedCutGroups.Batch030.cellsNumeric371 MergedCutGroups.Batch030.populationMatches371
    PopulationCertificates.Batch012.valid247 PopulationCertificates.Batch012.sound247 WitnessCertificates.Batch012.valid247 WitnessCertificates.Batch012.sound247 CountingCertificates.Batch012.valid247 CountingCertificates.Batch012.sound247 H st hI
theorem probabilityBound123 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch030.certificate371).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate247).dm (WitnessCertificates.Batch012.certificate247).beta (WitnessCertificates.Batch012.certificate247).L) ≤ ((CutFailureCertificates.Budget012.certificate247).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound247 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate247).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch030.certificate371).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch012.certificate247).omega:ℝ)) ≤ ((CutFailureCertificates.Budget012.certificate247).bound:ℝ) at hb
  exact (exponentialBound123 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches124 : (MergedCutGroups.Batch031.certificate374).AnchorMatches CountingCertificates.Batch012.certificate249 := by decide +kernel
theorem exponentialBound124 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch031.certificate374).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate249).dm (WitnessCertificates.Batch012.certificate249).beta (WitnessCertificates.Batch012.certificate249).L) ≤ (2*exp (-((CountingCertificates.Batch012.certificate249).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch031.certificate374).exponent:ℝ)*st.R))/((WitnessCertificates.Batch012.certificate249).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch031.certificate374 CountingCertificates.Batch012.certificate249 matches124 MergedCutGroups.Batch031.numericValid374 MergedCutGroups.Batch031.cellsSound374 MergedCutGroups.Batch031.cellsNumeric374 MergedCutGroups.Batch031.populationMatches374
    PopulationCertificates.Batch012.valid249 PopulationCertificates.Batch012.sound249 WitnessCertificates.Batch012.valid249 WitnessCertificates.Batch012.sound249 CountingCertificates.Batch012.valid249 CountingCertificates.Batch012.sound249 H st hI
theorem probabilityBound124 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch031.certificate374).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate249).dm (WitnessCertificates.Batch012.certificate249).beta (WitnessCertificates.Batch012.certificate249).L) ≤ ((CutFailureCertificates.Budget012.certificate249).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound249 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate249).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch031.certificate374).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch012.certificate249).omega:ℝ)) ≤ ((CutFailureCertificates.Budget012.certificate249).bound:ℝ) at hb
  exact (exponentialBound124 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches125 : (MergedCutGroups.Batch031.certificate377).AnchorMatches CountingCertificates.Batch012.certificate251 := by decide +kernel
theorem exponentialBound125 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch031.certificate377).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate251).dm (WitnessCertificates.Batch012.certificate251).beta (WitnessCertificates.Batch012.certificate251).L) ≤ (2*exp (-((CountingCertificates.Batch012.certificate251).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch031.certificate377).exponent:ℝ)*st.R))/((WitnessCertificates.Batch012.certificate251).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch031.certificate377 CountingCertificates.Batch012.certificate251 matches125 MergedCutGroups.Batch031.numericValid377 MergedCutGroups.Batch031.cellsSound377 MergedCutGroups.Batch031.cellsNumeric377 MergedCutGroups.Batch031.populationMatches377
    PopulationCertificates.Batch012.valid251 PopulationCertificates.Batch012.sound251 WitnessCertificates.Batch012.valid251 WitnessCertificates.Batch012.sound251 CountingCertificates.Batch012.valid251 CountingCertificates.Batch012.sound251 H st hI
theorem probabilityBound125 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch031.certificate377).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate251).dm (WitnessCertificates.Batch012.certificate251).beta (WitnessCertificates.Batch012.certificate251).L) ≤ ((CutFailureCertificates.Budget012.certificate251).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound251 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate251).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch031.certificate377).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch012.certificate251).omega:ℝ)) ≤ ((CutFailureCertificates.Budget012.certificate251).bound:ℝ) at hb
  exact (exponentialBound125 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches126 : (MergedCutGroups.Batch031.certificate380).AnchorMatches CountingCertificates.Batch012.certificate253 := by decide +kernel
theorem exponentialBound126 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch031.certificate380).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate253).dm (WitnessCertificates.Batch012.certificate253).beta (WitnessCertificates.Batch012.certificate253).L) ≤ (2*exp (-((CountingCertificates.Batch012.certificate253).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch031.certificate380).exponent:ℝ)*st.R))/((WitnessCertificates.Batch012.certificate253).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch031.certificate380 CountingCertificates.Batch012.certificate253 matches126 MergedCutGroups.Batch031.numericValid380 MergedCutGroups.Batch031.cellsSound380 MergedCutGroups.Batch031.cellsNumeric380 MergedCutGroups.Batch031.populationMatches380
    PopulationCertificates.Batch012.valid253 PopulationCertificates.Batch012.sound253 WitnessCertificates.Batch012.valid253 WitnessCertificates.Batch012.sound253 CountingCertificates.Batch012.valid253 CountingCertificates.Batch012.sound253 H st hI
theorem probabilityBound126 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch031.certificate380).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate253).dm (WitnessCertificates.Batch012.certificate253).beta (WitnessCertificates.Batch012.certificate253).L) ≤ ((CutFailureCertificates.Budget012.certificate253).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound253 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate253).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch031.certificate380).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch012.certificate253).omega:ℝ)) ≤ ((CutFailureCertificates.Budget012.certificate253).bound:ℝ) at hb
  exact (exponentialBound126 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches127 : (MergedCutGroups.Batch031.certificate383).AnchorMatches CountingCertificates.Batch012.certificate255 := by decide +kernel
theorem exponentialBound127 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch031.certificate383).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate255).dm (WitnessCertificates.Batch012.certificate255).beta (WitnessCertificates.Batch012.certificate255).L) ≤ (2*exp (-((CountingCertificates.Batch012.certificate255).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch031.certificate383).exponent:ℝ)*st.R))/((WitnessCertificates.Batch012.certificate255).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch031.certificate383 CountingCertificates.Batch012.certificate255 matches127 MergedCutGroups.Batch031.numericValid383 MergedCutGroups.Batch031.cellsSound383 MergedCutGroups.Batch031.cellsNumeric383 MergedCutGroups.Batch031.populationMatches383
    PopulationCertificates.Batch012.valid255 PopulationCertificates.Batch012.sound255 WitnessCertificates.Batch012.valid255 WitnessCertificates.Batch012.sound255 CountingCertificates.Batch012.valid255 CountingCertificates.Batch012.sound255 H st hI
theorem probabilityBound127 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch031.certificate383).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate255).dm (WitnessCertificates.Batch012.certificate255).beta (WitnessCertificates.Batch012.certificate255).L) ≤ ((CutFailureCertificates.Budget012.certificate255).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound255 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate255).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch031.certificate383).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch012.certificate255).omega:ℝ)) ≤ ((CutFailureCertificates.Budget012.certificate255).bound:ℝ) at hb
  exact (exponentialBound127 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches128 : (MergedCutGroups.Batch032.certificate386).AnchorMatches CountingCertificates.Batch012.certificate257 := by decide +kernel
theorem exponentialBound128 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch032.certificate386).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate257).dm (WitnessCertificates.Batch012.certificate257).beta (WitnessCertificates.Batch012.certificate257).L) ≤ (2*exp (-((CountingCertificates.Batch012.certificate257).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch032.certificate386).exponent:ℝ)*st.R))/((WitnessCertificates.Batch012.certificate257).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch032.certificate386 CountingCertificates.Batch012.certificate257 matches128 MergedCutGroups.Batch032.numericValid386 MergedCutGroups.Batch032.cellsSound386 MergedCutGroups.Batch032.cellsNumeric386 MergedCutGroups.Batch032.populationMatches386
    PopulationCertificates.Batch012.valid257 PopulationCertificates.Batch012.sound257 WitnessCertificates.Batch012.valid257 WitnessCertificates.Batch012.sound257 CountingCertificates.Batch012.valid257 CountingCertificates.Batch012.sound257 H st hI
theorem probabilityBound128 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch032.certificate386).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate257).dm (WitnessCertificates.Batch012.certificate257).beta (WitnessCertificates.Batch012.certificate257).L) ≤ ((CutFailureCertificates.Budget012.certificate257).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound257 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate257).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch032.certificate386).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch012.certificate257).omega:ℝ)) ≤ ((CutFailureCertificates.Budget012.certificate257).bound:ℝ) at hb
  exact (exponentialBound128 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches129 : (MergedCutGroups.Batch032.certificate389).AnchorMatches CountingCertificates.Batch012.certificate259 := by decide +kernel
theorem exponentialBound129 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch032.certificate389).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate259).dm (WitnessCertificates.Batch012.certificate259).beta (WitnessCertificates.Batch012.certificate259).L) ≤ (2*exp (-((CountingCertificates.Batch012.certificate259).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch032.certificate389).exponent:ℝ)*st.R))/((WitnessCertificates.Batch012.certificate259).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch032.certificate389 CountingCertificates.Batch012.certificate259 matches129 MergedCutGroups.Batch032.numericValid389 MergedCutGroups.Batch032.cellsSound389 MergedCutGroups.Batch032.cellsNumeric389 MergedCutGroups.Batch032.populationMatches389
    PopulationCertificates.Batch012.valid259 PopulationCertificates.Batch012.sound259 WitnessCertificates.Batch012.valid259 WitnessCertificates.Batch012.sound259 CountingCertificates.Batch012.valid259 CountingCertificates.Batch012.sound259 H st hI
theorem probabilityBound129 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch032.certificate389).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch012.certificate259).dm (WitnessCertificates.Batch012.certificate259).beta (WitnessCertificates.Batch012.certificate259).L) ≤ ((CutFailureCertificates.Budget012.certificate259).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget012.sound259 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch012.certificate259).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch032.certificate389).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch012.certificate259).omega:ℝ)) ≤ ((CutFailureCertificates.Budget012.certificate259).bound:ℝ) at hb
  exact (exponentialBound129 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches130 : (MergedCutGroups.Batch032.certificate392).AnchorMatches CountingCertificates.Batch013.certificate261 := by decide +kernel
theorem exponentialBound130 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch032.certificate392).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate261).dm (WitnessCertificates.Batch013.certificate261).beta (WitnessCertificates.Batch013.certificate261).L) ≤ (2*exp (-((CountingCertificates.Batch013.certificate261).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch032.certificate392).exponent:ℝ)*st.R))/((WitnessCertificates.Batch013.certificate261).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch032.certificate392 CountingCertificates.Batch013.certificate261 matches130 MergedCutGroups.Batch032.numericValid392 MergedCutGroups.Batch032.cellsSound392 MergedCutGroups.Batch032.cellsNumeric392 MergedCutGroups.Batch032.populationMatches392
    PopulationCertificates.Batch013.valid261 PopulationCertificates.Batch013.sound261 WitnessCertificates.Batch013.valid261 WitnessCertificates.Batch013.sound261 CountingCertificates.Batch013.valid261 CountingCertificates.Batch013.sound261 H st hI
theorem probabilityBound130 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch032.certificate392).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate261).dm (WitnessCertificates.Batch013.certificate261).beta (WitnessCertificates.Batch013.certificate261).L) ≤ ((CutFailureCertificates.Budget013.certificate261).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound261 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate261).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch032.certificate392).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch013.certificate261).omega:ℝ)) ≤ ((CutFailureCertificates.Budget013.certificate261).bound:ℝ) at hb
  exact (exponentialBound130 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches131 : (MergedCutGroups.Batch032.certificate395).AnchorMatches CountingCertificates.Batch013.certificate263 := by decide +kernel
theorem exponentialBound131 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch032.certificate395).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate263).dm (WitnessCertificates.Batch013.certificate263).beta (WitnessCertificates.Batch013.certificate263).L) ≤ (2*exp (-((CountingCertificates.Batch013.certificate263).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch032.certificate395).exponent:ℝ)*st.R))/((WitnessCertificates.Batch013.certificate263).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch032.certificate395 CountingCertificates.Batch013.certificate263 matches131 MergedCutGroups.Batch032.numericValid395 MergedCutGroups.Batch032.cellsSound395 MergedCutGroups.Batch032.cellsNumeric395 MergedCutGroups.Batch032.populationMatches395
    PopulationCertificates.Batch013.valid263 PopulationCertificates.Batch013.sound263 WitnessCertificates.Batch013.valid263 WitnessCertificates.Batch013.sound263 CountingCertificates.Batch013.valid263 CountingCertificates.Batch013.sound263 H st hI
theorem probabilityBound131 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch032.certificate395).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate263).dm (WitnessCertificates.Batch013.certificate263).beta (WitnessCertificates.Batch013.certificate263).L) ≤ ((CutFailureCertificates.Budget013.certificate263).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound263 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate263).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch032.certificate395).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch013.certificate263).omega:ℝ)) ≤ ((CutFailureCertificates.Budget013.certificate263).bound:ℝ) at hb
  exact (exponentialBound131 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches132 : (MergedCutGroups.Batch033.certificate398).AnchorMatches CountingCertificates.Batch013.certificate265 := by decide +kernel
theorem exponentialBound132 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch033.certificate398).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate265).dm (WitnessCertificates.Batch013.certificate265).beta (WitnessCertificates.Batch013.certificate265).L) ≤ (2*exp (-((CountingCertificates.Batch013.certificate265).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch033.certificate398).exponent:ℝ)*st.R))/((WitnessCertificates.Batch013.certificate265).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch033.certificate398 CountingCertificates.Batch013.certificate265 matches132 MergedCutGroups.Batch033.numericValid398 MergedCutGroups.Batch033.cellsSound398 MergedCutGroups.Batch033.cellsNumeric398 MergedCutGroups.Batch033.populationMatches398
    PopulationCertificates.Batch013.valid265 PopulationCertificates.Batch013.sound265 WitnessCertificates.Batch013.valid265 WitnessCertificates.Batch013.sound265 CountingCertificates.Batch013.valid265 CountingCertificates.Batch013.sound265 H st hI
theorem probabilityBound132 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch033.certificate398).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate265).dm (WitnessCertificates.Batch013.certificate265).beta (WitnessCertificates.Batch013.certificate265).L) ≤ ((CutFailureCertificates.Budget013.certificate265).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound265 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate265).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch033.certificate398).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch013.certificate265).omega:ℝ)) ≤ ((CutFailureCertificates.Budget013.certificate265).bound:ℝ) at hb
  exact (exponentialBound132 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches133 : (MergedCutGroups.Batch033.certificate401).AnchorMatches CountingCertificates.Batch013.certificate267 := by decide +kernel
theorem exponentialBound133 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch033.certificate401).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate267).dm (WitnessCertificates.Batch013.certificate267).beta (WitnessCertificates.Batch013.certificate267).L) ≤ (2*exp (-((CountingCertificates.Batch013.certificate267).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch033.certificate401).exponent:ℝ)*st.R))/((WitnessCertificates.Batch013.certificate267).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch033.certificate401 CountingCertificates.Batch013.certificate267 matches133 MergedCutGroups.Batch033.numericValid401 MergedCutGroups.Batch033.cellsSound401 MergedCutGroups.Batch033.cellsNumeric401 MergedCutGroups.Batch033.populationMatches401
    PopulationCertificates.Batch013.valid267 PopulationCertificates.Batch013.sound267 WitnessCertificates.Batch013.valid267 WitnessCertificates.Batch013.sound267 CountingCertificates.Batch013.valid267 CountingCertificates.Batch013.sound267 H st hI
theorem probabilityBound133 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch033.certificate401).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate267).dm (WitnessCertificates.Batch013.certificate267).beta (WitnessCertificates.Batch013.certificate267).L) ≤ ((CutFailureCertificates.Budget013.certificate267).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound267 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate267).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch033.certificate401).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch013.certificate267).omega:ℝ)) ≤ ((CutFailureCertificates.Budget013.certificate267).bound:ℝ) at hb
  exact (exponentialBound133 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches134 : (MergedCutGroups.Batch033.certificate404).AnchorMatches CountingCertificates.Batch013.certificate269 := by decide +kernel
theorem exponentialBound134 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch033.certificate404).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate269).dm (WitnessCertificates.Batch013.certificate269).beta (WitnessCertificates.Batch013.certificate269).L) ≤ (2*exp (-((CountingCertificates.Batch013.certificate269).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch033.certificate404).exponent:ℝ)*st.R))/((WitnessCertificates.Batch013.certificate269).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch033.certificate404 CountingCertificates.Batch013.certificate269 matches134 MergedCutGroups.Batch033.numericValid404 MergedCutGroups.Batch033.cellsSound404 MergedCutGroups.Batch033.cellsNumeric404 MergedCutGroups.Batch033.populationMatches404
    PopulationCertificates.Batch013.valid269 PopulationCertificates.Batch013.sound269 WitnessCertificates.Batch013.valid269 WitnessCertificates.Batch013.sound269 CountingCertificates.Batch013.valid269 CountingCertificates.Batch013.sound269 H st hI
theorem probabilityBound134 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch033.certificate404).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate269).dm (WitnessCertificates.Batch013.certificate269).beta (WitnessCertificates.Batch013.certificate269).L) ≤ ((CutFailureCertificates.Budget013.certificate269).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound269 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate269).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch033.certificate404).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch013.certificate269).omega:ℝ)) ≤ ((CutFailureCertificates.Budget013.certificate269).bound:ℝ) at hb
  exact (exponentialBound134 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches135 : (MergedCutGroups.Batch033.certificate407).AnchorMatches CountingCertificates.Batch013.certificate271 := by decide +kernel
theorem exponentialBound135 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch033.certificate407).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate271).dm (WitnessCertificates.Batch013.certificate271).beta (WitnessCertificates.Batch013.certificate271).L) ≤ (2*exp (-((CountingCertificates.Batch013.certificate271).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch033.certificate407).exponent:ℝ)*st.R))/((WitnessCertificates.Batch013.certificate271).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch033.certificate407 CountingCertificates.Batch013.certificate271 matches135 MergedCutGroups.Batch033.numericValid407 MergedCutGroups.Batch033.cellsSound407 MergedCutGroups.Batch033.cellsNumeric407 MergedCutGroups.Batch033.populationMatches407
    PopulationCertificates.Batch013.valid271 PopulationCertificates.Batch013.sound271 WitnessCertificates.Batch013.valid271 WitnessCertificates.Batch013.sound271 CountingCertificates.Batch013.valid271 CountingCertificates.Batch013.sound271 H st hI
theorem probabilityBound135 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch033.certificate407).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate271).dm (WitnessCertificates.Batch013.certificate271).beta (WitnessCertificates.Batch013.certificate271).L) ≤ ((CutFailureCertificates.Budget013.certificate271).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound271 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate271).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch033.certificate407).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch013.certificate271).omega:ℝ)) ≤ ((CutFailureCertificates.Budget013.certificate271).bound:ℝ) at hb
  exact (exponentialBound135 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches136 : (MergedCutGroups.Batch034.certificate410).AnchorMatches CountingCertificates.Batch013.certificate273 := by decide +kernel
theorem exponentialBound136 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch034.certificate410).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate273).dm (WitnessCertificates.Batch013.certificate273).beta (WitnessCertificates.Batch013.certificate273).L) ≤ (2*exp (-((CountingCertificates.Batch013.certificate273).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch034.certificate410).exponent:ℝ)*st.R))/((WitnessCertificates.Batch013.certificate273).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch034.certificate410 CountingCertificates.Batch013.certificate273 matches136 MergedCutGroups.Batch034.numericValid410 MergedCutGroups.Batch034.cellsSound410 MergedCutGroups.Batch034.cellsNumeric410 MergedCutGroups.Batch034.populationMatches410
    PopulationCertificates.Batch013.valid273 PopulationCertificates.Batch013.sound273 WitnessCertificates.Batch013.valid273 WitnessCertificates.Batch013.sound273 CountingCertificates.Batch013.valid273 CountingCertificates.Batch013.sound273 H st hI
theorem probabilityBound136 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch034.certificate410).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate273).dm (WitnessCertificates.Batch013.certificate273).beta (WitnessCertificates.Batch013.certificate273).L) ≤ ((CutFailureCertificates.Budget013.certificate273).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound273 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate273).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch034.certificate410).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch013.certificate273).omega:ℝ)) ≤ ((CutFailureCertificates.Budget013.certificate273).bound:ℝ) at hb
  exact (exponentialBound136 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches137 : (MergedCutGroups.Batch034.certificate413).AnchorMatches CountingCertificates.Batch013.certificate275 := by decide +kernel
theorem exponentialBound137 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch034.certificate413).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate275).dm (WitnessCertificates.Batch013.certificate275).beta (WitnessCertificates.Batch013.certificate275).L) ≤ (2*exp (-((CountingCertificates.Batch013.certificate275).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch034.certificate413).exponent:ℝ)*st.R))/((WitnessCertificates.Batch013.certificate275).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch034.certificate413 CountingCertificates.Batch013.certificate275 matches137 MergedCutGroups.Batch034.numericValid413 MergedCutGroups.Batch034.cellsSound413 MergedCutGroups.Batch034.cellsNumeric413 MergedCutGroups.Batch034.populationMatches413
    PopulationCertificates.Batch013.valid275 PopulationCertificates.Batch013.sound275 WitnessCertificates.Batch013.valid275 WitnessCertificates.Batch013.sound275 CountingCertificates.Batch013.valid275 CountingCertificates.Batch013.sound275 H st hI
theorem probabilityBound137 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch034.certificate413).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate275).dm (WitnessCertificates.Batch013.certificate275).beta (WitnessCertificates.Batch013.certificate275).L) ≤ ((CutFailureCertificates.Budget013.certificate275).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound275 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate275).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch034.certificate413).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch013.certificate275).omega:ℝ)) ≤ ((CutFailureCertificates.Budget013.certificate275).bound:ℝ) at hb
  exact (exponentialBound137 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches138 : (MergedCutGroups.Batch034.certificate416).AnchorMatches CountingCertificates.Batch013.certificate277 := by decide +kernel
theorem exponentialBound138 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch034.certificate416).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate277).dm (WitnessCertificates.Batch013.certificate277).beta (WitnessCertificates.Batch013.certificate277).L) ≤ (2*exp (-((CountingCertificates.Batch013.certificate277).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch034.certificate416).exponent:ℝ)*st.R))/((WitnessCertificates.Batch013.certificate277).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch034.certificate416 CountingCertificates.Batch013.certificate277 matches138 MergedCutGroups.Batch034.numericValid416 MergedCutGroups.Batch034.cellsSound416 MergedCutGroups.Batch034.cellsNumeric416 MergedCutGroups.Batch034.populationMatches416
    PopulationCertificates.Batch013.valid277 PopulationCertificates.Batch013.sound277 WitnessCertificates.Batch013.valid277 WitnessCertificates.Batch013.sound277 CountingCertificates.Batch013.valid277 CountingCertificates.Batch013.sound277 H st hI
theorem probabilityBound138 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch034.certificate416).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate277).dm (WitnessCertificates.Batch013.certificate277).beta (WitnessCertificates.Batch013.certificate277).L) ≤ ((CutFailureCertificates.Budget013.certificate277).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound277 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate277).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch034.certificate416).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch013.certificate277).omega:ℝ)) ≤ ((CutFailureCertificates.Budget013.certificate277).bound:ℝ) at hb
  exact (exponentialBound138 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches139 : (MergedCutGroups.Batch034.certificate419).AnchorMatches CountingCertificates.Batch013.certificate279 := by decide +kernel
theorem exponentialBound139 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch034.certificate419).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate279).dm (WitnessCertificates.Batch013.certificate279).beta (WitnessCertificates.Batch013.certificate279).L) ≤ (2*exp (-((CountingCertificates.Batch013.certificate279).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch034.certificate419).exponent:ℝ)*st.R))/((WitnessCertificates.Batch013.certificate279).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch034.certificate419 CountingCertificates.Batch013.certificate279 matches139 MergedCutGroups.Batch034.numericValid419 MergedCutGroups.Batch034.cellsSound419 MergedCutGroups.Batch034.cellsNumeric419 MergedCutGroups.Batch034.populationMatches419
    PopulationCertificates.Batch013.valid279 PopulationCertificates.Batch013.sound279 WitnessCertificates.Batch013.valid279 WitnessCertificates.Batch013.sound279 CountingCertificates.Batch013.valid279 CountingCertificates.Batch013.sound279 H st hI
theorem probabilityBound139 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch034.certificate419).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch013.certificate279).dm (WitnessCertificates.Batch013.certificate279).beta (WitnessCertificates.Batch013.certificate279).L) ≤ ((CutFailureCertificates.Budget013.certificate279).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget013.sound279 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch013.certificate279).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch034.certificate419).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch013.certificate279).omega:ℝ)) ≤ ((CutFailureCertificates.Budget013.certificate279).bound:ℝ) at hb
  exact (exponentialBound139 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch006
