import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch016
import Cycle12.CountingCertificates.Batch017
import Cycle12.CutFailureCertificates.Budget016
import Cycle12.CutFailureCertificates.Budget017
import Cycle12.MergedCutGroups.Batch040
import Cycle12.MergedCutGroups.Batch041
import Cycle12.MergedCutGroups.Batch042
import Cycle12.MergedCutGroups.Batch043
import Cycle12.MergedCutGroups.Batch044
import Cycle12.PopulationCertificates.Batch016
import Cycle12.PopulationCertificates.Batch017
import Cycle12.WitnessCertificates.Batch016
import Cycle12.WitnessCertificates.Batch017

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedAnchorFailures.Batch008
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches160 : (MergedCutGroups.Batch040.certificate482).AnchorMatches CountingCertificates.Batch016.certificate321 := by decide +kernel
theorem exponentialBound160 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch040.certificate482).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate321).dm (WitnessCertificates.Batch016.certificate321).beta (WitnessCertificates.Batch016.certificate321).L) ≤ (2*exp (-((CountingCertificates.Batch016.certificate321).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch040.certificate482).exponent:ℝ)*st.R))/((WitnessCertificates.Batch016.certificate321).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch040.certificate482 CountingCertificates.Batch016.certificate321 matches160 MergedCutGroups.Batch040.numericValid482 MergedCutGroups.Batch040.cellsSound482 MergedCutGroups.Batch040.cellsNumeric482 MergedCutGroups.Batch040.populationMatches482
    PopulationCertificates.Batch016.valid321 PopulationCertificates.Batch016.sound321 WitnessCertificates.Batch016.valid321 WitnessCertificates.Batch016.sound321 CountingCertificates.Batch016.valid321 CountingCertificates.Batch016.sound321 H st hI
theorem probabilityBound160 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch040.certificate482).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate321).dm (WitnessCertificates.Batch016.certificate321).beta (WitnessCertificates.Batch016.certificate321).L) ≤ ((CutFailureCertificates.Budget016.certificate321).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound321 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate321).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch040.certificate482).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch016.certificate321).omega:ℝ)) ≤ ((CutFailureCertificates.Budget016.certificate321).bound:ℝ) at hb
  exact (exponentialBound160 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches161 : (MergedCutGroups.Batch040.certificate485).AnchorMatches CountingCertificates.Batch016.certificate323 := by decide +kernel
theorem exponentialBound161 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch040.certificate485).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate323).dm (WitnessCertificates.Batch016.certificate323).beta (WitnessCertificates.Batch016.certificate323).L) ≤ (2*exp (-((CountingCertificates.Batch016.certificate323).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch040.certificate485).exponent:ℝ)*st.R))/((WitnessCertificates.Batch016.certificate323).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch040.certificate485 CountingCertificates.Batch016.certificate323 matches161 MergedCutGroups.Batch040.numericValid485 MergedCutGroups.Batch040.cellsSound485 MergedCutGroups.Batch040.cellsNumeric485 MergedCutGroups.Batch040.populationMatches485
    PopulationCertificates.Batch016.valid323 PopulationCertificates.Batch016.sound323 WitnessCertificates.Batch016.valid323 WitnessCertificates.Batch016.sound323 CountingCertificates.Batch016.valid323 CountingCertificates.Batch016.sound323 H st hI
theorem probabilityBound161 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch040.certificate485).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate323).dm (WitnessCertificates.Batch016.certificate323).beta (WitnessCertificates.Batch016.certificate323).L) ≤ ((CutFailureCertificates.Budget016.certificate323).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound323 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate323).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch040.certificate485).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch016.certificate323).omega:ℝ)) ≤ ((CutFailureCertificates.Budget016.certificate323).bound:ℝ) at hb
  exact (exponentialBound161 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches162 : (MergedCutGroups.Batch040.certificate488).AnchorMatches CountingCertificates.Batch016.certificate325 := by decide +kernel
theorem exponentialBound162 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch040.certificate488).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate325).dm (WitnessCertificates.Batch016.certificate325).beta (WitnessCertificates.Batch016.certificate325).L) ≤ (2*exp (-((CountingCertificates.Batch016.certificate325).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch040.certificate488).exponent:ℝ)*st.R))/((WitnessCertificates.Batch016.certificate325).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch040.certificate488 CountingCertificates.Batch016.certificate325 matches162 MergedCutGroups.Batch040.numericValid488 MergedCutGroups.Batch040.cellsSound488 MergedCutGroups.Batch040.cellsNumeric488 MergedCutGroups.Batch040.populationMatches488
    PopulationCertificates.Batch016.valid325 PopulationCertificates.Batch016.sound325 WitnessCertificates.Batch016.valid325 WitnessCertificates.Batch016.sound325 CountingCertificates.Batch016.valid325 CountingCertificates.Batch016.sound325 H st hI
theorem probabilityBound162 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch040.certificate488).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate325).dm (WitnessCertificates.Batch016.certificate325).beta (WitnessCertificates.Batch016.certificate325).L) ≤ ((CutFailureCertificates.Budget016.certificate325).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound325 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate325).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch040.certificate488).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch016.certificate325).omega:ℝ)) ≤ ((CutFailureCertificates.Budget016.certificate325).bound:ℝ) at hb
  exact (exponentialBound162 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches163 : (MergedCutGroups.Batch040.certificate491).AnchorMatches CountingCertificates.Batch016.certificate327 := by decide +kernel
theorem exponentialBound163 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch040.certificate491).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate327).dm (WitnessCertificates.Batch016.certificate327).beta (WitnessCertificates.Batch016.certificate327).L) ≤ (2*exp (-((CountingCertificates.Batch016.certificate327).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch040.certificate491).exponent:ℝ)*st.R))/((WitnessCertificates.Batch016.certificate327).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch040.certificate491 CountingCertificates.Batch016.certificate327 matches163 MergedCutGroups.Batch040.numericValid491 MergedCutGroups.Batch040.cellsSound491 MergedCutGroups.Batch040.cellsNumeric491 MergedCutGroups.Batch040.populationMatches491
    PopulationCertificates.Batch016.valid327 PopulationCertificates.Batch016.sound327 WitnessCertificates.Batch016.valid327 WitnessCertificates.Batch016.sound327 CountingCertificates.Batch016.valid327 CountingCertificates.Batch016.sound327 H st hI
theorem probabilityBound163 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch040.certificate491).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate327).dm (WitnessCertificates.Batch016.certificate327).beta (WitnessCertificates.Batch016.certificate327).L) ≤ ((CutFailureCertificates.Budget016.certificate327).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound327 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate327).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch040.certificate491).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch016.certificate327).omega:ℝ)) ≤ ((CutFailureCertificates.Budget016.certificate327).bound:ℝ) at hb
  exact (exponentialBound163 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches164 : (MergedCutGroups.Batch041.certificate494).AnchorMatches CountingCertificates.Batch016.certificate329 := by decide +kernel
theorem exponentialBound164 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch041.certificate494).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate329).dm (WitnessCertificates.Batch016.certificate329).beta (WitnessCertificates.Batch016.certificate329).L) ≤ (2*exp (-((CountingCertificates.Batch016.certificate329).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch041.certificate494).exponent:ℝ)*st.R))/((WitnessCertificates.Batch016.certificate329).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch041.certificate494 CountingCertificates.Batch016.certificate329 matches164 MergedCutGroups.Batch041.numericValid494 MergedCutGroups.Batch041.cellsSound494 MergedCutGroups.Batch041.cellsNumeric494 MergedCutGroups.Batch041.populationMatches494
    PopulationCertificates.Batch016.valid329 PopulationCertificates.Batch016.sound329 WitnessCertificates.Batch016.valid329 WitnessCertificates.Batch016.sound329 CountingCertificates.Batch016.valid329 CountingCertificates.Batch016.sound329 H st hI
theorem probabilityBound164 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch041.certificate494).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate329).dm (WitnessCertificates.Batch016.certificate329).beta (WitnessCertificates.Batch016.certificate329).L) ≤ ((CutFailureCertificates.Budget016.certificate329).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound329 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate329).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch041.certificate494).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch016.certificate329).omega:ℝ)) ≤ ((CutFailureCertificates.Budget016.certificate329).bound:ℝ) at hb
  exact (exponentialBound164 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches165 : (MergedCutGroups.Batch041.certificate497).AnchorMatches CountingCertificates.Batch016.certificate331 := by decide +kernel
theorem exponentialBound165 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch041.certificate497).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate331).dm (WitnessCertificates.Batch016.certificate331).beta (WitnessCertificates.Batch016.certificate331).L) ≤ (2*exp (-((CountingCertificates.Batch016.certificate331).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch041.certificate497).exponent:ℝ)*st.R))/((WitnessCertificates.Batch016.certificate331).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch041.certificate497 CountingCertificates.Batch016.certificate331 matches165 MergedCutGroups.Batch041.numericValid497 MergedCutGroups.Batch041.cellsSound497 MergedCutGroups.Batch041.cellsNumeric497 MergedCutGroups.Batch041.populationMatches497
    PopulationCertificates.Batch016.valid331 PopulationCertificates.Batch016.sound331 WitnessCertificates.Batch016.valid331 WitnessCertificates.Batch016.sound331 CountingCertificates.Batch016.valid331 CountingCertificates.Batch016.sound331 H st hI
theorem probabilityBound165 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch041.certificate497).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate331).dm (WitnessCertificates.Batch016.certificate331).beta (WitnessCertificates.Batch016.certificate331).L) ≤ ((CutFailureCertificates.Budget016.certificate331).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound331 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate331).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch041.certificate497).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch016.certificate331).omega:ℝ)) ≤ ((CutFailureCertificates.Budget016.certificate331).bound:ℝ) at hb
  exact (exponentialBound165 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches166 : (MergedCutGroups.Batch041.certificate500).AnchorMatches CountingCertificates.Batch016.certificate333 := by decide +kernel
theorem exponentialBound166 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch041.certificate500).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate333).dm (WitnessCertificates.Batch016.certificate333).beta (WitnessCertificates.Batch016.certificate333).L) ≤ (2*exp (-((CountingCertificates.Batch016.certificate333).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch041.certificate500).exponent:ℝ)*st.R))/((WitnessCertificates.Batch016.certificate333).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch041.certificate500 CountingCertificates.Batch016.certificate333 matches166 MergedCutGroups.Batch041.numericValid500 MergedCutGroups.Batch041.cellsSound500 MergedCutGroups.Batch041.cellsNumeric500 MergedCutGroups.Batch041.populationMatches500
    PopulationCertificates.Batch016.valid333 PopulationCertificates.Batch016.sound333 WitnessCertificates.Batch016.valid333 WitnessCertificates.Batch016.sound333 CountingCertificates.Batch016.valid333 CountingCertificates.Batch016.sound333 H st hI
theorem probabilityBound166 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch041.certificate500).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate333).dm (WitnessCertificates.Batch016.certificate333).beta (WitnessCertificates.Batch016.certificate333).L) ≤ ((CutFailureCertificates.Budget016.certificate333).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound333 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate333).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch041.certificate500).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch016.certificate333).omega:ℝ)) ≤ ((CutFailureCertificates.Budget016.certificate333).bound:ℝ) at hb
  exact (exponentialBound166 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches167 : (MergedCutGroups.Batch041.certificate503).AnchorMatches CountingCertificates.Batch016.certificate335 := by decide +kernel
theorem exponentialBound167 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch041.certificate503).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate335).dm (WitnessCertificates.Batch016.certificate335).beta (WitnessCertificates.Batch016.certificate335).L) ≤ (2*exp (-((CountingCertificates.Batch016.certificate335).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch041.certificate503).exponent:ℝ)*st.R))/((WitnessCertificates.Batch016.certificate335).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch041.certificate503 CountingCertificates.Batch016.certificate335 matches167 MergedCutGroups.Batch041.numericValid503 MergedCutGroups.Batch041.cellsSound503 MergedCutGroups.Batch041.cellsNumeric503 MergedCutGroups.Batch041.populationMatches503
    PopulationCertificates.Batch016.valid335 PopulationCertificates.Batch016.sound335 WitnessCertificates.Batch016.valid335 WitnessCertificates.Batch016.sound335 CountingCertificates.Batch016.valid335 CountingCertificates.Batch016.sound335 H st hI
theorem probabilityBound167 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch041.certificate503).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate335).dm (WitnessCertificates.Batch016.certificate335).beta (WitnessCertificates.Batch016.certificate335).L) ≤ ((CutFailureCertificates.Budget016.certificate335).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound335 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate335).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch041.certificate503).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch016.certificate335).omega:ℝ)) ≤ ((CutFailureCertificates.Budget016.certificate335).bound:ℝ) at hb
  exact (exponentialBound167 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches168 : (MergedCutGroups.Batch042.certificate506).AnchorMatches CountingCertificates.Batch016.certificate337 := by decide +kernel
theorem exponentialBound168 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch042.certificate506).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate337).dm (WitnessCertificates.Batch016.certificate337).beta (WitnessCertificates.Batch016.certificate337).L) ≤ (2*exp (-((CountingCertificates.Batch016.certificate337).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch042.certificate506).exponent:ℝ)*st.R))/((WitnessCertificates.Batch016.certificate337).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch042.certificate506 CountingCertificates.Batch016.certificate337 matches168 MergedCutGroups.Batch042.numericValid506 MergedCutGroups.Batch042.cellsSound506 MergedCutGroups.Batch042.cellsNumeric506 MergedCutGroups.Batch042.populationMatches506
    PopulationCertificates.Batch016.valid337 PopulationCertificates.Batch016.sound337 WitnessCertificates.Batch016.valid337 WitnessCertificates.Batch016.sound337 CountingCertificates.Batch016.valid337 CountingCertificates.Batch016.sound337 H st hI
theorem probabilityBound168 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch042.certificate506).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate337).dm (WitnessCertificates.Batch016.certificate337).beta (WitnessCertificates.Batch016.certificate337).L) ≤ ((CutFailureCertificates.Budget016.certificate337).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound337 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate337).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch042.certificate506).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch016.certificate337).omega:ℝ)) ≤ ((CutFailureCertificates.Budget016.certificate337).bound:ℝ) at hb
  exact (exponentialBound168 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches169 : (MergedCutGroups.Batch042.certificate509).AnchorMatches CountingCertificates.Batch016.certificate339 := by decide +kernel
theorem exponentialBound169 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch042.certificate509).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate339).dm (WitnessCertificates.Batch016.certificate339).beta (WitnessCertificates.Batch016.certificate339).L) ≤ (2*exp (-((CountingCertificates.Batch016.certificate339).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch042.certificate509).exponent:ℝ)*st.R))/((WitnessCertificates.Batch016.certificate339).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch042.certificate509 CountingCertificates.Batch016.certificate339 matches169 MergedCutGroups.Batch042.numericValid509 MergedCutGroups.Batch042.cellsSound509 MergedCutGroups.Batch042.cellsNumeric509 MergedCutGroups.Batch042.populationMatches509
    PopulationCertificates.Batch016.valid339 PopulationCertificates.Batch016.sound339 WitnessCertificates.Batch016.valid339 WitnessCertificates.Batch016.sound339 CountingCertificates.Batch016.valid339 CountingCertificates.Batch016.sound339 H st hI
theorem probabilityBound169 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch042.certificate509).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch016.certificate339).dm (WitnessCertificates.Batch016.certificate339).beta (WitnessCertificates.Batch016.certificate339).L) ≤ ((CutFailureCertificates.Budget016.certificate339).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget016.sound339 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch016.certificate339).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch042.certificate509).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch016.certificate339).omega:ℝ)) ≤ ((CutFailureCertificates.Budget016.certificate339).bound:ℝ) at hb
  exact (exponentialBound169 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches170 : (MergedCutGroups.Batch042.certificate512).AnchorMatches CountingCertificates.Batch017.certificate341 := by decide +kernel
theorem exponentialBound170 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch042.certificate512).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate341).dm (WitnessCertificates.Batch017.certificate341).beta (WitnessCertificates.Batch017.certificate341).L) ≤ (2*exp (-((CountingCertificates.Batch017.certificate341).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch042.certificate512).exponent:ℝ)*st.R))/((WitnessCertificates.Batch017.certificate341).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch042.certificate512 CountingCertificates.Batch017.certificate341 matches170 MergedCutGroups.Batch042.numericValid512 MergedCutGroups.Batch042.cellsSound512 MergedCutGroups.Batch042.cellsNumeric512 MergedCutGroups.Batch042.populationMatches512
    PopulationCertificates.Batch017.valid341 PopulationCertificates.Batch017.sound341 WitnessCertificates.Batch017.valid341 WitnessCertificates.Batch017.sound341 CountingCertificates.Batch017.valid341 CountingCertificates.Batch017.sound341 H st hI
theorem probabilityBound170 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch042.certificate512).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate341).dm (WitnessCertificates.Batch017.certificate341).beta (WitnessCertificates.Batch017.certificate341).L) ≤ ((CutFailureCertificates.Budget017.certificate341).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound341 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate341).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch042.certificate512).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch017.certificate341).omega:ℝ)) ≤ ((CutFailureCertificates.Budget017.certificate341).bound:ℝ) at hb
  exact (exponentialBound170 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches171 : (MergedCutGroups.Batch042.certificate515).AnchorMatches CountingCertificates.Batch017.certificate343 := by decide +kernel
theorem exponentialBound171 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch042.certificate515).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate343).dm (WitnessCertificates.Batch017.certificate343).beta (WitnessCertificates.Batch017.certificate343).L) ≤ (2*exp (-((CountingCertificates.Batch017.certificate343).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch042.certificate515).exponent:ℝ)*st.R))/((WitnessCertificates.Batch017.certificate343).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch042.certificate515 CountingCertificates.Batch017.certificate343 matches171 MergedCutGroups.Batch042.numericValid515 MergedCutGroups.Batch042.cellsSound515 MergedCutGroups.Batch042.cellsNumeric515 MergedCutGroups.Batch042.populationMatches515
    PopulationCertificates.Batch017.valid343 PopulationCertificates.Batch017.sound343 WitnessCertificates.Batch017.valid343 WitnessCertificates.Batch017.sound343 CountingCertificates.Batch017.valid343 CountingCertificates.Batch017.sound343 H st hI
theorem probabilityBound171 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch042.certificate515).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate343).dm (WitnessCertificates.Batch017.certificate343).beta (WitnessCertificates.Batch017.certificate343).L) ≤ ((CutFailureCertificates.Budget017.certificate343).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound343 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate343).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch042.certificate515).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch017.certificate343).omega:ℝ)) ≤ ((CutFailureCertificates.Budget017.certificate343).bound:ℝ) at hb
  exact (exponentialBound171 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches172 : (MergedCutGroups.Batch043.certificate518).AnchorMatches CountingCertificates.Batch017.certificate345 := by decide +kernel
theorem exponentialBound172 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch043.certificate518).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate345).dm (WitnessCertificates.Batch017.certificate345).beta (WitnessCertificates.Batch017.certificate345).L) ≤ (2*exp (-((CountingCertificates.Batch017.certificate345).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch043.certificate518).exponent:ℝ)*st.R))/((WitnessCertificates.Batch017.certificate345).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch043.certificate518 CountingCertificates.Batch017.certificate345 matches172 MergedCutGroups.Batch043.numericValid518 MergedCutGroups.Batch043.cellsSound518 MergedCutGroups.Batch043.cellsNumeric518 MergedCutGroups.Batch043.populationMatches518
    PopulationCertificates.Batch017.valid345 PopulationCertificates.Batch017.sound345 WitnessCertificates.Batch017.valid345 WitnessCertificates.Batch017.sound345 CountingCertificates.Batch017.valid345 CountingCertificates.Batch017.sound345 H st hI
theorem probabilityBound172 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch043.certificate518).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate345).dm (WitnessCertificates.Batch017.certificate345).beta (WitnessCertificates.Batch017.certificate345).L) ≤ ((CutFailureCertificates.Budget017.certificate345).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound345 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate345).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch043.certificate518).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch017.certificate345).omega:ℝ)) ≤ ((CutFailureCertificates.Budget017.certificate345).bound:ℝ) at hb
  exact (exponentialBound172 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches173 : (MergedCutGroups.Batch043.certificate521).AnchorMatches CountingCertificates.Batch017.certificate347 := by decide +kernel
theorem exponentialBound173 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch043.certificate521).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate347).dm (WitnessCertificates.Batch017.certificate347).beta (WitnessCertificates.Batch017.certificate347).L) ≤ (2*exp (-((CountingCertificates.Batch017.certificate347).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch043.certificate521).exponent:ℝ)*st.R))/((WitnessCertificates.Batch017.certificate347).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch043.certificate521 CountingCertificates.Batch017.certificate347 matches173 MergedCutGroups.Batch043.numericValid521 MergedCutGroups.Batch043.cellsSound521 MergedCutGroups.Batch043.cellsNumeric521 MergedCutGroups.Batch043.populationMatches521
    PopulationCertificates.Batch017.valid347 PopulationCertificates.Batch017.sound347 WitnessCertificates.Batch017.valid347 WitnessCertificates.Batch017.sound347 CountingCertificates.Batch017.valid347 CountingCertificates.Batch017.sound347 H st hI
theorem probabilityBound173 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch043.certificate521).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate347).dm (WitnessCertificates.Batch017.certificate347).beta (WitnessCertificates.Batch017.certificate347).L) ≤ ((CutFailureCertificates.Budget017.certificate347).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound347 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate347).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch043.certificate521).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch017.certificate347).omega:ℝ)) ≤ ((CutFailureCertificates.Budget017.certificate347).bound:ℝ) at hb
  exact (exponentialBound173 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches174 : (MergedCutGroups.Batch043.certificate524).AnchorMatches CountingCertificates.Batch017.certificate349 := by decide +kernel
theorem exponentialBound174 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch043.certificate524).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate349).dm (WitnessCertificates.Batch017.certificate349).beta (WitnessCertificates.Batch017.certificate349).L) ≤ (2*exp (-((CountingCertificates.Batch017.certificate349).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch043.certificate524).exponent:ℝ)*st.R))/((WitnessCertificates.Batch017.certificate349).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch043.certificate524 CountingCertificates.Batch017.certificate349 matches174 MergedCutGroups.Batch043.numericValid524 MergedCutGroups.Batch043.cellsSound524 MergedCutGroups.Batch043.cellsNumeric524 MergedCutGroups.Batch043.populationMatches524
    PopulationCertificates.Batch017.valid349 PopulationCertificates.Batch017.sound349 WitnessCertificates.Batch017.valid349 WitnessCertificates.Batch017.sound349 CountingCertificates.Batch017.valid349 CountingCertificates.Batch017.sound349 H st hI
theorem probabilityBound174 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch043.certificate524).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate349).dm (WitnessCertificates.Batch017.certificate349).beta (WitnessCertificates.Batch017.certificate349).L) ≤ ((CutFailureCertificates.Budget017.certificate349).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound349 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate349).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch043.certificate524).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch017.certificate349).omega:ℝ)) ≤ ((CutFailureCertificates.Budget017.certificate349).bound:ℝ) at hb
  exact (exponentialBound174 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches175 : (MergedCutGroups.Batch043.certificate527).AnchorMatches CountingCertificates.Batch017.certificate351 := by decide +kernel
theorem exponentialBound175 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch043.certificate527).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate351).dm (WitnessCertificates.Batch017.certificate351).beta (WitnessCertificates.Batch017.certificate351).L) ≤ (2*exp (-((CountingCertificates.Batch017.certificate351).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch043.certificate527).exponent:ℝ)*st.R))/((WitnessCertificates.Batch017.certificate351).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch043.certificate527 CountingCertificates.Batch017.certificate351 matches175 MergedCutGroups.Batch043.numericValid527 MergedCutGroups.Batch043.cellsSound527 MergedCutGroups.Batch043.cellsNumeric527 MergedCutGroups.Batch043.populationMatches527
    PopulationCertificates.Batch017.valid351 PopulationCertificates.Batch017.sound351 WitnessCertificates.Batch017.valid351 WitnessCertificates.Batch017.sound351 CountingCertificates.Batch017.valid351 CountingCertificates.Batch017.sound351 H st hI
theorem probabilityBound175 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch043.certificate527).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate351).dm (WitnessCertificates.Batch017.certificate351).beta (WitnessCertificates.Batch017.certificate351).L) ≤ ((CutFailureCertificates.Budget017.certificate351).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound351 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate351).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch043.certificate527).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch017.certificate351).omega:ℝ)) ≤ ((CutFailureCertificates.Budget017.certificate351).bound:ℝ) at hb
  exact (exponentialBound175 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches176 : (MergedCutGroups.Batch044.certificate530).AnchorMatches CountingCertificates.Batch017.certificate353 := by decide +kernel
theorem exponentialBound176 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch044.certificate530).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate353).dm (WitnessCertificates.Batch017.certificate353).beta (WitnessCertificates.Batch017.certificate353).L) ≤ (2*exp (-((CountingCertificates.Batch017.certificate353).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch044.certificate530).exponent:ℝ)*st.R))/((WitnessCertificates.Batch017.certificate353).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch044.certificate530 CountingCertificates.Batch017.certificate353 matches176 MergedCutGroups.Batch044.numericValid530 MergedCutGroups.Batch044.cellsSound530 MergedCutGroups.Batch044.cellsNumeric530 MergedCutGroups.Batch044.populationMatches530
    PopulationCertificates.Batch017.valid353 PopulationCertificates.Batch017.sound353 WitnessCertificates.Batch017.valid353 WitnessCertificates.Batch017.sound353 CountingCertificates.Batch017.valid353 CountingCertificates.Batch017.sound353 H st hI
theorem probabilityBound176 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch044.certificate530).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate353).dm (WitnessCertificates.Batch017.certificate353).beta (WitnessCertificates.Batch017.certificate353).L) ≤ ((CutFailureCertificates.Budget017.certificate353).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound353 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate353).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch044.certificate530).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch017.certificate353).omega:ℝ)) ≤ ((CutFailureCertificates.Budget017.certificate353).bound:ℝ) at hb
  exact (exponentialBound176 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches177 : (MergedCutGroups.Batch044.certificate533).AnchorMatches CountingCertificates.Batch017.certificate355 := by decide +kernel
theorem exponentialBound177 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch044.certificate533).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate355).dm (WitnessCertificates.Batch017.certificate355).beta (WitnessCertificates.Batch017.certificate355).L) ≤ (2*exp (-((CountingCertificates.Batch017.certificate355).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch044.certificate533).exponent:ℝ)*st.R))/((WitnessCertificates.Batch017.certificate355).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch044.certificate533 CountingCertificates.Batch017.certificate355 matches177 MergedCutGroups.Batch044.numericValid533 MergedCutGroups.Batch044.cellsSound533 MergedCutGroups.Batch044.cellsNumeric533 MergedCutGroups.Batch044.populationMatches533
    PopulationCertificates.Batch017.valid355 PopulationCertificates.Batch017.sound355 WitnessCertificates.Batch017.valid355 WitnessCertificates.Batch017.sound355 CountingCertificates.Batch017.valid355 CountingCertificates.Batch017.sound355 H st hI
theorem probabilityBound177 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch044.certificate533).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate355).dm (WitnessCertificates.Batch017.certificate355).beta (WitnessCertificates.Batch017.certificate355).L) ≤ ((CutFailureCertificates.Budget017.certificate355).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound355 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate355).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch044.certificate533).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch017.certificate355).omega:ℝ)) ≤ ((CutFailureCertificates.Budget017.certificate355).bound:ℝ) at hb
  exact (exponentialBound177 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches178 : (MergedCutGroups.Batch044.certificate536).AnchorMatches CountingCertificates.Batch017.certificate357 := by decide +kernel
theorem exponentialBound178 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch044.certificate536).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate357).dm (WitnessCertificates.Batch017.certificate357).beta (WitnessCertificates.Batch017.certificate357).L) ≤ (2*exp (-((CountingCertificates.Batch017.certificate357).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch044.certificate536).exponent:ℝ)*st.R))/((WitnessCertificates.Batch017.certificate357).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch044.certificate536 CountingCertificates.Batch017.certificate357 matches178 MergedCutGroups.Batch044.numericValid536 MergedCutGroups.Batch044.cellsSound536 MergedCutGroups.Batch044.cellsNumeric536 MergedCutGroups.Batch044.populationMatches536
    PopulationCertificates.Batch017.valid357 PopulationCertificates.Batch017.sound357 WitnessCertificates.Batch017.valid357 WitnessCertificates.Batch017.sound357 CountingCertificates.Batch017.valid357 CountingCertificates.Batch017.sound357 H st hI
theorem probabilityBound178 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch044.certificate536).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate357).dm (WitnessCertificates.Batch017.certificate357).beta (WitnessCertificates.Batch017.certificate357).L) ≤ ((CutFailureCertificates.Budget017.certificate357).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound357 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate357).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch044.certificate536).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch017.certificate357).omega:ℝ)) ≤ ((CutFailureCertificates.Budget017.certificate357).bound:ℝ) at hb
  exact (exponentialBound178 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches179 : (MergedCutGroups.Batch044.certificate539).AnchorMatches CountingCertificates.Batch017.certificate359 := by decide +kernel
theorem exponentialBound179 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch044.certificate539).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate359).dm (WitnessCertificates.Batch017.certificate359).beta (WitnessCertificates.Batch017.certificate359).L) ≤ (2*exp (-((CountingCertificates.Batch017.certificate359).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch044.certificate539).exponent:ℝ)*st.R))/((WitnessCertificates.Batch017.certificate359).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch044.certificate539 CountingCertificates.Batch017.certificate359 matches179 MergedCutGroups.Batch044.numericValid539 MergedCutGroups.Batch044.cellsSound539 MergedCutGroups.Batch044.cellsNumeric539 MergedCutGroups.Batch044.populationMatches539
    PopulationCertificates.Batch017.valid359 PopulationCertificates.Batch017.sound359 WitnessCertificates.Batch017.valid359 WitnessCertificates.Batch017.sound359 CountingCertificates.Batch017.valid359 CountingCertificates.Batch017.sound359 H st hI
theorem probabilityBound179 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch044.certificate539).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch017.certificate359).dm (WitnessCertificates.Batch017.certificate359).beta (WitnessCertificates.Batch017.certificate359).L) ≤ ((CutFailureCertificates.Budget017.certificate359).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget017.sound359 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch017.certificate359).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch044.certificate539).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch017.certificate359).omega:ℝ)) ≤ ((CutFailureCertificates.Budget017.certificate359).bound:ℝ) at hb
  exact (exponentialBound179 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch008
