import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch020
import Cycle12.CountingCertificates.Batch021
import Cycle12.CutFailureCertificates.Budget020
import Cycle12.CutFailureCertificates.Budget021
import Cycle12.MergedCutGroups.Batch050
import Cycle12.MergedCutGroups.Batch051
import Cycle12.MergedCutGroups.Batch052
import Cycle12.MergedCutGroups.Batch053
import Cycle12.MergedCutGroups.Batch054
import Cycle12.PopulationCertificates.Batch020
import Cycle12.PopulationCertificates.Batch021
import Cycle12.WitnessCertificates.Batch020
import Cycle12.WitnessCertificates.Batch021

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedAnchorFailures.Batch010
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches200 : (MergedCutGroups.Batch050.certificate602).AnchorMatches CountingCertificates.Batch020.certificate401 := by decide +kernel
theorem exponentialBound200 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch050.certificate602).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate401).dm (WitnessCertificates.Batch020.certificate401).beta (WitnessCertificates.Batch020.certificate401).L) ≤ (2*exp (-((CountingCertificates.Batch020.certificate401).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch050.certificate602).exponent:ℝ)*st.R))/((WitnessCertificates.Batch020.certificate401).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch050.certificate602 CountingCertificates.Batch020.certificate401 matches200 MergedCutGroups.Batch050.numericValid602 MergedCutGroups.Batch050.cellsSound602 MergedCutGroups.Batch050.cellsNumeric602 MergedCutGroups.Batch050.populationMatches602
    PopulationCertificates.Batch020.valid401 PopulationCertificates.Batch020.sound401 WitnessCertificates.Batch020.valid401 WitnessCertificates.Batch020.sound401 CountingCertificates.Batch020.valid401 CountingCertificates.Batch020.sound401 H st hI
theorem probabilityBound200 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch050.certificate602).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate401).dm (WitnessCertificates.Batch020.certificate401).beta (WitnessCertificates.Batch020.certificate401).L) ≤ ((CutFailureCertificates.Budget020.certificate401).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound401 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate401).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch050.certificate602).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch020.certificate401).omega:ℝ)) ≤ ((CutFailureCertificates.Budget020.certificate401).bound:ℝ) at hb
  exact (exponentialBound200 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches201 : (MergedCutGroups.Batch050.certificate605).AnchorMatches CountingCertificates.Batch020.certificate403 := by decide +kernel
theorem exponentialBound201 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch050.certificate605).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate403).dm (WitnessCertificates.Batch020.certificate403).beta (WitnessCertificates.Batch020.certificate403).L) ≤ (2*exp (-((CountingCertificates.Batch020.certificate403).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch050.certificate605).exponent:ℝ)*st.R))/((WitnessCertificates.Batch020.certificate403).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch050.certificate605 CountingCertificates.Batch020.certificate403 matches201 MergedCutGroups.Batch050.numericValid605 MergedCutGroups.Batch050.cellsSound605 MergedCutGroups.Batch050.cellsNumeric605 MergedCutGroups.Batch050.populationMatches605
    PopulationCertificates.Batch020.valid403 PopulationCertificates.Batch020.sound403 WitnessCertificates.Batch020.valid403 WitnessCertificates.Batch020.sound403 CountingCertificates.Batch020.valid403 CountingCertificates.Batch020.sound403 H st hI
theorem probabilityBound201 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch050.certificate605).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate403).dm (WitnessCertificates.Batch020.certificate403).beta (WitnessCertificates.Batch020.certificate403).L) ≤ ((CutFailureCertificates.Budget020.certificate403).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound403 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate403).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch050.certificate605).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch020.certificate403).omega:ℝ)) ≤ ((CutFailureCertificates.Budget020.certificate403).bound:ℝ) at hb
  exact (exponentialBound201 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches202 : (MergedCutGroups.Batch050.certificate608).AnchorMatches CountingCertificates.Batch020.certificate405 := by decide +kernel
theorem exponentialBound202 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch050.certificate608).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate405).dm (WitnessCertificates.Batch020.certificate405).beta (WitnessCertificates.Batch020.certificate405).L) ≤ (2*exp (-((CountingCertificates.Batch020.certificate405).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch050.certificate608).exponent:ℝ)*st.R))/((WitnessCertificates.Batch020.certificate405).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch050.certificate608 CountingCertificates.Batch020.certificate405 matches202 MergedCutGroups.Batch050.numericValid608 MergedCutGroups.Batch050.cellsSound608 MergedCutGroups.Batch050.cellsNumeric608 MergedCutGroups.Batch050.populationMatches608
    PopulationCertificates.Batch020.valid405 PopulationCertificates.Batch020.sound405 WitnessCertificates.Batch020.valid405 WitnessCertificates.Batch020.sound405 CountingCertificates.Batch020.valid405 CountingCertificates.Batch020.sound405 H st hI
theorem probabilityBound202 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch050.certificate608).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate405).dm (WitnessCertificates.Batch020.certificate405).beta (WitnessCertificates.Batch020.certificate405).L) ≤ ((CutFailureCertificates.Budget020.certificate405).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound405 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate405).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch050.certificate608).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch020.certificate405).omega:ℝ)) ≤ ((CutFailureCertificates.Budget020.certificate405).bound:ℝ) at hb
  exact (exponentialBound202 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches203 : (MergedCutGroups.Batch050.certificate611).AnchorMatches CountingCertificates.Batch020.certificate407 := by decide +kernel
theorem exponentialBound203 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch050.certificate611).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate407).dm (WitnessCertificates.Batch020.certificate407).beta (WitnessCertificates.Batch020.certificate407).L) ≤ (2*exp (-((CountingCertificates.Batch020.certificate407).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch050.certificate611).exponent:ℝ)*st.R))/((WitnessCertificates.Batch020.certificate407).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch050.certificate611 CountingCertificates.Batch020.certificate407 matches203 MergedCutGroups.Batch050.numericValid611 MergedCutGroups.Batch050.cellsSound611 MergedCutGroups.Batch050.cellsNumeric611 MergedCutGroups.Batch050.populationMatches611
    PopulationCertificates.Batch020.valid407 PopulationCertificates.Batch020.sound407 WitnessCertificates.Batch020.valid407 WitnessCertificates.Batch020.sound407 CountingCertificates.Batch020.valid407 CountingCertificates.Batch020.sound407 H st hI
theorem probabilityBound203 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch050.certificate611).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate407).dm (WitnessCertificates.Batch020.certificate407).beta (WitnessCertificates.Batch020.certificate407).L) ≤ ((CutFailureCertificates.Budget020.certificate407).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound407 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate407).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch050.certificate611).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch020.certificate407).omega:ℝ)) ≤ ((CutFailureCertificates.Budget020.certificate407).bound:ℝ) at hb
  exact (exponentialBound203 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches204 : (MergedCutGroups.Batch051.certificate614).AnchorMatches CountingCertificates.Batch020.certificate409 := by decide +kernel
theorem exponentialBound204 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch051.certificate614).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate409).dm (WitnessCertificates.Batch020.certificate409).beta (WitnessCertificates.Batch020.certificate409).L) ≤ (2*exp (-((CountingCertificates.Batch020.certificate409).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch051.certificate614).exponent:ℝ)*st.R))/((WitnessCertificates.Batch020.certificate409).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch051.certificate614 CountingCertificates.Batch020.certificate409 matches204 MergedCutGroups.Batch051.numericValid614 MergedCutGroups.Batch051.cellsSound614 MergedCutGroups.Batch051.cellsNumeric614 MergedCutGroups.Batch051.populationMatches614
    PopulationCertificates.Batch020.valid409 PopulationCertificates.Batch020.sound409 WitnessCertificates.Batch020.valid409 WitnessCertificates.Batch020.sound409 CountingCertificates.Batch020.valid409 CountingCertificates.Batch020.sound409 H st hI
theorem probabilityBound204 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch051.certificate614).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate409).dm (WitnessCertificates.Batch020.certificate409).beta (WitnessCertificates.Batch020.certificate409).L) ≤ ((CutFailureCertificates.Budget020.certificate409).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound409 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate409).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch051.certificate614).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch020.certificate409).omega:ℝ)) ≤ ((CutFailureCertificates.Budget020.certificate409).bound:ℝ) at hb
  exact (exponentialBound204 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches205 : (MergedCutGroups.Batch051.certificate617).AnchorMatches CountingCertificates.Batch020.certificate411 := by decide +kernel
theorem exponentialBound205 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch051.certificate617).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate411).dm (WitnessCertificates.Batch020.certificate411).beta (WitnessCertificates.Batch020.certificate411).L) ≤ (2*exp (-((CountingCertificates.Batch020.certificate411).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch051.certificate617).exponent:ℝ)*st.R))/((WitnessCertificates.Batch020.certificate411).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch051.certificate617 CountingCertificates.Batch020.certificate411 matches205 MergedCutGroups.Batch051.numericValid617 MergedCutGroups.Batch051.cellsSound617 MergedCutGroups.Batch051.cellsNumeric617 MergedCutGroups.Batch051.populationMatches617
    PopulationCertificates.Batch020.valid411 PopulationCertificates.Batch020.sound411 WitnessCertificates.Batch020.valid411 WitnessCertificates.Batch020.sound411 CountingCertificates.Batch020.valid411 CountingCertificates.Batch020.sound411 H st hI
theorem probabilityBound205 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch051.certificate617).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate411).dm (WitnessCertificates.Batch020.certificate411).beta (WitnessCertificates.Batch020.certificate411).L) ≤ ((CutFailureCertificates.Budget020.certificate411).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound411 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate411).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch051.certificate617).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch020.certificate411).omega:ℝ)) ≤ ((CutFailureCertificates.Budget020.certificate411).bound:ℝ) at hb
  exact (exponentialBound205 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches206 : (MergedCutGroups.Batch051.certificate620).AnchorMatches CountingCertificates.Batch020.certificate413 := by decide +kernel
theorem exponentialBound206 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch051.certificate620).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate413).dm (WitnessCertificates.Batch020.certificate413).beta (WitnessCertificates.Batch020.certificate413).L) ≤ (2*exp (-((CountingCertificates.Batch020.certificate413).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch051.certificate620).exponent:ℝ)*st.R))/((WitnessCertificates.Batch020.certificate413).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch051.certificate620 CountingCertificates.Batch020.certificate413 matches206 MergedCutGroups.Batch051.numericValid620 MergedCutGroups.Batch051.cellsSound620 MergedCutGroups.Batch051.cellsNumeric620 MergedCutGroups.Batch051.populationMatches620
    PopulationCertificates.Batch020.valid413 PopulationCertificates.Batch020.sound413 WitnessCertificates.Batch020.valid413 WitnessCertificates.Batch020.sound413 CountingCertificates.Batch020.valid413 CountingCertificates.Batch020.sound413 H st hI
theorem probabilityBound206 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch051.certificate620).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate413).dm (WitnessCertificates.Batch020.certificate413).beta (WitnessCertificates.Batch020.certificate413).L) ≤ ((CutFailureCertificates.Budget020.certificate413).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound413 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate413).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch051.certificate620).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch020.certificate413).omega:ℝ)) ≤ ((CutFailureCertificates.Budget020.certificate413).bound:ℝ) at hb
  exact (exponentialBound206 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches207 : (MergedCutGroups.Batch051.certificate623).AnchorMatches CountingCertificates.Batch020.certificate415 := by decide +kernel
theorem exponentialBound207 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch051.certificate623).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate415).dm (WitnessCertificates.Batch020.certificate415).beta (WitnessCertificates.Batch020.certificate415).L) ≤ (2*exp (-((CountingCertificates.Batch020.certificate415).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch051.certificate623).exponent:ℝ)*st.R))/((WitnessCertificates.Batch020.certificate415).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch051.certificate623 CountingCertificates.Batch020.certificate415 matches207 MergedCutGroups.Batch051.numericValid623 MergedCutGroups.Batch051.cellsSound623 MergedCutGroups.Batch051.cellsNumeric623 MergedCutGroups.Batch051.populationMatches623
    PopulationCertificates.Batch020.valid415 PopulationCertificates.Batch020.sound415 WitnessCertificates.Batch020.valid415 WitnessCertificates.Batch020.sound415 CountingCertificates.Batch020.valid415 CountingCertificates.Batch020.sound415 H st hI
theorem probabilityBound207 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch051.certificate623).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate415).dm (WitnessCertificates.Batch020.certificate415).beta (WitnessCertificates.Batch020.certificate415).L) ≤ ((CutFailureCertificates.Budget020.certificate415).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound415 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate415).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch051.certificate623).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch020.certificate415).omega:ℝ)) ≤ ((CutFailureCertificates.Budget020.certificate415).bound:ℝ) at hb
  exact (exponentialBound207 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches208 : (MergedCutGroups.Batch052.certificate626).AnchorMatches CountingCertificates.Batch020.certificate417 := by decide +kernel
theorem exponentialBound208 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch052.certificate626).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate417).dm (WitnessCertificates.Batch020.certificate417).beta (WitnessCertificates.Batch020.certificate417).L) ≤ (2*exp (-((CountingCertificates.Batch020.certificate417).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch052.certificate626).exponent:ℝ)*st.R))/((WitnessCertificates.Batch020.certificate417).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch052.certificate626 CountingCertificates.Batch020.certificate417 matches208 MergedCutGroups.Batch052.numericValid626 MergedCutGroups.Batch052.cellsSound626 MergedCutGroups.Batch052.cellsNumeric626 MergedCutGroups.Batch052.populationMatches626
    PopulationCertificates.Batch020.valid417 PopulationCertificates.Batch020.sound417 WitnessCertificates.Batch020.valid417 WitnessCertificates.Batch020.sound417 CountingCertificates.Batch020.valid417 CountingCertificates.Batch020.sound417 H st hI
theorem probabilityBound208 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch052.certificate626).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate417).dm (WitnessCertificates.Batch020.certificate417).beta (WitnessCertificates.Batch020.certificate417).L) ≤ ((CutFailureCertificates.Budget020.certificate417).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound417 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate417).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch052.certificate626).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch020.certificate417).omega:ℝ)) ≤ ((CutFailureCertificates.Budget020.certificate417).bound:ℝ) at hb
  exact (exponentialBound208 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches209 : (MergedCutGroups.Batch052.certificate629).AnchorMatches CountingCertificates.Batch020.certificate419 := by decide +kernel
theorem exponentialBound209 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch052.certificate629).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate419).dm (WitnessCertificates.Batch020.certificate419).beta (WitnessCertificates.Batch020.certificate419).L) ≤ (2*exp (-((CountingCertificates.Batch020.certificate419).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch052.certificate629).exponent:ℝ)*st.R))/((WitnessCertificates.Batch020.certificate419).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch052.certificate629 CountingCertificates.Batch020.certificate419 matches209 MergedCutGroups.Batch052.numericValid629 MergedCutGroups.Batch052.cellsSound629 MergedCutGroups.Batch052.cellsNumeric629 MergedCutGroups.Batch052.populationMatches629
    PopulationCertificates.Batch020.valid419 PopulationCertificates.Batch020.sound419 WitnessCertificates.Batch020.valid419 WitnessCertificates.Batch020.sound419 CountingCertificates.Batch020.valid419 CountingCertificates.Batch020.sound419 H st hI
theorem probabilityBound209 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch052.certificate629).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch020.certificate419).dm (WitnessCertificates.Batch020.certificate419).beta (WitnessCertificates.Batch020.certificate419).L) ≤ ((CutFailureCertificates.Budget020.certificate419).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget020.sound419 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch020.certificate419).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch052.certificate629).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch020.certificate419).omega:ℝ)) ≤ ((CutFailureCertificates.Budget020.certificate419).bound:ℝ) at hb
  exact (exponentialBound209 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches210 : (MergedCutGroups.Batch052.certificate632).AnchorMatches CountingCertificates.Batch021.certificate421 := by decide +kernel
theorem exponentialBound210 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch052.certificate632).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate421).dm (WitnessCertificates.Batch021.certificate421).beta (WitnessCertificates.Batch021.certificate421).L) ≤ (2*exp (-((CountingCertificates.Batch021.certificate421).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch052.certificate632).exponent:ℝ)*st.R))/((WitnessCertificates.Batch021.certificate421).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch052.certificate632 CountingCertificates.Batch021.certificate421 matches210 MergedCutGroups.Batch052.numericValid632 MergedCutGroups.Batch052.cellsSound632 MergedCutGroups.Batch052.cellsNumeric632 MergedCutGroups.Batch052.populationMatches632
    PopulationCertificates.Batch021.valid421 PopulationCertificates.Batch021.sound421 WitnessCertificates.Batch021.valid421 WitnessCertificates.Batch021.sound421 CountingCertificates.Batch021.valid421 CountingCertificates.Batch021.sound421 H st hI
theorem probabilityBound210 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch052.certificate632).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate421).dm (WitnessCertificates.Batch021.certificate421).beta (WitnessCertificates.Batch021.certificate421).L) ≤ ((CutFailureCertificates.Budget021.certificate421).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound421 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate421).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch052.certificate632).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch021.certificate421).omega:ℝ)) ≤ ((CutFailureCertificates.Budget021.certificate421).bound:ℝ) at hb
  exact (exponentialBound210 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches211 : (MergedCutGroups.Batch052.certificate635).AnchorMatches CountingCertificates.Batch021.certificate423 := by decide +kernel
theorem exponentialBound211 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch052.certificate635).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate423).dm (WitnessCertificates.Batch021.certificate423).beta (WitnessCertificates.Batch021.certificate423).L) ≤ (2*exp (-((CountingCertificates.Batch021.certificate423).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch052.certificate635).exponent:ℝ)*st.R))/((WitnessCertificates.Batch021.certificate423).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch052.certificate635 CountingCertificates.Batch021.certificate423 matches211 MergedCutGroups.Batch052.numericValid635 MergedCutGroups.Batch052.cellsSound635 MergedCutGroups.Batch052.cellsNumeric635 MergedCutGroups.Batch052.populationMatches635
    PopulationCertificates.Batch021.valid423 PopulationCertificates.Batch021.sound423 WitnessCertificates.Batch021.valid423 WitnessCertificates.Batch021.sound423 CountingCertificates.Batch021.valid423 CountingCertificates.Batch021.sound423 H st hI
theorem probabilityBound211 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch052.certificate635).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate423).dm (WitnessCertificates.Batch021.certificate423).beta (WitnessCertificates.Batch021.certificate423).L) ≤ ((CutFailureCertificates.Budget021.certificate423).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound423 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate423).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch052.certificate635).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch021.certificate423).omega:ℝ)) ≤ ((CutFailureCertificates.Budget021.certificate423).bound:ℝ) at hb
  exact (exponentialBound211 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches212 : (MergedCutGroups.Batch053.certificate638).AnchorMatches CountingCertificates.Batch021.certificate425 := by decide +kernel
theorem exponentialBound212 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch053.certificate638).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate425).dm (WitnessCertificates.Batch021.certificate425).beta (WitnessCertificates.Batch021.certificate425).L) ≤ (2*exp (-((CountingCertificates.Batch021.certificate425).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch053.certificate638).exponent:ℝ)*st.R))/((WitnessCertificates.Batch021.certificate425).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch053.certificate638 CountingCertificates.Batch021.certificate425 matches212 MergedCutGroups.Batch053.numericValid638 MergedCutGroups.Batch053.cellsSound638 MergedCutGroups.Batch053.cellsNumeric638 MergedCutGroups.Batch053.populationMatches638
    PopulationCertificates.Batch021.valid425 PopulationCertificates.Batch021.sound425 WitnessCertificates.Batch021.valid425 WitnessCertificates.Batch021.sound425 CountingCertificates.Batch021.valid425 CountingCertificates.Batch021.sound425 H st hI
theorem probabilityBound212 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch053.certificate638).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate425).dm (WitnessCertificates.Batch021.certificate425).beta (WitnessCertificates.Batch021.certificate425).L) ≤ ((CutFailureCertificates.Budget021.certificate425).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound425 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate425).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch053.certificate638).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch021.certificate425).omega:ℝ)) ≤ ((CutFailureCertificates.Budget021.certificate425).bound:ℝ) at hb
  exact (exponentialBound212 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches213 : (MergedCutGroups.Batch053.certificate641).AnchorMatches CountingCertificates.Batch021.certificate427 := by decide +kernel
theorem exponentialBound213 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch053.certificate641).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate427).dm (WitnessCertificates.Batch021.certificate427).beta (WitnessCertificates.Batch021.certificate427).L) ≤ (2*exp (-((CountingCertificates.Batch021.certificate427).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch053.certificate641).exponent:ℝ)*st.R))/((WitnessCertificates.Batch021.certificate427).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch053.certificate641 CountingCertificates.Batch021.certificate427 matches213 MergedCutGroups.Batch053.numericValid641 MergedCutGroups.Batch053.cellsSound641 MergedCutGroups.Batch053.cellsNumeric641 MergedCutGroups.Batch053.populationMatches641
    PopulationCertificates.Batch021.valid427 PopulationCertificates.Batch021.sound427 WitnessCertificates.Batch021.valid427 WitnessCertificates.Batch021.sound427 CountingCertificates.Batch021.valid427 CountingCertificates.Batch021.sound427 H st hI
theorem probabilityBound213 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch053.certificate641).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate427).dm (WitnessCertificates.Batch021.certificate427).beta (WitnessCertificates.Batch021.certificate427).L) ≤ ((CutFailureCertificates.Budget021.certificate427).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound427 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate427).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch053.certificate641).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch021.certificate427).omega:ℝ)) ≤ ((CutFailureCertificates.Budget021.certificate427).bound:ℝ) at hb
  exact (exponentialBound213 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches214 : (MergedCutGroups.Batch053.certificate644).AnchorMatches CountingCertificates.Batch021.certificate429 := by decide +kernel
theorem exponentialBound214 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch053.certificate644).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate429).dm (WitnessCertificates.Batch021.certificate429).beta (WitnessCertificates.Batch021.certificate429).L) ≤ (2*exp (-((CountingCertificates.Batch021.certificate429).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch053.certificate644).exponent:ℝ)*st.R))/((WitnessCertificates.Batch021.certificate429).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch053.certificate644 CountingCertificates.Batch021.certificate429 matches214 MergedCutGroups.Batch053.numericValid644 MergedCutGroups.Batch053.cellsSound644 MergedCutGroups.Batch053.cellsNumeric644 MergedCutGroups.Batch053.populationMatches644
    PopulationCertificates.Batch021.valid429 PopulationCertificates.Batch021.sound429 WitnessCertificates.Batch021.valid429 WitnessCertificates.Batch021.sound429 CountingCertificates.Batch021.valid429 CountingCertificates.Batch021.sound429 H st hI
theorem probabilityBound214 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch053.certificate644).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate429).dm (WitnessCertificates.Batch021.certificate429).beta (WitnessCertificates.Batch021.certificate429).L) ≤ ((CutFailureCertificates.Budget021.certificate429).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound429 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate429).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch053.certificate644).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch021.certificate429).omega:ℝ)) ≤ ((CutFailureCertificates.Budget021.certificate429).bound:ℝ) at hb
  exact (exponentialBound214 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches215 : (MergedCutGroups.Batch053.certificate647).AnchorMatches CountingCertificates.Batch021.certificate431 := by decide +kernel
theorem exponentialBound215 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch053.certificate647).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate431).dm (WitnessCertificates.Batch021.certificate431).beta (WitnessCertificates.Batch021.certificate431).L) ≤ (2*exp (-((CountingCertificates.Batch021.certificate431).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch053.certificate647).exponent:ℝ)*st.R))/((WitnessCertificates.Batch021.certificate431).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch053.certificate647 CountingCertificates.Batch021.certificate431 matches215 MergedCutGroups.Batch053.numericValid647 MergedCutGroups.Batch053.cellsSound647 MergedCutGroups.Batch053.cellsNumeric647 MergedCutGroups.Batch053.populationMatches647
    PopulationCertificates.Batch021.valid431 PopulationCertificates.Batch021.sound431 WitnessCertificates.Batch021.valid431 WitnessCertificates.Batch021.sound431 CountingCertificates.Batch021.valid431 CountingCertificates.Batch021.sound431 H st hI
theorem probabilityBound215 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch053.certificate647).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate431).dm (WitnessCertificates.Batch021.certificate431).beta (WitnessCertificates.Batch021.certificate431).L) ≤ ((CutFailureCertificates.Budget021.certificate431).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound431 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate431).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch053.certificate647).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch021.certificate431).omega:ℝ)) ≤ ((CutFailureCertificates.Budget021.certificate431).bound:ℝ) at hb
  exact (exponentialBound215 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches216 : (MergedCutGroups.Batch054.certificate650).AnchorMatches CountingCertificates.Batch021.certificate433 := by decide +kernel
theorem exponentialBound216 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch054.certificate650).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate433).dm (WitnessCertificates.Batch021.certificate433).beta (WitnessCertificates.Batch021.certificate433).L) ≤ (2*exp (-((CountingCertificates.Batch021.certificate433).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch054.certificate650).exponent:ℝ)*st.R))/((WitnessCertificates.Batch021.certificate433).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch054.certificate650 CountingCertificates.Batch021.certificate433 matches216 MergedCutGroups.Batch054.numericValid650 MergedCutGroups.Batch054.cellsSound650 MergedCutGroups.Batch054.cellsNumeric650 MergedCutGroups.Batch054.populationMatches650
    PopulationCertificates.Batch021.valid433 PopulationCertificates.Batch021.sound433 WitnessCertificates.Batch021.valid433 WitnessCertificates.Batch021.sound433 CountingCertificates.Batch021.valid433 CountingCertificates.Batch021.sound433 H st hI
theorem probabilityBound216 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch054.certificate650).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate433).dm (WitnessCertificates.Batch021.certificate433).beta (WitnessCertificates.Batch021.certificate433).L) ≤ ((CutFailureCertificates.Budget021.certificate433).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound433 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate433).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch054.certificate650).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch021.certificate433).omega:ℝ)) ≤ ((CutFailureCertificates.Budget021.certificate433).bound:ℝ) at hb
  exact (exponentialBound216 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches217 : (MergedCutGroups.Batch054.certificate653).AnchorMatches CountingCertificates.Batch021.certificate435 := by decide +kernel
theorem exponentialBound217 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch054.certificate653).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate435).dm (WitnessCertificates.Batch021.certificate435).beta (WitnessCertificates.Batch021.certificate435).L) ≤ (2*exp (-((CountingCertificates.Batch021.certificate435).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch054.certificate653).exponent:ℝ)*st.R))/((WitnessCertificates.Batch021.certificate435).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch054.certificate653 CountingCertificates.Batch021.certificate435 matches217 MergedCutGroups.Batch054.numericValid653 MergedCutGroups.Batch054.cellsSound653 MergedCutGroups.Batch054.cellsNumeric653 MergedCutGroups.Batch054.populationMatches653
    PopulationCertificates.Batch021.valid435 PopulationCertificates.Batch021.sound435 WitnessCertificates.Batch021.valid435 WitnessCertificates.Batch021.sound435 CountingCertificates.Batch021.valid435 CountingCertificates.Batch021.sound435 H st hI
theorem probabilityBound217 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch054.certificate653).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate435).dm (WitnessCertificates.Batch021.certificate435).beta (WitnessCertificates.Batch021.certificate435).L) ≤ ((CutFailureCertificates.Budget021.certificate435).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound435 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate435).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch054.certificate653).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch021.certificate435).omega:ℝ)) ≤ ((CutFailureCertificates.Budget021.certificate435).bound:ℝ) at hb
  exact (exponentialBound217 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches218 : (MergedCutGroups.Batch054.certificate656).AnchorMatches CountingCertificates.Batch021.certificate437 := by decide +kernel
theorem exponentialBound218 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch054.certificate656).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate437).dm (WitnessCertificates.Batch021.certificate437).beta (WitnessCertificates.Batch021.certificate437).L) ≤ (2*exp (-((CountingCertificates.Batch021.certificate437).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch054.certificate656).exponent:ℝ)*st.R))/((WitnessCertificates.Batch021.certificate437).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch054.certificate656 CountingCertificates.Batch021.certificate437 matches218 MergedCutGroups.Batch054.numericValid656 MergedCutGroups.Batch054.cellsSound656 MergedCutGroups.Batch054.cellsNumeric656 MergedCutGroups.Batch054.populationMatches656
    PopulationCertificates.Batch021.valid437 PopulationCertificates.Batch021.sound437 WitnessCertificates.Batch021.valid437 WitnessCertificates.Batch021.sound437 CountingCertificates.Batch021.valid437 CountingCertificates.Batch021.sound437 H st hI
theorem probabilityBound218 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch054.certificate656).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate437).dm (WitnessCertificates.Batch021.certificate437).beta (WitnessCertificates.Batch021.certificate437).L) ≤ ((CutFailureCertificates.Budget021.certificate437).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound437 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate437).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch054.certificate656).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch021.certificate437).omega:ℝ)) ≤ ((CutFailureCertificates.Budget021.certificate437).bound:ℝ) at hb
  exact (exponentialBound218 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches219 : (MergedCutGroups.Batch054.certificate659).AnchorMatches CountingCertificates.Batch021.certificate439 := by decide +kernel
theorem exponentialBound219 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch054.certificate659).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate439).dm (WitnessCertificates.Batch021.certificate439).beta (WitnessCertificates.Batch021.certificate439).L) ≤ (2*exp (-((CountingCertificates.Batch021.certificate439).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch054.certificate659).exponent:ℝ)*st.R))/((WitnessCertificates.Batch021.certificate439).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch054.certificate659 CountingCertificates.Batch021.certificate439 matches219 MergedCutGroups.Batch054.numericValid659 MergedCutGroups.Batch054.cellsSound659 MergedCutGroups.Batch054.cellsNumeric659 MergedCutGroups.Batch054.populationMatches659
    PopulationCertificates.Batch021.valid439 PopulationCertificates.Batch021.sound439 WitnessCertificates.Batch021.valid439 WitnessCertificates.Batch021.sound439 CountingCertificates.Batch021.valid439 CountingCertificates.Batch021.sound439 H st hI
theorem probabilityBound219 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch054.certificate659).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch021.certificate439).dm (WitnessCertificates.Batch021.certificate439).beta (WitnessCertificates.Batch021.certificate439).L) ≤ ((CutFailureCertificates.Budget021.certificate439).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget021.sound439 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch021.certificate439).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch054.certificate659).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch021.certificate439).omega:ℝ)) ≤ ((CutFailureCertificates.Budget021.certificate439).bound:ℝ) at hb
  exact (exponentialBound219 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch010
