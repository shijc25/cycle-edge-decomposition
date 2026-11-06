import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch000
import Cycle12.CountingCertificates.Batch001
import Cycle12.CutFailureCertificates.Budget000
import Cycle12.CutFailureCertificates.Budget001
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

namespace Cycle12.CertifiedAnchorFailures.Batch000
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches0 : (MergedCutGroups.Batch000.certificate2).AnchorMatches CountingCertificates.Batch000.certificate1 := by decide +kernel
theorem exponentialBound0 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch000.certificate2).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate1).dm (WitnessCertificates.Batch000.certificate1).beta (WitnessCertificates.Batch000.certificate1).L) ≤ (2*exp (-((CountingCertificates.Batch000.certificate1).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch000.certificate2).exponent:ℝ)*st.R))/((WitnessCertificates.Batch000.certificate1).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch000.certificate2 CountingCertificates.Batch000.certificate1 matches0 MergedCutGroups.Batch000.numericValid2 MergedCutGroups.Batch000.cellsSound2 MergedCutGroups.Batch000.cellsNumeric2 MergedCutGroups.Batch000.populationMatches2
    PopulationCertificates.Batch000.valid1 PopulationCertificates.Batch000.sound1 WitnessCertificates.Batch000.valid1 WitnessCertificates.Batch000.sound1 CountingCertificates.Batch000.valid1 CountingCertificates.Batch000.sound1 H st hI
theorem probabilityBound0 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch000.certificate2).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate1).dm (WitnessCertificates.Batch000.certificate1).beta (WitnessCertificates.Batch000.certificate1).L) ≤ ((CutFailureCertificates.Budget000.certificate1).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound1 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate1).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch000.certificate2).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch000.certificate1).omega:ℝ)) ≤ ((CutFailureCertificates.Budget000.certificate1).bound:ℝ) at hb
  exact (exponentialBound0 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches1 : (MergedCutGroups.Batch000.certificate5).AnchorMatches CountingCertificates.Batch000.certificate3 := by decide +kernel
theorem exponentialBound1 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch000.certificate5).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate3).dm (WitnessCertificates.Batch000.certificate3).beta (WitnessCertificates.Batch000.certificate3).L) ≤ (2*exp (-((CountingCertificates.Batch000.certificate3).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch000.certificate5).exponent:ℝ)*st.R))/((WitnessCertificates.Batch000.certificate3).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch000.certificate5 CountingCertificates.Batch000.certificate3 matches1 MergedCutGroups.Batch000.numericValid5 MergedCutGroups.Batch000.cellsSound5 MergedCutGroups.Batch000.cellsNumeric5 MergedCutGroups.Batch000.populationMatches5
    PopulationCertificates.Batch000.valid3 PopulationCertificates.Batch000.sound3 WitnessCertificates.Batch000.valid3 WitnessCertificates.Batch000.sound3 CountingCertificates.Batch000.valid3 CountingCertificates.Batch000.sound3 H st hI
theorem probabilityBound1 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch000.certificate5).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate3).dm (WitnessCertificates.Batch000.certificate3).beta (WitnessCertificates.Batch000.certificate3).L) ≤ ((CutFailureCertificates.Budget000.certificate3).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound3 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate3).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch000.certificate5).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch000.certificate3).omega:ℝ)) ≤ ((CutFailureCertificates.Budget000.certificate3).bound:ℝ) at hb
  exact (exponentialBound1 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches2 : (MergedCutGroups.Batch000.certificate8).AnchorMatches CountingCertificates.Batch000.certificate5 := by decide +kernel
theorem exponentialBound2 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch000.certificate8).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate5).dm (WitnessCertificates.Batch000.certificate5).beta (WitnessCertificates.Batch000.certificate5).L) ≤ (2*exp (-((CountingCertificates.Batch000.certificate5).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch000.certificate8).exponent:ℝ)*st.R))/((WitnessCertificates.Batch000.certificate5).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch000.certificate8 CountingCertificates.Batch000.certificate5 matches2 MergedCutGroups.Batch000.numericValid8 MergedCutGroups.Batch000.cellsSound8 MergedCutGroups.Batch000.cellsNumeric8 MergedCutGroups.Batch000.populationMatches8
    PopulationCertificates.Batch000.valid5 PopulationCertificates.Batch000.sound5 WitnessCertificates.Batch000.valid5 WitnessCertificates.Batch000.sound5 CountingCertificates.Batch000.valid5 CountingCertificates.Batch000.sound5 H st hI
theorem probabilityBound2 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch000.certificate8).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate5).dm (WitnessCertificates.Batch000.certificate5).beta (WitnessCertificates.Batch000.certificate5).L) ≤ ((CutFailureCertificates.Budget000.certificate5).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound5 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate5).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch000.certificate8).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch000.certificate5).omega:ℝ)) ≤ ((CutFailureCertificates.Budget000.certificate5).bound:ℝ) at hb
  exact (exponentialBound2 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches3 : (MergedCutGroups.Batch000.certificate11).AnchorMatches CountingCertificates.Batch000.certificate7 := by decide +kernel
theorem exponentialBound3 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch000.certificate11).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate7).dm (WitnessCertificates.Batch000.certificate7).beta (WitnessCertificates.Batch000.certificate7).L) ≤ (2*exp (-((CountingCertificates.Batch000.certificate7).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch000.certificate11).exponent:ℝ)*st.R))/((WitnessCertificates.Batch000.certificate7).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch000.certificate11 CountingCertificates.Batch000.certificate7 matches3 MergedCutGroups.Batch000.numericValid11 MergedCutGroups.Batch000.cellsSound11 MergedCutGroups.Batch000.cellsNumeric11 MergedCutGroups.Batch000.populationMatches11
    PopulationCertificates.Batch000.valid7 PopulationCertificates.Batch000.sound7 WitnessCertificates.Batch000.valid7 WitnessCertificates.Batch000.sound7 CountingCertificates.Batch000.valid7 CountingCertificates.Batch000.sound7 H st hI
theorem probabilityBound3 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch000.certificate11).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate7).dm (WitnessCertificates.Batch000.certificate7).beta (WitnessCertificates.Batch000.certificate7).L) ≤ ((CutFailureCertificates.Budget000.certificate7).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound7 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate7).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch000.certificate11).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch000.certificate7).omega:ℝ)) ≤ ((CutFailureCertificates.Budget000.certificate7).bound:ℝ) at hb
  exact (exponentialBound3 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches4 : (MergedCutGroups.Batch001.certificate14).AnchorMatches CountingCertificates.Batch000.certificate9 := by decide +kernel
theorem exponentialBound4 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch001.certificate14).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate9).dm (WitnessCertificates.Batch000.certificate9).beta (WitnessCertificates.Batch000.certificate9).L) ≤ (2*exp (-((CountingCertificates.Batch000.certificate9).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch001.certificate14).exponent:ℝ)*st.R))/((WitnessCertificates.Batch000.certificate9).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch001.certificate14 CountingCertificates.Batch000.certificate9 matches4 MergedCutGroups.Batch001.numericValid14 MergedCutGroups.Batch001.cellsSound14 MergedCutGroups.Batch001.cellsNumeric14 MergedCutGroups.Batch001.populationMatches14
    PopulationCertificates.Batch000.valid9 PopulationCertificates.Batch000.sound9 WitnessCertificates.Batch000.valid9 WitnessCertificates.Batch000.sound9 CountingCertificates.Batch000.valid9 CountingCertificates.Batch000.sound9 H st hI
theorem probabilityBound4 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch001.certificate14).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate9).dm (WitnessCertificates.Batch000.certificate9).beta (WitnessCertificates.Batch000.certificate9).L) ≤ ((CutFailureCertificates.Budget000.certificate9).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound9 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate9).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch001.certificate14).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch000.certificate9).omega:ℝ)) ≤ ((CutFailureCertificates.Budget000.certificate9).bound:ℝ) at hb
  exact (exponentialBound4 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches5 : (MergedCutGroups.Batch001.certificate17).AnchorMatches CountingCertificates.Batch000.certificate11 := by decide +kernel
theorem exponentialBound5 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch001.certificate17).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate11).dm (WitnessCertificates.Batch000.certificate11).beta (WitnessCertificates.Batch000.certificate11).L) ≤ (2*exp (-((CountingCertificates.Batch000.certificate11).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch001.certificate17).exponent:ℝ)*st.R))/((WitnessCertificates.Batch000.certificate11).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch001.certificate17 CountingCertificates.Batch000.certificate11 matches5 MergedCutGroups.Batch001.numericValid17 MergedCutGroups.Batch001.cellsSound17 MergedCutGroups.Batch001.cellsNumeric17 MergedCutGroups.Batch001.populationMatches17
    PopulationCertificates.Batch000.valid11 PopulationCertificates.Batch000.sound11 WitnessCertificates.Batch000.valid11 WitnessCertificates.Batch000.sound11 CountingCertificates.Batch000.valid11 CountingCertificates.Batch000.sound11 H st hI
theorem probabilityBound5 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch001.certificate17).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate11).dm (WitnessCertificates.Batch000.certificate11).beta (WitnessCertificates.Batch000.certificate11).L) ≤ ((CutFailureCertificates.Budget000.certificate11).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound11 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate11).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch001.certificate17).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch000.certificate11).omega:ℝ)) ≤ ((CutFailureCertificates.Budget000.certificate11).bound:ℝ) at hb
  exact (exponentialBound5 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches6 : (MergedCutGroups.Batch001.certificate20).AnchorMatches CountingCertificates.Batch000.certificate13 := by decide +kernel
theorem exponentialBound6 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch001.certificate20).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate13).dm (WitnessCertificates.Batch000.certificate13).beta (WitnessCertificates.Batch000.certificate13).L) ≤ (2*exp (-((CountingCertificates.Batch000.certificate13).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch001.certificate20).exponent:ℝ)*st.R))/((WitnessCertificates.Batch000.certificate13).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch001.certificate20 CountingCertificates.Batch000.certificate13 matches6 MergedCutGroups.Batch001.numericValid20 MergedCutGroups.Batch001.cellsSound20 MergedCutGroups.Batch001.cellsNumeric20 MergedCutGroups.Batch001.populationMatches20
    PopulationCertificates.Batch000.valid13 PopulationCertificates.Batch000.sound13 WitnessCertificates.Batch000.valid13 WitnessCertificates.Batch000.sound13 CountingCertificates.Batch000.valid13 CountingCertificates.Batch000.sound13 H st hI
theorem probabilityBound6 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch001.certificate20).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate13).dm (WitnessCertificates.Batch000.certificate13).beta (WitnessCertificates.Batch000.certificate13).L) ≤ ((CutFailureCertificates.Budget000.certificate13).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound13 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate13).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch001.certificate20).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch000.certificate13).omega:ℝ)) ≤ ((CutFailureCertificates.Budget000.certificate13).bound:ℝ) at hb
  exact (exponentialBound6 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches7 : (MergedCutGroups.Batch001.certificate23).AnchorMatches CountingCertificates.Batch000.certificate15 := by decide +kernel
theorem exponentialBound7 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch001.certificate23).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate15).dm (WitnessCertificates.Batch000.certificate15).beta (WitnessCertificates.Batch000.certificate15).L) ≤ (2*exp (-((CountingCertificates.Batch000.certificate15).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch001.certificate23).exponent:ℝ)*st.R))/((WitnessCertificates.Batch000.certificate15).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch001.certificate23 CountingCertificates.Batch000.certificate15 matches7 MergedCutGroups.Batch001.numericValid23 MergedCutGroups.Batch001.cellsSound23 MergedCutGroups.Batch001.cellsNumeric23 MergedCutGroups.Batch001.populationMatches23
    PopulationCertificates.Batch000.valid15 PopulationCertificates.Batch000.sound15 WitnessCertificates.Batch000.valid15 WitnessCertificates.Batch000.sound15 CountingCertificates.Batch000.valid15 CountingCertificates.Batch000.sound15 H st hI
theorem probabilityBound7 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch001.certificate23).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate15).dm (WitnessCertificates.Batch000.certificate15).beta (WitnessCertificates.Batch000.certificate15).L) ≤ ((CutFailureCertificates.Budget000.certificate15).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound15 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate15).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch001.certificate23).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch000.certificate15).omega:ℝ)) ≤ ((CutFailureCertificates.Budget000.certificate15).bound:ℝ) at hb
  exact (exponentialBound7 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches8 : (MergedCutGroups.Batch002.certificate26).AnchorMatches CountingCertificates.Batch000.certificate17 := by decide +kernel
theorem exponentialBound8 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch002.certificate26).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate17).dm (WitnessCertificates.Batch000.certificate17).beta (WitnessCertificates.Batch000.certificate17).L) ≤ (2*exp (-((CountingCertificates.Batch000.certificate17).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch002.certificate26).exponent:ℝ)*st.R))/((WitnessCertificates.Batch000.certificate17).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch002.certificate26 CountingCertificates.Batch000.certificate17 matches8 MergedCutGroups.Batch002.numericValid26 MergedCutGroups.Batch002.cellsSound26 MergedCutGroups.Batch002.cellsNumeric26 MergedCutGroups.Batch002.populationMatches26
    PopulationCertificates.Batch000.valid17 PopulationCertificates.Batch000.sound17 WitnessCertificates.Batch000.valid17 WitnessCertificates.Batch000.sound17 CountingCertificates.Batch000.valid17 CountingCertificates.Batch000.sound17 H st hI
theorem probabilityBound8 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch002.certificate26).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate17).dm (WitnessCertificates.Batch000.certificate17).beta (WitnessCertificates.Batch000.certificate17).L) ≤ ((CutFailureCertificates.Budget000.certificate17).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound17 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate17).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch002.certificate26).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch000.certificate17).omega:ℝ)) ≤ ((CutFailureCertificates.Budget000.certificate17).bound:ℝ) at hb
  exact (exponentialBound8 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches9 : (MergedCutGroups.Batch002.certificate29).AnchorMatches CountingCertificates.Batch000.certificate19 := by decide +kernel
theorem exponentialBound9 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch002.certificate29).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate19).dm (WitnessCertificates.Batch000.certificate19).beta (WitnessCertificates.Batch000.certificate19).L) ≤ (2*exp (-((CountingCertificates.Batch000.certificate19).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch002.certificate29).exponent:ℝ)*st.R))/((WitnessCertificates.Batch000.certificate19).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch002.certificate29 CountingCertificates.Batch000.certificate19 matches9 MergedCutGroups.Batch002.numericValid29 MergedCutGroups.Batch002.cellsSound29 MergedCutGroups.Batch002.cellsNumeric29 MergedCutGroups.Batch002.populationMatches29
    PopulationCertificates.Batch000.valid19 PopulationCertificates.Batch000.sound19 WitnessCertificates.Batch000.valid19 WitnessCertificates.Batch000.sound19 CountingCertificates.Batch000.valid19 CountingCertificates.Batch000.sound19 H st hI
theorem probabilityBound9 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch002.certificate29).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch000.certificate19).dm (WitnessCertificates.Batch000.certificate19).beta (WitnessCertificates.Batch000.certificate19).L) ≤ ((CutFailureCertificates.Budget000.certificate19).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget000.sound19 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch000.certificate19).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch002.certificate29).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch000.certificate19).omega:ℝ)) ≤ ((CutFailureCertificates.Budget000.certificate19).bound:ℝ) at hb
  exact (exponentialBound9 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches10 : (MergedCutGroups.Batch002.certificate32).AnchorMatches CountingCertificates.Batch001.certificate21 := by decide +kernel
theorem exponentialBound10 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch002.certificate32).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate21).dm (WitnessCertificates.Batch001.certificate21).beta (WitnessCertificates.Batch001.certificate21).L) ≤ (2*exp (-((CountingCertificates.Batch001.certificate21).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch002.certificate32).exponent:ℝ)*st.R))/((WitnessCertificates.Batch001.certificate21).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch002.certificate32 CountingCertificates.Batch001.certificate21 matches10 MergedCutGroups.Batch002.numericValid32 MergedCutGroups.Batch002.cellsSound32 MergedCutGroups.Batch002.cellsNumeric32 MergedCutGroups.Batch002.populationMatches32
    PopulationCertificates.Batch001.valid21 PopulationCertificates.Batch001.sound21 WitnessCertificates.Batch001.valid21 WitnessCertificates.Batch001.sound21 CountingCertificates.Batch001.valid21 CountingCertificates.Batch001.sound21 H st hI
theorem probabilityBound10 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch002.certificate32).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate21).dm (WitnessCertificates.Batch001.certificate21).beta (WitnessCertificates.Batch001.certificate21).L) ≤ ((CutFailureCertificates.Budget001.certificate21).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound21 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate21).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch002.certificate32).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch001.certificate21).omega:ℝ)) ≤ ((CutFailureCertificates.Budget001.certificate21).bound:ℝ) at hb
  exact (exponentialBound10 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches11 : (MergedCutGroups.Batch002.certificate35).AnchorMatches CountingCertificates.Batch001.certificate23 := by decide +kernel
theorem exponentialBound11 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch002.certificate35).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate23).dm (WitnessCertificates.Batch001.certificate23).beta (WitnessCertificates.Batch001.certificate23).L) ≤ (2*exp (-((CountingCertificates.Batch001.certificate23).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch002.certificate35).exponent:ℝ)*st.R))/((WitnessCertificates.Batch001.certificate23).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch002.certificate35 CountingCertificates.Batch001.certificate23 matches11 MergedCutGroups.Batch002.numericValid35 MergedCutGroups.Batch002.cellsSound35 MergedCutGroups.Batch002.cellsNumeric35 MergedCutGroups.Batch002.populationMatches35
    PopulationCertificates.Batch001.valid23 PopulationCertificates.Batch001.sound23 WitnessCertificates.Batch001.valid23 WitnessCertificates.Batch001.sound23 CountingCertificates.Batch001.valid23 CountingCertificates.Batch001.sound23 H st hI
theorem probabilityBound11 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch002.certificate35).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate23).dm (WitnessCertificates.Batch001.certificate23).beta (WitnessCertificates.Batch001.certificate23).L) ≤ ((CutFailureCertificates.Budget001.certificate23).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound23 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate23).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch002.certificate35).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch001.certificate23).omega:ℝ)) ≤ ((CutFailureCertificates.Budget001.certificate23).bound:ℝ) at hb
  exact (exponentialBound11 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches12 : (MergedCutGroups.Batch003.certificate38).AnchorMatches CountingCertificates.Batch001.certificate25 := by decide +kernel
theorem exponentialBound12 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch003.certificate38).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate25).dm (WitnessCertificates.Batch001.certificate25).beta (WitnessCertificates.Batch001.certificate25).L) ≤ (2*exp (-((CountingCertificates.Batch001.certificate25).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch003.certificate38).exponent:ℝ)*st.R))/((WitnessCertificates.Batch001.certificate25).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch003.certificate38 CountingCertificates.Batch001.certificate25 matches12 MergedCutGroups.Batch003.numericValid38 MergedCutGroups.Batch003.cellsSound38 MergedCutGroups.Batch003.cellsNumeric38 MergedCutGroups.Batch003.populationMatches38
    PopulationCertificates.Batch001.valid25 PopulationCertificates.Batch001.sound25 WitnessCertificates.Batch001.valid25 WitnessCertificates.Batch001.sound25 CountingCertificates.Batch001.valid25 CountingCertificates.Batch001.sound25 H st hI
theorem probabilityBound12 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch003.certificate38).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate25).dm (WitnessCertificates.Batch001.certificate25).beta (WitnessCertificates.Batch001.certificate25).L) ≤ ((CutFailureCertificates.Budget001.certificate25).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound25 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate25).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch003.certificate38).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch001.certificate25).omega:ℝ)) ≤ ((CutFailureCertificates.Budget001.certificate25).bound:ℝ) at hb
  exact (exponentialBound12 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches13 : (MergedCutGroups.Batch003.certificate41).AnchorMatches CountingCertificates.Batch001.certificate27 := by decide +kernel
theorem exponentialBound13 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch003.certificate41).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate27).dm (WitnessCertificates.Batch001.certificate27).beta (WitnessCertificates.Batch001.certificate27).L) ≤ (2*exp (-((CountingCertificates.Batch001.certificate27).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch003.certificate41).exponent:ℝ)*st.R))/((WitnessCertificates.Batch001.certificate27).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch003.certificate41 CountingCertificates.Batch001.certificate27 matches13 MergedCutGroups.Batch003.numericValid41 MergedCutGroups.Batch003.cellsSound41 MergedCutGroups.Batch003.cellsNumeric41 MergedCutGroups.Batch003.populationMatches41
    PopulationCertificates.Batch001.valid27 PopulationCertificates.Batch001.sound27 WitnessCertificates.Batch001.valid27 WitnessCertificates.Batch001.sound27 CountingCertificates.Batch001.valid27 CountingCertificates.Batch001.sound27 H st hI
theorem probabilityBound13 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch003.certificate41).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate27).dm (WitnessCertificates.Batch001.certificate27).beta (WitnessCertificates.Batch001.certificate27).L) ≤ ((CutFailureCertificates.Budget001.certificate27).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound27 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate27).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch003.certificate41).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch001.certificate27).omega:ℝ)) ≤ ((CutFailureCertificates.Budget001.certificate27).bound:ℝ) at hb
  exact (exponentialBound13 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches14 : (MergedCutGroups.Batch003.certificate44).AnchorMatches CountingCertificates.Batch001.certificate29 := by decide +kernel
theorem exponentialBound14 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch003.certificate44).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate29).dm (WitnessCertificates.Batch001.certificate29).beta (WitnessCertificates.Batch001.certificate29).L) ≤ (2*exp (-((CountingCertificates.Batch001.certificate29).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch003.certificate44).exponent:ℝ)*st.R))/((WitnessCertificates.Batch001.certificate29).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch003.certificate44 CountingCertificates.Batch001.certificate29 matches14 MergedCutGroups.Batch003.numericValid44 MergedCutGroups.Batch003.cellsSound44 MergedCutGroups.Batch003.cellsNumeric44 MergedCutGroups.Batch003.populationMatches44
    PopulationCertificates.Batch001.valid29 PopulationCertificates.Batch001.sound29 WitnessCertificates.Batch001.valid29 WitnessCertificates.Batch001.sound29 CountingCertificates.Batch001.valid29 CountingCertificates.Batch001.sound29 H st hI
theorem probabilityBound14 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch003.certificate44).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate29).dm (WitnessCertificates.Batch001.certificate29).beta (WitnessCertificates.Batch001.certificate29).L) ≤ ((CutFailureCertificates.Budget001.certificate29).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound29 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate29).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch003.certificate44).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch001.certificate29).omega:ℝ)) ≤ ((CutFailureCertificates.Budget001.certificate29).bound:ℝ) at hb
  exact (exponentialBound14 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches15 : (MergedCutGroups.Batch003.certificate47).AnchorMatches CountingCertificates.Batch001.certificate31 := by decide +kernel
theorem exponentialBound15 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch003.certificate47).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate31).dm (WitnessCertificates.Batch001.certificate31).beta (WitnessCertificates.Batch001.certificate31).L) ≤ (2*exp (-((CountingCertificates.Batch001.certificate31).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch003.certificate47).exponent:ℝ)*st.R))/((WitnessCertificates.Batch001.certificate31).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch003.certificate47 CountingCertificates.Batch001.certificate31 matches15 MergedCutGroups.Batch003.numericValid47 MergedCutGroups.Batch003.cellsSound47 MergedCutGroups.Batch003.cellsNumeric47 MergedCutGroups.Batch003.populationMatches47
    PopulationCertificates.Batch001.valid31 PopulationCertificates.Batch001.sound31 WitnessCertificates.Batch001.valid31 WitnessCertificates.Batch001.sound31 CountingCertificates.Batch001.valid31 CountingCertificates.Batch001.sound31 H st hI
theorem probabilityBound15 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch003.certificate47).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate31).dm (WitnessCertificates.Batch001.certificate31).beta (WitnessCertificates.Batch001.certificate31).L) ≤ ((CutFailureCertificates.Budget001.certificate31).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound31 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate31).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch003.certificate47).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch001.certificate31).omega:ℝ)) ≤ ((CutFailureCertificates.Budget001.certificate31).bound:ℝ) at hb
  exact (exponentialBound15 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches16 : (MergedCutGroups.Batch004.certificate50).AnchorMatches CountingCertificates.Batch001.certificate33 := by decide +kernel
theorem exponentialBound16 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch004.certificate50).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate33).dm (WitnessCertificates.Batch001.certificate33).beta (WitnessCertificates.Batch001.certificate33).L) ≤ (2*exp (-((CountingCertificates.Batch001.certificate33).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch004.certificate50).exponent:ℝ)*st.R))/((WitnessCertificates.Batch001.certificate33).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch004.certificate50 CountingCertificates.Batch001.certificate33 matches16 MergedCutGroups.Batch004.numericValid50 MergedCutGroups.Batch004.cellsSound50 MergedCutGroups.Batch004.cellsNumeric50 MergedCutGroups.Batch004.populationMatches50
    PopulationCertificates.Batch001.valid33 PopulationCertificates.Batch001.sound33 WitnessCertificates.Batch001.valid33 WitnessCertificates.Batch001.sound33 CountingCertificates.Batch001.valid33 CountingCertificates.Batch001.sound33 H st hI
theorem probabilityBound16 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch004.certificate50).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate33).dm (WitnessCertificates.Batch001.certificate33).beta (WitnessCertificates.Batch001.certificate33).L) ≤ ((CutFailureCertificates.Budget001.certificate33).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound33 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate33).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch004.certificate50).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch001.certificate33).omega:ℝ)) ≤ ((CutFailureCertificates.Budget001.certificate33).bound:ℝ) at hb
  exact (exponentialBound16 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches17 : (MergedCutGroups.Batch004.certificate53).AnchorMatches CountingCertificates.Batch001.certificate35 := by decide +kernel
theorem exponentialBound17 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch004.certificate53).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate35).dm (WitnessCertificates.Batch001.certificate35).beta (WitnessCertificates.Batch001.certificate35).L) ≤ (2*exp (-((CountingCertificates.Batch001.certificate35).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch004.certificate53).exponent:ℝ)*st.R))/((WitnessCertificates.Batch001.certificate35).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch004.certificate53 CountingCertificates.Batch001.certificate35 matches17 MergedCutGroups.Batch004.numericValid53 MergedCutGroups.Batch004.cellsSound53 MergedCutGroups.Batch004.cellsNumeric53 MergedCutGroups.Batch004.populationMatches53
    PopulationCertificates.Batch001.valid35 PopulationCertificates.Batch001.sound35 WitnessCertificates.Batch001.valid35 WitnessCertificates.Batch001.sound35 CountingCertificates.Batch001.valid35 CountingCertificates.Batch001.sound35 H st hI
theorem probabilityBound17 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch004.certificate53).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate35).dm (WitnessCertificates.Batch001.certificate35).beta (WitnessCertificates.Batch001.certificate35).L) ≤ ((CutFailureCertificates.Budget001.certificate35).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound35 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate35).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch004.certificate53).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch001.certificate35).omega:ℝ)) ≤ ((CutFailureCertificates.Budget001.certificate35).bound:ℝ) at hb
  exact (exponentialBound17 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches18 : (MergedCutGroups.Batch004.certificate56).AnchorMatches CountingCertificates.Batch001.certificate37 := by decide +kernel
theorem exponentialBound18 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch004.certificate56).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate37).dm (WitnessCertificates.Batch001.certificate37).beta (WitnessCertificates.Batch001.certificate37).L) ≤ (2*exp (-((CountingCertificates.Batch001.certificate37).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch004.certificate56).exponent:ℝ)*st.R))/((WitnessCertificates.Batch001.certificate37).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch004.certificate56 CountingCertificates.Batch001.certificate37 matches18 MergedCutGroups.Batch004.numericValid56 MergedCutGroups.Batch004.cellsSound56 MergedCutGroups.Batch004.cellsNumeric56 MergedCutGroups.Batch004.populationMatches56
    PopulationCertificates.Batch001.valid37 PopulationCertificates.Batch001.sound37 WitnessCertificates.Batch001.valid37 WitnessCertificates.Batch001.sound37 CountingCertificates.Batch001.valid37 CountingCertificates.Batch001.sound37 H st hI
theorem probabilityBound18 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch004.certificate56).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate37).dm (WitnessCertificates.Batch001.certificate37).beta (WitnessCertificates.Batch001.certificate37).L) ≤ ((CutFailureCertificates.Budget001.certificate37).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound37 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate37).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch004.certificate56).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch001.certificate37).omega:ℝ)) ≤ ((CutFailureCertificates.Budget001.certificate37).bound:ℝ) at hb
  exact (exponentialBound18 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches19 : (MergedCutGroups.Batch004.certificate59).AnchorMatches CountingCertificates.Batch001.certificate39 := by decide +kernel
theorem exponentialBound19 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch004.certificate59).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate39).dm (WitnessCertificates.Batch001.certificate39).beta (WitnessCertificates.Batch001.certificate39).L) ≤ (2*exp (-((CountingCertificates.Batch001.certificate39).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch004.certificate59).exponent:ℝ)*st.R))/((WitnessCertificates.Batch001.certificate39).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch004.certificate59 CountingCertificates.Batch001.certificate39 matches19 MergedCutGroups.Batch004.numericValid59 MergedCutGroups.Batch004.cellsSound59 MergedCutGroups.Batch004.cellsNumeric59 MergedCutGroups.Batch004.populationMatches59
    PopulationCertificates.Batch001.valid39 PopulationCertificates.Batch001.sound39 WitnessCertificates.Batch001.valid39 WitnessCertificates.Batch001.sound39 CountingCertificates.Batch001.valid39 CountingCertificates.Batch001.sound39 H st hI
theorem probabilityBound19 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch004.certificate59).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch001.certificate39).dm (WitnessCertificates.Batch001.certificate39).beta (WitnessCertificates.Batch001.certificate39).L) ≤ ((CutFailureCertificates.Budget001.certificate39).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget001.sound39 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch001.certificate39).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch004.certificate59).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch001.certificate39).omega:ℝ)) ≤ ((CutFailureCertificates.Budget001.certificate39).bound:ℝ) at hb
  exact (exponentialBound19 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch000
