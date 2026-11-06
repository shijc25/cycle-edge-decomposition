import Cycle12.CertifiedAnchorFailure
import Cycle12.CountingCertificates.Batch008
import Cycle12.CountingCertificates.Batch009
import Cycle12.CutFailureCertificates.Budget008
import Cycle12.CutFailureCertificates.Budget009
import Cycle12.MergedCutGroups.Batch020
import Cycle12.MergedCutGroups.Batch021
import Cycle12.MergedCutGroups.Batch022
import Cycle12.MergedCutGroups.Batch023
import Cycle12.MergedCutGroups.Batch024
import Cycle12.PopulationCertificates.Batch008
import Cycle12.PopulationCertificates.Batch009
import Cycle12.WitnessCertificates.Batch008
import Cycle12.WitnessCertificates.Batch009

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.CertifiedAnchorFailures.Batch004
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matches80 : (MergedCutGroups.Batch020.certificate242).AnchorMatches CountingCertificates.Batch008.certificate161 := by decide +kernel
theorem exponentialBound80 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch020.certificate242).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate161).dm (WitnessCertificates.Batch008.certificate161).beta (WitnessCertificates.Batch008.certificate161).L) ≤ (2*exp (-((CountingCertificates.Batch008.certificate161).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch020.certificate242).exponent:ℝ)*st.R))/((WitnessCertificates.Batch008.certificate161).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch020.certificate242 CountingCertificates.Batch008.certificate161 matches80 MergedCutGroups.Batch020.numericValid242 MergedCutGroups.Batch020.cellsSound242 MergedCutGroups.Batch020.cellsNumeric242 MergedCutGroups.Batch020.populationMatches242
    PopulationCertificates.Batch008.valid161 PopulationCertificates.Batch008.sound161 WitnessCertificates.Batch008.valid161 WitnessCertificates.Batch008.sound161 CountingCertificates.Batch008.valid161 CountingCertificates.Batch008.sound161 H st hI
theorem probabilityBound80 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch020.certificate242).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate161).dm (WitnessCertificates.Batch008.certificate161).beta (WitnessCertificates.Batch008.certificate161).L) ≤ ((CutFailureCertificates.Budget008.certificate161).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound161 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate161).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch020.certificate242).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch008.certificate161).omega:ℝ)) ≤ ((CutFailureCertificates.Budget008.certificate161).bound:ℝ) at hb
  exact (exponentialBound80 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches81 : (MergedCutGroups.Batch020.certificate245).AnchorMatches CountingCertificates.Batch008.certificate163 := by decide +kernel
theorem exponentialBound81 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch020.certificate245).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate163).dm (WitnessCertificates.Batch008.certificate163).beta (WitnessCertificates.Batch008.certificate163).L) ≤ (2*exp (-((CountingCertificates.Batch008.certificate163).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch020.certificate245).exponent:ℝ)*st.R))/((WitnessCertificates.Batch008.certificate163).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch020.certificate245 CountingCertificates.Batch008.certificate163 matches81 MergedCutGroups.Batch020.numericValid245 MergedCutGroups.Batch020.cellsSound245 MergedCutGroups.Batch020.cellsNumeric245 MergedCutGroups.Batch020.populationMatches245
    PopulationCertificates.Batch008.valid163 PopulationCertificates.Batch008.sound163 WitnessCertificates.Batch008.valid163 WitnessCertificates.Batch008.sound163 CountingCertificates.Batch008.valid163 CountingCertificates.Batch008.sound163 H st hI
theorem probabilityBound81 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch020.certificate245).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate163).dm (WitnessCertificates.Batch008.certificate163).beta (WitnessCertificates.Batch008.certificate163).L) ≤ ((CutFailureCertificates.Budget008.certificate163).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound163 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate163).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch020.certificate245).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch008.certificate163).omega:ℝ)) ≤ ((CutFailureCertificates.Budget008.certificate163).bound:ℝ) at hb
  exact (exponentialBound81 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches82 : (MergedCutGroups.Batch020.certificate248).AnchorMatches CountingCertificates.Batch008.certificate165 := by decide +kernel
theorem exponentialBound82 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch020.certificate248).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate165).dm (WitnessCertificates.Batch008.certificate165).beta (WitnessCertificates.Batch008.certificate165).L) ≤ (2*exp (-((CountingCertificates.Batch008.certificate165).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch020.certificate248).exponent:ℝ)*st.R))/((WitnessCertificates.Batch008.certificate165).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch020.certificate248 CountingCertificates.Batch008.certificate165 matches82 MergedCutGroups.Batch020.numericValid248 MergedCutGroups.Batch020.cellsSound248 MergedCutGroups.Batch020.cellsNumeric248 MergedCutGroups.Batch020.populationMatches248
    PopulationCertificates.Batch008.valid165 PopulationCertificates.Batch008.sound165 WitnessCertificates.Batch008.valid165 WitnessCertificates.Batch008.sound165 CountingCertificates.Batch008.valid165 CountingCertificates.Batch008.sound165 H st hI
theorem probabilityBound82 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch020.certificate248).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate165).dm (WitnessCertificates.Batch008.certificate165).beta (WitnessCertificates.Batch008.certificate165).L) ≤ ((CutFailureCertificates.Budget008.certificate165).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound165 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate165).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch020.certificate248).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch008.certificate165).omega:ℝ)) ≤ ((CutFailureCertificates.Budget008.certificate165).bound:ℝ) at hb
  exact (exponentialBound82 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches83 : (MergedCutGroups.Batch020.certificate251).AnchorMatches CountingCertificates.Batch008.certificate167 := by decide +kernel
theorem exponentialBound83 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch020.certificate251).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate167).dm (WitnessCertificates.Batch008.certificate167).beta (WitnessCertificates.Batch008.certificate167).L) ≤ (2*exp (-((CountingCertificates.Batch008.certificate167).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch020.certificate251).exponent:ℝ)*st.R))/((WitnessCertificates.Batch008.certificate167).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch020.certificate251 CountingCertificates.Batch008.certificate167 matches83 MergedCutGroups.Batch020.numericValid251 MergedCutGroups.Batch020.cellsSound251 MergedCutGroups.Batch020.cellsNumeric251 MergedCutGroups.Batch020.populationMatches251
    PopulationCertificates.Batch008.valid167 PopulationCertificates.Batch008.sound167 WitnessCertificates.Batch008.valid167 WitnessCertificates.Batch008.sound167 CountingCertificates.Batch008.valid167 CountingCertificates.Batch008.sound167 H st hI
theorem probabilityBound83 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch020.certificate251).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate167).dm (WitnessCertificates.Batch008.certificate167).beta (WitnessCertificates.Batch008.certificate167).L) ≤ ((CutFailureCertificates.Budget008.certificate167).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound167 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate167).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch020.certificate251).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch008.certificate167).omega:ℝ)) ≤ ((CutFailureCertificates.Budget008.certificate167).bound:ℝ) at hb
  exact (exponentialBound83 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches84 : (MergedCutGroups.Batch021.certificate254).AnchorMatches CountingCertificates.Batch008.certificate169 := by decide +kernel
theorem exponentialBound84 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch021.certificate254).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate169).dm (WitnessCertificates.Batch008.certificate169).beta (WitnessCertificates.Batch008.certificate169).L) ≤ (2*exp (-((CountingCertificates.Batch008.certificate169).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch021.certificate254).exponent:ℝ)*st.R))/((WitnessCertificates.Batch008.certificate169).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch021.certificate254 CountingCertificates.Batch008.certificate169 matches84 MergedCutGroups.Batch021.numericValid254 MergedCutGroups.Batch021.cellsSound254 MergedCutGroups.Batch021.cellsNumeric254 MergedCutGroups.Batch021.populationMatches254
    PopulationCertificates.Batch008.valid169 PopulationCertificates.Batch008.sound169 WitnessCertificates.Batch008.valid169 WitnessCertificates.Batch008.sound169 CountingCertificates.Batch008.valid169 CountingCertificates.Batch008.sound169 H st hI
theorem probabilityBound84 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch021.certificate254).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate169).dm (WitnessCertificates.Batch008.certificate169).beta (WitnessCertificates.Batch008.certificate169).L) ≤ ((CutFailureCertificates.Budget008.certificate169).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound169 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate169).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch021.certificate254).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch008.certificate169).omega:ℝ)) ≤ ((CutFailureCertificates.Budget008.certificate169).bound:ℝ) at hb
  exact (exponentialBound84 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches85 : (MergedCutGroups.Batch021.certificate257).AnchorMatches CountingCertificates.Batch008.certificate171 := by decide +kernel
theorem exponentialBound85 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch021.certificate257).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate171).dm (WitnessCertificates.Batch008.certificate171).beta (WitnessCertificates.Batch008.certificate171).L) ≤ (2*exp (-((CountingCertificates.Batch008.certificate171).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch021.certificate257).exponent:ℝ)*st.R))/((WitnessCertificates.Batch008.certificate171).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch021.certificate257 CountingCertificates.Batch008.certificate171 matches85 MergedCutGroups.Batch021.numericValid257 MergedCutGroups.Batch021.cellsSound257 MergedCutGroups.Batch021.cellsNumeric257 MergedCutGroups.Batch021.populationMatches257
    PopulationCertificates.Batch008.valid171 PopulationCertificates.Batch008.sound171 WitnessCertificates.Batch008.valid171 WitnessCertificates.Batch008.sound171 CountingCertificates.Batch008.valid171 CountingCertificates.Batch008.sound171 H st hI
theorem probabilityBound85 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch021.certificate257).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate171).dm (WitnessCertificates.Batch008.certificate171).beta (WitnessCertificates.Batch008.certificate171).L) ≤ ((CutFailureCertificates.Budget008.certificate171).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound171 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate171).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch021.certificate257).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch008.certificate171).omega:ℝ)) ≤ ((CutFailureCertificates.Budget008.certificate171).bound:ℝ) at hb
  exact (exponentialBound85 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches86 : (MergedCutGroups.Batch021.certificate260).AnchorMatches CountingCertificates.Batch008.certificate173 := by decide +kernel
theorem exponentialBound86 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch021.certificate260).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate173).dm (WitnessCertificates.Batch008.certificate173).beta (WitnessCertificates.Batch008.certificate173).L) ≤ (2*exp (-((CountingCertificates.Batch008.certificate173).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch021.certificate260).exponent:ℝ)*st.R))/((WitnessCertificates.Batch008.certificate173).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch021.certificate260 CountingCertificates.Batch008.certificate173 matches86 MergedCutGroups.Batch021.numericValid260 MergedCutGroups.Batch021.cellsSound260 MergedCutGroups.Batch021.cellsNumeric260 MergedCutGroups.Batch021.populationMatches260
    PopulationCertificates.Batch008.valid173 PopulationCertificates.Batch008.sound173 WitnessCertificates.Batch008.valid173 WitnessCertificates.Batch008.sound173 CountingCertificates.Batch008.valid173 CountingCertificates.Batch008.sound173 H st hI
theorem probabilityBound86 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch021.certificate260).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate173).dm (WitnessCertificates.Batch008.certificate173).beta (WitnessCertificates.Batch008.certificate173).L) ≤ ((CutFailureCertificates.Budget008.certificate173).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound173 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate173).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch021.certificate260).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch008.certificate173).omega:ℝ)) ≤ ((CutFailureCertificates.Budget008.certificate173).bound:ℝ) at hb
  exact (exponentialBound86 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches87 : (MergedCutGroups.Batch021.certificate263).AnchorMatches CountingCertificates.Batch008.certificate175 := by decide +kernel
theorem exponentialBound87 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch021.certificate263).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate175).dm (WitnessCertificates.Batch008.certificate175).beta (WitnessCertificates.Batch008.certificate175).L) ≤ (2*exp (-((CountingCertificates.Batch008.certificate175).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch021.certificate263).exponent:ℝ)*st.R))/((WitnessCertificates.Batch008.certificate175).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch021.certificate263 CountingCertificates.Batch008.certificate175 matches87 MergedCutGroups.Batch021.numericValid263 MergedCutGroups.Batch021.cellsSound263 MergedCutGroups.Batch021.cellsNumeric263 MergedCutGroups.Batch021.populationMatches263
    PopulationCertificates.Batch008.valid175 PopulationCertificates.Batch008.sound175 WitnessCertificates.Batch008.valid175 WitnessCertificates.Batch008.sound175 CountingCertificates.Batch008.valid175 CountingCertificates.Batch008.sound175 H st hI
theorem probabilityBound87 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch021.certificate263).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate175).dm (WitnessCertificates.Batch008.certificate175).beta (WitnessCertificates.Batch008.certificate175).L) ≤ ((CutFailureCertificates.Budget008.certificate175).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound175 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate175).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch021.certificate263).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch008.certificate175).omega:ℝ)) ≤ ((CutFailureCertificates.Budget008.certificate175).bound:ℝ) at hb
  exact (exponentialBound87 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches88 : (MergedCutGroups.Batch022.certificate266).AnchorMatches CountingCertificates.Batch008.certificate177 := by decide +kernel
theorem exponentialBound88 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch022.certificate266).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate177).dm (WitnessCertificates.Batch008.certificate177).beta (WitnessCertificates.Batch008.certificate177).L) ≤ (2*exp (-((CountingCertificates.Batch008.certificate177).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch022.certificate266).exponent:ℝ)*st.R))/((WitnessCertificates.Batch008.certificate177).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch022.certificate266 CountingCertificates.Batch008.certificate177 matches88 MergedCutGroups.Batch022.numericValid266 MergedCutGroups.Batch022.cellsSound266 MergedCutGroups.Batch022.cellsNumeric266 MergedCutGroups.Batch022.populationMatches266
    PopulationCertificates.Batch008.valid177 PopulationCertificates.Batch008.sound177 WitnessCertificates.Batch008.valid177 WitnessCertificates.Batch008.sound177 CountingCertificates.Batch008.valid177 CountingCertificates.Batch008.sound177 H st hI
theorem probabilityBound88 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch022.certificate266).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate177).dm (WitnessCertificates.Batch008.certificate177).beta (WitnessCertificates.Batch008.certificate177).L) ≤ ((CutFailureCertificates.Budget008.certificate177).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound177 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate177).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch022.certificate266).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch008.certificate177).omega:ℝ)) ≤ ((CutFailureCertificates.Budget008.certificate177).bound:ℝ) at hb
  exact (exponentialBound88 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches89 : (MergedCutGroups.Batch022.certificate269).AnchorMatches CountingCertificates.Batch008.certificate179 := by decide +kernel
theorem exponentialBound89 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch022.certificate269).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate179).dm (WitnessCertificates.Batch008.certificate179).beta (WitnessCertificates.Batch008.certificate179).L) ≤ (2*exp (-((CountingCertificates.Batch008.certificate179).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch022.certificate269).exponent:ℝ)*st.R))/((WitnessCertificates.Batch008.certificate179).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch022.certificate269 CountingCertificates.Batch008.certificate179 matches89 MergedCutGroups.Batch022.numericValid269 MergedCutGroups.Batch022.cellsSound269 MergedCutGroups.Batch022.cellsNumeric269 MergedCutGroups.Batch022.populationMatches269
    PopulationCertificates.Batch008.valid179 PopulationCertificates.Batch008.sound179 WitnessCertificates.Batch008.valid179 WitnessCertificates.Batch008.sound179 CountingCertificates.Batch008.valid179 CountingCertificates.Batch008.sound179 H st hI
theorem probabilityBound89 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch022.certificate269).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch008.certificate179).dm (WitnessCertificates.Batch008.certificate179).beta (WitnessCertificates.Batch008.certificate179).L) ≤ ((CutFailureCertificates.Budget008.certificate179).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget008.sound179 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch008.certificate179).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch022.certificate269).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch008.certificate179).omega:ℝ)) ≤ ((CutFailureCertificates.Budget008.certificate179).bound:ℝ) at hb
  exact (exponentialBound89 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches90 : (MergedCutGroups.Batch022.certificate272).AnchorMatches CountingCertificates.Batch009.certificate181 := by decide +kernel
theorem exponentialBound90 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch022.certificate272).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate181).dm (WitnessCertificates.Batch009.certificate181).beta (WitnessCertificates.Batch009.certificate181).L) ≤ (2*exp (-((CountingCertificates.Batch009.certificate181).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch022.certificate272).exponent:ℝ)*st.R))/((WitnessCertificates.Batch009.certificate181).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch022.certificate272 CountingCertificates.Batch009.certificate181 matches90 MergedCutGroups.Batch022.numericValid272 MergedCutGroups.Batch022.cellsSound272 MergedCutGroups.Batch022.cellsNumeric272 MergedCutGroups.Batch022.populationMatches272
    PopulationCertificates.Batch009.valid181 PopulationCertificates.Batch009.sound181 WitnessCertificates.Batch009.valid181 WitnessCertificates.Batch009.sound181 CountingCertificates.Batch009.valid181 CountingCertificates.Batch009.sound181 H st hI
theorem probabilityBound90 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch022.certificate272).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate181).dm (WitnessCertificates.Batch009.certificate181).beta (WitnessCertificates.Batch009.certificate181).L) ≤ ((CutFailureCertificates.Budget009.certificate181).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound181 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate181).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch022.certificate272).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch009.certificate181).omega:ℝ)) ≤ ((CutFailureCertificates.Budget009.certificate181).bound:ℝ) at hb
  exact (exponentialBound90 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches91 : (MergedCutGroups.Batch022.certificate275).AnchorMatches CountingCertificates.Batch009.certificate183 := by decide +kernel
theorem exponentialBound91 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch022.certificate275).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate183).dm (WitnessCertificates.Batch009.certificate183).beta (WitnessCertificates.Batch009.certificate183).L) ≤ (2*exp (-((CountingCertificates.Batch009.certificate183).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch022.certificate275).exponent:ℝ)*st.R))/((WitnessCertificates.Batch009.certificate183).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch022.certificate275 CountingCertificates.Batch009.certificate183 matches91 MergedCutGroups.Batch022.numericValid275 MergedCutGroups.Batch022.cellsSound275 MergedCutGroups.Batch022.cellsNumeric275 MergedCutGroups.Batch022.populationMatches275
    PopulationCertificates.Batch009.valid183 PopulationCertificates.Batch009.sound183 WitnessCertificates.Batch009.valid183 WitnessCertificates.Batch009.sound183 CountingCertificates.Batch009.valid183 CountingCertificates.Batch009.sound183 H st hI
theorem probabilityBound91 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch022.certificate275).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate183).dm (WitnessCertificates.Batch009.certificate183).beta (WitnessCertificates.Batch009.certificate183).L) ≤ ((CutFailureCertificates.Budget009.certificate183).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound183 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate183).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch022.certificate275).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch009.certificate183).omega:ℝ)) ≤ ((CutFailureCertificates.Budget009.certificate183).bound:ℝ) at hb
  exact (exponentialBound91 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches92 : (MergedCutGroups.Batch023.certificate278).AnchorMatches CountingCertificates.Batch009.certificate185 := by decide +kernel
theorem exponentialBound92 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch023.certificate278).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate185).dm (WitnessCertificates.Batch009.certificate185).beta (WitnessCertificates.Batch009.certificate185).L) ≤ (2*exp (-((CountingCertificates.Batch009.certificate185).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch023.certificate278).exponent:ℝ)*st.R))/((WitnessCertificates.Batch009.certificate185).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch023.certificate278 CountingCertificates.Batch009.certificate185 matches92 MergedCutGroups.Batch023.numericValid278 MergedCutGroups.Batch023.cellsSound278 MergedCutGroups.Batch023.cellsNumeric278 MergedCutGroups.Batch023.populationMatches278
    PopulationCertificates.Batch009.valid185 PopulationCertificates.Batch009.sound185 WitnessCertificates.Batch009.valid185 WitnessCertificates.Batch009.sound185 CountingCertificates.Batch009.valid185 CountingCertificates.Batch009.sound185 H st hI
theorem probabilityBound92 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch023.certificate278).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate185).dm (WitnessCertificates.Batch009.certificate185).beta (WitnessCertificates.Batch009.certificate185).L) ≤ ((CutFailureCertificates.Budget009.certificate185).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound185 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate185).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch023.certificate278).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch009.certificate185).omega:ℝ)) ≤ ((CutFailureCertificates.Budget009.certificate185).bound:ℝ) at hb
  exact (exponentialBound92 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches93 : (MergedCutGroups.Batch023.certificate281).AnchorMatches CountingCertificates.Batch009.certificate187 := by decide +kernel
theorem exponentialBound93 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch023.certificate281).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate187).dm (WitnessCertificates.Batch009.certificate187).beta (WitnessCertificates.Batch009.certificate187).L) ≤ (2*exp (-((CountingCertificates.Batch009.certificate187).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch023.certificate281).exponent:ℝ)*st.R))/((WitnessCertificates.Batch009.certificate187).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch023.certificate281 CountingCertificates.Batch009.certificate187 matches93 MergedCutGroups.Batch023.numericValid281 MergedCutGroups.Batch023.cellsSound281 MergedCutGroups.Batch023.cellsNumeric281 MergedCutGroups.Batch023.populationMatches281
    PopulationCertificates.Batch009.valid187 PopulationCertificates.Batch009.sound187 WitnessCertificates.Batch009.valid187 WitnessCertificates.Batch009.sound187 CountingCertificates.Batch009.valid187 CountingCertificates.Batch009.sound187 H st hI
theorem probabilityBound93 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch023.certificate281).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate187).dm (WitnessCertificates.Batch009.certificate187).beta (WitnessCertificates.Batch009.certificate187).L) ≤ ((CutFailureCertificates.Budget009.certificate187).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound187 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate187).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch023.certificate281).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch009.certificate187).omega:ℝ)) ≤ ((CutFailureCertificates.Budget009.certificate187).bound:ℝ) at hb
  exact (exponentialBound93 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches94 : (MergedCutGroups.Batch023.certificate284).AnchorMatches CountingCertificates.Batch009.certificate189 := by decide +kernel
theorem exponentialBound94 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch023.certificate284).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate189).dm (WitnessCertificates.Batch009.certificate189).beta (WitnessCertificates.Batch009.certificate189).L) ≤ (2*exp (-((CountingCertificates.Batch009.certificate189).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch023.certificate284).exponent:ℝ)*st.R))/((WitnessCertificates.Batch009.certificate189).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch023.certificate284 CountingCertificates.Batch009.certificate189 matches94 MergedCutGroups.Batch023.numericValid284 MergedCutGroups.Batch023.cellsSound284 MergedCutGroups.Batch023.cellsNumeric284 MergedCutGroups.Batch023.populationMatches284
    PopulationCertificates.Batch009.valid189 PopulationCertificates.Batch009.sound189 WitnessCertificates.Batch009.valid189 WitnessCertificates.Batch009.sound189 CountingCertificates.Batch009.valid189 CountingCertificates.Batch009.sound189 H st hI
theorem probabilityBound94 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch023.certificate284).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate189).dm (WitnessCertificates.Batch009.certificate189).beta (WitnessCertificates.Batch009.certificate189).L) ≤ ((CutFailureCertificates.Budget009.certificate189).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound189 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate189).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch023.certificate284).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch009.certificate189).omega:ℝ)) ≤ ((CutFailureCertificates.Budget009.certificate189).bound:ℝ) at hb
  exact (exponentialBound94 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches95 : (MergedCutGroups.Batch023.certificate287).AnchorMatches CountingCertificates.Batch009.certificate191 := by decide +kernel
theorem exponentialBound95 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch023.certificate287).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate191).dm (WitnessCertificates.Batch009.certificate191).beta (WitnessCertificates.Batch009.certificate191).L) ≤ (2*exp (-((CountingCertificates.Batch009.certificate191).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch023.certificate287).exponent:ℝ)*st.R))/((WitnessCertificates.Batch009.certificate191).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch023.certificate287 CountingCertificates.Batch009.certificate191 matches95 MergedCutGroups.Batch023.numericValid287 MergedCutGroups.Batch023.cellsSound287 MergedCutGroups.Batch023.cellsNumeric287 MergedCutGroups.Batch023.populationMatches287
    PopulationCertificates.Batch009.valid191 PopulationCertificates.Batch009.sound191 WitnessCertificates.Batch009.valid191 WitnessCertificates.Batch009.sound191 CountingCertificates.Batch009.valid191 CountingCertificates.Batch009.sound191 H st hI
theorem probabilityBound95 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch023.certificate287).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate191).dm (WitnessCertificates.Batch009.certificate191).beta (WitnessCertificates.Batch009.certificate191).L) ≤ ((CutFailureCertificates.Budget009.certificate191).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound191 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate191).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch023.certificate287).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch009.certificate191).omega:ℝ)) ≤ ((CutFailureCertificates.Budget009.certificate191).bound:ℝ) at hb
  exact (exponentialBound95 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches96 : (MergedCutGroups.Batch024.certificate290).AnchorMatches CountingCertificates.Batch009.certificate193 := by decide +kernel
theorem exponentialBound96 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch024.certificate290).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate193).dm (WitnessCertificates.Batch009.certificate193).beta (WitnessCertificates.Batch009.certificate193).L) ≤ (2*exp (-((CountingCertificates.Batch009.certificate193).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch024.certificate290).exponent:ℝ)*st.R))/((WitnessCertificates.Batch009.certificate193).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch024.certificate290 CountingCertificates.Batch009.certificate193 matches96 MergedCutGroups.Batch024.numericValid290 MergedCutGroups.Batch024.cellsSound290 MergedCutGroups.Batch024.cellsNumeric290 MergedCutGroups.Batch024.populationMatches290
    PopulationCertificates.Batch009.valid193 PopulationCertificates.Batch009.sound193 WitnessCertificates.Batch009.valid193 WitnessCertificates.Batch009.sound193 CountingCertificates.Batch009.valid193 CountingCertificates.Batch009.sound193 H st hI
theorem probabilityBound96 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch024.certificate290).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate193).dm (WitnessCertificates.Batch009.certificate193).beta (WitnessCertificates.Batch009.certificate193).L) ≤ ((CutFailureCertificates.Budget009.certificate193).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound193 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate193).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch024.certificate290).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch009.certificate193).omega:ℝ)) ≤ ((CutFailureCertificates.Budget009.certificate193).bound:ℝ) at hb
  exact (exponentialBound96 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches97 : (MergedCutGroups.Batch024.certificate293).AnchorMatches CountingCertificates.Batch009.certificate195 := by decide +kernel
theorem exponentialBound97 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch024.certificate293).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate195).dm (WitnessCertificates.Batch009.certificate195).beta (WitnessCertificates.Batch009.certificate195).L) ≤ (2*exp (-((CountingCertificates.Batch009.certificate195).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch024.certificate293).exponent:ℝ)*st.R))/((WitnessCertificates.Batch009.certificate195).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch024.certificate293 CountingCertificates.Batch009.certificate195 matches97 MergedCutGroups.Batch024.numericValid293 MergedCutGroups.Batch024.cellsSound293 MergedCutGroups.Batch024.cellsNumeric293 MergedCutGroups.Batch024.populationMatches293
    PopulationCertificates.Batch009.valid195 PopulationCertificates.Batch009.sound195 WitnessCertificates.Batch009.valid195 WitnessCertificates.Batch009.sound195 CountingCertificates.Batch009.valid195 CountingCertificates.Batch009.sound195 H st hI
theorem probabilityBound97 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch024.certificate293).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate195).dm (WitnessCertificates.Batch009.certificate195).beta (WitnessCertificates.Batch009.certificate195).L) ≤ ((CutFailureCertificates.Budget009.certificate195).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound195 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate195).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch024.certificate293).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch009.certificate195).omega:ℝ)) ≤ ((CutFailureCertificates.Budget009.certificate195).bound:ℝ) at hb
  exact (exponentialBound97 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches98 : (MergedCutGroups.Batch024.certificate296).AnchorMatches CountingCertificates.Batch009.certificate197 := by decide +kernel
theorem exponentialBound98 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch024.certificate296).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate197).dm (WitnessCertificates.Batch009.certificate197).beta (WitnessCertificates.Batch009.certificate197).L) ≤ (2*exp (-((CountingCertificates.Batch009.certificate197).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch024.certificate296).exponent:ℝ)*st.R))/((WitnessCertificates.Batch009.certificate197).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch024.certificate296 CountingCertificates.Batch009.certificate197 matches98 MergedCutGroups.Batch024.numericValid296 MergedCutGroups.Batch024.cellsSound296 MergedCutGroups.Batch024.cellsNumeric296 MergedCutGroups.Batch024.populationMatches296
    PopulationCertificates.Batch009.valid197 PopulationCertificates.Batch009.sound197 WitnessCertificates.Batch009.valid197 WitnessCertificates.Batch009.sound197 CountingCertificates.Batch009.valid197 CountingCertificates.Batch009.sound197 H st hI
theorem probabilityBound98 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch024.certificate296).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate197).dm (WitnessCertificates.Batch009.certificate197).beta (WitnessCertificates.Batch009.certificate197).L) ≤ ((CutFailureCertificates.Budget009.certificate197).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound197 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate197).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch024.certificate296).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch009.certificate197).omega:ℝ)) ≤ ((CutFailureCertificates.Budget009.certificate197).bound:ℝ) at hb
  exact (exponentialBound98 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

theorem matches99 : (MergedCutGroups.Batch024.certificate299).AnchorMatches CountingCertificates.Batch009.certificate199 := by decide +kernel
theorem exponentialBound99 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch024.certificate299).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate199).dm (WitnessCertificates.Batch009.certificate199).beta (WitnessCertificates.Batch009.certificate199).L) ≤ (2*exp (-((CountingCertificates.Batch009.certificate199).aa:ℝ)*st.R)+2*exp (-((MergedCutGroups.Batch024.certificate299).exponent:ℝ)*st.R))/((WitnessCertificates.Batch009.certificate199).omega:ℝ) :=
  certified_anchor_failure MergedCutGroups.Batch024.certificate299 CountingCertificates.Batch009.certificate199 matches99 MergedCutGroups.Batch024.numericValid299 MergedCutGroups.Batch024.cellsSound299 MergedCutGroups.Batch024.cellsNumeric299 MergedCutGroups.Batch024.populationMatches299
    PopulationCertificates.Batch009.valid199 PopulationCertificates.Batch009.sound199 WitnessCertificates.Batch009.valid199 WitnessCertificates.Batch009.sound199 CountingCertificates.Batch009.valid199 CountingCertificates.Batch009.sound199 H st hI
theorem probabilityBound99 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (st : CoverMarkedGraphState (MergedCutGroups.Batch024.certificate299).geometry H) (hI : CoverSparseCutIrreducible H) :
    (fixedSizeLaw (univ:Finset V) st.N).prob (FixedAnchorFailure H st.N st.z (WitnessCertificates.Batch009.certificate199).dm (WitnessCertificates.Batch009.certificate199).beta (WitnessCertificates.Batch009.certificate199).L) ≤ ((CutFailureCertificates.Budget009.certificate199).bound:ℝ) := by
  have hb := CutFailureCertificates.Budget009.sound199 st.R st.scale_lower
  change ((((2:ℚ):ℝ)*exp (-((CountingCertificates.Batch009.certificate199).aa:ℝ)*st.R)+(((2:ℚ):ℝ)*exp (-((MergedCutGroups.Batch024.certificate299).exponent:ℝ)*st.R)+0))/((WitnessCertificates.Batch009.certificate199).omega:ℝ)) ≤ ((CutFailureCertificates.Budget009.certificate199).bound:ℝ) at hb
  exact (exponentialBound99 H st hI).trans (by simpa only [Rat.cast_ofNat,add_zero] using hb)

end
end Cycle12.CertifiedAnchorFailures.Batch004
